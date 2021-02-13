use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet};
use std::io::Write;
use std::path::{Path, PathBuf};
use std::rc::Rc;

use anyhow::bail;
use canonical_path::CanonicalPathBuf;
use clap::{ArgSettings, Clap};
use libpijul::pristine::*;
use libpijul::*;
use log::{debug, error, info, trace};

use crate::repository::*;

#[derive(Clap, Debug)]
pub struct Git {
    /// Process this path instead of the current directory, creating a Pijul repository if necessary.
    pub repo_path: Option<PathBuf>,
    /// Time the import, and output values to this file.
    #[clap(long = "stats", setting = ArgSettings::Hidden)]
    stats: Option<PathBuf>,
    /// Check only the first n commits processed.
    #[clap(default_value = "0", setting = ArgSettings::Hidden)]
    check: usize,
}

struct OpenRepo {
    repo: Repository,
    stats: Option<std::fs::File>,
    n: usize,
    check: usize,
    current_commit: Option<git2::Oid>,
}

impl Git {
    pub async fn run(self) -> Result<(), anyhow::Error> {
        let repo = if let Ok(repo) = Repository::find_root(self.repo_path.clone()).await {
            repo
        } else {
            Repository::init(self.repo_path.clone()).await?
        };
        let git = git2::Repository::open(&repo.path)?;
        let head = git.head()?;
        info!("Loading history…");
        let oid = head.target().unwrap();
        let mut path_git = repo.path.join(libpijul::DOT_DIR);
        path_git.push("git");
        std::fs::create_dir_all(&path_git)?;
        let mut env_git = ::sanakirja::Env::new(&path_git, 1 << 15)?;
        let dag = Dag::dfs(&git, oid, &mut env_git)?;

        trace!(target: "dag", "{:?}", dag);
        info!("Done");
        let mut pristine = repo.path.join(DOT_DIR);
        pristine.push(PRISTINE_DIR);
        std::fs::create_dir_all(&pristine)?;
        let mut repo = OpenRepo {
            repo,
            stats: self.stats.and_then(|f| std::fs::File::create(f).ok()),
            n: 0,
            check: self.check,
            current_commit: None,
        };
        import(&git, &mut env_git, &mut repo, &dag).await?;
        Ok(())
    }
}

#[derive(Debug)]
struct Dag {
    children: BTreeMap<git2::Oid, Vec<git2::Oid>>,
    parents: BTreeMap<git2::Oid, Vec<git2::Oid>>,
    root: Vec<(git2::Oid, Option<libpijul::Merkle>)>,
}

impl Dag {
    /// Load a Git repository in memory. The main reason this is
    /// needed is to compute the *backward* relations from a commit to
    /// its parents.
    fn dfs(
        git: &git2::Repository,
        oid: git2::Oid,
        env_git: &mut ::sanakirja::Env<::sanakirja::Exclusive>,
    ) -> Result<Self, anyhow::Error> {
        use ::sanakirja::Transaction;
        let mut stack = vec![git.find_commit(oid)?];
        let mut oids_set = BTreeSet::new();
        let mut dag = Dag {
            children: BTreeMap::new(),
            parents: BTreeMap::new(),
            root: Vec::new(),
        };
        oids_set.insert(oid.clone());
        let mut txn_git = ::sanakirja::Env::mut_txn_begin(env_git)?;
        let db: ::sanakirja::Db<git2::Oid, libpijul::Merkle> = if let Some(db) = txn_git.root(0) {
            db
        } else {
            txn_git.create_db()?
        };
        let mut state = BTreeMap::new();
        for x in txn_git.iter(&db, None)? {
            let (commit, merk) = x?;
            state.insert(commit, merk);
        }
        debug!("state = {:?}", state);
        while let Some(commit) = stack.pop() {
            if let Some(state) = state.get(&commit.id()) {
                dag.root.push((commit.id(), Some(*state)));
                continue;
            }
            let mut has_parents = false;
            for p in commit.parents() {
                trace!("parent {:?}", p);
                dag.children
                    .entry(p.id())
                    .or_insert(Vec::new())
                    .push(commit.id());
                dag.parents
                    .entry(commit.id())
                    .or_insert(Vec::new())
                    .push(p.id());
                if oids_set.insert(p.id()) {
                    stack.push(p);
                }
                has_parents = true
            }
            if !has_parents {
                dag.root.push((commit.id(), None))
            }
        }
        txn_git.set_root(0, db);
        ::sanakirja::Commit::commit(txn_git)?;
        Ok(dag)
    }

    fn collect_dead_parents<T: MutTxnTExt>(
        &self,
        oid: &git2::Oid,
        todo: &mut Todo,
        txn: &mut T,
    ) -> Result<(), anyhow::Error> {
        if let Some(parents) = self.parents.get(oid) {
            debug!("parents {:?}", parents);
            for p in parents {
                let rc = todo.refs.get_mut(p).unwrap();
                *rc -= 1;
                if *rc == 0 {
                    let p_name = format!("{}", p);
                    debug!("dropping channel {:?}", p_name);
                    txn.drop_channel(&p_name)?;
                }
            }
        }
        Ok(())
    }

    fn insert_children_in_todo(&self, oid: &git2::Oid, todo: &mut Todo) {
        if let Some(c) = self.children.get(&oid) {
            for child in c {
                debug!("child = {:?}", c);
                if todo.next_todo_set.insert(*child) {
                    todo.next_todo.push(*child);
                }
                *todo.refs.entry(*oid).or_insert(0) += 1;
            }
        } else {
            debug!("no children")
        }
    }
}

#[derive(Debug)]
struct Todo {
    todo: Vec<git2::Oid>,
    todo_set: BTreeSet<git2::Oid>,
    next_todo: Vec<git2::Oid>,
    next_todo_set: BTreeSet<git2::Oid>,
    // For each key k, number of items in the union of todo and
    // next_todo that have k as a parent. Moreover, all commits that
    // were imported are in this map.
    refs: BTreeMap<git2::Oid, usize>,
}

impl Todo {
    fn new() -> Self {
        Todo {
            todo: Vec::new(),
            todo_set: BTreeSet::new(),
            next_todo: Vec::new(),
            next_todo_set: BTreeSet::new(),
            refs: BTreeMap::new(),
        }
    }

    fn swap_next(&mut self, todo: Vec<git2::Oid>) {
        self.todo = todo;
        std::mem::swap(&mut self.todo, &mut self.next_todo);
        self.todo_set.clear();
        std::mem::swap(&mut self.todo_set, &mut self.next_todo_set);
    }

    fn insert_next(&mut self, oid: git2::Oid) {
        if self.next_todo_set.insert(oid) {
            self.next_todo.push(oid)
        }
    }

    fn is_empty(&self) -> bool {
        self.todo.is_empty()
    }

    fn all_processed(&self, parents: &[git2::Oid]) -> bool {
        parents.iter().all(|x| self.refs.contains_key(x))
    }
}

/// Import the entire Git DAG into Pijul.
async fn import(
    git: &git2::Repository,
    env_git: &mut ::sanakirja::Env<::sanakirja::Exclusive>,
    repo: &mut OpenRepo,
    dag: &Dag,
) -> Result<(), anyhow::Error> {
    let mut ws = libpijul::ApplyWorkspace::new();
    let mut todo = Todo::new();

    let txn = repo.repo.pristine.mut_txn_begin();
    for &(oid, merkle) in dag.root.iter() {
        if let Some(merkle) = merkle {
            let oid_ = format!("{}", oid);
            let channel = txn.load_channel(&oid_)?.unwrap();
            let (_, (_, merkle_)) = txn
                .changeid_reverse_log(&channel.borrow(), None)?
                .next()
                .unwrap()?;
            if merkle != merkle_ {
                bail!("Pijul channel changed since last import. Please unrecord channel {} to state {}", oid_, merkle.to_base32())
            }
            if let Some(children) = dag.children.get(&oid) {
                *todo.refs.entry(oid).or_insert(0) += children.len();
                for c in children.iter() {
                    todo.insert_next(*c);
                }
            }
        } else {
            todo.insert_next(oid);
            if let Some(parents) = dag.parents.get(&oid) {
                for p in parents.iter() {
                    *todo.refs.entry(*p).or_insert(0) += 1;
                }
            }
        }
    }
    std::mem::drop(txn);
    todo.swap_next(Vec::new());

    while !todo.is_empty() {
        debug!("TODO: {:?}", todo);
        let mut todo_ = std::mem::replace(&mut todo.todo, Vec::new());
        {
            let mut txn = repo.repo.pristine.mut_txn_begin();
            let mut draining = todo_.drain(..);
            while let Some(oid) = draining.next() {
                let mut channel = if let Some(parents) = dag.parents.get(&oid) {
                    // If we don't have all the parents, continue.
                    if !todo.all_processed(&parents) {
                        todo.insert_next(oid);
                        continue;
                    }
                    let first_parent = parents.iter().next().unwrap();
                    let parent_name = format!("{}", first_parent);
                    let parent_channel = txn.load_channel(&parent_name)?.unwrap();

                    let name = format!("{}", oid);
                    let channel = txn.fork(&parent_channel, &name)?;

                    channel
                } else {
                    // Create a new channel for this commit.
                    let name = format!("{}", oid);
                    let channel = txn.open_or_create_channel(&name)?;
                    channel
                };

                let mut stats = Stats::new(oid);
                import_commit_parents(
                    repo,
                    dag,
                    &mut txn,
                    &mut channel,
                    &oid,
                    &mut ws,
                    &mut stats,
                )?;
                let state = import_commit(git, repo, &mut txn, &mut channel, &oid, &mut stats)?;
                save_state(env_git, &oid, state)?;
                dag.collect_dead_parents(&oid, &mut todo, &mut txn)?;
                dag.insert_children_in_todo(&oid, &mut todo);

                if let Some(ref mut f) = repo.stats {
                    stats.write(repo.n, &repo.repo.path, f)?
                }
                // Just add the remaining commits to the todo list,
                // because we prefer to move each channel as far as
                // possible before switching channels.
                while let Some(oid) = draining.next() {
                    todo.insert_next(oid)
                }
            }
            txn.commit()?;
            repo.repo.lock.commit().await?;
        }
        todo.swap_next(todo_)
    }
    Ok(())
}

fn save_state(
    git: &mut ::sanakirja::Env<::sanakirja::Exclusive>,
    oid: &git2::Oid,
    state: libpijul::Merkle,
) -> Result<(), anyhow::Error> {
    use ::sanakirja::{Commit, Transaction};
    let mut txn = ::sanakirja::Env::mut_txn_begin(git)?;
    let mut db: ::sanakirja::Db<git2::Oid, libpijul::Merkle> = if let Some(db) = txn.root(0) {
        db
    } else {
        txn.create_db()?
    };
    txn.put(&mut rand::thread_rng(), &mut db, *oid, state)?;
    txn.set_root(0, db);
    txn.commit()?;
    Ok(())
}

fn make_apply_plan<T: TxnTExt>(
    repo: &OpenRepo,
    txn: &T,
    channel: &ChannelRef<T>,
    dag: &Dag,
    oid: &git2::Oid,
) -> Result<(bool, Vec<(libpijul::Hash, u64)>), anyhow::Error> {
    let mut to_apply = Vec::new();
    let mut to_apply_set = BTreeSet::new();
    let mut needs_output = false;
    if let Some(parents) = dag.parents.get(&oid) {
        for p in parents {
            // If one of the parents is not the repo's current commit,
            // then we're doing either a merge or a checkout of
            // another branch. If that is the case, we need to output
            // the entire repository to update the
            // tree/revtree/inodes/revinodes tables.
            if let Some(current_commit) = repo.current_commit {
                if current_commit != *p {
                    needs_output = true
                }
            }
            let p_name = format!("{}", p);
            let p_channel = txn.load_channel(&p_name)?.unwrap();
            for x in txn.log(&p_channel.borrow(), 0)? {
                let (n, (h, _)) = x?;
                if txn.has_change(&channel, h)?.is_none() {
                    if to_apply_set.insert(h) {
                        to_apply.push((h, n));
                    }
                }
            }
        }
    } else {
        needs_output = true
    }

    // Since we're pulling from multiple channels, the change numbers
    // are not necessarily in order (especially since we've
    // de-duplicated using `to_apply_set`.

    to_apply.sort_by(|a, b| a.1.cmp(&b.1));
    Ok((needs_output, to_apply))
}

/// Apply the changes corresponding to a commit's parents to `channel`.
fn import_commit_parents<T: TxnTExt + MutTxnTExt + GraphIter>(
    repo: &mut OpenRepo,
    dag: &Dag,
    txn: &mut T,
    channel: &mut ChannelRef<T>,
    oid: &git2::Oid,
    ws: &mut libpijul::ApplyWorkspace,
    stats: &mut Stats,
) -> Result<(), anyhow::Error> {
    // Apply all the parent's logs to `channel`
    let (needs_output, to_apply) = make_apply_plan(repo, txn, channel, dag, oid)?;
    let parent_application_time = std::time::Instant::now();
    for h in to_apply.iter() {
        debug!("to_apply {:?}", h)
    }
    for (h, _) in to_apply.iter() {
        info!("applying {:?} to {:?}", h, txn.name(&channel.borrow()));

        txn.apply_change_ws(&repo.repo.changes, channel, *h, ws)?;
        if repo.check > 0 && repo.n % repo.check == 0 {
            check_alive_debug(&repo.repo.changes, txn, &channel.borrow(), line!())?;
        }
    }
    if repo.check > 0 && repo.n % repo.check == 0 {
        check_alive_debug(&repo.repo.changes, txn, &channel.borrow(), line!())?;
    }
    stats.parent_application_time = if to_apply.is_empty() {
        std::time::Duration::from_secs(0)
    } else {
        parent_application_time.elapsed()
    };
    debug!(
        "last_recorded {:?}, name {:?}",
        repo.repo.config.current_channel,
        txn.name(&channel.borrow()),
    );
    stats.output_time = if !to_apply.is_empty() || needs_output {
        debug!("outputting");
        let output_time = std::time::Instant::now();
        txn.output_repository_no_pending(
            &mut repo.repo.working_copy,
            &repo.repo.changes,
            channel,
            "",
            false,
            None,
        )?;
        let t = output_time.elapsed();
        if repo.check > 0 && repo.n % repo.check == 0 {
            check_alive_debug(&repo.repo.changes, txn, &channel.borrow(), line!())?;
        }
        t
    } else {
        std::time::Duration::from_secs(0)
    };
    if repo.check > 0 && repo.n % repo.check == 0 {
        check_tree_inodes(txn, txn.graph(&channel.borrow()));
    }
    Ok(())
}

/// Reset to the Git commit specified by `child`, telling Pijul which
/// files were moved in the reset.
fn git_reset<'a, T: TxnTExt + MutTxnTExt>(
    git: &'a git2::Repository,
    repo: &mut OpenRepo,

    txn: &mut T,
    channel: &mut ChannelRef<T>,

    child: &git2::Oid,

    stats: &mut Stats,
) -> Result<(git2::Object<'a>, BTreeSet<PathBuf>), anyhow::Error> {
    // Reset the Git branch.
    debug!("resetting the git branch to {:?}", child);
    let reset_time = std::time::Instant::now();
    let object = git.find_object(*child, None)?;
    let reset_was_useful = Rc::new(RefCell::new(false));
    let mut builder = git2::build::CheckoutBuilder::new();
    let repo_path = repo.repo.path.clone();
    let reset_was_useful_ = reset_was_useful.clone();
    builder
        .force()
        .remove_untracked(true)
        .remove_ignored(true)
        .progress(move |file, a, b| {
            debug!("Git progress: {:?} {:?} {:?}", file, a, b);
            if let Some(file) = file {
                let file = repo_path.join(file);
                if let Ok(meta) = std::fs::metadata(&file) {
                    if !meta.file_type().is_symlink() {
                        *reset_was_useful_.borrow_mut() = true
                    }
                }
            }
        });
    builder.notify(|notif, file, _, _, _| {
        info!("Git reset: {:?} {:?}", notif, file);
        true
    });
    git.reset(&object, git2::ResetType::Hard, Some(&mut builder))?;
    repo.current_commit = Some(*child);
    stats.reset_time = reset_time.elapsed();
    debug!("reset done");

    let mut prefixes = BTreeSet::new();
    {
        let commit = object.as_commit().unwrap();
        let new_tree = commit.tree().unwrap();

        debug!("inspecting commit");
        let git_diff_time = std::time::Instant::now();
        for parent in commit.parents() {
            let old_tree = parent.tree().unwrap();
            let mut diff = git
                .diff_tree_to_tree(Some(&old_tree), Some(&new_tree), None)
                .unwrap();
            diff.find_similar(None).unwrap();
            let mut moves = Vec::new();
            for delta in diff.deltas() {
                let old_path = delta.old_file().path().unwrap();
                let new_path = delta.new_file().path().unwrap();
                match delta.status() {
                    git2::Delta::Renamed => {
                        info!(
                            "mv {:?} {:?}",
                            old_path.to_string_lossy(),
                            new_path.to_string_lossy()
                        );
                        if let Ok((vertex, _)) = txn.follow_oldest_path(
                            &repo.repo.changes,
                            &channel,
                            &old_path.to_string_lossy(),
                        ) {
                            if let Some(inode) = txn.get_revinodes(vertex, None)? {
                                if let Some(old_path) = libpijul::fs::inode_filename(txn, inode)? {
                                    debug!(
                                        "moving {:?} ({:?}) from {:?} to {:?}",
                                        inode, vertex, old_path, new_path
                                    );
                                    let mut tmp_path = new_path.to_path_buf();
                                    tmp_path.pop();
                                    use rand::Rng;
                                    let s: String = rand::thread_rng()
                                        .sample_iter(&rand::distributions::Alphanumeric)
                                        .take(30)
                                        .map(|x| x as char)
                                        .collect();
                                    tmp_path.push(&s);
                                    if let Err(e) =
                                        txn.move_file(&old_path, &tmp_path.to_string_lossy())
                                    {
                                        error!("{}", e);
                                    } else {
                                        moves.push((tmp_path, new_path));
                                    }
                                }
                            }
                        }
                        let new_path = new_path.to_path_buf();
                        prefixes.insert(new_path);
                    }
                    git2::Delta::Deleted => {
                        let old_path = old_path.to_path_buf();
                        prefixes.insert(old_path);
                    }
                    _ => {
                        if delta.new_file().mode() != git2::FileMode::Link {
                            debug!("delta old = {:?} new = {:?}", old_path, new_path);
                            let old_path = old_path.to_path_buf();
                            let new_path = new_path.to_path_buf();
                            prefixes.insert(old_path);
                            prefixes.insert(new_path);
                        }
                    }
                }
            }
            debug!("moves = {:?}", moves);
            for (a, b) in moves.drain(..) {
                if let Err(e) = txn.move_file(&a.to_string_lossy(), &b.to_string_lossy()) {
                    error!("{}", e);
                }
            }
        }
        stats.git_diff_time = git_diff_time.elapsed();
        debug!("done inspecting commit");
        if prefixes.contains(std::path::Path::new("")) {
            prefixes.clear();
        }
        // Root has no parents so record everything
        if prefixes.is_empty() {
            prefixes.insert(repo.repo.path.clone());
        }
        debug!("record prefixes {:?}", prefixes);
    }
    Ok((object, prefixes))
}

/// Reset to the Git commit specified as `child`, and record the
/// corresponding change in Pijul.
fn import_commit<T: TxnTExt + MutTxnTExt + GraphIter>(
    git: &git2::Repository,
    repo: &mut OpenRepo,
    txn: &mut T,
    channel: &mut ChannelRef<T>,
    child: &git2::Oid,
    stats: &mut Stats,
) -> Result<libpijul::Merkle, anyhow::Error> {
    let (object, prefixes) = git_reset(git, repo, txn, channel, child, stats)?;
    for p in prefixes.iter() {
        if let Ok(m) = std::fs::metadata(&p) {
            if m.is_dir() {
                txn.add_dir(p.to_str().unwrap()).unwrap_or(());
            } else {
                txn.add_file(p.to_str().unwrap()).unwrap_or(());
            }
        }
    }
    let commit = object.as_commit().unwrap();
    let signature = commit.author();
    // Record+Apply
    debug!("recording on channel {:?}", txn.name(&channel.borrow()));
    let record_time = std::time::Instant::now();

    let prefix_vec: Vec<_> = prefixes.into_iter().collect();
    if let Some(msg) = commit.message() {
        info!("Importing commit {:?}: {}", child, msg);
    } else {
        info!("Importing commit {:?} (no message)", child);
    }
    let rec = record_apply(
        txn,
        channel,
        &mut repo.repo.working_copy,
        &repo.repo.changes,
        &CanonicalPathBuf::canonicalize(&repo.repo.path)?,
        &prefix_vec,
        libpijul::change::ChangeHeader {
            message: commit.message().unwrap().to_string(),
            authors: vec![libpijul::change::Author {
                name: signature.name().unwrap().to_string(),
                email: signature.email().map(|e| e.to_string()),
                full_name: None,
            }],
            description: None,
            timestamp: chrono::DateTime::from_utc(
                chrono::NaiveDateTime::from_timestamp(signature.when().seconds(), 0),
                chrono::Utc,
            ),
        },
    );
    let (n_actions, hash, state) = match rec {
        Ok(x) => x,
        Err(libpijul::LocalApplyError::ChangeAlreadyOnChannel { hash }) => {
            error!("change already on channel: {:?}", hash);
            return Ok(txn.current_state(&channel.borrow())?);
        }
        Err(e) => return Err(e.into()),
    };
    stats.record_time = record_time.elapsed();

    if repo.check > 0 && repo.n % repo.check == 0 {
        check_alive_debug(&repo.repo.changes, txn, &channel.borrow(), line!())?;
    }

    stats.n_actions = n_actions;
    stats.hash = hash;

    if let Some(ref mut cur) = repo.repo.config.current_channel {
        cur.clear();
        cur.push_str(txn.name(&channel.borrow()));
    } else {
        repo.repo.config.current_channel = Some(txn.name(&channel.borrow()).to_string())
    }
    repo.repo.save_config()?;

    if repo.check > 0 && repo.n % repo.check == 0 {
        check_tree_inodes(txn, txn.graph(&channel.borrow()));
    }
    repo.n += 1;
    Ok(state)
}

fn record_apply<T: TxnT + TxnTExt + MutTxnTExt, C: libpijul::changestore::ChangeStore>(
    txn: &mut T,
    channel: &mut ChannelRef<T>,
    working_copy: &mut libpijul::working_copy::FileSystem,
    changes: &C,
    repo_path: &CanonicalPathBuf,
    prefixes: &[PathBuf],
    header: libpijul::change::ChangeHeader,
) -> Result<
    (usize, Option<libpijul::Hash>, libpijul::Merkle),
    libpijul::LocalApplyError<T::GraphError>,
> {
    let mut state = libpijul::RecordBuilder::new();
    let num_cpus = num_cpus::get();
    for p in prefixes.iter() {
        let result = working_copy.record_prefix(
            txn,
            channel,
            changes,
            &mut state,
            repo_path.clone(),
            p,
            num_cpus,
        );
        use libpijul::working_copy::filesystem::*;
        match result {
            Ok(_) => {}
            Err(Error::Add(AddError::Fs(FsError::NotFound(_)))) => {}
            Err(Error::Add(AddError::Fs(FsError::AlreadyInRepo(_)))) => {}
            Err(e) => {
                error!("While adding {:?}: {}", p, e);
            }
        }
    }
    let rec = state.finish();
    if rec.actions.is_empty() {
        return Ok((
            0,
            None,
            txn.current_state(&channel.borrow()).map_err(TxnErr)?,
        ));
    }
    let actions: Vec<_> = rec
        .actions
        .into_iter()
        .map(|rec| rec.globalize(txn).unwrap())
        .collect();
    let n = actions.len();
    let (dependencies, extra_known) =
        libpijul::change::dependencies(txn, &channel.borrow(), actions.iter())?;
    let mut change = libpijul::change::LocalChange::make_change(
        txn,
        channel,
        actions,
        rec.contents,
        header,
        Vec::new(),
    )?;
    change.dependencies = dependencies;
    change.extra_known = extra_known;
    debug!("saving change");
    let hash = changes.save_change(&change).unwrap();
    debug!("saved");
    let (_, m) = txn.apply_local_change(channel, &change, hash, &rec.updatables)?;
    Ok((n, Some(hash), m))
}

struct Stats {
    child: git2::Oid,
    n_changes: usize,
    parent_application_time: std::time::Duration,
    output_time: std::time::Duration,
    reset_time: std::time::Duration,
    git_diff_time: std::time::Duration,
    record_time: std::time::Duration,
    n_actions: usize,
    n_files: usize,
    n_dirs: usize,
    total_size: u64,
    changes_size: u64,
    pristine_size: u64,
    hash: Option<libpijul::Hash>,
}

impl Stats {
    fn new(child: git2::Oid) -> Self {
        let z = std::time::Duration::from_secs(0);
        Stats {
            child,
            n_changes: 0,
            parent_application_time: z,
            output_time: z,
            reset_time: z,
            git_diff_time: z,
            record_time: z,
            n_actions: 0,
            n_files: 0,
            n_dirs: 0,
            total_size: 0,
            changes_size: 0,
            pristine_size: 0,
            hash: None,
        }
    }

    fn write(
        &mut self,
        n: usize,
        repo_path: &Path,
        f: &mut std::fs::File,
    ) -> Result<(), anyhow::Error> {
        // Count files.
        let mut walk = ignore::WalkBuilder::new(&repo_path);
        walk.add_ignore(DOT_DIR).unwrap();
        for f in walk.build() {
            let meta = f?.metadata()?;
            if meta.is_dir() {
                self.n_dirs += 1
            } else {
                self.n_files += 1;
                self.total_size += meta.len();
            }
        }

        let dot_dir = repo_path.join(DOT_DIR);
        let pristine_dir = dot_dir.join(PRISTINE_DIR);
        let changes_dir = dot_dir.join(CHANGES_DIR);
        if let Ok(walk) = std::fs::read_dir(&pristine_dir) {
            for f in walk {
                let meta = f?.metadata()?;
                self.pristine_size += meta.len();
            }
        }
        if let Ok(walk) = std::fs::read_dir(&changes_dir) {
            for f in walk {
                let meta = f?.metadata()?;
                self.changes_size += meta.len();
                self.n_changes += 1
            }
        }
        let timers = libpijul::get_timers();
        writeln!(
            f, "{}, {}, {}, {}, {}, {}, {}, {}, {}, {}, {}, {}, {}, {}, {}, {}, {}, {}, {}, {}, {}, {}, {}, {}",
            self.child,
            n,
            self.parent_application_time.as_secs_f64(),
            timers.alive_output.as_secs_f64(),
            timers.alive_retrieve.as_secs_f64(),
            timers.alive_graph.as_secs_f64(),
            timers.alive_contents.as_secs_f64(),
            timers.alive_write.as_secs_f64(),
            timers.apply.as_secs_f64(),
            timers.record.as_secs_f64(),
            timers.repair_context.as_secs_f64(),
            timers.check_cyclic_paths.as_secs_f64(),
            timers.find_alive.as_secs_f64(),
            self.output_time.as_secs_f64(),
            self.reset_time.as_secs_f64(),
            self.git_diff_time.as_secs_f64(),
            self.record_time.as_secs_f64(),
            self.n_actions,
            self.n_files,
            self.n_dirs,
            self.total_size,
            self.changes_size,
            self.pristine_size,
            if let Some(ref h) = self.hash { h.to_base32() } else { String::new() },
        )?;
        libpijul::reset_timers();
        Ok(())
    }
}
