use std::collections::HashSet;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use anyhow::{bail, Context};
use lazy_static::lazy_static;
use libpijul::pristine::{Base32, ChannelRef, Hash, Merkle, MutTxnT, RemoteRef, TxnT};
use libpijul::DOT_DIR;
use libpijul::{MutTxnTExt, TxnTExt};
use log::{debug, info};
use tokio::sync::Mutex;

use crate::repository::*;

pub mod ssh;
use ssh::*;

pub mod local;
use local::*;

pub mod http;
use http::*;

pub enum RemoteRepo {
    Local(Local),
    Ssh(Ssh),
    Http(Http),
    LocalChannel(String),
    None,
}

lazy_static! {
    static ref PROGRESS: Arc<indicatif::MultiProgress> = Arc::new(indicatif::MultiProgress::new());
    static ref SPINNER: Arc<Mutex<Option<indicatif::ProgressBar>>> = Arc::new(Mutex::new(None));
}

impl Repository {
    pub async fn remote(
        &self,
        self_path: Option<&Path>,
        name: &str,
        channel: &str,
        no_cert_check: bool,
    ) -> Result<RemoteRepo, anyhow::Error> {
        if let Some(name) = self.config.remotes.get(name) {
            unknown_remote(self_path, name, channel, no_cert_check).await
        } else {
            unknown_remote(self_path, name, channel, no_cert_check).await
        }
    }
}

pub async fn unknown_remote(
    self_path: Option<&Path>,
    name: &str,
    channel: &str,
    no_cert_check: bool,
) -> Result<RemoteRepo, anyhow::Error> {
    if let Ok(url) = url::Url::parse(name) {
        let scheme = url.scheme();
        if scheme == "http" || scheme == "https" {
            debug!("unknown_remote, http = {:?}", name);
            return Ok(RemoteRepo::Http(Http {
                url,
                channel: channel.to_string(),
                client: reqwest::ClientBuilder::new()
                    .danger_accept_invalid_certs(no_cert_check)
                    .build()?,
                name: name.to_string(),
            }));
        } else if scheme == "ssh" {
            return if let Some(mut ssh) = ssh_remote(name) {
                debug!("unknown_remote, ssh = {:?}", ssh);
                Ok(RemoteRepo::Ssh(ssh.connect(name, channel).await?))
            } else {
                bail!("Remote not found: {:?}", name)
            };
        } else {
            bail!("Remote scheme not supported: {:?}", scheme)
        }
    }
    if let Ok(root) = std::fs::canonicalize(name) {
        if let Some(path) = self_path {
            let path = std::fs::canonicalize(path)?;
            if path == root {
                return Ok(RemoteRepo::LocalChannel(channel.to_string()));
            }
        }

        let mut dot_dir = root.join(DOT_DIR);
        let changes_dir = dot_dir.join(CHANGES_DIR);

        dot_dir.push(PRISTINE_DIR);
        debug!("dot_dir = {:?}", dot_dir);
        if let Ok(pristine) = libpijul::pristine::sanakirja::Pristine::new(&dot_dir) {
            debug!("pristine done");
            return Ok(RemoteRepo::Local(Local {
                root: Path::new(name).to_path_buf(),
                channel: channel.to_string(),
                changes_dir,
                pristine: Arc::new(pristine),
                name: name.to_string(),
            }));
        }
    }
    if let Some(mut ssh) = ssh_remote(name) {
        debug!("unknown_remote, ssh = {:?}", ssh);
        Ok(RemoteRepo::Ssh(ssh.connect(name, channel).await?))
    } else {
        bail!("Remote not found: {:?}", name)
    }
}

impl RemoteRepo {
    fn name(&self) -> Option<&str> {
        match *self {
            RemoteRepo::Ssh(ref s) => Some(s.name.as_str()),
            RemoteRepo::Local(ref l) => Some(l.name.as_str()),
            RemoteRepo::Http(ref h) => Some(h.name.as_str()),
            RemoteRepo::LocalChannel(_) => None,
            RemoteRepo::None => unreachable!(),
        }
    }

    pub fn repo_name(&self) -> Result<Option<String>, anyhow::Error> {
        match *self {
            RemoteRepo::Ssh(ref s) => {
                if let Some(sep) = s.name.rfind(|c| c == ':' || c == '/') {
                    Ok(Some(s.name.split_at(sep + 1).1.to_string()))
                } else {
                    Ok(Some(s.name.as_str().to_string()))
                }
            }
            RemoteRepo::Local(ref l) => {
                if let Some(file) = l.root.file_name() {
                    Ok(Some(
                        file.to_str()
                            .context("failed to decode local repository name")?
                            .to_string(),
                    ))
                } else {
                    Ok(None)
                }
            }
            RemoteRepo::Http(ref h) => {
                if let Some(name) = libpijul::path::file_name(h.url.path()) {
                    if !name.trim().is_empty() {
                        return Ok(Some(name.trim().to_string()));
                    }
                }
                Ok(h.url.host().map(|h| h.to_string()))
            }
            RemoteRepo::LocalChannel(_) => Ok(None),
            RemoteRepo::None => unreachable!(),
        }
    }

    pub async fn finish(&mut self) -> Result<(), anyhow::Error> {
        if let RemoteRepo::Ssh(s) = self {
            s.finish().await?
        }
        Ok(())
    }

    pub async fn update_changelist<T: MutTxnTExt + TxnTExt>(
        &mut self,
        txn: &mut T,
        path: &[String],
    ) -> Result<Option<(HashSet<Position<Hash>>, RemoteRef<T>)>, anyhow::Error> {
        let progress = indicatif::ProgressBar::new_spinner();
        progress.set_style(
            indicatif::ProgressStyle::default_spinner()
                .template("{spinner} Updating remote changelist"),
        );
        progress.enable_steady_tick(100);
        *SPINNER.lock().await = Some(progress);
        debug!("update_changelist");
        let name = if let Some(name) = self.name() {
            name
        } else {
            return Ok(None);
        };
        let mut remote = txn.open_or_create_remote(name).unwrap();
        let n = self
            .dichotomy_changelist(txn, &remote.borrow().remote)
            .await?;
        debug!("update changelist {:?}", n);
        let v: Vec<_> = txn
            .iter_remote(&remote.borrow().remote, n)?
            .filter_map(|k| {
                let k = k.unwrap().0;
                if k >= n {
                    Some(k)
                } else {
                    None
                }
            })
            .collect();
        for k in v {
            debug!("deleting {:?}", k);
            txn.del_remote(&mut remote, k)?;
        }
        let paths = self.download_changelist(txn, &mut remote, n, path).await?;
        if let Some(progress) = SPINNER.lock().await.take() {
            progress.set_style(
                indicatif::ProgressStyle::default_spinner()
                    .template("✓ Updating remote changelist"),
            );
            progress.finish();
        }
        Ok(Some((paths, remote)))
    }

    async fn dichotomy_changelist<T: MutTxnT + TxnTExt>(
        &mut self,
        txn: &T,
        remote: &T::Remote,
    ) -> Result<u64, anyhow::Error> {
        let mut a = 0;
        let (mut b, (_, state)) = if let Some(last) = txn.last_remote(remote)? {
            last
        } else {
            debug!("the local copy of the remote has no changes");
            return Ok(0);
        };
        if let Some((_, s)) = self.get_state(txn, Some(b)).await? {
            if s == state {
                // The local list is already up to date.
                return Ok(b + 1);
            }
        }
        // Else, find the last state we have in common with the
        // remote, it might be older than the last known state (if
        // changes were unrecorded on the remote).
        while a < b {
            let mid = (a + b) / 2;
            let (mid, (_, state)) = txn.get_remote_state(remote, mid)?.unwrap();
            let remote_state = self.get_state(txn, Some(mid)).await?;
            debug!("dichotomy {:?} {:?} {:?}", mid, state, remote_state);
            if let Some((_, remote_state)) = remote_state {
                if remote_state == state {
                    if a == mid {
                        return Ok(a + 1);
                    } else {
                        a = mid;
                        continue;
                    }
                }
            }
            if b == mid {
                break;
            } else {
                b = mid
            }
        }
        Ok(a)
    }

    async fn get_state<T: libpijul::TxnTExt>(
        &mut self,
        txn: &T,
        mid: Option<u64>,
    ) -> Result<Option<(u64, Merkle)>, anyhow::Error> {
        match *self {
            RemoteRepo::Local(ref mut l) => l.get_state(mid),
            RemoteRepo::Ssh(ref mut s) => s.get_state(mid).await,
            RemoteRepo::Http(ref mut h) => h.get_state(mid).await,
            RemoteRepo::LocalChannel(ref channel) => {
                if let Some(channel) = txn.load_channel(&channel)? {
                    local::get_state(txn, &channel, mid)
                } else {
                    Ok(None)
                }
            }
            RemoteRepo::None => unreachable!(),
        }
    }

    pub async fn archive<W: std::io::Write + Send + 'static>(
        &mut self,
        prefix: Option<String>,
        state: Option<(Merkle, &[Hash])>,
        w: W,
    ) -> Result<u64, anyhow::Error> {
        match *self {
            RemoteRepo::Local(ref mut l) => {
                debug!("archiving local repo");
                let changes = libpijul::changestore::filesystem::FileSystem::from_root(&l.root);
                let mut tarball = libpijul::output::Tarball::new(w, prefix);
                let conflicts = if let Some((state, extra)) = state {
                    let mut txn = l.pristine.mut_txn_begin();
                    let mut channel = txn.load_channel(&l.channel)?.unwrap();
                    txn.archive_with_state(&changes, &mut channel, state, extra, &mut tarball)?
                } else {
                    let txn = l.pristine.txn_begin()?;
                    let channel = txn.load_channel(&l.channel)?.unwrap();
                    txn.archive(&changes, &channel, &mut tarball)?
                };
                Ok(conflicts.len() as u64)
            }
            RemoteRepo::Ssh(ref mut s) => s.archive(prefix, state, w).await,
            RemoteRepo::Http(ref mut h) => h.archive(prefix, state, w).await,
            RemoteRepo::LocalChannel(_) => unreachable!(),
            RemoteRepo::None => unreachable!(),
        }
    }

    async fn download_changelist<T: MutTxnTExt>(
        &mut self,
        txn: &mut T,
        remote: &mut RemoteRef<T>,
        from: u64,
        paths: &[String],
    ) -> Result<HashSet<Position<Hash>>, anyhow::Error> {
        match *self {
            RemoteRepo::Local(ref mut l) => l.download_changelist(txn, remote, from, paths),
            RemoteRepo::Ssh(ref mut s) => s.download_changelist(txn, remote, from, paths).await,
            RemoteRepo::Http(ref h) => h.download_changelist(txn, remote, from, paths).await,
            RemoteRepo::LocalChannel(_) => Ok(HashSet::new()),
            RemoteRepo::None => unreachable!(),
        }
    }

    pub async fn upload_changes<T: MutTxnTExt>(
        &mut self,
        txn: &mut T,
        local: PathBuf,
        to_channel: Option<&str>,
        changes: &[Hash],
    ) -> Result<(), anyhow::Error> {
        match self {
            RemoteRepo::Local(ref mut l) => l.upload_changes(local, to_channel, changes),
            RemoteRepo::Ssh(ref mut s) => s.upload_changes(local, to_channel, changes).await,
            RemoteRepo::Http(ref h) => h.upload_changes(local, to_channel, changes).await,
            RemoteRepo::LocalChannel(ref channel) => {
                let mut channel = txn.open_or_create_channel(channel)?;
                let store = libpijul::changestore::filesystem::FileSystem::from_changes(local);
                local::upload_changes(&store, txn, &mut channel, changes)
            }
            RemoteRepo::None => unreachable!(),
        }
    }

    /// Start (and possibly complete) the download of a change.
    pub async fn download_changes(
        &mut self,
        hashes: &[libpijul::pristine::Hash],
        send: &mut tokio::sync::mpsc::Sender<libpijul::pristine::Hash>,
        path: &mut PathBuf,
        full: bool,
    ) -> Result<bool, anyhow::Error> {
        debug!("download_changes");
        match *self {
            RemoteRepo::Local(ref mut l) => l.download_changes(hashes, send, path).await?,
            RemoteRepo::Ssh(ref mut s) => s.download_changes(hashes, send, path, full).await?,
            RemoteRepo::Http(ref mut h) => h.download_changes(hashes, send, path, full).await?,
            RemoteRepo::LocalChannel(_) => {}
            RemoteRepo::None => unreachable!(),
        }
        libpijul::changestore::filesystem::pop_filename(path);
        Ok(true)
    }

    pub async fn pull<T: MutTxnTExt + TxnTExt>(
        &mut self,
        repo: &mut Repository,
        txn: &mut T,
        channel: &mut ChannelRef<T>,
        to_apply: &[Hash],
        inodes: &HashSet<Position<Hash>>,
        do_apply: bool,
    ) -> Result<Vec<Hash>, anyhow::Error> {
        let (mut send, mut recv) = tokio::sync::mpsc::channel(100);

        let mut change_path_ = repo.changes_dir.clone();
        let mut to_download_ = Vec::new();
        for h in to_apply {
            libpijul::changestore::filesystem::push_filename(&mut change_path_, h);
            if std::fs::metadata(&change_path_).is_err() {
                to_download_.push(*h)
            }
            libpijul::changestore::filesystem::pop_filename(&mut change_path_);
        }
        let to_download = to_download_.clone();

        let mut self_ = std::mem::replace(self, RemoteRepo::None);
        let t = tokio::spawn(async move {
            self_
                .download_changes(&to_download_, &mut send, &mut change_path_, false)
                .await?;
            Ok::<_, anyhow::Error>(self_)
        });

        let mut ws = libpijul::ApplyWorkspace::new();
        let mut change_path = repo.changes_dir.clone();
        let progress = if do_apply {
            let p = indicatif::ProgressBar::new(to_download.len() as u64);
            p.set_style(
                indicatif::ProgressStyle::default_bar()
                    .template("  Applying changes    {wide_bar} {pos:>5}/{len}"),
            );
            Some(PROGRESS.add(p))
        } else {
            None
        };
        let t_progress = std::thread::spawn(|| {
            PROGRESS.join().unwrap_or(());
        });
        let mut to_apply_inodes = Vec::new();
        for h in to_apply {
            libpijul::changestore::filesystem::push_filename(&mut change_path, &h);
            debug!("change_path = {:?}", change_path);
            while std::fs::metadata(&change_path).is_err() {
                debug!("waiting");
                let r = recv.recv().await;
                debug!("r = {:?}", r);
                if r.is_none() {
                    if let Some(ref progress) = progress {
                        progress.abandon();
                    }
                    break;
                }
            }
            libpijul::changestore::filesystem::pop_filename(&mut change_path);

            let touches_inodes = inodes.is_empty()
                || {
                    debug!("inodes = {:?}", inodes);
                    use libpijul::changestore::ChangeStore;
                    let changes = repo.changes.get_changes(h)?;
                    changes.iter().any(|c| {
                        c.iter().any(|c| {
                            let inode = c.inode();
                            debug!("inode = {:?}", inode);
                            if let Some(h) = inode.change {
                                inodes.contains(&Position {
                                    change: h,
                                    pos: inode.pos,
                                })
                            } else {
                                false
                            }
                        })
                    })
                }
                || { inodes.iter().any(|i| i.change == *h) };

            if touches_inodes {
                to_apply_inodes.push(*h);
            } else {
                continue;
            }

            if let Some(ref progress) = progress {
                info!("Applying {:?}", h);
                progress.inc(1);
                txn.apply_change_ws(&repo.changes, channel, *h, &mut ws)?;
            } else {
                debug!("not applying {:?}", h)
            }
        }
        if let Some(progress) = progress {
            if !progress.is_finished() {
                progress.set_style(
                    indicatif::ProgressStyle::default_bar()
                        .template("✓ Applying changes    {pos:>5}/{len}"),
                );
                progress.finish()
            }
        }
        std::mem::drop(recv);
        debug!("waiting for spawned process");
        *self = t.await??;
        t_progress.join().unwrap();
        Ok(to_apply_inodes)
    }

    pub async fn clone_tag<T: MutTxnTExt + TxnTExt>(
        &mut self,
        repo: &mut Repository,
        txn: &mut T,
        channel: &mut ChannelRef<T>,
        tag: &[Hash],
    ) -> Result<(), anyhow::Error> {
        let (mut send_signal, mut recv_signal) = tokio::sync::mpsc::channel(100);
        let (send_hash, mut recv_hash) = tokio::sync::mpsc::channel(100);

        let mut change_path_ = repo.changes_dir.clone();
        let mut self_ = std::mem::replace(self, RemoteRepo::None);
        let t = tokio::spawn(async move {
            while let Some(hash) = recv_hash.recv().await {
                self_
                    .download_changes(&[hash], &mut send_signal, &mut change_path_, false)
                    .await?;
            }
            Ok(self_)
        });

        for &h in tag.iter() {
            send_hash.send(h).await?;
        }

        let mut change_path = repo.changes_dir.clone();
        let mut hashes = Vec::new();
        while let Some(hash) = recv_signal.recv().await {
            libpijul::changestore::filesystem::push_filename(&mut change_path, &hash);
            std::fs::create_dir_all(change_path.parent().unwrap())?;
            use libpijul::changestore::ChangeStore;
            hashes.push(hash);
            for dep in repo.changes.get_dependencies(&hash)? {
                let dep: libpijul::pristine::Hash = dep;
                send_hash.send(dep).await?;
            }
            libpijul::changestore::filesystem::pop_filename(&mut change_path);
        }
        std::mem::drop(recv_signal);
        std::mem::drop(send_hash);
        let mut ws = libpijul::ApplyWorkspace::new();
        while let Some(hash) = hashes.pop() {
            txn.apply_change_ws(&repo.changes, channel, hash, &mut ws)?;
        }
        let r: Result<_, anyhow::Error> = t.await?;
        *self = r?;
        Ok(())
    }

    pub async fn clone_state<T: MutTxnTExt + TxnTExt>(
        &mut self,
        repo: &mut Repository,
        txn: &mut T,
        channel: &mut ChannelRef<T>,
        state: Merkle,
        lazy: bool,
    ) -> Result<(), anyhow::Error> {
        self.update_changelist(txn, &[]).await?;
        let name = self.name().unwrap();
        let remote = txn.open_or_create_remote(name).unwrap();
        if let RemoteRepo::Ssh(ref mut s) = self {
            s.clone_channel(repo, txn, channel, lazy).await?;
            let mut to_unrecord = Vec::new();
            let mut found = false;
            for x in txn.iter_rev_remote(&remote.borrow().remote, None)? {
                let (n, (h, s)) = x?;
                debug!("{:?} {:?} {:?}", n, h, s);
                if s == state {
                    found = true;
                    break;
                }
                to_unrecord.push(h);
            }
            if !found {
                bail!("State not found: {:?}", state)
            }
            self.pull(repo, txn, channel, &to_unrecord, &HashSet::new(), false)
                .await?;
            for unrec in to_unrecord.iter() {
                txn.unrecord(&repo.changes, channel, unrec)?;
            }
            return Ok(());
        }

        let mut to_pull = Vec::new();
        let mut found = false;
        for x in txn.iter_remote(&remote.borrow().remote, 0)? {
            let (n, (h, s)) = x?;
            debug!("{:?} {:?} {:?}", n, h, s);
            to_pull.push(h);
            if s == state {
                found = true;
                break;
            }
        }
        if !found {
            bail!("State not found: {:?}", state)
        }
        self.pull(repo, txn, channel, &to_pull, &HashSet::new(), true)
            .await?;
        Ok(())
    }

    pub async fn complete_changes<T: MutTxnT + TxnTExt>(
        &mut self,
        repo: &crate::repository::Repository,
        txn: &T,
        local_channel: &mut ChannelRef<T>,
        changes: &[Hash],
        full: bool,
    ) -> Result<(), anyhow::Error> {
        use libpijul::changestore::ChangeStore;
        let (send_hash, mut recv_hash) = tokio::sync::mpsc::channel(100);
        let (mut send_sig, mut recv_sig) = tokio::sync::mpsc::channel(100);
        let mut self_ = std::mem::replace(self, RemoteRepo::None);
        let mut changes_dir = repo.changes_dir.clone();
        let t = tokio::spawn(async move {
            while let Some(h) = recv_hash.recv().await {
                debug!("downloading full patch: {:?}", h);
                self_
                    .download_changes(&[h], &mut send_sig, &mut changes_dir, true)
                    .await?;
            }
            let result: Result<_, anyhow::Error> = Ok(self_);
            result
        });

        for c in changes {
            if repo.changes.has_contents(*c, txn.get_internal(*c)?) {
                debug!("has contents {:?}", c);
                continue;
            }
            if full {
                debug!("sending send_hash");
                send_hash.send(*c).await?;
                debug!("sent");
                continue;
            }
            let change = if let Some(i) = txn.get_internal(*c)? {
                i
            } else {
                continue;
            };
            // Check if at least one non-empty vertex from c is still alive.
            let v = libpijul::pristine::Vertex {
                change,
                start: libpijul::pristine::ChangePosition(0),
                end: libpijul::pristine::ChangePosition(0),
            };
            let channel = local_channel.borrow();
            if txn.is_alive(&channel, v)? {
                send_hash.send(*c).await?;
            }
        }
        debug!("dropping send_hash");
        std::mem::drop(send_hash);
        while recv_sig.recv().await.is_some() {}
        *self = t.await??;
        Ok(())
    }

    pub async fn clone_channel<T: MutTxnTExt + TxnTExt>(
        &mut self,
        repo: &mut Repository,
        txn: &mut T,
        local_channel: &mut ChannelRef<T>,
        lazy: bool,
        path: &[String],
    ) -> Result<(), anyhow::Error> {
        if path.is_empty() {
            if let RemoteRepo::Ssh(s) = self {
                return s.clone_channel(repo, txn, local_channel, lazy).await;
            }
        }
        let (inodes, remote_changes) = self
            .update_changelist(txn, path)
            .await?
            .expect("Remote is not self");
        let mut pullable = Vec::new();
        for x in txn.iter_remote(&remote_changes.borrow().remote, 0)? {
            let (_, (h, _)) = x?;
            pullable.push(h)
        }
        self.pull(repo, txn, local_channel, &pullable, &inodes, true)
            .await?;
        Ok(())
    }
}

use libpijul::pristine::{ChangePosition, Position};
use regex::Regex;

lazy_static! {
    static ref CHANGELIST_LINE: Regex =
        Regex::new(r#"(?P<num>[0-9]+)\.(?P<hash>[A-Za-z0-9]+)\.(?P<merkle>[A-Za-z0-9]+)"#).unwrap();
    static ref PATHS_LINE: Regex =
        Regex::new(r#"(?P<hash>[A-Za-z0-9]+)\.(?P<num>[0-9]+)"#).unwrap();
}

enum ListLine {
    Change { n: u64, h: Hash, m: Merkle },
    Position(Position<Hash>),
    Error(String),
}

fn parse_line(data: &str) -> Result<ListLine, anyhow::Error> {
    debug!("data = {:?}", data);
    if let Some(caps) = CHANGELIST_LINE.captures(data) {
        if let (Some(h), Some(m)) = (
            Hash::from_base32(caps.name("hash").unwrap().as_str().as_bytes()),
            Merkle::from_base32(caps.name("merkle").unwrap().as_str().as_bytes()),
        ) {
            return Ok(ListLine::Change {
                n: caps.name("num").unwrap().as_str().parse().unwrap(),
                h,
                m,
            });
        }
    }
    if data.starts_with("error:") {
        return Ok(ListLine::Error(data.split_at(6).1.to_string()));
    }
    if let Some(caps) = PATHS_LINE.captures(data) {
        return Ok(ListLine::Position(Position {
            change: Hash::from_base32(caps.name("hash").unwrap().as_str().as_bytes()).unwrap(),
            pos: ChangePosition(caps.name("num").unwrap().as_str().parse().unwrap()),
        }));
    }
    debug!("offending line: {:?}", data);
    bail!("Protocol error")
}
