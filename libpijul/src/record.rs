//! Hunk a change from a pristine and a working copy.
use crate::alive::retrieve;
use crate::change::*;
use crate::changestore::ChangeStore;
use crate::diff;
pub use crate::diff::Algorithm;
use crate::path::{components, Components};
use crate::pristine::*;
use crate::small_string::SmallString;
use crate::working_copy::WorkingCopy;
use std::collections::{HashMap, HashSet};

#[derive(Debug, Error)]
pub enum RecordError<
    C: std::error::Error + 'static,
    W: std::error::Error,
    T: std::error::Error + 'static,
> {
    #[error("Changestore error: {0}")]
    Changestore(C),
    #[error("Working copy error: {0}")]
    WorkingCopy(W),
    #[error("System time error: {0}")]
    SystemTimeError(#[from] std::time::SystemTimeError),
    #[error(transparent)]
    Txn(T),
    #[error(transparent)]
    Diff(#[from] diff::DiffError<C, T>),
    #[error("Path not in repository: {0}")]
    PathNotInRepo(String),
    #[error(transparent)]
    Io(#[from] std::io::Error),
}

impl<
        C: std::error::Error + 'static,
        W: std::error::Error + 'static,
        T: std::error::Error + 'static,
    > std::convert::From<TxnErr<T>> for RecordError<C, W, T>
{
    fn from(e: TxnErr<T>) -> Self {
        RecordError::Txn(e.0)
    }
}

/// A change in the process of being recorded. This is typically
/// created using `Builder::new`.
pub struct Builder {
    pub(crate) rec: Recorded,
    pub(crate) redundant: Vec<(Vertex<ChangeId>, Edge)>,
    recorded_inodes: HashMap<Inode, Position<Option<ChangeId>>>,
    deleted_vertices: HashSet<Position<ChangeId>>,
    former_parents: Vec<Parent>,
    pub force_rediff: bool,
    pub ignore_missing: bool,
}

#[derive(Debug)]
struct Parent {
    basename: String,
    metadata: InodeMetadata,
    parent: Position<Option<ChangeId>>,
}

/// The result of recording a change:
pub struct Recorded {
    /// The "byte contents" of the change.
    pub contents: Vec<u8>,
    /// The current records, to be lated converted into change operations.
    pub actions: Vec<Hunk<Option<ChangeId>, Local>>,
    /// The updates that need to be made to the ~tree~ and ~revtree~
    /// tables when this change is applied to the local repository.
    pub updatables: HashMap<usize, InodeUpdate>,
    /// The size of the largest file that was recorded in this change.
    pub largest_file: u64,
    /// Whether we have recorded binary files.
    pub has_binary_files: bool,
    /// Timestamp of the oldest changed file. If nothing changed,
    /// returns now().
    pub oldest_change: std::time::SystemTime,
}

impl Default for Builder {
    fn default() -> Self {
        Self {
            rec: Recorded {
                contents: Vec::new(),
                actions: Vec::new(),
                updatables: HashMap::new(),
                largest_file: 0,
                has_binary_files: false,
                oldest_change: std::time::SystemTime::UNIX_EPOCH,
            },
            redundant: Vec::new(),
            recorded_inodes: HashMap::new(),
            deleted_vertices: HashSet::new(),
            former_parents: Vec::new(),
            force_rediff: false,
            ignore_missing: false,
        }
    }
}

impl Builder {
    /// Initialise a `Builder`.
    pub fn new() -> Self {
        Self::default()
    }

    /// Finish the recording.
    pub fn finish(self) -> Recorded {
        self.rec
    }
}

/// An account of the files that have been added, moved or deleted, as
/// returned by record, and used by apply (when applying a change
/// created locally) to update the trees and inodes databases.
#[derive(Debug, Hash, PartialEq, Eq)]
pub enum InodeUpdate {
    Add {
        /// Inode vertex in the graph.
        pos: ChangePosition,
        /// `Inode` added by this file addition.
        inode: Inode,
    },
    Deleted {
        /// `Inode` of the deleted file.
        inode: Inode,
    },
}

#[derive(Debug, Clone)]
struct RecordItem<'a> {
    v_papa: Position<Option<ChangeId>>,
    papa: Inode,
    inode: Inode,
    basename: String,
    full_path: String,
    metadata: InodeMetadata,
    components: Components<'a>,
}

impl<'a> RecordItem<'a> {
    fn root(prefix: &'a str) -> Self {
        RecordItem {
            inode: Inode::ROOT,
            papa: Inode::ROOT,
            v_papa: Position::OPTION_ROOT,
            basename: String::new(),
            full_path: String::new(),
            metadata: InodeMetadata::new(0, true),
            components: components(prefix),
        }
    }
}

const CHECK_UTF8: usize = 1000;

/// Ignore inodes that are in another channel
fn get_inodes<T: ChannelTxnT + TreeTxnT<TreeError = <T as GraphTxnT>::GraphError>>(
    txn: &T,
    channel: &T::Channel,
    inode: Inode,
) -> Result<Option<Position<ChangeId>>, TxnErr<T::GraphError>> {
    if let Some(vertex) = txn.get_inodes(inode, None)? {
        if txn
            .get_changeset(txn.changes(channel), vertex.change)?
            .is_some()
        {
            Ok(Some(vertex))
        } else {
            Ok(None)
        }
    } else {
        Ok(None)
    }
}

impl Builder {
    pub fn record<T, W: WorkingCopy, C: ChangeStore>(
        &mut self,
        txn: &mut T,
        diff_algorithm: diff::Algorithm,
        channel: &mut T::Channel,
        working_copy: &mut W,
        changes: &C,
        prefix: &str,
    ) -> Result<(), RecordError<C::Error, W::Error, T::GraphError>>
    where
        T: ChannelMutTxnT + TreeTxnT<TreeError = <T as GraphTxnT>::GraphError>,
        <W as WorkingCopy>::Error: 'static,
    {
        let now = std::time::Instant::now();
        let mut stack = vec![RecordItem::root(prefix)];
        while let Some(mut item) = stack.pop() {
            debug!("stack.pop() = Some({:?})", item);

            // Check for moves and file conflicts.
            let vertex = if let Some(vertex) = self.recorded_inodes.get(&item.inode) {
                *vertex
            } else if item.inode == Inode::ROOT {
                self.recorded_inodes
                    .insert(Inode::ROOT, Position::OPTION_ROOT);
                self.delete_obsolete_children(
                    txn,
                    txn.graph(channel),
                    working_copy,
                    changes,
                    &item.full_path,
                    Position::ROOT,
                )?;
                Position::OPTION_ROOT
            } else if let Some(vertex) = get_inodes(txn, &channel, item.inode)? {
                self.delete_obsolete_children(
                    txn,
                    txn.graph(channel),
                    working_copy,
                    changes,
                    &item.full_path,
                    vertex,
                )?;
                self.record_existing_file(
                    txn,
                    diff_algorithm,
                    &channel,
                    working_copy,
                    changes,
                    &item,
                    vertex,
                )?;
                self.recorded_inodes.insert(item.inode, vertex.to_option());
                vertex.to_option()
            } else {
                match self.add_file(working_copy, item.clone()) {
                    Ok(Some(vertex)) => {
                        // Path addition (maybe just a single directory).
                        self.recorded_inodes.insert(item.inode, vertex);
                        vertex
                    }
                    _ => continue,
                }
            };

            // Move on to the next step.
            self.push_children::<_, _, C>(
                txn,
                &channel,
                working_copy,
                &mut item,
                vertex,
                &mut stack,
                prefix,
            )?;
        }
        crate::TIMERS.lock().unwrap().record += now.elapsed();
        Ok(())
    }

    fn add_file<W: WorkingCopy>(
        &mut self,
        working_copy: &mut W,
        item: RecordItem,
    ) -> Result<Option<Position<Option<ChangeId>>>, W::Error> {
        debug!("record_file_addition {:?}", item);
        let meta = working_copy.file_metadata(&item.full_path)?;
        let name_start = ChangePosition(self.rec.contents.len() as u64);
        meta.write(&mut self.rec.contents).unwrap();
        self.rec.contents.extend(item.basename.as_bytes());
        let name_end = ChangePosition(self.rec.contents.len() as u64);
        self.rec.contents.push(0);
        let inode_pos = ChangePosition(self.rec.contents.len() as u64);
        self.rec.contents.push(0);

        let contents = if meta.is_file() {
            let start = ChangePosition(self.rec.contents.len() as u64);
            working_copy.read_file(&item.full_path, &mut self.rec.contents)?;
            let end = ChangePosition(self.rec.contents.len() as u64);
            self.rec.largest_file = self.rec.largest_file.max(end.0 - start.0);
            self.rec.has_binary_files |= {
                let s = start.0 as usize;
                let e = (end.0 as usize).min(s + CHECK_UTF8 + 4);
                let utf8 = std::str::from_utf8(&self.rec.contents[s..e]);
                debug!("utf8 = {:?}", utf8);
                match utf8 {
                    Err(e) => e.valid_up_to() < CHECK_UTF8,
                    Ok(_) => false,
                }
            };
            self.rec.contents.push(0);
            if end > start {
                Some(Atom::NewVertex(NewVertex {
                    up_context: vec![Position {
                        change: None,
                        pos: inode_pos,
                    }],
                    down_context: vec![],
                    start,
                    end,
                    flag: EdgeFlags::BLOCK,
                    inode: Position {
                        change: None,
                        pos: inode_pos,
                    },
                }))
            } else {
                None
            }
        } else {
            None
        };
        self.rec.actions.push(Hunk::FileAdd {
            add_name: Atom::NewVertex(NewVertex {
                up_context: vec![item.v_papa],
                down_context: vec![],
                start: name_start,
                end: name_end,
                flag: EdgeFlags::FOLDER | EdgeFlags::BLOCK,
                inode: item.v_papa,
            }),
            add_inode: Atom::NewVertex(NewVertex {
                up_context: vec![Position {
                    change: None,
                    pos: name_end,
                }],
                down_context: vec![],
                start: inode_pos,
                end: inode_pos,
                flag: EdgeFlags::FOLDER | EdgeFlags::BLOCK,
                inode: item.v_papa,
            }),
            contents,
            path: item.full_path.clone(),
        });
        debug!("{:?}", self.rec.actions.last().unwrap());
        self.rec.updatables.insert(
            self.rec.actions.len(),
            InodeUpdate::Add {
                inode: item.inode,
                pos: inode_pos,
            },
        );
        if meta.is_dir() {
            Ok(Some(Position {
                change: None,
                pos: inode_pos,
            }))
        } else {
            Ok(None)
        }
    }

    fn record_existing_file<
        T: ChannelMutTxnT + TreeTxnT<TreeError = <T as GraphTxnT>::GraphError>,
        W: WorkingCopy,
        C: ChangeStore,
    >(
        &mut self,
        txn: &mut T,
        diff_algorithm: diff::Algorithm,
        channel: &T::Channel,
        working_copy: &mut W,
        changes: &C,
        item: &RecordItem,
        vertex: Position<ChangeId>,
    ) -> Result<(), RecordError<C::Error, W::Error, T::GraphError>>
    where
        <W as crate::working_copy::WorkingCopy>::Error: 'static,
    {
        debug!(
            "record_existing_file {:?}: {:?} {:?}",
            item.full_path, item.inode, vertex
        );
        // Former parent(s) of vertex
        self.former_parents.clear();
        let f0 = EdgeFlags::FOLDER | EdgeFlags::PARENT;
        let f1 = EdgeFlags::all();
        let mut is_deleted = true;
        for name_ in iter_adjacent(txn, txn.graph(channel), vertex.inode_vertex(), f0, f1)? {
            let name_ = name_?;
            if !name_.flag.contains(EdgeFlags::PARENT) {
                continue;
            }
            debug!("name_ = {:?}", name_);
            if name_.flag.contains(EdgeFlags::DELETED) {
                debug!("is_deleted {:?}: {:?}", item.full_path, name_);
                is_deleted = true;
                break;
            }
            let name_dest = txn.find_block_end(txn.graph(channel), name_.dest).unwrap();
            let mut name = Vec::new();
            changes
                .get_contents(|p| txn.get_external(p).unwrap(), name_dest, &mut name)
                .map_err(RecordError::Changestore)?;
            let (metadata, basename) = name.split_at(2);
            let metadata = InodeMetadata::from_basename(metadata);
            let basename = std::str::from_utf8(basename).unwrap().to_string();
            debug!(
                "former basename of {:?}: {:?} {:?}",
                vertex, basename, metadata
            );
            if let Some(v_papa) = iter_adjacent(txn, txn.graph(channel), name_dest, f0, f1)?.next()
            {
                let v_papa = v_papa?;
                if !v_papa.flag.contains(EdgeFlags::DELETED) {
                    self.former_parents.push(Parent {
                        basename,
                        metadata,
                        parent: v_papa.dest.to_option(),
                    })
                }
            }
        }
        debug!(
            "record_existing_file: {:?} {:?} {:?}",
            item, self.former_parents, is_deleted,
        );
        assert!(!self.former_parents.is_empty());
        if let Ok(new_meta) = working_copy.file_metadata(&item.full_path) {
            debug!("new_meta = {:?}", new_meta);
            if self.former_parents.len() > 1
                || self.former_parents[0].basename != item.basename
                || self.former_parents[0].metadata != item.metadata
                || self.former_parents[0].parent != item.v_papa
                || is_deleted
            {
                // This parent has changed.
                let new_papa = *self.recorded_inodes.get(&item.papa).unwrap();
                debug!("new_papa = {:?}", new_papa);
                self.record_moved_file::<_, _, W>(
                    changes,
                    txn,
                    txn.graph(channel),
                    &item,
                    vertex,
                    new_papa,
                    self.former_parents[0].metadata,
                )?
            }
            if new_meta.is_file()
                && (self.force_rediff
                    || self.modified_since_last_commit(
                        txn,
                        &channel,
                        working_copy,
                        &item.full_path,
                    )?)
            {
                let mut ret = retrieve(txn, txn.graph(channel), vertex)?;
                let mut b = Vec::new();
                working_copy
                    .read_file(&item.full_path, &mut b)
                    .map_err(RecordError::WorkingCopy)?;
                debug!("diffing…");
                let len = self.rec.actions.len();
                self.diff(
                    changes,
                    txn,
                    &channel,
                    diff_algorithm,
                    item.full_path.clone(),
                    vertex.to_option(),
                    &mut ret,
                    &b,
                )?;
                if self.rec.actions.len() > len {
                    if let Ok(last_modified) = working_copy.modified_time(&item.full_path) {
                        if self.rec.oldest_change == std::time::SystemTime::UNIX_EPOCH {
                            self.rec.oldest_change = last_modified;
                        } else {
                            self.rec.oldest_change = self.rec.oldest_change.min(last_modified);
                        }
                    }
                }
                debug!(
                    "new actions: {:?}, total {:?}",
                    &self.rec.actions.len() - len,
                    self.rec.actions.len()
                );
            }
        } else {
            debug!("calling record_deleted_file on {:?}", item.full_path);
            self.record_deleted_file(
                txn,
                txn.graph(channel),
                working_copy,
                &item.full_path,
                vertex,
            )?
        }
        Ok(())
    }

    fn delete_obsolete_children<
        T: GraphTxnT + TreeTxnT<TreeError = <T as GraphTxnT>::GraphError>,
        W: WorkingCopy,
        C: ChangeStore,
    >(
        &mut self,
        txn: &T,
        channel: &T::Graph,
        working_copy: &W,
        changes: &C,
        full_path: &str,
        v: Position<ChangeId>,
    ) -> Result<(), RecordError<C::Error, W::Error, T::GraphError>>
    where
        <W as WorkingCopy>::Error: 'static,
    {
        if self.ignore_missing {
            return Ok(());
        }
        let f0 = EdgeFlags::FOLDER | EdgeFlags::BLOCK;
        let f1 = f0 | EdgeFlags::PSEUDO;
        debug!("delete_obsolete_children, v = {:?}", v);
        for child in iter_adjacent(txn, channel, v.inode_vertex(), f0, f1)? {
            let child = child?;
            let child = txn.find_block(channel, child.dest).unwrap();
            for grandchild in iter_adjacent(txn, channel, child, f0, f1)? {
                let grandchild = grandchild?;
                debug!("grandchild {:?}", grandchild);
                let needs_deletion =
                    if let Some(inode) = txn.get_revinodes(grandchild.dest, None)? {
                        debug!("inode = {:?} {:?}", inode, txn.get_revtree(inode, None));
                        if let Some(path) = crate::fs::inode_filename(txn, inode)? {
                            working_copy.file_metadata(&path).is_err()
                        } else {
                            true
                        }
                    } else {
                        true
                    };
                if needs_deletion {
                    let mut name = Vec::new();
                    changes
                        .get_contents(|p| txn.get_external(p).unwrap(), child, &mut name)
                        .map_err(RecordError::Changestore)?;
                    let mut full_path = full_path.to_string();
                    if name.len() > 2 {
                        if let Ok(name) = std::str::from_utf8(&name[2..]) {
                            if !full_path.is_empty() {
                                full_path.push('/');
                            }
                            full_path.push_str(name);
                        }
                    }
                    // delete recursively.
                    self.record_deleted_file(
                        txn,
                        &channel,
                        working_copy,
                        &full_path,
                        grandchild.dest,
                    )?
                }
            }
        }
        Ok(())
    }

    fn push_children<
        'a,
        T: ChannelTxnT + TreeTxnT<TreeError = <T as GraphTxnT>::GraphError>,
        W: WorkingCopy,
        C: ChangeStore,
    >(
        &mut self,
        txn: &T,
        channel: &T::Channel,
        working_copy: &W,
        item: &mut RecordItem<'a>,
        vertex: Position<Option<ChangeId>>,
        stack: &mut Vec<RecordItem<'a>>,
        prefix: &str,
    ) -> Result<(), RecordError<C::Error, W::Error, T::GraphError>>
    where
        <W as crate::working_copy::WorkingCopy>::Error: 'static,
    {
        debug!("push_children, item = {:?}", item);
        let comp = item.components.next();
        let full_path = item.full_path.clone();
        let fileid = OwnedPathId {
            parent_inode: item.inode,
            basename: SmallString::new(),
        };
        let mut has_matching_children = false;
        for x in txn.iter_tree(fileid.clone(), None)? {
            let (fileid_, child_inode) = x?;
            debug!("push_children {:?} {:?}", fileid_, child_inode);
            if fileid_.parent_inode < fileid.parent_inode || fileid_.basename.is_empty() {
                continue;
            } else if fileid_.parent_inode > fileid.parent_inode {
                break;
            }
            if let Some(comp) = comp {
                if comp != fileid_.basename.as_str() {
                    continue;
                }
            }
            has_matching_children = true;
            let basename = fileid_.basename.as_str().to_string();
            let full_path = if full_path.is_empty() {
                basename.clone()
            } else {
                full_path.clone() + "/" + &basename
            };
            debug!("fileid_ {:?} child_inode {:?}", fileid_, child_inode);
            if let Ok(meta) = working_copy.file_metadata(&full_path) {
                stack.push(RecordItem {
                    papa: item.inode,
                    inode: child_inode,
                    v_papa: vertex,
                    basename,
                    full_path,
                    metadata: meta,
                    components: item.components.clone(),
                })
            } else if let Some(vertex) = get_inodes(txn, &channel, child_inode)? {
                self.record_deleted_file(txn, txn.graph(channel), working_copy, &full_path, vertex)?
            }
        }
        if comp.is_some() && !has_matching_children {
            debug!("comp = {:?}", comp);
            return Err(RecordError::PathNotInRepo(prefix.to_string()));
        }
        Ok(())
    }

    fn modified_since_last_commit<T: ChannelTxnT, W: WorkingCopy>(
        &mut self,
        txn: &T,
        channel: &T::Channel,
        working_copy: &W,
        prefix: &str,
    ) -> Result<bool, std::time::SystemTimeError> {
        if let Ok(last_modified) = working_copy.modified_time(prefix) {
            debug!(
                "last_modified = {:?}, channel.last = {:?}",
                last_modified
                    .duration_since(std::time::UNIX_EPOCH)?
                    .as_secs(),
                txn.last_modified(channel)
            );
            Ok(last_modified
                .duration_since(std::time::UNIX_EPOCH)?
                .as_secs()
                > txn.last_modified(channel))
        } else {
            Ok(true)
        }
    }
}

impl Builder {
    fn record_moved_file<T: GraphTxnT, C: ChangeStore, W: WorkingCopy>(
        &mut self,
        changes: &C,
        txn: &T,
        channel: &T::Graph,
        item: &RecordItem,
        vertex: Position<ChangeId>,
        new_papa: Position<Option<ChangeId>>,
        old_meta: InodeMetadata,
    ) -> Result<(), RecordError<C::Error, W::Error, T::GraphError>>
    where
        <W as crate::working_copy::WorkingCopy>::Error: 'static,
    {
        debug!("record_moved_file {:?} {:?}", item, old_meta);
        let name_start = ChangePosition(self.rec.contents.len() as u64);
        item.metadata.write(&mut self.rec.contents).unwrap();
        self.rec.contents.extend(item.basename.as_bytes());
        let name_end = ChangePosition(self.rec.contents.len() as u64);
        self.rec.contents.push(0);
        let name = &self.rec.contents[name_start.0 as usize..name_end.0 as usize];
        let mut moved = collect_moved_edges::<_, _, W>(
            txn,
            changes,
            channel,
            new_papa,
            vertex,
            item.metadata,
            old_meta,
            name,
        )?;
        debug!("moved = {:#?}", moved);
        if !moved.resurrect.is_empty() {
            moved.resurrect.extend(moved.alive.into_iter());
            if !moved.need_new_name {
                moved.resurrect.extend(moved.edges.drain(..));
            }
            self.rec.actions.push(Hunk::FileUndel {
                undel: Atom::EdgeMap(EdgeMap {
                    edges: moved.resurrect,
                    inode: item.v_papa,
                }),
                contents: None,
                path: item.full_path.clone(),
            });
        }
        if !moved.edges.is_empty() {
            if moved.need_new_name {
                self.rec.actions.push(Hunk::FileMove {
                    del: Atom::EdgeMap(EdgeMap {
                        edges: moved.edges,
                        inode: item.v_papa,
                    }),
                    add: Atom::NewVertex(NewVertex {
                        up_context: vec![item.v_papa],
                        down_context: vec![vertex.to_option()],
                        start: name_start,
                        end: name_end,
                        flag: EdgeFlags::FOLDER | EdgeFlags::BLOCK,
                        inode: item.v_papa,
                    }),
                    path: item.full_path.clone(),
                });
            } else {
                self.rec.actions.push(Hunk::SolveNameConflict {
                    name: Atom::EdgeMap(EdgeMap {
                        edges: moved.edges,
                        inode: item.v_papa,
                    }),
                    path: item.full_path.clone(),
                });
                self.rec.contents.truncate(name_start.0 as usize)
            }
        } else {
            self.rec.contents.truncate(name_start.0 as usize)
        }
        Ok(())
    }
}

#[derive(Debug)]
struct MovedEdges {
    edges: Vec<NewEdge<Option<ChangeId>>>,
    alive: Vec<NewEdge<Option<ChangeId>>>,
    resurrect: Vec<NewEdge<Option<ChangeId>>>,
    need_new_name: bool,
}

fn collect_moved_edges<T: GraphTxnT, C: ChangeStore, W: WorkingCopy>(
    txn: &T,
    changes: &C,
    channel: &T::Graph,
    parent_pos: Position<Option<ChangeId>>,
    current_pos: Position<ChangeId>,
    new_meta: InodeMetadata,
    old_meta: InodeMetadata,
    name: &[u8],
) -> Result<MovedEdges, RecordError<C::Error, W::Error, T::GraphError>>
where
    <W as crate::working_copy::WorkingCopy>::Error: 'static,
{
    debug!("collect_moved_edges {:?}", current_pos);
    let mut moved = MovedEdges {
        edges: Vec::new(),
        alive: Vec::new(),
        resurrect: Vec::new(),
        need_new_name: true,
    };
    let mut del_del = HashMap::new();
    let mut alive = HashMap::new();
    let mut previous_name = Vec::new();
    for parent in iter_adjacent(
        txn,
        channel,
        current_pos.inode_vertex(),
        EdgeFlags::FOLDER | EdgeFlags::PARENT,
        EdgeFlags::all(),
    )? {
        let parent = parent?;
        if !parent.flag.contains(EdgeFlags::FOLDER | EdgeFlags::PARENT) {
            continue;
        }
        debug!("parent = {:?}", parent);
        let mut parent_was_resurrected = false;
        if !parent.flag.contains(EdgeFlags::PSEUDO) {
            if parent.flag.contains(EdgeFlags::DELETED) {
                moved.resurrect.push(NewEdge {
                    previous: parent.flag - EdgeFlags::PARENT,
                    flag: EdgeFlags::FOLDER | EdgeFlags::BLOCK,
                    from: parent.dest.to_option(),
                    to: current_pos.inode_vertex().to_option(),
                    introduced_by: Some(parent.introduced_by),
                });
                parent_was_resurrected = true;
                let v = alive
                    .entry((parent.dest, current_pos.inode_vertex()))
                    .or_insert_with(Vec::new);
                v.push(None)
            } else {
                let v = alive
                    .entry((parent.dest, current_pos.inode_vertex()))
                    .or_insert_with(Vec::new);
                v.push(Some(parent.introduced_by))
            }
        }
        previous_name.clear();
        let parent_dest = txn.find_block_end(channel, parent.dest).unwrap();
        changes
            .get_contents(
                |p| txn.get_external(p).unwrap(),
                parent_dest,
                &mut previous_name,
            )
            .map_err(RecordError::Changestore)?;
        debug!(
            "parent_dest {:?} {:?}",
            parent_dest,
            std::str::from_utf8(&previous_name[2..])
        );
        debug!("new_meta = {:?}, old_meta = {:?}", new_meta, old_meta);
        let name_changed =
            (previous_name[2..] != name[2..]) || (new_meta != old_meta && cfg!(not(windows)));
        for grandparent in iter_adjacent(
            txn,
            channel,
            parent_dest,
            EdgeFlags::FOLDER | EdgeFlags::PARENT,
            EdgeFlags::all(),
        )? {
            let grandparent = grandparent?;
            if !grandparent
                .flag
                .contains(EdgeFlags::FOLDER | EdgeFlags::PARENT)
                || grandparent.flag.contains(EdgeFlags::PSEUDO)
            {
                continue;
            }
            debug!("grandparent: {:?}", grandparent);
            let grandparent_dest = txn.find_block_end(channel, grandparent.dest).unwrap();
            assert_eq!(grandparent_dest.start, grandparent_dest.end);
            debug!(
                "grandparent_dest {:?} {:?}",
                grandparent_dest,
                std::str::from_utf8(&previous_name[2..])
            );
            let grandparent_changed = parent_pos != grandparent.dest.to_option();
            debug!("change = {:?}", grandparent_changed || name_changed);

            if grandparent.flag.contains(EdgeFlags::DELETED) {
                if !grandparent_changed && !name_changed {
                    // We resurrect the name
                    moved.resurrect.push(NewEdge {
                        previous: grandparent.flag - EdgeFlags::PARENT,
                        flag: EdgeFlags::FOLDER | EdgeFlags::BLOCK,
                        from: grandparent.dest.to_option(),
                        to: parent_dest.to_option(),
                        introduced_by: Some(grandparent.introduced_by),
                    });
                    if !parent_was_resurrected && !parent.flag.contains(EdgeFlags::PSEUDO) {
                        moved.alive.push(NewEdge {
                            previous: parent.flag - EdgeFlags::PARENT,
                            flag: EdgeFlags::FOLDER | EdgeFlags::BLOCK,
                            from: parent.dest.to_option(),
                            to: current_pos.inode_vertex().to_option(),
                            introduced_by: Some(parent.introduced_by),
                        })
                    }
                    moved.need_new_name = false
                } else {
                    // Clean up the extra deleted edges.
                    debug!("cleanup");
                    let v = del_del
                        .entry((grandparent.dest, parent_dest))
                        .or_insert_with(Vec::new);
                    v.push(Some(grandparent.introduced_by))
                }
            } else if grandparent_changed || name_changed {
                moved.edges.push(NewEdge {
                    previous: parent.flag - EdgeFlags::PARENT,
                    flag: EdgeFlags::FOLDER | EdgeFlags::BLOCK | EdgeFlags::DELETED,
                    from: grandparent.dest.to_option(),
                    to: parent_dest.to_option(),
                    introduced_by: Some(grandparent.introduced_by),
                });
                // The following is really important in missing context detection:
                if !parent_was_resurrected && !parent.flag.contains(EdgeFlags::PSEUDO) {
                    moved.alive.push(NewEdge {
                        previous: parent.flag - EdgeFlags::PARENT,
                        flag: EdgeFlags::FOLDER | EdgeFlags::BLOCK,
                        from: parent.dest.to_option(),
                        to: current_pos.inode_vertex().to_option(),
                        introduced_by: Some(parent.introduced_by),
                    })
                }
            } else {
                let v = alive
                    .entry((grandparent.dest, parent_dest))
                    .or_insert_with(Vec::new);
                v.push(Some(grandparent.introduced_by));
                moved.need_new_name = false
            }
        }
    }

    for ((from, to), intro) in del_del {
        if intro.len() > 1 {
            for introduced_by in intro {
                if introduced_by.is_some() {
                    moved.edges.push(NewEdge {
                        previous: EdgeFlags::FOLDER | EdgeFlags::BLOCK | EdgeFlags::DELETED,
                        flag: EdgeFlags::FOLDER | EdgeFlags::BLOCK | EdgeFlags::DELETED,
                        from: from.to_option(),
                        to: to.to_option(),
                        introduced_by,
                    })
                }
            }
        }
    }

    for ((from, to), intro) in alive {
        if intro.len() > 1 || !moved.resurrect.is_empty() {
            for introduced_by in intro {
                if introduced_by.is_some() {
                    moved.alive.push(NewEdge {
                        previous: EdgeFlags::FOLDER | EdgeFlags::BLOCK,
                        flag: EdgeFlags::FOLDER | EdgeFlags::BLOCK,
                        from: from.to_option(),
                        to: to.to_option(),
                        introduced_by,
                    })
                }
            }
        }
    }

    Ok(moved)
}

impl Builder {
    fn record_deleted_file<
        T: GraphTxnT + TreeTxnT<TreeError = <T as GraphTxnT>::GraphError>,
        W: WorkingCopy,
    >(
        &mut self,
        txn: &T,
        channel: &T::Graph,
        working_copy: &W,
        full_path: &str,
        current_vertex: Position<ChangeId>,
    ) -> Result<(), TxnErr<T::GraphError>> {
        debug!("record_deleted_file {:?} {:?}", current_vertex, full_path);
        let mut stack = vec![(current_vertex.inode_vertex(), None)];
        let mut visited = HashSet::new();
        while let Some((vertex, inode)) = stack.pop() {
            debug!("vertex {:?}, inode {:?}", vertex, inode);
            if let Some(path) = tree_path(txn, vertex.start_pos())? {
                if working_copy.file_metadata(&path).is_ok() {
                    debug!("not deleting {:?}", path);
                    continue;
                }
            }

            // Kill this vertex
            if let Some(inode) = inode {
                self.delete_file_edge(txn, channel, vertex, inode)?
            } else if vertex.start == vertex.end {
                debug!("delete_recursively {:?}", vertex);
                // Killing an inode.
                if !self.deleted_vertices.insert(vertex.start_pos()) {
                    continue;
                }
                if let Some(inode) = txn.get_revinodes(vertex.start_pos(), None)? {
                    debug!(
                        "delete_recursively, vertex = {:?}, inode = {:?}",
                        vertex, inode
                    );
                    self.recorded_inodes
                        .insert(inode, vertex.start_pos().to_option());
                    self.rec
                        .updatables
                        .insert(self.rec.actions.len(), InodeUpdate::Deleted { inode });
                }
                self.delete_inode_vertex(txn, channel, vertex, vertex.start_pos(), full_path)?
            }

            // Move on to the descendants.
            for edge in iter_adjacent(
                txn,
                channel,
                vertex,
                EdgeFlags::empty(),
                EdgeFlags::all() - EdgeFlags::DELETED - EdgeFlags::PARENT,
            )? {
                let edge = edge?;
                debug!("delete_recursively, edge: {:?}", edge);
                let dest = txn
                    .find_block(channel, edge.dest)
                    .expect("delete_recursively, descendants");
                let inode = if inode.is_some() {
                    assert!(!edge.flag.contains(EdgeFlags::FOLDER));
                    inode
                } else if edge.flag.contains(EdgeFlags::FOLDER) {
                    None
                } else {
                    assert_eq!(vertex.start, vertex.end);
                    Some(vertex.start_pos())
                };
                if visited.insert(edge.dest) {
                    stack.push((dest, inode))
                }
            }
        }
        Ok(())
    }

    fn delete_inode_vertex<T: GraphTxnT>(
        &mut self,
        txn: &T,
        channel: &T::Graph,
        vertex: Vertex<ChangeId>,
        inode: Position<ChangeId>,
        path: &str,
    ) -> Result<(), TxnErr<T::GraphError>> {
        debug!("delete_inode_vertex {:?}", path);
        let mut edges = Vec::new();
        for parent in iter_adjacent(
            txn,
            channel,
            vertex,
            EdgeFlags::FOLDER | EdgeFlags::PARENT,
            EdgeFlags::all(),
        )? {
            let parent = parent?;
            if !parent.flag.contains(EdgeFlags::PARENT) {
                continue;
            }
            assert!(parent.flag.contains(EdgeFlags::FOLDER));
            let parent_dest = txn.find_block_end(channel, parent.dest).unwrap();
            for grandparent in iter_adjacent(
                txn,
                channel,
                parent_dest,
                EdgeFlags::FOLDER | EdgeFlags::PARENT,
                EdgeFlags::all(),
            )? {
                let grandparent = grandparent?;
                if !grandparent.flag.contains(EdgeFlags::PARENT)
                    || grandparent.flag.contains(EdgeFlags::PSEUDO)
                {
                    continue;
                }
                assert!(grandparent.flag.contains(EdgeFlags::PARENT));
                assert!(grandparent.flag.contains(EdgeFlags::FOLDER));
                edges.push(NewEdge {
                    previous: grandparent.flag - EdgeFlags::PARENT,
                    flag: EdgeFlags::FOLDER | EdgeFlags::BLOCK | EdgeFlags::DELETED,
                    from: grandparent.dest.to_option(),
                    to: parent_dest.to_option(),
                    introduced_by: Some(grandparent.introduced_by),
                });
            }
            if !parent.flag.contains(EdgeFlags::PSEUDO) {
                edges.push(NewEdge {
                    previous: parent.flag - EdgeFlags::PARENT,
                    flag: EdgeFlags::FOLDER | EdgeFlags::BLOCK | EdgeFlags::DELETED,
                    from: parent.dest.to_option(),
                    to: vertex.to_option(),
                    introduced_by: Some(parent.introduced_by),
                });
            }
        }
        debug!("deleting {:?}", edges);
        if !edges.is_empty() {
            self.rec.actions.push(Hunk::FileDel {
                del: Atom::EdgeMap(EdgeMap {
                    edges,
                    inode: inode.to_option(),
                }),
                contents: None,
                path: path.to_string(),
            })
        }
        Ok(())
    }

    fn delete_file_edge<T: GraphTxnT>(
        &mut self,
        txn: &T,
        channel: &T::Graph,
        to: Vertex<ChangeId>,
        inode: Position<ChangeId>,
    ) -> Result<(), TxnErr<T::GraphError>> {
        if let Some(Hunk::FileDel {
            ref mut contents, ..
        }) = self.rec.actions.last_mut()
        {
            if contents.is_none() {
                *contents = Some(Atom::EdgeMap(EdgeMap {
                    edges: Vec::new(),
                    inode: inode.to_option(),
                }))
            }
            if let Some(Atom::EdgeMap(mut e)) = contents.take() {
                for parent in iter_adjacent(
                    txn,
                    channel,
                    to,
                    EdgeFlags::PARENT,
                    EdgeFlags::all() - EdgeFlags::DELETED,
                )? {
                    let parent = parent?;
                    if parent.flag.contains(EdgeFlags::PSEUDO) {
                        continue;
                    }
                    assert!(parent.flag.contains(EdgeFlags::PARENT));
                    assert!(!parent.flag.contains(EdgeFlags::FOLDER));
                    e.edges.push(NewEdge {
                        previous: parent.flag - EdgeFlags::PARENT,
                        flag: (parent.flag - EdgeFlags::PARENT) | EdgeFlags::DELETED,
                        from: parent.dest.to_option(),
                        to: to.to_option(),
                        introduced_by: Some(parent.introduced_by),
                    })
                }
                if !e.edges.is_empty() {
                    *contents = Some(Atom::EdgeMap(e))
                }
            }
        }
        Ok(())
    }
}
