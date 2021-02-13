//! Manipulating the internal representation of files and directories
//! tracked by Pijul (i.e. adding files, removing files, getting file
//! names…).
//!
//! Pijul tracks files in two different ways: one is the *graph*,
//! where changes are applied. The other one is the *working copy*,
//! where some filesystem changes are not yet recorded. The purpose of
//! this double representation is to be able to compare a file from
//! the graph with its version in the working copy, even if its name
//! has changed in the working copy.
//!
//! The functions of this module work at exactly one of these two
//! levels. Changing the graph is done by recording and applying a
//! change, and changing the working copy is done either by some of the
//! functions in this module, or by outputting the graph to the
//! working copy (using the [output module](../output/index.html)).
use crate::changestore::*;
use crate::pristine::*;
use crate::small_string::*;
use std::collections::HashSet;
use std::iter::Iterator;

#[derive(Debug, Error)]
pub enum FsError<T: std::error::Error + 'static> {
    #[error(transparent)]
    NotFound(#[from] FsNotFound),
    #[error("File already in repository: {0}")]
    AlreadyInRepo(String),
    #[error(transparent)]
    Txn(T),
}

#[derive(Debug, Error)]
pub enum FsErrorC<C: std::error::Error + 'static, T: std::error::Error + 'static> {
    #[error(transparent)]
    Txn(T),
    #[error(transparent)]
    Changestore(C),
    #[error(transparent)]
    NotFound(#[from] FsNotFound),
}

#[derive(Debug, Error)]
#[error("Path not found: {0}")]
pub struct FsNotFound(String);

impl<T: std::error::Error + 'static> std::convert::From<TxnErr<T>> for FsError<T> {
    fn from(e: TxnErr<T>) -> Self {
        FsError::Txn(e.0)
    }
}

impl<C: std::error::Error + 'static, T: std::error::Error + 'static> std::convert::From<TxnErr<T>>
    for FsErrorC<C, T>
{
    fn from(e: TxnErr<T>) -> Self {
        FsErrorC::Txn(e.0)
    }
}

pub(crate) fn create_new_inode<T: TreeMutTxnT>(txn: &mut T) -> Result<Inode, TxnErr<T::TreeError>> {
    let mut already_taken = true;
    let mut inode: Inode = Inode::ROOT;
    while already_taken {
        inode = Inode::random();
        already_taken = txn.get_revtree(inode, None)?.is_some();
    }
    Ok(inode)
}

/// Test whether `inode` is the inode of a directory (as opposed to a
/// file).
pub fn is_directory<T: TreeTxnT>(txn: &T, inode: Inode) -> Result<bool, TxnErr<T::TreeError>> {
    if inode == Inode::ROOT {
        return Ok(true);
    }
    let pathid = OwnedPathId {
        parent_inode: inode,
        basename: SmallString::new(),
    };
    for x in txn.iter_tree(pathid.clone(), None)? {
        let (pid, _) = x?;
        if pid < pathid {
            continue;
        } else if pid > pathid {
            break;
        }
        return Ok(true);
    }
    Ok(false)
}

fn closest_in_repo_ancestor<'a, T: TreeTxnT>(
    txn: &T,
    path: &'a str,
) -> Result<(Inode, std::iter::Peekable<crate::path::Components<'a>>), TxnErr<T::TreeError>> {
    let mut components = crate::path::components(path).peekable();
    let mut fileid = OwnedPathId {
        parent_inode: Inode::ROOT,
        basename: SmallString::new(),
    };
    while let Some(c) = components.peek() {
        trace!("component {:?}", c);
        fileid.basename.clone_from_str(c);
        trace!("{:?}", fileid);
        let mut found = false;
        for x in txn.iter_tree(fileid.clone(), None)? {
            let (id, inode) = x?;
            trace!(
                "id = {:?}, inode = {:?}, cmp = {:?}",
                id,
                inode,
                id > fileid
            );
            if id > fileid {
                break;
            } else if id < fileid {
                continue;
            }
            found = true;
            fileid.parent_inode = inode;
            break;
        }
        if found {
            components.next();
        } else {
            break;
        }
    }
    Ok((fileid.parent_inode, components))
}

/// Find the inode corresponding to that path, if it exists.
pub fn find_inode<T: TreeTxnT>(txn: &T, path: &str) -> Result<Inode, FsError<T::TreeError>> {
    debug!("find_inode");
    let (inode, mut remaining_path_components) = closest_in_repo_ancestor(txn, path)?;
    debug!("/find_inode");
    if let Some(c) = remaining_path_components.next() {
        debug!("c = {:?}", c);
        Err(FsNotFound(path.to_string()).into())
    } else {
        Ok(inode)
    }
}

/// Returns whether a path is registered in the working copy.
pub fn is_tracked<T: TreeTxnT>(txn: &T, path: &str) -> Result<bool, TxnErr<T::TreeError>> {
    debug!("is_tracked {:?}", path);
    let (_, mut remaining_path_components) = closest_in_repo_ancestor(txn, path)?;
    debug!("/is_tracked {:?}", path);
    Ok(remaining_path_components.next().is_none())
}

/// Find the filename leading from the root to ~inode~.
pub fn inode_filename<T: TreeTxnT>(
    txn: &T,
    inode: Inode,
) -> Result<Option<String>, TxnErr<T::TreeError>> {
    let mut components = Vec::new();
    let mut current = inode;
    loop {
        match txn.get_revtree(current, None)? {
            Some(v) => {
                components.push(v.basename);
                current = v.parent_inode;
                if current == Inode::ROOT {
                    break;
                }
            }
            None => {
                debug!("filename_of_inode: not in tree");
                return Ok(None);
            }
        }
    }

    let mut path = String::new();
    for c in components.iter().rev() {
        if !path.is_empty() {
            path.push('/')
        }
        path.push_str(c.as_str());
    }
    Ok(Some(path))
}

/// Record the information that `parent_inode` is now a parent of
/// file `filename`, and `filename` has inode `child_inode`.
fn make_new_child<T: TreeMutTxnT>(
    txn: &mut T,
    parent_inode: Inode,
    filename: &str,
    is_dir: bool,
    child_inode: Option<Inode>,
) -> Result<Inode, FsError<T::TreeError>> {
    let parent_id = OwnedPathId {
        parent_inode,
        basename: SmallString::from_str(filename),
    };

    if let Some(inode) = txn.get_tree(parent_id.as_file_id(), None)? {
        debug!("inode = {:?}", inode);
        if let Some(child) = child_inode {
            if child == inode {
                // No need to do anything.
                Ok(inode)
            } else {
                del_tree_with_rev(txn, parent_id.as_file_id(), inode)?;
                if let Some(vertex) = txn.get_inodes(inode, None)? {
                    del_inodes_with_rev(txn, inode, vertex)?;
                }
                put_tree_with_rev(txn, parent_id.as_file_id(), child)?;
                Ok(child)
            }
        } else {
            Err(FsError::AlreadyInRepo(filename.to_string()))
        }
    } else {
        let child_inode = match child_inode {
            None => create_new_inode(txn)?,
            Some(i) => i,
        };
        debug!("make_new_child: {:?} {:?}", parent_id, child_inode);
        put_tree_with_rev(txn, parent_id.as_file_id(), child_inode)?;

        if is_dir {
            let dir_id = OwnedPathId {
                parent_inode: child_inode,
                basename: SmallString::new(),
            };
            txn.put_tree(dir_id.as_file_id(), child_inode)?;
        };
        Ok(child_inode)
    }
}

pub(crate) fn add_inode<T: TreeMutTxnT>(
    txn: &mut T,
    inode: Option<Inode>,
    path: &str,
    is_dir: bool,
) -> Result<(), FsError<T::TreeError>> {
    debug!("add_inode");
    if let Some(parent) = crate::path::parent(path) {
        let (current_inode, unrecorded_path) = closest_in_repo_ancestor(txn, parent)?;
        let mut current_inode = current_inode;
        debug!("add_inode: closest = {:?}", current_inode);
        for c in unrecorded_path {
            debug!("unrecorded: {:?}", c);
            current_inode = make_new_child(txn, current_inode, c, true, None)?;
        }
        let file_name = crate::path::file_name(path).unwrap();
        debug!("add_inode: file_name = {:?}", file_name);
        make_new_child(txn, current_inode, file_name, is_dir, inode)?;
    }
    Ok(())
}

/// Move an inode (file or directory) from `origin` to `destination`,
/// (in the working copy).
///
/// **Warning**: both `origin` and `destination` must be full paths to
/// the inode being moved (unlike e.g. in the `mv` Unix command).
pub fn move_file<T: TreeMutTxnT>(
    txn: &mut T,
    origin: &str,
    destination: &str,
) -> Result<(), FsError<T::TreeError>> {
    debug!("move_file: {},{}", origin, destination);
    move_file_by_inode(txn, find_inode(txn, origin)?, destination)?;
    Ok(())
}

pub fn move_file_by_inode<T: TreeMutTxnT>(
    txn: &mut T,
    inode: Inode,
    destination: &str,
) -> Result<(), FsError<T::TreeError>> {
    let fileref = txn.get_revtree(inode, None)?.unwrap().to_owned();
    debug!("fileref = {:?}", fileref);
    del_tree_with_rev(txn, fileref.as_file_id(), inode)?;
    debug!("inode={:?} destination={}", inode, destination);
    let is_dir = txn
        .get_tree(
            (OwnedPathId {
                parent_inode: inode,
                basename: SmallString::new(),
            })
            .as_file_id(),
            None,
        )?
        .is_some();
    add_inode(txn, Some(inode), destination, is_dir)?;
    Ok(())
}

pub(crate) fn rec_delete<T: TreeMutTxnT>(
    txn: &mut T,
    parent: OwnedPathId,
    inode: Inode,
    delete_inodes: bool,
) -> Result<(), FsError<T::TreeError>> {
    let file_id = OwnedPathId {
        parent_inode: inode,
        basename: SmallString::new(),
    };
    let mut children = Vec::new();
    let mut is_dir = false;
    for x in txn.iter_tree(file_id.clone(), None)? {
        let (k, inode) = x?;
        if k.parent_inode > file_id.parent_inode {
            break;
        } else if k.parent_inode < file_id.parent_inode {
            continue;
        }
        debug!("iter_tree: {:?} {:?}", k, inode);
        is_dir = true;
        if !k.basename.is_empty() {
            children.push((k, inode))
        }
    }
    for (k, inode_) in children {
        assert_ne!(inode, inode_);
        rec_delete(txn, k, inode_, delete_inodes)?;
    }
    debug!(
        "rec_delete: {:?}, {:?}, {:?}, {:?}",
        parent, file_id, inode, is_dir
    );
    if is_dir {
        assert!(inode.is_root() || txn.del_tree(file_id.as_file_id(), Some(inode))?);
    }
    if !inode.is_root() && del_tree_with_rev(txn, parent.as_file_id(), inode)? {
        if delete_inodes {
            if let Some(vertex) = txn.get_inodes(inode, None)? {
                del_inodes_with_rev(txn, inode, vertex)?;
            }
        }
    } else {
        debug!(
            "rec_delete: {:?} {:?} not present",
            parent.as_file_id(),
            inode
        );
    }
    Ok(())
}

/// Removes a file from the repository.
pub fn remove_file<T: TreeMutTxnT>(txn: &mut T, path: &str) -> Result<(), FsError<T::TreeError>> {
    debug!("remove file {:?}", path);
    let inode = find_inode(txn, path)?;
    let parent = if inode.is_root() {
        OwnedPathId {
            parent_inode: Inode::ROOT,
            basename: SmallString::new(),
        }
    } else {
        txn.get_revtree(inode, None)?.unwrap().to_owned()
    };
    debug!("remove file {:?} {:?}", parent, inode);
    rec_delete(txn, parent, inode, false)?;
    Ok(())
}

/// An iterator over the children (i.e. one level down) of an inode in
/// the working copy.
///
/// Constructed using
/// [`working_copy_children`](fn.working_copy_children.html).
pub struct WorkingCopyChildren<'txn, T: TreeTxnT> {
    iter: crate::pristine::Cursor<T, &'txn T, T::TreeCursor, OwnedPathId, Inode>,
    inode: Inode,
}

impl<'txn, T: TreeTxnT> Iterator for WorkingCopyChildren<'txn, T> {
    type Item = Result<(SmallString, Inode), T::TreeError>;
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            match self.iter.next() {
                Some(Ok((k, v))) => {
                    if k.parent_inode == self.inode {
                        if k.basename.len() > 0 {
                            return Some(Ok((k.basename, v)));
                        }
                    } else if k.parent_inode > self.inode {
                        return None;
                    }
                }
                None => return None,
                Some(Err(e)) => return Some(Err(e.0)),
            }
        }
    }
}

/// Returns a list of the children of an inode, in the working copy.
pub fn working_copy_children<T: TreeTxnT>(
    txn: &T,
    inode: Inode,
) -> Result<WorkingCopyChildren<T>, T::TreeError> {
    Ok(WorkingCopyChildren {
        iter: txn
            .iter_tree(
                OwnedPathId {
                    parent_inode: inode,
                    basename: SmallString::new(),
                },
                None,
            )
            .map_err(|e| e.0)?,
        inode,
    })
}

/// An iterator over all the paths in the working copy.
///
/// Constructed using [`iter_working_copy`](fn.iter_working_copy.html).
pub struct WorkingCopyIterator<'txn, T: TreeTxnT> {
    stack: Vec<(Inode, String)>,
    txn: &'txn T,
}

impl<'txn, T: TreeTxnT> Iterator for WorkingCopyIterator<'txn, T> {
    type Item = Result<(Inode, String), T::TreeError>;
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if let Some((inode, name)) = self.stack.pop() {
                let fileid = OwnedPathId {
                    parent_inode: inode,
                    basename: SmallString::from_str(""),
                };
                let len = self.stack.len();
                let iter = match self.txn.iter_tree(fileid, None) {
                    Ok(iter) => iter,
                    Err(e) => return Some(Err(e.0)),
                };
                for x in iter {
                    let (k, v) = match x {
                        Ok(x) => x,
                        Err(e) => return Some(Err(e.0)),
                    };
                    if k.parent_inode < inode {
                        continue;
                    } else if k.parent_inode > inode {
                        break;
                    }
                    if !k.basename.is_empty() {
                        let mut name = name.clone();
                        crate::path::push(&mut name, k.basename.as_str());
                        self.stack.push((v, name))
                    }
                }
                (&mut self.stack[len..]).reverse();
                if !name.is_empty() {
                    return Some(Ok((inode, name)));
                }
            } else {
                return None;
            }
        }
    }
}

/// Returns an iterator over all the files in the working copy.
pub fn iter_working_copy<T: TreeTxnT>(txn: &T, root: Inode) -> WorkingCopyIterator<T> {
    WorkingCopyIterator {
        stack: vec![(root, String::new())],
        txn,
    }
}

/// An iterator over the descendants of an
/// inode key in the graph.
///
/// Constructed using
/// [`iter_graph_descendants`](fn.iter_graph_descendants.html).
pub struct GraphDescendants<'txn, T: GraphTxnT> {
    txn: &'txn T,
    channel: &'txn T::Graph,
    stack: Vec<AdjacentIterator<'txn, T>>,
    visited: HashSet<Position<ChangeId>>,
}

impl<'txn, T: GraphTxnT> Iterator for GraphDescendants<'txn, T> {
    type Item = Result<Position<ChangeId>, T::GraphError>;
    fn next(&mut self) -> Option<Self::Item> {
        if let Some(mut adj) = self.stack.pop() {
            match adj.next() {
                Some(Ok(child)) => {
                    self.stack.push(adj);
                    let dest = match self.txn.find_block(self.channel, child.dest) {
                        Ok(dest) => dest,
                        Err(BlockError::Txn(t)) => return Some(Err(t)),
                        Err(e) => panic!("{}", e),
                    };
                    let grandchild = match iter_adjacent(
                        self.txn,
                        self.channel,
                        dest,
                        EdgeFlags::FOLDER,
                        EdgeFlags::FOLDER | EdgeFlags::PSEUDO | EdgeFlags::BLOCK,
                    ) {
                        Ok(mut x) => match x.next().unwrap() {
                            Ok(x) => x,
                            Err(e) => return Some(Err(e.0)),
                        },
                        Err(e) => return Some(Err(e.0)),
                    };

                    if self.visited.insert(grandchild.dest) {
                        match iter_adjacent(
                            self.txn,
                            self.channel,
                            grandchild.dest.inode_vertex(),
                            EdgeFlags::FOLDER,
                            EdgeFlags::FOLDER | EdgeFlags::PSEUDO | EdgeFlags::BLOCK,
                        ) {
                            Ok(adj) => self.stack.push(adj),
                            Err(e) => return Some(Err(e.0)),
                        }
                    }
                    return Some(Ok(grandchild.dest));
                }
                Some(Err(e)) => return Some(Err(e.0)),
                None => {
                    // No child left, actually pop.
                }
            }
        }
        None
    }
}

/// Returns a list of files under the given key.  The root key is
/// [`pristine::Vertex::ROOT`](../pristine/constant.Vertex::ROOT.html).
pub fn iter_graph_descendants<'txn, T: GraphTxnT>(
    txn: &'txn T,
    channel: &'txn T::Graph,
    key: Position<ChangeId>,
) -> Result<GraphDescendants<'txn, T>, T::GraphError> {
    Ok(GraphDescendants {
        stack: vec![iter_adjacent(
            txn,
            &channel,
            key.inode_vertex(),
            EdgeFlags::FOLDER,
            EdgeFlags::FOLDER | EdgeFlags::PSEUDO | EdgeFlags::BLOCK,
        )
        .map_err(|e| e.0)?],
        visited: HashSet::new(),
        txn,
        channel,
    })
}

/// An iterator over the children (i.e. a single level down) of an
/// inode key in the graph.
///
/// Constructed using
/// [`iter_graph_children`](fn.iter_graph_children.html).
pub struct GraphChildren<'txn, 'changes, T: GraphTxnT, P: ChangeStore + 'changes> {
    txn: &'txn T,
    channel: &'txn T::Graph,
    adj: AdjacentIterator<'txn, T>,
    changes: &'changes P,
    buf: Vec<u8>,
}

impl<'txn, 'changes, T: GraphTxnT, P: ChangeStore + 'changes> Iterator
    for GraphChildren<'txn, 'changes, T, P>
{
    type Item = Result<(Position<ChangeId>, ChangeId, InodeMetadata, String), T::GraphError>;
    fn next(&mut self) -> Option<Self::Item> {
        let child = match self.adj.next()? {
            Ok(child) => child,
            Err(e) => return Some(Err(e.0)),
        };
        let dest = self.txn.find_block(self.channel, child.dest).unwrap();
        let mut buf = std::mem::replace(&mut self.buf, Vec::new());
        self.changes
            .get_contents(|p| self.txn.get_external(p).unwrap(), dest, &mut buf)
            .unwrap();
        self.buf = buf;
        let (perms, basename) = self.buf.split_at(2);
        let perms = InodeMetadata::from_basename(perms);
        let basename = std::str::from_utf8(basename).unwrap();

        let grandchild = match iter_adjacent(
            self.txn,
            self.channel,
            dest,
            EdgeFlags::FOLDER,
            EdgeFlags::FOLDER | EdgeFlags::PSEUDO | EdgeFlags::BLOCK,
        ) {
            Ok(mut adj) => match adj.next() {
                Some(Ok(n)) => n,
                None => unreachable!(),
                Some(Err(e)) => return Some(Err(e.0)),
            },
            Err(e) => return Some(Err(e.0)),
        };
        Some(Ok((
            grandchild.dest,
            grandchild.introduced_by,
            perms,
            basename.to_string(),
        )))
    }
}

/// Returns a list of files under the given key.  The root key is
/// [`pristine::Vertex::ROOT`](../pristine/constant.Vertex::ROOT.html).
pub fn iter_graph_children<'txn, 'changes, T, P>(
    txn: &'txn T,
    changes: &'changes P,
    channel: &'txn T::Graph,
    key: Position<ChangeId>,
) -> Result<GraphChildren<'txn, 'changes, T, P>, T::GraphError>
where
    T: GraphTxnT,
    P: ChangeStore,
{
    Ok(GraphChildren {
        buf: Vec::new(),
        adj: iter_adjacent(
            txn,
            channel,
            key.inode_vertex(),
            EdgeFlags::FOLDER,
            EdgeFlags::FOLDER | EdgeFlags::PSEUDO | EdgeFlags::BLOCK,
        )
        .map_err(|e| e.0)?,
        txn,
        channel,
        changes,
    })
}

/// An iterator over the basenames of an "inode key" in the graph.
///
/// See [`iter_basenames`](fn.iter_basenames.html).
pub struct GraphBasenames<'txn, 'changes, T: GraphTxnT, P: ChangeStore + 'changes> {
    txn: &'txn T,
    channel: &'txn T::Graph,
    adj: AdjacentIterator<'txn, T>,
    changes: &'changes P,
    buf: Vec<u8>,
}

impl<'txn, 'changes, T: GraphTxnT, P: ChangeStore + 'changes> Iterator
    for GraphBasenames<'txn, 'changes, T, P>
{
    type Item = Result<(Position<ChangeId>, InodeMetadata, String), T::GraphError>;
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let parent = match self.adj.next() {
                Some(Ok(n)) => n,
                Some(Err(e)) => return Some(Err(e.0)),
                None => return None,
            };
            let dest = self.txn.find_block_end(&self.channel, parent.dest).unwrap();
            let mut buf = std::mem::replace(&mut self.buf, Vec::new());
            self.changes
                .get_contents(|p| self.txn.get_external(p).unwrap(), dest, &mut buf)
                .unwrap();
            self.buf = buf;
            let (perms, basename) = self.buf.split_at(2);
            let perms = InodeMetadata::from_basename(perms);
            let basename = std::str::from_utf8(basename).unwrap().to_string();
            match iter_adjacent(
                self.txn,
                &self.channel,
                dest,
                EdgeFlags::FOLDER | EdgeFlags::PARENT,
                EdgeFlags::FOLDER | EdgeFlags::PARENT | EdgeFlags::PSEUDO | EdgeFlags::BLOCK,
            ) {
                Ok(mut adj) => match adj.next() {
                    Some(Ok(grandparent)) => return Some(Ok((grandparent.dest, perms, basename))),
                    Some(Err(e)) => return Some(Err(e.0)),
                    None => {}
                },
                Err(e) => return Some(Err(e.0)),
            }
        }
    }
}

/// List all the basenames of an "inode key" in the graph (more than
/// one name means a conflict).
///
/// See also [`iter_paths`](fn.iter_paths.html).
pub fn iter_basenames<'txn, 'changes, T, P>(
    txn: &'txn T,
    changes: &'changes P,
    channel: &'txn T::Graph,
    pos: Position<ChangeId>,
) -> Result<GraphBasenames<'txn, 'changes, T, P>, T::GraphError>
where
    T: GraphTxnT,
    P: ChangeStore,
{
    Ok(GraphBasenames {
        buf: Vec::new(),
        adj: iter_adjacent(
            txn,
            channel,
            pos.inode_vertex(),
            EdgeFlags::FOLDER | EdgeFlags::PARENT,
            EdgeFlags::FOLDER | EdgeFlags::PARENT | EdgeFlags::PSEUDO,
        )
        .map_err(|e| e.0)?,
        txn,
        channel,
        changes,
    })
}

/// Traverse the paths in the graph to a key. **Warning:** there might
/// be a number of paths exponential in the number of conflicts.
///
/// This function takes a closure `f`, which gets called on each path
/// with an iterator over the keys from the root to `key`. This
/// function stops when `f` returns `false` (or when all the paths
/// have been traversed).
///
/// See also [`iter_basenames`](fn.iter_basenames.html).
pub fn iter_paths<T: GraphTxnT, F: FnMut(&mut dyn Iterator<Item = Position<ChangeId>>) -> bool>(
    txn: &T,
    graph: &T::Graph,
    key: Position<ChangeId>,
    mut f: F,
) -> Result<(), TxnErr<T::GraphError>> {
    let mut stack: Vec<(Position<ChangeId>, bool)> = vec![(key, true)];
    while let Some((cur_key, on_stack)) = stack.pop() {
        if cur_key.is_root() {
            if !f(&mut stack
                .iter()
                .filter_map(|(key, on_path)| if *on_path { Some(*key) } else { None }))
            {
                break;
            }
        } else if !on_stack {
            stack.push((cur_key, true));
            let len = stack.len();
            let f = EdgeFlags::parent_folder();
            for parent in iter_adjacent(
                txn,
                &graph,
                cur_key.inode_vertex(),
                f,
                f | EdgeFlags::PSEUDO,
            )? {
                let parent_dest = txn.find_block_end(&graph, parent?.dest).unwrap();
                for grandparent in
                    iter_adjacent(txn, &graph, parent_dest, f, f | EdgeFlags::PSEUDO)?
                {
                    stack.push((grandparent?.dest, false))
                }
            }
            if stack.len() == len {
                stack.pop();
            }
        }
    }
    Ok(())
}

pub(crate) fn follow_oldest_path<T: ChannelTxnT, C: ChangeStore>(
    changes: &C,
    txn: &T,
    channel: &T::Channel,
    path: &str,
) -> Result<(Position<ChangeId>, bool), FsErrorC<C::Error, T::GraphError>> {
    use crate::pristine::*;
    debug!("follow_oldest_path = {:?}", path);
    let mut current = Position::ROOT;
    let flag0 = EdgeFlags::FOLDER;
    let flag1 = flag0 | EdgeFlags::BLOCK | EdgeFlags::PSEUDO;
    let mut name_buf = Vec::new();
    let mut ambiguous = false;
    for c in crate::path::components(path) {
        let mut next = None;
        for name in iter_adjacent(
            txn,
            txn.graph(channel),
            current.inode_vertex(),
            flag0,
            flag1,
        )? {
            let name = name?;
            let name_dest = txn.find_block(txn.graph(channel), name.dest).unwrap();
            name_buf.clear();
            debug!("getting contents {:?}", name);
            changes
                .get_contents(|h| txn.get_external(h).unwrap(), name_dest, &mut name_buf)
                .map_err(FsErrorC::Changestore)?;

            if std::str::from_utf8(&name_buf[2..]) == Ok(c) {
                let age = txn
                    .get_changeset(txn.changes(&channel), name.dest.change)
                    .unwrap();
                if let Some((ref mut next, ref mut next_age)) = next {
                    ambiguous = true;
                    if age < *next_age {
                        *next = name_dest;
                        *next_age = age;
                    }
                } else {
                    next = Some((name_dest, age));
                }
            }
        }
        if let Some((next, _)) = next {
            current = iter_adjacent(txn, txn.graph(channel), next, flag0, flag1)?
                .next()
                .unwrap()?
                .dest
        } else {
            return Err(FsErrorC::NotFound(FsNotFound(path.to_string())));
        }
    }
    Ok((current, ambiguous))
}

pub fn find_path<T: ChannelTxnT, C: ChangeStore>(
    changes: &C,
    txn: &T,
    channel: &T::Channel,
    youngest: bool,
    mut v: Position<ChangeId>,
) -> Result<(String, bool), crate::output::FileError<C::Error, T::GraphError>> {
    debug!("oldest_path = {:?}", v);
    let mut path = Vec::new();
    let mut name_buf = Vec::new();
    let flag0 = EdgeFlags::FOLDER | EdgeFlags::PARENT;
    let flag1 = EdgeFlags::all();
    let mut all_alive = true;
    while !v.change.is_root() {
        let mut next_v = None;
        let mut alive = false;
        let inode_vertex = txn.find_block_end(txn.graph(channel), v).unwrap();
        assert_eq!(inode_vertex, v.inode_vertex());
        for name in iter_adjacent(txn, txn.graph(channel), v.inode_vertex(), flag0, flag1)? {
            let name = name?;
            if !name.flag.contains(EdgeFlags::PARENT) {
                continue;
            }
            debug!("oldest_path, name = {:?}", name);
            let age = txn
                .get_changeset(txn.changes(&channel), name.dest.change)?
                .unwrap();

            let name_dest = txn.find_block_end(txn.graph(channel), name.dest).unwrap();
            debug!("name_dest = {:?}", name_dest);
            let mut next = None;
            for e in iter_adjacent(txn, txn.graph(channel), name_dest, flag0, flag1)? {
                let e = e?;
                if e.flag.contains(EdgeFlags::PARENT | EdgeFlags::FOLDER) {
                    next = Some(e);
                    break;
                }
            }
            if let Some(next) = next {
                debug!("oldest_path, next = {:?}", next);
                if !next.flag.contains(EdgeFlags::DELETED) {
                    alive = true;
                } else if alive {
                    break;
                } else {
                    all_alive = false
                }
                if let Some((_, p_age, _)) = next_v {
                    if (age > p_age) ^ youngest {
                        continue;
                    }
                }
                next_v = Some((name_dest, age, next.dest));
            }
        }
        let (name, _, next) = next_v.unwrap();
        if alive {
            name_buf.clear();
            debug!("getting contents {:?}", name);
            changes
                .get_contents(|h| txn.get_external(h).unwrap(), name, &mut name_buf)
                .map_err(crate::output::FileError::Changestore)?;
            path.push(std::str::from_utf8(&name_buf[2..]).unwrap().to_string());
        }
        debug!("next = {:?}", next);
        v = next;
    }
    path.reverse();
    Ok((path.join("/"), all_alive))
}

pub fn get_latest_touch<'a, T: ChannelTxnT + DepsTxnT<DepsError = <T as GraphTxnT>::GraphError>>(
    txn: &T,
    channel: &T::Channel,
    pos: Position<ChangeId>,
) -> Result<(u64, ChangeId), TxnErr<T::GraphError>> {
    let mut latest_change = 0;
    let mut id = ChangeId::ROOT;
    let mut touch_iter = Some(txn.iter_touched(pos)?);
    let mut log_iter = changeid_rev_log(txn, &channel, None)?;
    let mut continue_ = true;
    while continue_ {
        continue_ = false;
        if let Some(ref mut it) = touch_iter {
            if let Some(c) = it.next() {
                debug!("inode, change = {:?}", c);
                let (inode, change) = c?;
                if inode > pos {
                    touch_iter = None;
                } else if inode == pos {
                    if let Some(t) = txn.get_changeset(txn.changes(&channel), change)? {
                        if t >= latest_change {
                            latest_change = t;
                            id = change;
                        }
                    }
                    continue_ = true;
                }
            }
        }
        if let Some(l) = log_iter.next() {
            debug!("int = {:?}", l);
            let (n, (int, _)) = l?;
            if txn.get_touched_files(pos, Some(int))?.is_some() {
                id = int;
                latest_change = n;
                break;
            }
            continue_ = true;
        }
    }
    Ok((latest_change, id))
}
