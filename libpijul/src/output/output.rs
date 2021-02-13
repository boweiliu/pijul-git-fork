//! Output the pristine to the working copy, synchronising file
//! changes (file additions, deletions and renames) in the process.
use super::{collect_children, OutputError, OutputItem, PristineOutputError};
use crate::alive::retrieve;
use crate::changestore::ChangeStore;
use crate::fs::{create_new_inode, inode_filename};
use crate::pristine::*;
use crate::small_string::SmallString;
use crate::working_copy::WorkingCopy;
use crate::{alive, path, vertex_buffer};
use std::collections::hash_map::Entry;
use std::collections::{HashMap, HashSet};

/// A structure representing a file with conflicts.
#[derive(Debug)]
pub enum Conflict {
    Name { path: String },
    ZombieFile { path: String },
    MultipleNames { pos: Position<ChangeId> },
    Zombie { path: String, line: usize },
    Cyclic { path: String, line: usize },
    Order { path: String, line: usize },
}

/// Output updates the working copy after applying changes, including
/// the graph-file correspondence.
///
/// **WARNING:** This overwrites the working copy, cancelling any
/// unrecorded change.
pub fn output_repository_no_pending<T: MutTxnT, R: WorkingCopy, P: ChangeStore>(
    repo: &mut R,
    changes: &P,
    txn: &mut T,
    channel: &mut ChannelRef<T>,
    prefix: &str,
    output_name_conflicts: bool,
    if_modified_since: Option<std::time::SystemTime>,
) -> Result<Vec<Conflict>, OutputError<P::Error, T::GraphError, R::Error>> {
    output_repository(
        repo,
        changes,
        txn,
        &mut channel.r.borrow_mut(),
        ChangeId::ROOT,
        &mut crate::path::components(prefix),
        output_name_conflicts,
        if_modified_since,
    )
}

fn output_repository<
    'a,
    T: TreeMutTxnT + ChannelMutTxnT + GraphMutTxnT<GraphError = <T as TreeTxnT>::TreeError>,
    R: WorkingCopy,
    P: ChangeStore,
    I: Iterator<Item = &'a str>,
>(
    repo: &mut R,
    changes: &P,
    txn: &mut T,
    channel: &mut T::Channel,
    pending_change_id: ChangeId,
    prefix: &mut I,
    output_name_conflicts: bool,
    if_modified_after: Option<std::time::SystemTime>,
) -> Result<Vec<Conflict>, OutputError<P::Error, T::TreeError, R::Error>> {
    let mut conflicts = Vec::new();
    let mut files = HashMap::new();
    let mut next_files = HashMap::new();
    let mut next_prefix_basename = prefix.next();
    let mut is_first_none = true;
    if next_prefix_basename.is_none() {
        let dead = collect_dead_files(txn, txn.graph(channel), pending_change_id, Inode::ROOT)?;
        debug!("dead (line {}) = {:?}", line!(), dead);
        kill_dead_files::<T, R, P>(txn, repo, &dead)?;
        is_first_none = false;
    }
    collect_children(
        txn,
        changes,
        txn.graph(channel),
        Position::ROOT,
        Inode::ROOT,
        "",
        next_prefix_basename,
        &mut files,
    )?;
    debug!("done collecting: {:?}", files);
    let mut done_inodes = HashSet::new();
    let mut done_vertices = HashMap::new();
    // Actual moves is used to avoid a situation where have two files
    // a and b, first rename a -> b, and then b -> c.
    let mut actual_moves = Vec::new();
    while !files.is_empty() {
        debug!("files {:?}", files.len());
        next_files.clear();
        next_prefix_basename = prefix.next();

        for (a, mut b) in files.drain() {
            debug!("files: {:?} {:?}", a, b);
            b.sort_unstable_by(|u, v| {
                txn.get_changeset(txn.changes(&channel), u.0.change)
                    .unwrap()
                    .cmp(
                        &txn.get_changeset(txn.changes(&channel), v.0.change)
                            .unwrap(),
                    )
            });
            let mut is_first_name = true;
            for (name_key, mut output_item) in b {
                match done_vertices.entry(output_item.pos) {
                    Entry::Occupied(e) => {
                        debug!("pos already visited: {:?} {:?}", a, output_item.pos);
                        if *e.get() != name_key {
                            conflicts.push(Conflict::MultipleNames {
                                pos: output_item.pos,
                            });
                        }
                        continue;
                    }
                    Entry::Vacant(e) => {
                        e.insert(name_key);
                    }
                }

                let output_item_inode =
                    if let Some(inode) = txn.get_revinodes(output_item.pos, None)? {
                        Some((inode, txn.get_inodes(inode, None)?.unwrap()))
                    } else {
                        None
                    };

                if let Some((inode, _)) = output_item_inode {
                    if !done_inodes.insert(inode) {
                        debug!("inode already visited: {:?} {:?}", a, inode);
                        continue;
                    }
                }
                let name = if !is_first_name {
                    if output_name_conflicts {
                        let name = make_conflicting_name(&a, name_key);
                        conflicts.push(Conflict::Name { path: name.clone() });
                        name
                    } else {
                        debug!("not outputting {:?} {:?}", a, name_key);
                        conflicts.push(Conflict::Name {
                            path: a.to_string(),
                        });
                        break;
                    }
                } else {
                    is_first_name = false;
                    a.clone()
                };
                let file_name = path::file_name(&name).unwrap();
                path::push(&mut output_item.path, file_name);
                let path = std::mem::replace(&mut output_item.path, String::new());
                let inode = move_or_create::<T, R, P>(
                    txn,
                    repo,
                    &output_item,
                    output_item_inode,
                    &path,
                    &file_name,
                    &mut actual_moves,
                )?;
                if next_prefix_basename.is_none() && is_first_none {
                    let dead =
                        collect_dead_files(txn, txn.graph(channel), pending_change_id, inode)?;
                    debug!("dead (line {}) = {:?}", line!(), dead);
                    kill_dead_files::<T, R, P>(txn, repo, &dead)?;
                    is_first_none = false;
                }
                if output_item.meta.is_dir() {
                    repo.create_dir_all(&path)
                        .map_err(OutputError::WorkingCopy)?;
                    collect_children(
                        txn,
                        changes,
                        txn.graph(channel),
                        output_item.pos,
                        inode,
                        &path,
                        next_prefix_basename,
                        &mut next_files,
                    )?;
                } else {
                    if needs_output(repo, if_modified_after, &path) {
                        repo.write_file(&path, |w: &mut dyn std::io::Write| {
                            output_file::<_, _, R>(
                                txn,
                                channel,
                                changes,
                                &output_item,
                                &mut conflicts,
                                w,
                            )
                        })
                        .map_err(OutputError::from)?
                    } else {
                        debug!("Not outputting {:?}", path)
                    }
                }
                if output_item.is_zombie {
                    conflicts.push(Conflict::ZombieFile {
                        path: name.to_string(),
                    })
                }
                repo.set_permissions(&path, output_item.meta.permissions())
                    .map_err(OutputError::WorkingCopy)?;
            }
        }
        std::mem::swap(&mut files, &mut next_files);
    }
    for (a, b) in actual_moves.iter() {
        repo.rename(a, b).map_err(OutputError::WorkingCopy)?
    }
    Ok(conflicts)
}

fn make_conflicting_name(name: &str, name_key: Vertex<ChangeId>) -> String {
    let parent = path::parent(name).unwrap();
    let basename = path::file_name(name).unwrap();
    let mut parent = parent.to_string();
    path::push(
        &mut parent,
        &format!("{}.{}", basename, &name_key.change.to_base32()),
    );
    parent
}

fn needs_output<R: WorkingCopy>(
    repo: &R,
    if_modified_after: Option<std::time::SystemTime>,
    path: &str,
) -> bool {
    if let Some(m) = if_modified_after {
        if let Ok(last) = repo.modified_time(path) {
            debug!("modified_after: {:?} {:?}", m, last);
            if let Ok(d) = last.duration_since(m) {
                return d.as_secs() > 0;
            } else {
                return false;
            }
        }
    }
    true
}

fn move_or_create<T: TreeMutTxnT, R: WorkingCopy, C: ChangeStore>(
    txn: &mut T,
    repo: &mut R,
    output_item: &OutputItem,
    output_item_inode: Option<(Inode, Position<ChangeId>)>,
    path: &str,
    file_name: &str,
    actual_moves: &mut Vec<(String, String)>,
) -> Result<Inode, OutputError<C::Error, T::TreeError, R::Error>> {
    let file_id = OwnedPathId {
        parent_inode: output_item.parent,
        basename: SmallString::from_str(&file_name),
    };
    let file_id_ = file_id.as_file_id();
    debug!("move_or_create {:?}", file_id_);

    if let Some((inode, _)) = output_item_inode {
        // If the file already exists, find its
        // current name and rename it if that name
        // is different.
        if let Some(ref current_name) = inode_filename(txn, inode)? {
            debug!("current_name = {:?}, path = {:?}", current_name, path);
            if current_name != path {
                let parent = txn.get_revtree(inode, None)?.unwrap().to_owned();
                debug!("parent = {:?}, inode = {:?}", parent, inode);
                del_tree_with_rev(txn, parent.as_file_id(), inode)?;

                let mut tmp_path = path.to_string();
                crate::path::pop(&mut tmp_path);
                use rand::Rng;
                let s: String = rand::thread_rng()
                    .sample_iter(&rand::distributions::Alphanumeric)
                    .take(30)
                    .map(|c| c as char)
                    .collect();
                crate::path::push(&mut tmp_path, &s);

                repo.rename(&current_name, &tmp_path)
                    .map_err(OutputError::WorkingCopy)?;
                actual_moves.push((tmp_path, path.to_string()));

                // If the new location is overwriting an existing one,
                // actually overwrite.
                if let Some(inode) = txn.get_tree(file_id_, None)? {
                    crate::fs::rec_delete(txn, file_id.clone(), inode, true)
                        .map_err(PristineOutputError::Fs)?;
                }
                put_inodes_with_rev(txn, inode, output_item.pos)?;
                put_tree_with_rev(txn, file_id_, inode)?;
            }
        } else {
            debug!("no current name, inserting {:?} {:?}", file_id_, inode);
            if let Some(inode) = txn.get_tree(file_id_, None)? {
                crate::fs::rec_delete(txn, file_id.clone(), inode, true)
                    .map_err(PristineOutputError::Fs)?;
            }
            put_inodes_with_rev(txn, inode, output_item.pos)?;
            put_tree_with_rev(txn, file_id_, inode)?;
        }
        Ok(inode)
    } else {
        if let Some(inode) = txn.get_tree(file_id_, None)? {
            crate::fs::rec_delete(txn, file_id.clone(), inode, true)
                .map_err(PristineOutputError::Fs)?;
        }
        let inode = create_new_inode(txn)?;
        debug!(
            "created new inode {:?} {:?} {:?}",
            inode, output_item.pos, file_id_
        );
        put_inodes_with_rev(txn, inode, output_item.pos)?;
        put_tree_with_rev(txn, file_id_, inode)?;
        if output_item.meta.is_dir() {
            let path_id = OwnedPathId {
                parent_inode: inode,
                basename: SmallString::new(),
            };
            txn.put_tree(path_id.as_file_id(), inode)?;
        }
        Ok(inode)
    }
}

fn output_file<T: ChannelMutTxnT + GraphMutTxnT, P: ChangeStore, W: WorkingCopy>(
    txn: &mut T,
    channel: &mut T::Channel,
    changes: &P,
    output_item: &OutputItem,
    conflicts: &mut Vec<Conflict>,
    w: &mut dyn std::io::Write,
) -> Result<(), OutputError<P::Error, T::GraphError, W::Error>> {
    let mut l = retrieve(txn, txn.graph(channel), output_item.pos)?;
    let mut f = vertex_buffer::ConflictsWriter::new(w, &output_item.path, conflicts);
    let mut forward = Vec::new();
    alive::output_graph(changes, txn, channel, &mut f, &mut l, &mut forward)
        .map_err(PristineOutputError::from)?;
    for &(vertex, edge) in forward.iter() {
        // Unwrap ok since `edge` is in the channel.
        let dest = txn.find_block(txn.graph(channel), edge.dest).unwrap();
        debug!("deleting forward edge {:?} {:?} {:?}", vertex, dest, edge);
        del_graph_with_rev(
            txn,
            T::graph_mut(channel),
            edge.flag,
            vertex,
            dest,
            edge.introduced_by,
        )?;
    }
    Ok(())
}

fn collect_dead_files<T: TreeMutTxnT + GraphTxnT<GraphError = <T as TreeTxnT>::TreeError>>(
    txn: &mut T,
    channel: &T::Graph,
    pending_change_id: ChangeId,
    inode: Inode,
) -> Result<HashMap<OwnedPathId, (Inode, Option<String>)>, TxnErr<T::GraphError>> {
    let mut inodes = vec![(inode, false)];
    let mut next_inodes = Vec::new();
    let mut dead = HashMap::new();
    while !inodes.is_empty() {
        for (inode, parent_is_dead) in inodes.drain(..) {
            for x in txn.iter_tree(
                OwnedPathId {
                    parent_inode: inode,
                    basename: SmallString::from_str(""),
                },
                None,
            )? {
                let (id, inode_) = x?;
                if id.parent_inode > inode {
                    break;
                } else if id.parent_inode < inode {
                    continue;
                }
                let is_dead = parent_is_dead || {
                    if let Some(vertex) = txn.get_inodes(inode_, None)? {
                        vertex.change != pending_change_id
                            && !is_alive(txn, channel, vertex.inode_vertex())?
                    } else {
                        true
                    }
                };
                if is_dead {
                    dead.insert(id.to_owned(), (inode_, inode_filename(txn, inode_)?));
                }
                if inode_ != inode {
                    next_inodes.push((inode_, is_dead))
                }
            }
        }
        std::mem::swap(&mut inodes, &mut next_inodes)
    }
    Ok(dead)
}

fn kill_dead_files<T: TreeMutTxnT, W: WorkingCopy, C: ChangeStore>(
    txn: &mut T,
    repo: &mut W,
    dead: &HashMap<OwnedPathId, (Inode, Option<String>)>,
) -> Result<(), OutputError<C::Error, T::TreeError, W::Error>> {
    for (fileid, (inode, ref name)) in dead.iter() {
        debug!("killing {:?} {:?} {:?}", fileid, inode, name);
        del_tree_with_rev(txn, fileid.as_file_id(), *inode)?;
        if let Some(vertex) = txn.get_inodes(*inode, None)? {
            debug!("kill_dead_files {:?} {:?}", inode, vertex);
            del_inodes_with_rev(txn, *inode, vertex)?;
            if let Some(name) = name {
                repo.remove_path(&name).map_err(OutputError::WorkingCopy)?
            }
        }
    }
    Ok(())
}
