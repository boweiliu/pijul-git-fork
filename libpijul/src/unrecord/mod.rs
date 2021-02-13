use crate::apply;
use crate::change::*;
use crate::changestore::*;
use crate::missing_context::*;
use crate::pristine::*;

use std::collections::{HashMap, HashSet};

mod working_copy;

#[derive(Debug, Error)]
pub enum UnrecordError<
    ChangestoreError: std::error::Error + 'static,
    TxnError: std::error::Error + 'static,
> {
    #[error("Changestore error: {0}")]
    Changestore(ChangestoreError),
    #[error(transparent)]
    Txn(TxnError),
    #[error(transparent)]
    Block(#[from] crate::pristine::BlockError<TxnError>),
    #[error(transparent)]
    InconsistentChange(#[from] crate::pristine::InconsistentChange<TxnError>),
    #[error("Change not in channel: {}", hash.to_base32())]
    ChangeNotInChannel { hash: ChangeId },
    #[error("Change {} is depended upon by {}", change_id.to_base32(), dependent.to_base32())]
    ChangeIsDependedUpon {
        change_id: ChangeId,
        dependent: ChangeId,
    },
    #[error(transparent)]
    Missing(#[from] crate::missing_context::MissingError<TxnError>),
    #[error(transparent)]
    LocalApply(#[from] crate::apply::LocalApplyError<TxnError>),
    #[error(transparent)]
    Apply(#[from] crate::apply::ApplyError<ChangestoreError, TxnError>),
}

impl<T: std::error::Error + 'static, C: std::error::Error + 'static> std::convert::From<TxnErr<T>>
    for UnrecordError<C, T>
{
    fn from(t: TxnErr<T>) -> Self {
        UnrecordError::Txn(t.0)
    }
}

pub fn unrecord<T: MutTxnT, P: ChangeStore>(
    txn: &mut T,
    channel: &mut ChannelRef<T>,
    changes: &P,
    hash: &Hash,
) -> Result<bool, UnrecordError<P::Error, T::GraphError>> {
    let change = changes
        .get_change(hash)
        .map_err(UnrecordError::Changestore)?;
    let change_id = if let Some(h) = txn.get_internal(*hash)? {
        h
    } else {
        return Ok(false);
    };
    let unused = unused_in_other_channels(txn, &channel, change_id)?;
    let mut channel = channel.r.borrow_mut();

    del_channel_changes::<T, P>(txn, &mut channel, change_id)?;

    unapply(txn, &mut channel, changes, change_id, &change)?;

    if unused {
        assert!(txn.get_revdep(change_id, None)?.is_none());
        while txn.del_dep(change_id, None)? {}
        txn.del_external(change_id, None)?;
        txn.del_internal(*hash, None)?;
        for dep in change.dependencies.iter() {
            let dep = txn.get_internal(*dep)?.unwrap();
            txn.del_revdep(dep, Some(change_id))?;
        }
        Ok(false)
    } else {
        Ok(true)
    }
}

fn del_channel_changes<
    T: ChannelMutTxnT + DepsTxnT<DepsError = <T as GraphTxnT>::GraphError>,
    P: ChangeStore,
>(
    txn: &mut T,
    channel: &mut T::Channel,
    change_id: ChangeId,
) -> Result<(), UnrecordError<P::Error, T::GraphError>> {
    let timestamp = if let Some(ts) = txn.get_changeset(txn.changes(channel), change_id)? {
        ts
    } else {
        return Err(UnrecordError::ChangeNotInChannel { hash: change_id });
    };

    for x in txn.iter_revdep(change_id)? {
        let (p, d) = x?;
        if p < change_id {
            continue;
        } else if p > change_id {
            break;
        }
        if txn.get_changeset(txn.changes(channel), d)?.is_some() {
            return Err(UnrecordError::ChangeIsDependedUpon {
                change_id,
                dependent: d,
            });
        }
    }

    txn.del_changes(channel, change_id, timestamp)?;
    Ok(())
}

fn unused_in_other_channels<T: TxnT>(
    txn: &mut T,
    channel: &ChannelRef<T>,
    change_id: ChangeId,
) -> Result<bool, TxnErr<T::GraphError>> {
    let channel = channel.borrow();
    for br in txn.iter_channels("")? {
        let br = br?;
        let br = br.borrow();
        if txn.name(&br) != txn.name(&channel)
            && txn.get_changeset(txn.changes(&br), change_id)?.is_some()
        {
            return Ok(false);
        }
    }
    Ok(true)
}

fn unapply<
    T: ChannelMutTxnT + TreeMutTxnT<TreeError = <T as GraphTxnT>::GraphError>,
    C: ChangeStore,
>(
    txn: &mut T,
    channel: &mut T::Channel,
    changes: &C,
    change_id: ChangeId,
    change: &Change,
) -> Result<(), UnrecordError<C::Error, T::GraphError>> {
    let mut clean_inodes = HashSet::new();
    let mut ws = Workspace::default();
    for change_ in change.changes.iter().rev().flat_map(|r| r.rev_iter()) {
        match *change_ {
            Atom::EdgeMap(ref newedges) => unapply_edges(
                changes,
                txn,
                T::graph_mut(channel),
                change_id,
                newedges,
                &mut ws,
            )?,
            Atom::NewVertex(ref newvertex) => {
                if clean_inodes.insert(newvertex.inode) {
                    crate::alive::remove_forward_edges(
                        txn,
                        T::graph_mut(channel),
                        internal_pos(txn, &newvertex.inode, change_id)?,
                    )?
                }
                unapply_newvertex::<T, C>(
                    txn,
                    T::graph_mut(channel),
                    change_id,
                    &mut ws,
                    newvertex,
                )?
            }
        }
    }
    repair_newvertex_contexts::<T, C>(txn, T::graph_mut(channel), &mut ws, change_id)?;
    for change in change.changes.iter().rev().flat_map(|r| r.rev_iter()) {
        if let Atom::EdgeMap(ref n) = *change {
            remove_zombies::<_, C>(txn, T::graph_mut(channel), &mut ws, change_id, n)?;
            repair_edges_context(
                changes,
                txn,
                T::graph_mut(channel),
                &mut ws.apply.missing_context,
                change_id,
                n,
            )?
        }
    }

    for change_ in change.changes.iter().rev().flat_map(|r| r.rev_iter()) {
        match *change_ {
            Atom::EdgeMap(ref newedges) if newedges.edges[0].flag.contains(EdgeFlags::FOLDER) => {
                if newedges.edges[0].flag.contains(EdgeFlags::DELETED) {
                    working_copy::undo_file_deletion(txn, changes, channel, change_id, newedges)?
                } else {
                    working_copy::undo_file_reinsertion::<C, _>(txn, change_id, newedges)?
                }
            }
            Atom::NewVertex(ref new_vertex)
                if new_vertex.flag.contains(EdgeFlags::FOLDER)
                    && new_vertex.down_context.is_empty() =>
            {
                working_copy::undo_file_addition(txn, change_id, new_vertex)?;
            }
            _ => {}
        }
    }

    crate::apply::clean_obsolete_pseudo_edges(
        txn,
        T::graph_mut(channel),
        &mut ws.apply,
        change_id,
    )?;
    crate::apply::repair_cyclic_paths(txn, T::graph_mut(channel), &mut ws.apply)?;
    txn.touch_channel(channel, Some(0));
    Ok(())
}

#[derive(Default)]
struct Workspace {
    up: HashMap<Vertex<ChangeId>, Position<Option<Hash>>>,
    down: HashMap<Vertex<ChangeId>, Position<Option<Hash>>>,
    parents: HashSet<Vertex<ChangeId>>,
    del: Vec<Edge>,
    apply: crate::apply::Workspace,
    stack: Vec<Vertex<ChangeId>>,
    del_edges: Vec<(Vertex<ChangeId>, Edge)>,
}

fn unapply_newvertex<T: GraphMutTxnT, C: ChangeStore>(
    txn: &mut T,
    channel: &mut T::Graph,
    change_id: ChangeId,
    ws: &mut Workspace,
    new_vertex: &NewVertex<Option<Hash>>,
) -> Result<(), UnrecordError<C::Error, T::GraphError>> {
    let mut pos = Position {
        change: change_id,
        pos: new_vertex.start,
    };
    debug!("unapply_newvertex = {:?}", new_vertex);
    while let Ok(vertex) = txn.find_block(channel, pos) {
        debug!("vertex = {:?}", vertex);
        for e in iter_adj_all(txn, channel, vertex)? {
            let e = e?;
            debug!("e = {:?}", e);
            if !e.flag.is_deleted() {
                if e.flag.is_parent() {
                    if !e.flag.is_folder() {
                        let up_v = txn.find_block_end(channel, e.dest)?;
                        ws.up.insert(up_v, new_vertex.inode);
                    }
                } else {
                    let down_v = txn.find_block(channel, e.dest)?;
                    ws.down.insert(down_v, new_vertex.inode);
                    if e.flag.is_folder() {
                        ws.apply.missing_context.files.insert(down_v);
                    }
                }
            }
            ws.del.push(e)
        }
        debug!("del = {:#?}", ws.del);
        ws.up.remove(&vertex);
        ws.down.remove(&vertex);
        ws.perform_del::<C, T>(txn, channel, vertex)?;
        if vertex.end < new_vertex.end {
            pos.pos = vertex.end
        }
    }
    Ok(())
}

impl Workspace {
    fn perform_del<C: ChangeStore, T: GraphMutTxnT>(
        &mut self,
        txn: &mut T,
        channel: &mut T::Graph,
        vertex: Vertex<ChangeId>,
    ) -> Result<(), UnrecordError<C::Error, T::GraphError>> {
        for e in self.del.drain(..) {
            let (a, b) = if e.flag.is_parent() {
                (txn.find_block_end(channel, e.dest)?, vertex)
            } else {
                (vertex, txn.find_block(channel, e.dest)?)
            };
            del_graph_with_rev(
                txn,
                channel,
                e.flag - EdgeFlags::PARENT,
                a,
                b,
                e.introduced_by,
            )?;
        }
        Ok(())
    }
}

fn repair_newvertex_contexts<T: GraphMutTxnT, C: ChangeStore>(
    txn: &mut T,
    channel: &mut T::Graph,
    ws: &mut Workspace,
    change_id: ChangeId,
) -> Result<(), UnrecordError<C::Error, T::GraphError>> {
    debug!("up = {:#?}", ws.up);
    for (up, inode) in ws.up.drain() {
        if !is_alive(txn, channel, up)? {
            continue;
        }
        crate::missing_context::repair_missing_down_context(
            txn,
            channel,
            &mut ws.apply.missing_context,
            inode,
            up,
            &[up],
        )?
    }

    debug!("down = {:#?}", ws.down);
    for (down, inode) in ws.down.drain() {
        if !is_alive(txn, channel, down)? {
            continue;
        }
        for parent in iter_adjacent(
            txn,
            channel,
            down,
            EdgeFlags::PARENT,
            EdgeFlags::all() - EdgeFlags::DELETED,
        )? {
            let parent = parent?;
            let parent = txn.find_block_end(channel, parent.dest)?;
            if !is_alive(txn, channel, parent)? {
                ws.parents.insert(parent);
            }
        }
        debug!("parents {:#?}", ws.parents);
        for up in ws.parents.drain() {
            crate::missing_context::repair_missing_up_context(
                txn,
                channel,
                &mut ws.apply.missing_context,
                change_id,
                inode,
                up,
                &[down],
            )?
        }
    }
    Ok(())
}

fn unapply_edges<T: GraphMutTxnT, P: ChangeStore>(
    changes: &P,
    txn: &mut T,
    channel: &mut T::Graph,
    change_id: ChangeId,
    newedges: &EdgeMap<Option<Hash>>,
    ws: &mut Workspace,
) -> Result<(), UnrecordError<P::Error, T::GraphError>> {
    debug!("newedges = {:#?}", newedges);
    let ext = txn.get_external(change_id)?.unwrap();
    for edge in newedges.edges.iter() {
        let intro = internal(txn, &edge.introduced_by, change_id)?.unwrap();
        apply::put_newedge(
            txn,
            channel,
            &mut ws.apply,
            intro,
            newedges.inode,
            &edge.reverse(Some(ext)),
            |txn, channel, a, b| {
                must_reintroduce(txn, channel, changes, a, b, ext, intro, change_id)
            },
        )?;
    }
    Ok(())
}

fn must_reintroduce<T: GraphTxnT, C: ChangeStore>(
    txn: &T,
    channel: &T::Graph,
    changes: &C,
    a: Vertex<ChangeId>,
    b: Vertex<ChangeId>,
    intro: Hash,
    intro_id: ChangeId,
    current_id: ChangeId,
) -> Result<bool, UnrecordError<C::Error, T::GraphError>> {
    debug!("a = {:?}, b = {:?}", a, b);
    // does a patch introduced by an edge parallel to
    // this one remove this edge from the graph?
    let b_ext = Position {
        change: txn.get_external(b.change)?,
        pos: b.start,
    };
    let mut stack = Vec::new();
    for e in iter_adj_all(txn, channel, a)? {
        let e = e?;
        if e.flag.contains(EdgeFlags::PARENT)
            || e.dest != b.start_pos()
            || e.introduced_by.is_root()
            || e.introduced_by == current_id
        {
            continue;
        }
        // Optimisation to avoid opening change files in the vast
        // majority of cases: if there is an edge `e` parallel to a ->
        // b introduced by the change that introduced a or b, don't
        // reinsert a -> b: that edge was removed by `e`.
        if a.change == intro_id || b.change == intro_id {
            return Ok(false);
        }
        stack.push(e.introduced_by)
    }
    edge_is_in_channel(txn, changes, b_ext, intro, &mut stack)
}

fn edge_is_in_channel<T: GraphTxnT, C: ChangeStore>(
    txn: &T,
    changes: &C,
    pos: Position<Option<Hash>>,
    introduced_by: Hash,
    stack: &mut Vec<ChangeId>,
) -> Result<bool, UnrecordError<C::Error, T::GraphError>> {
    let mut visited = HashSet::new();
    while let Some(s) = stack.pop() {
        if !visited.insert(s) {
            continue;
        }
        debug!("stack: {:?}", s);
        for next in changes
            .change_deletes_position(|c| txn.get_external(c).unwrap(), s, pos)
            .map_err(UnrecordError::Changestore)?
        {
            if next == introduced_by {
                return Ok(false);
            } else if let Some(i) = txn.get_internal(next)? {
                stack.push(i)
            }
        }
    }
    Ok(true)
}

fn remove_zombies<T: GraphMutTxnT, C: ChangeStore>(
    txn: &mut T,
    channel: &mut T::Graph,
    ws: &mut Workspace,
    change_id: ChangeId,
    newedges: &EdgeMap<Option<Hash>>,
) -> Result<(), UnrecordError<C::Error, T::GraphError>> {
    debug!("remove_zombies, change_id = {:?}", change_id);
    for edge in newedges.edges.iter() {
        let to = internal_pos(txn, &edge.to.start_pos(), change_id)?;
        collect_zombies(txn, channel, change_id, to, ws)?;
        debug!("remove_zombies = {:#?}", ws.del_edges);
        for (v, mut e) in ws.del_edges.drain(..) {
            if e.flag.contains(EdgeFlags::PARENT) {
                let u = txn.find_block_end(channel, e.dest)?;
                e.flag -= EdgeFlags::PARENT;
                del_graph_with_rev(txn, channel, e.flag, u, v, e.introduced_by)?;
            } else {
                let w = txn.find_block(channel, e.dest)?;
                del_graph_with_rev(txn, channel, e.flag, v, w, e.introduced_by)?;
            }
        }
    }
    Ok(())
}

fn collect_zombies<T: GraphTxnT>(
    txn: &T,
    channel: &T::Graph,
    change_id: ChangeId,
    to: Position<ChangeId>,
    ws: &mut Workspace,
) -> Result<(), BlockError<T::GraphError>> {
    ws.stack.push(txn.find_block(channel, to)?);
    while let Some(v) = ws.stack.pop() {
        debug!("remove_zombies, v = {:?}", v);
        if !ws.parents.insert(v) {
            continue;
        }
        for e in iter_adj_all(txn, channel, v)? {
            let e = e?;
            debug!("e = {:?}", e);
            if !(e.introduced_by == change_id || e.flag & EdgeFlags::bp() == EdgeFlags::PARENT) {
                continue;
            }
            if e.flag.contains(EdgeFlags::PARENT) {
                ws.stack.push(txn.find_block_end(channel, e.dest)?)
            } else {
                ws.stack.push(txn.find_block(channel, e.dest)?)
            }
            if e.introduced_by == change_id {
                ws.del_edges.push((v, e))
            }
        }
    }
    ws.stack.clear();
    ws.parents.clear();
    Ok(())
}

fn repair_edges_context<T: GraphMutTxnT, P: ChangeStore>(
    changes: &P,
    txn: &mut T,
    channel: &mut T::Graph,
    ws: &mut crate::missing_context::Workspace,
    change_id: ChangeId,
    n: &EdgeMap<Option<Hash>>,
) -> Result<(), UnrecordError<P::Error, T::GraphError>> {
    let change_hash = txn.get_external(change_id)?.unwrap();
    for e in n.edges.iter() {
        assert!(!e.flag.contains(EdgeFlags::PARENT));
        let intro = internal(txn, &e.introduced_by, change_id)?.unwrap();
        if e.previous.contains(EdgeFlags::DELETED) {
            repair_context_deleted(
                txn,
                channel,
                ws,
                n.inode,
                intro,
                |h| changes.knows(&change_hash, &h).unwrap(),
                &e.reverse(Some(change_hash)),
            )?
        } else {
            let to = internal_pos(txn, &e.to.start_pos(), change_id)?;
            let to = txn.find_block(channel, to)?;
            if !is_alive(txn, channel, to)? {
                continue;
            }
            repair_context_nondeleted(
                txn,
                channel,
                ws,
                n.inode,
                intro,
                |h| changes.knows(&change_hash, &h).unwrap(),
                &e.reverse(Some(change_hash)),
            )?
        }
    }
    Ok(())
}
