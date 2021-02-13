use crate::pristine::*;
use std::collections::HashSet;

pub(crate) fn find_alive_down<T: GraphTxnT>(
    txn: &T,
    channel: &T::Graph,
    vertex0: Vertex<ChangeId>,
) -> Result<HashSet<Vertex<ChangeId>>, BlockError<T::GraphError>> {
    let mut stack = vec![Edge {
        dest: vertex0.start_pos(),
        introduced_by: ChangeId::ROOT,
        flag: EdgeFlags::empty(),
    }];
    let mut visited = HashSet::new();
    let mut alive = HashSet::new();
    while let Some(elt) = stack.pop() {
        if !visited.insert(elt.dest) {
            continue;
        }
        let vertex = txn.find_block(&channel, elt.dest)?;
        debug!("elt = {:?}, vertex = {:?}", elt, vertex);
        let elt_index = stack.len();
        for v in iter_adj_all(txn, &channel, vertex)? {
            let v = v?;
            if v.flag.contains(EdgeFlags::FOLDER) {
                continue;
            }
            debug!("v = {:?}", v);
            if v.flag.contains(EdgeFlags::PARENT) {
                if v.flag.contains(EdgeFlags::BLOCK)
                    && !v.flag.contains(EdgeFlags::DELETED)
                    && vertex != vertex0
                    && !v.flag.contains(EdgeFlags::PSEUDO)
                {
                    alive.insert(vertex);
                    stack.truncate(elt_index);
                    break;
                } else {
                    continue;
                }
            }
            stack.push(v)
        }
    }
    Ok(alive)
}

pub(crate) fn find_alive_up<T: GraphTxnT>(
    txn: &T,
    channel: &T::Graph,
    files: &mut HashSet<Vertex<ChangeId>>,
    vertex0: Vertex<ChangeId>,
    change: ChangeId,
) -> Result<HashSet<Vertex<ChangeId>>, BlockError<T::GraphError>> {
    let mut alive = HashSet::new();
    let mut stack = vec![Edge {
        dest: vertex0.end_pos(),
        introduced_by: ChangeId::ROOT,
        flag: EdgeFlags::empty(),
    }];
    let mut visited = HashSet::new();
    while let Some(elt) = stack.pop() {
        if elt.dest.is_root() {
            continue;
        }
        if !visited.insert(elt.dest) {
            continue;
        }
        let vertex = txn.find_block_end(&channel, elt.dest)?;
        debug!("find_alive_up: elt = {:?}, vertex = {:?}", elt, vertex);
        let elt_index = stack.len();
        let mut is_file = false;
        let mut it = iter_adj_all(txn, &channel, vertex)?;
        while let Some(v) = it.next() {
            let v = v?;
            debug!("find_alive_up: v = {:?}", v);
            if !v.flag.is_parent() {
                is_file |= !v.flag.is_folder();
                continue;
            }
            if v.flag & EdgeFlags::pseudof() == EdgeFlags::PSEUDO {
                continue;
            }
            if !v.flag.is_deleted() {
                if v.flag.is_folder() {
                    for e in it {
                        let e = e?;
                        is_file |= !e.flag.intersects(EdgeFlags::parent_folder())
                    }
                    if is_file {
                        alive.insert(vertex);
                        files.insert(vertex);
                    }
                    break;
                } else {
                    alive.insert(vertex);
                    if v.introduced_by != change {
                        stack.truncate(elt_index);
                        break;
                    }
                }
            }
            if v.flag.is_folder() {
                if is_file {
                    alive.insert(vertex);
                    files.insert(vertex);
                }
                break;
            } else {
                stack.push(v)
            }
        }
        debug!("is_file = {:?}", is_file);
    }
    Ok(alive)
}
