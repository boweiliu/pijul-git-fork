use super::dfs::{Path, PathElement};
use super::{Flags, Graph, VertexId};
use crate::changestore::ChangeStore;
use crate::output::FileError;
use crate::pristine::*;
use crate::vector2::Vector2;
use crate::vertex_buffer::VertexBuffer;

#[derive(Debug)]
struct ConflictStackElt {
    conflict: Vec<Path>,
    side: usize,
    idx: usize,
}

fn output_conflict<T: ChannelTxnT, B: VertexBuffer, P: ChangeStore>(
    changes: &P,
    txn: &T,
    channel: &T::Channel,
    line_buf: &mut B,
    graph: &Graph,
    sccs: &Vector2<VertexId>,
    conflict: Path,
) -> Result<(), FileError<P::Error, T::GraphError>> {
    let mut stack = vec![ConflictStackElt {
        conflict: vec![conflict],
        side: 0,
        idx: 0,
    }];
    while let Some(mut elt) = stack.pop() {
        let n_sides = elt.conflict.len();
        if n_sides > 1 && elt.side == 0 && elt.idx == 0 {
            line_buf.begin_conflict()?;
            elt.conflict.sort_by(|a, b| {
                let a_ = a
                    .path
                    .iter()
                    .map(|a| a.oldest_vertex(changes, txn, channel, graph, sccs).unwrap())
                    .min()
                    .unwrap();
                let b_ = b
                    .path
                    .iter()
                    .map(|b| b.oldest_vertex(changes, txn, channel, graph, sccs).unwrap())
                    .min()
                    .unwrap();
                a_.cmp(&b_)
            });
        }

        let mut next = None;
        'outer: while elt.side < n_sides {
            if elt.side > 0 && elt.idx == 0 {
                line_buf.conflict_next()?;
            }
            while elt.idx < elt.conflict[elt.side].path.len() {
                match elt.conflict[elt.side].path[elt.idx] {
                    PathElement::Scc { scc } => {
                        output_scc(changes, txn, graph, &sccs[scc], line_buf)?;
                        elt.idx += 1;
                    }
                    PathElement::Conflict { ref mut sides } => {
                        let sides = std::mem::replace(sides, Vec::new());
                        elt.idx += 1;
                        next = Some(ConflictStackElt {
                            side: 0,
                            idx: 0,
                            conflict: sides,
                        });
                        break 'outer;
                    }
                }
            }
            elt.side += 1;
            elt.idx = 0;
        }

        if elt.side >= n_sides {
            if n_sides > 1 {
                line_buf.end_conflict()?;
            }
        } else {
            stack.push(elt);
            stack.push(next.unwrap())
        }
    }
    Ok(())
}

impl PathElement {
    fn oldest_vertex<T: ChannelTxnT, C: ChangeStore>(
        &self,
        changes: &C,
        txn: &T,
        channel: &T::Channel,
        graph: &Graph,
        sccs: &Vector2<VertexId>,
    ) -> Result<u64, TxnErr<T::GraphError>> {
        match *self {
            PathElement::Scc { ref scc } => {
                let mut min: Option<u64> = None;
                for x in sccs[*scc].iter() {
                    if let Some(t) =
                        txn.get_changeset(txn.changes(&channel), graph[*x].vertex.change)?
                    {
                        if let Some(ref mut m) = min {
                            *m = (*m).min(t)
                        } else {
                            min = Some(t)
                        }
                    } else {
                        if log_enabled!(log::Level::Debug) {
                            let f = std::fs::File::create("debug_oldest").unwrap();
                            graph
                                .debug(changes, txn, txn.graph(channel), false, true, f)
                                .unwrap();
                        }
                        panic!("vertex not in channel: {:?}", graph[*x].vertex)
                    }
                }
                Ok(min.unwrap())
            }
            PathElement::Conflict { ref sides } => {
                let mut min: Option<u64> = None;
                for x in sides.iter() {
                    for y in x.path.iter() {
                        let t = y.oldest_vertex(changes, txn, channel, graph, sccs)?;
                        if let Some(ref mut m) = min {
                            *m = (*m).min(t)
                        } else {
                            min = Some(t)
                        }
                    }
                }
                Ok(min.unwrap())
            }
        }
    }
}

fn output_scc<T: GraphTxnT, B: VertexBuffer, P: ChangeStore>(
    changes: &P,
    txn: &T,
    graph: &Graph,
    scc: &[VertexId],
    vbuf: &mut B,
) -> Result<(), FileError<P::Error, T::GraphError>> {
    if scc.len() > 1 {
        vbuf.begin_cyclic_conflict()?;
    }
    for &v in scc.iter() {
        let now = std::time::Instant::now();
        if graph[v].flags.contains(Flags::ZOMBIE) {
            vbuf.begin_zombie_conflict()?;
        }
        crate::TIMERS.lock().unwrap().alive_write += now.elapsed();

        let vertex = graph[v].vertex;

        let get_contents = |buf: &mut Vec<u8>| {
            let now = std::time::Instant::now();
            let result = changes
                .get_contents(|p| txn.get_external(p).unwrap(), vertex, buf)
                .map(|_| ())
                .map_err(FileError::Changestore);
            crate::TIMERS.lock().unwrap().alive_contents += now.elapsed();
            result
        };

        let now = std::time::Instant::now();
        debug!("outputting {:?}", vertex);
        vbuf.output_line(vertex, get_contents)?;
        if graph[v].flags.contains(Flags::ZOMBIE) {
            vbuf.end_conflict()?;
        }
        crate::TIMERS.lock().unwrap().alive_write += now.elapsed();
    }
    let now = std::time::Instant::now();
    if scc.len() > 1 {
        vbuf.end_cyclic_conflict()?;
    }
    crate::TIMERS.lock().unwrap().alive_write += now.elapsed();
    Ok(())
}

pub fn output_graph<T: ChannelTxnT, B: VertexBuffer, P: ChangeStore>(
    changes: &P,
    txn: &T,
    channel: &T::Channel,
    line_buf: &mut B,
    graph: &mut Graph,
    forward: &mut Vec<(Vertex<ChangeId>, Edge)>,
) -> Result<(), crate::output::FileError<P::Error, T::GraphError>> {
    if graph.lines.len() <= 1 {
        return Ok(());
    }
    let now0 = std::time::Instant::now();
    let scc = graph.tarjan(); // SCCs are given here in reverse order.
    let (conflict_tree, forward_scc) = graph.dfs(&scc);
    graph.collect_forward_edges(txn, txn.graph(channel), &scc, &forward_scc, forward)?;

    crate::TIMERS.lock().unwrap().alive_graph += now0.elapsed();
    let now1 = std::time::Instant::now();
    debug!("conflict_tree = {:?}", conflict_tree);
    output_conflict(changes, txn, channel, line_buf, graph, &scc, conflict_tree)?;
    crate::TIMERS.lock().unwrap().alive_output += now1.elapsed();
    Ok(())
}
