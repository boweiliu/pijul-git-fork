use super::*;
use byteorder::ByteOrder;

#[derive(Debug, Error)]
pub enum ChannelDumpError<T: std::error::Error + 'static> {
    #[error(transparent)]
    Txn(T),
    #[error("Channel name already exists: {0}")]
    ChannelNameExists(String),
}

impl<T: std::error::Error + 'static> std::convert::From<TxnErr<T>> for ChannelDumpError<T> {
    fn from(e: TxnErr<T>) -> Self {
        ChannelDumpError::Txn(e.0)
    }
}

enum DumpChannelState<
    T: ChannelTxnT + GraphIter + DepsTxnT<DepsError = <T as GraphTxnT>::GraphError>,
    RT: std::ops::Deref<Target = T>,
> {
    Changes {
        log: crate::pristine::Cursor<T, RT, T::RevchangesetCursor, u64, (ChangeId, Merkle)>,
        current: ChangeId,
        deps: Option<crate::pristine::Cursor<T, RT, T::DepCursor, ChangeId, ChangeId>>,
    },
    Graph {
        cursor: T::GraphCursor,
        current: Vertex<ChangeId>,
        is_first: bool,
    },
}

pub struct DumpChannel<
    T: ChannelTxnT + GraphIter + DepsTxnT<DepsError = <T as GraphTxnT>::GraphError>,
    RT: std::ops::Deref<Target = T>,
    C: std::ops::Deref<Target = T::Channel>,
> {
    state: Option<DumpChannelState<T, RT>>,
    txn: RT,
    channel: C,
}

pub enum DumpChunk {
    Dep([u8; 9]),
    Hash([u8; 42]),
    Edge([u8; 50]),
    End([u8; 25]),
}

impl std::ops::Deref for DumpChunk {
    type Target = [u8];
    fn deref(&self) -> &Self::Target {
        match *self {
            DumpChunk::Dep(ref h) => h,
            DumpChunk::Hash(ref h) => h,
            DumpChunk::Edge(ref e) => e,
            DumpChunk::End(ref e) => e,
        }
    }
}

#[repr(u8)]
enum Msg {
    Hash = 253,
    Dep = 254,
    Vertex = 255,
}

impl<
        T: ChannelTxnT + GraphIter + DepsTxnT<DepsError = <T as GraphTxnT>::GraphError>,
        RT: std::ops::Deref<Target = T> + Clone,
        C: std::ops::Deref<Target = T::Channel>,
    > Iterator for DumpChannel<T, RT, C>
{
    type Item = Result<DumpChunk, TxnErr<T::GraphError>>;
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            match self.state.take() {
                Some(DumpChannelState::Changes {
                    mut log,
                    current,
                    deps,
                }) => {
                    if let Some(mut deps) = deps {
                        while let Some(x) = deps.next() {
                            let (h, dep) = match x {
                                Ok(x) => x,
                                Err(e) => return Some(Err(e)),
                            };
                            if h > current {
                                break;
                            } else if h < current {
                                continue;
                            }
                            let mut msg = [Msg::Dep as u8; 9];
                            byteorder::BigEndian::write_u64(&mut msg[1..], dep.0);
                            self.state = Some(DumpChannelState::Changes {
                                log,
                                current,
                                deps: Some(deps),
                            });
                            debug!("dep msg = {:?}", msg);
                            return Some(Ok(DumpChunk::Dep(msg)));
                        }
                    }
                    if let Some(x) = log.next() {
                        let (_, (h, _)) = match x {
                            Ok(e) => e,
                            Err(e) => return Some(Err(e)),
                        };
                        let deps = match T::iter_dep_ref(self.txn.clone(), h) {
                            Ok(e) => Some(e),
                            Err(e) => return Some(Err(e)),
                        };
                        self.state = Some(DumpChannelState::Changes {
                            log,
                            current: h,
                            deps,
                        });
                        let ext = match self.txn.get_external(h) {
                            Ok(ext) => ext.unwrap(),
                            Err(e) => return Some(Err(e)),
                        };

                        let mut msg = [Msg::Hash as u8; 1 + 33 + 8];
                        (&mut msg[1..34]).clone_from_slice(&ext.to_bytes()[..]);
                        byteorder::BigEndian::write_u64(&mut msg[34..], h.0);
                        return Some(Ok(DumpChunk::Hash(msg)));
                    } else {
                        self.state = Some(DumpChannelState::Graph {
                            cursor: match self.txn.iter_graph(self.txn.graph(&self.channel)) {
                                Ok(c) => c,
                                Err(e) => return Some(Err(e)),
                            },
                            current: Vertex::ROOT,
                            is_first: true,
                        })
                    }
                }
                Some(DumpChannelState::Graph {
                    mut cursor,
                    mut current,
                    is_first,
                }) => {
                    if let Some(x) = self
                        .txn
                        .next_graph(self.txn.graph(&self.channel), &mut cursor)
                    {
                        let (v, e) = match x {
                            Err(e) => return Some(Err(e)),
                            Ok(x) => x,
                        };
                        if !e.flag.contains(EdgeFlags::PARENT) {
                            self.state = Some(DumpChannelState::Graph {
                                cursor,
                                current,
                                is_first,
                            });
                            continue;
                        }
                        if v != current || is_first {
                            let mut buf = [Msg::Vertex as u8; 50];
                            byteorder::LittleEndian::write_u64(&mut buf[1..], v.change.0);
                            byteorder::LittleEndian::write_u64(&mut buf[9..], v.start.0);
                            byteorder::LittleEndian::write_u64(&mut buf[17..], v.end.0);
                            current = v;
                            buf[25] = e.flag.bits();
                            byteorder::LittleEndian::write_u64(&mut buf[26..], e.dest.change.0);
                            byteorder::LittleEndian::write_u64(&mut buf[34..], e.dest.pos.0);
                            byteorder::LittleEndian::write_u64(&mut buf[42..], e.introduced_by.0);
                            self.state = Some(DumpChannelState::Graph {
                                cursor,
                                current,
                                is_first: false,
                            });
                            debug!("sending {:?}", &buf[..]);
                            return Some(Ok(DumpChunk::Edge(buf)));
                        } else {
                            let mut buf = [0; 25];
                            buf[0] = e.flag.bits();
                            byteorder::LittleEndian::write_u64(&mut buf[1..], e.dest.change.0);
                            byteorder::LittleEndian::write_u64(&mut buf[9..], e.dest.pos.0);
                            byteorder::LittleEndian::write_u64(&mut buf[17..], e.introduced_by.0);
                            self.state = Some(DumpChannelState::Graph {
                                cursor,
                                current,
                                is_first: false,
                            });
                            debug!("sending {:?}", &buf[..]);
                            return Some(Ok(DumpChunk::End(buf)));
                        }
                    } else {
                        self.state = None;
                        let mut buf = [Msg::Vertex as u8; 25];
                        byteorder::LittleEndian::write_u64(&mut buf[1..], Vertex::BOTTOM.change.0);
                        byteorder::LittleEndian::write_u64(&mut buf[9..], Vertex::BOTTOM.start.0);
                        byteorder::LittleEndian::write_u64(&mut buf[17..], Vertex::BOTTOM.end.0);
                        debug!("sending {:?}", buf);
                        return Some(Ok(DumpChunk::End(buf)));
                    }
                }
                None => return None,
            }
        }
    }
}

pub fn dump_channel<
    T: ChannelTxnT + GraphIter + DepsTxnT<DepsError = <T as GraphTxnT>::GraphError>,
    RT: std::ops::Deref<Target = T> + Clone,
    C: std::ops::Deref<Target = T::Channel>,
>(
    txn: RT,
    channel: C,
) -> Result<DumpChannel<T, RT, C>, TxnErr<T::GraphError>> {
    Ok(DumpChannel {
        state: Some(DumpChannelState::Changes {
            log: changeid_log_ref(txn.clone(), &channel, 0)?,
            current: ChangeId::ROOT,
            deps: None,
        }),
        txn,
        channel,
    })
}

pub struct ChannelFromDump<'a, T: ChannelMutTxnT> {
    txn: &'a mut T,
    channel: ChannelRef<T>,
    buf: Buf,
    current: Vertex<ChangeId>,
    reverses: Vec<(Vertex<ChangeId>, Edge)>,
    starts: HashMap<Position<ChangeId>, ChangePosition>,
    current_changeid: Option<ChangeId>,
    local_changeid: HashMap<ChangeId, ChangeId>,
    pub alive: HashSet<ChangeId>,
}

/// The following type does zero-copy buffering: if there are enough
/// bytes in the part we just read, we just return these bytes. Else,
/// we copy the bytes in cache, and complete the cache once we have
/// enough bytes.
///
/// The size of the cache could be generic, but since edges and
/// vertices take 25 bytes, hashes 33, and [u8; 33] doesn't implement
/// AsMut<[u8]>, we just use a fixed-sized array of length 33.
pub struct Buf {
    /// Internal cache.
    buf: [u8; 68],
    /// Length of the internal cache that is currently used.
    buf_len: usize,
    /// Position in the last buffer that was read. The `read` method
    /// must be called with the same buffer until that method returns
    /// `None`.
    pos: usize,
}

impl Buf {
    /// Create a new buffer.
    fn new() -> Self {
        Buf {
            buf: [0; 68],
            buf_len: 0,
            pos: 0,
        }
    }

    /// Read `wanted` number of bytes from `bytes` using the internal
    /// cache if needed.  This method must be called with the same
    /// `bytes` buffer until it returns `None`.
    fn read<'a>(&'a mut self, bytes: &'a [u8], wanted: usize) -> Option<&'a [u8]> {
        trace!(
            "bytes = {:?}, self.buf = {:?} {:?} {:?}",
            bytes,
            &self.buf[..],
            self.buf_len,
            self.pos
        );
        assert!(wanted < self.buf.len());
        if self.buf_len > 0 {
            let needs = wanted - self.buf_len;
            if self.pos + needs > bytes.len() {
                // Not enough bytes to complete the internal buffer,
                // we need to save these extra bytes.
                let len = self.buf_len + bytes.len();
                (&mut self.buf[self.buf_len..len]).clone_from_slice(&bytes[self.pos..]);
                self.buf_len = len;
                self.pos = 0;
                None
            } else {
                // There are enough bytes, output them.
                (&mut self.buf[self.buf_len..wanted])
                    .clone_from_slice(&bytes[self.pos..self.pos + needs]);
                self.buf_len = 0;
                self.pos += needs;
                Some(&self.buf[..wanted])
            }
        } else if bytes.len() - self.pos >= wanted {
            // The internal buffer is empty, and `bytes` is long enough.
            let buf = &bytes[self.pos..self.pos + wanted];
            self.pos += wanted;
            Some(buf)
        } else {
            // The internal buffer is empty and `bytes` is too short,
            // save the extra bytes.
            self.buf_len = bytes.len() - self.pos;
            (&mut self.buf[..self.buf_len]).clone_from_slice(&bytes[self.pos..]);
            self.pos = 0;
            None
        }
    }

    fn current<'a>(&self, bytes: &'a [u8]) -> Option<&'a u8> {
        // debug!("self.pos = {:?}", self.pos);
        bytes.get(self.pos)
    }
}

impl<'a, T: ChannelMutTxnT + DepsMutTxnT + DepsTxnT<DepsError = <T as GraphTxnT>::GraphError>>
    ChannelFromDump<'a, T>
{
    pub fn new(txn: &'a mut T, channel: ChannelRef<T>) -> Self {
        let mut starts = HashMap::with_capacity(4096);
        starts.insert(Position::ROOT, Position::ROOT.pos);
        ChannelFromDump {
            txn,
            channel,
            buf: Buf::new(),
            current: Vertex::ROOT,
            reverses: Vec::with_capacity(4096),
            starts,
            current_changeid: None,
            local_changeid: HashMap::new(),
            alive: HashSet::new(),
        }
    }

    pub fn read(&mut self, bytes: &[u8]) -> Result<bool, TxnErr<T::GraphError>> {
        let mut channel = self.channel.borrow_mut();
        while let Some(&cur) = self.buf.current(bytes) {
            debug!("cur = {:?}", cur);
            if cur == Msg::Hash as u8 {
                if let Some(buf) = self.buf.read(bytes, 42) {
                    let hash = Hash::from_bytes(&buf[1..34]).unwrap();
                    let mut p = ChangeId(byteorder::BigEndian::read_u64(&buf[34..]));
                    // Test if `p` is already taken for another hash.
                    if let Some(hh) = self.txn.get_external(p)? {
                        if hh != hash {
                            let pp = make_changeid(self.txn, &hash)?;
                            self.local_changeid.insert(p, pp);
                            p = pp
                        }
                    }
                    let t = self.txn.apply_counter(&channel);
                    debug!("hash = {:?} {:?}", hash, p);
                    self.txn.put_external(p, hash)?;
                    self.txn.put_internal(hash, p)?;
                    self.txn.put_changes(&mut channel, p, t, &hash)?;
                    self.current_changeid = Some(p);
                }
            } else if cur == Msg::Dep as u8 {
                debug!("dep");
                if let Some(buf) = self.buf.read(bytes, 9) {
                    let mut a = ChangeId(byteorder::BigEndian::read_u64(&buf[1..9]));
                    if let Some(aa) = self.local_changeid.get(&a) {
                        a = *aa
                    }
                    if let Some(cur) = self.current_changeid {
                        self.txn.put_dep(cur, a)?;
                        self.txn.put_revdep(a, cur)?;
                    }
                    debug!("cur = {:?}, a = {:?}", self.current_changeid, a);
                }
            } else if cur == Msg::Vertex as u8 {
                // New vertex
                if let Some(buf) = self.buf.read(bytes, 25) {
                    self.current = read_vertex(buf);
                    debug!("new vertex {:?}", self.current);
                    if self.current == Vertex::BOTTOM {
                        finish_channel(self.txn, &mut channel, &self.reverses, &self.starts)?;
                        return Ok(true);
                    }
                    if let Some(aa) = self.local_changeid.get(&self.current.change) {
                        self.current.change = *aa
                    }
                } else {
                    break;
                }
            } else if let Some(buf) = self.buf.read(bytes, 25) {
                // Edge
                let mut edge = read_edge(buf);
                if let Some(aa) = self.local_changeid.get(&edge.dest.change) {
                    edge.dest.change = *aa
                }
                if let Some(aa) = self.local_changeid.get(&edge.introduced_by) {
                    edge.introduced_by = *aa
                }
                if !edge.flag.contains(EdgeFlags::DELETED) {
                    self.alive.insert(edge.dest.change);
                }
                debug!("put edge {:?} {:?}", self.current, edge);
                self.txn
                    .put_graph(T::graph_mut(&mut channel), self.current, edge)?;
                self.reverses.push((self.current, edge));
                self.starts
                    .insert(self.current.end_pos(), self.current.start);
            } else {
                break;
            }
        }
        self.buf.pos = 0;
        Ok(false)
    }

    pub fn edges(&self) -> &[(Vertex<ChangeId>, Edge)] {
        &self.reverses[..]
    }
}

fn finish_channel<T: super::ChannelMutTxnT>(
    txn: &mut T,
    channel: &mut T::Channel,
    reverses: &[(Vertex<ChangeId>, Edge)],
    ends: &HashMap<Position<ChangeId>, ChangePosition>,
) -> Result<(), TxnErr<T::GraphError>> {
    debug!("ends: {:?}", ends);
    for &(v, e) in reverses {
        debug!("{:?}", e);
        let u = Vertex {
            change: e.dest.change,
            start: *ends.get(&e.dest).unwrap(),
            end: e.dest.pos,
        };
        let mut e = e;
        e.flag ^= EdgeFlags::PARENT;
        e.dest = v.start_pos();
        txn.put_graph(T::graph_mut(channel), u, e)?;
    }
    Ok(())
}

fn read_vertex(bytes: &[u8]) -> Vertex<ChangeId> {
    let change = byteorder::LittleEndian::read_u64(&bytes[1..]);
    let start = byteorder::LittleEndian::read_u64(&bytes[9..]);
    let end = byteorder::LittleEndian::read_u64(&bytes[17..]);
    Vertex {
        change: ChangeId(change),
        start: ChangePosition(start),
        end: ChangePosition(end),
    }
}

fn read_edge(bytes: &[u8]) -> Edge {
    let flag = EdgeFlags::from_bits(bytes[0]).unwrap();
    let change = byteorder::LittleEndian::read_u64(&bytes[1..]);
    let p = byteorder::LittleEndian::read_u64(&bytes[9..]);
    let introduced_by = byteorder::LittleEndian::read_u64(&bytes[17..]);
    Edge {
        flag,
        dest: Position {
            change: ChangeId(change),
            pos: ChangePosition(p),
        },
        introduced_by: ChangeId(introduced_by),
    }
}
