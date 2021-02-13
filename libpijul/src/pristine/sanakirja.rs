use super::*;
use crate::small_string;
use ::sanakirja::{Alignment, Commit, Db, Representable, Transaction, UnsafeDb};
use byteorder::{ByteOrder, LittleEndian};
use rand::rngs::ThreadRng;
use rand::thread_rng;
use std::cell::RefCell;
use std::collections::hash_map::Entry;
use std::collections::HashMap;
use std::path::Path;
use std::sync::Arc;

/// A Sanakirja pristine.
pub struct Pristine {
    pub env: Arc<::sanakirja::Env<::sanakirja::Exclusive>>,
}

#[derive(Debug, Error)]
pub enum SanakirjaError {
    #[error(transparent)]
    Sanakirja(#[from] ::sanakirja::Error),
    #[error("Pristine locked")]
    PristineLocked,
    #[error("Pristine corrupt")]
    PristineCorrupt,
    #[error(transparent)]
    Borrow(#[from] std::cell::BorrowError),
}

impl std::convert::From<::sanakirja::CRCError> for SanakirjaError {
    fn from(_: ::sanakirja::CRCError) -> Self {
        SanakirjaError::PristineCorrupt
    }
}

impl std::convert::From<::sanakirja::CRCError> for TxnErr<SanakirjaError> {
    fn from(_: ::sanakirja::CRCError) -> Self {
        TxnErr(SanakirjaError::PristineCorrupt)
    }
}

impl std::convert::From<::sanakirja::Error> for TxnErr<SanakirjaError> {
    fn from(e: ::sanakirja::Error) -> Self {
        TxnErr(e.into())
    }
}

impl std::convert::From<TxnErr<::sanakirja::Error>> for TxnErr<SanakirjaError> {
    fn from(e: TxnErr<::sanakirja::Error>) -> Self {
        TxnErr(e.0.into())
    }
}

impl Pristine {
    pub fn new<P: AsRef<Path>>(name: P) -> Result<Self, SanakirjaError> {
        Self::new_with_size(name, 1 << 20)
    }
    pub unsafe fn new_nolock<P: AsRef<Path>>(name: P) -> Result<Self, SanakirjaError> {
        Self::new_with_size_nolock(name, 1 << 20)
    }
    pub fn new_with_size<P: AsRef<Path>>(name: P, size: u64) -> Result<Self, SanakirjaError> {
        let env = ::sanakirja::Env::try_new(name, size);
        match env {
            Ok(env) => Ok(Pristine { env: Arc::new(env) }),
            Err(::sanakirja::Error::IO(e)) => {
                if let std::io::ErrorKind::WouldBlock = e.kind() {
                    Err(SanakirjaError::PristineLocked)
                } else {
                    Err(SanakirjaError::Sanakirja(::sanakirja::Error::IO(e)))
                }
            }
            Err(e) => Err(SanakirjaError::Sanakirja(e)),
        }
    }
    pub unsafe fn new_with_size_nolock<P: AsRef<Path>>(
        name: P,
        size: u64,
    ) -> Result<Self, SanakirjaError> {
        Ok(Pristine {
            env: Arc::new(::sanakirja::Env::new_nolock(name, size)?),
        })
    }
    pub fn new_anon() -> Result<Self, SanakirjaError> {
        Self::new_anon_with_size(1 << 20)
    }
    pub fn new_anon_with_size(size: u64) -> Result<Self, SanakirjaError> {
        Ok(Pristine {
            env: Arc::new(::sanakirja::Env::new_anon(size)?),
        })
    }
}

#[derive(Debug, PartialEq, Clone, Copy)]
#[repr(usize)]
pub enum Root {
    Tree,
    RevTree,
    Inodes,
    RevInodes,
    Internal,
    External,
    RevDep,
    Channels,
    TouchedFiles,
    Dep,
    RevTouchedFiles,
    Partials,
    Remotes,
}

impl Pristine {
    pub fn txn_begin(&self) -> Result<Txn, SanakirjaError> {
        let txn = ::sanakirja::Env::txn_begin(self.env.clone())?;
        fn begin(
            txn: ::sanakirja::Txn<
                ::sanakirja::Exclusive,
                Arc<::sanakirja::Env<::sanakirja::Exclusive>>,
            >,
        ) -> Option<Txn> {
            Some(Txn {
                channels: txn.root(Root::Channels as usize)?,
                external: txn.root(Root::External as usize)?,
                internal: txn.root(Root::Internal as usize)?,
                inodes: txn.root(Root::Inodes as usize)?,
                revinodes: txn.root(Root::RevInodes as usize)?,
                tree: txn.root(Root::Tree as usize)?,
                revtree: txn.root(Root::RevTree as usize)?,
                revdep: txn.root(Root::RevDep as usize)?,
                touched_files: txn.root(Root::TouchedFiles as usize)?,
                rev_touched_files: txn.root(Root::RevTouchedFiles as usize)?,
                partials: txn.root(Root::Partials as usize)?,
                dep: txn.root(Root::Dep as usize)?,
                remotes: txn.root(Root::Remotes as usize)?,
                rng: thread_rng(),
                open_channels: RefCell::new(HashMap::new()),
                open_remotes: RefCell::new(HashMap::new()),
                txn,
            })
        }
        if let Some(txn) = begin(txn) {
            Ok(txn)
        } else {
            Err(SanakirjaError::PristineCorrupt)
        }
    }

    pub fn mut_txn_begin(&self) -> MutTxn<()> {
        let mut txn = ::sanakirja::Env::mut_txn_begin(self.env.clone()).unwrap();
        MutTxn {
            channels: txn
                .root(Root::Channels as usize)
                .unwrap_or_else(|| txn.create_db().unwrap()),
            external: txn
                .root(Root::External as usize)
                .unwrap_or_else(|| txn.create_db().unwrap()),
            internal: txn
                .root(Root::Internal as usize)
                .unwrap_or_else(|| txn.create_db().unwrap()),
            inodes: txn
                .root(Root::Inodes as usize)
                .unwrap_or_else(|| txn.create_db().unwrap()),
            revinodes: txn
                .root(Root::RevInodes as usize)
                .unwrap_or_else(|| txn.create_db().unwrap()),
            tree: txn
                .root(Root::Tree as usize)
                .unwrap_or_else(|| txn.create_db().unwrap()),
            revtree: txn
                .root(Root::RevTree as usize)
                .unwrap_or_else(|| txn.create_db().unwrap()),
            revdep: txn
                .root(Root::RevDep as usize)
                .unwrap_or_else(|| txn.create_db().unwrap()),
            dep: txn
                .root(Root::Dep as usize)
                .unwrap_or_else(|| txn.create_db().unwrap()),
            touched_files: txn
                .root(Root::TouchedFiles as usize)
                .unwrap_or_else(|| txn.create_db().unwrap()),
            rev_touched_files: txn
                .root(Root::RevTouchedFiles as usize)
                .unwrap_or_else(|| txn.create_db().unwrap()),
            partials: txn
                .root(Root::Partials as usize)
                .unwrap_or_else(|| txn.create_db().unwrap()),
            remotes: txn
                .root(Root::Remotes as usize)
                .unwrap_or_else(|| txn.create_db().unwrap()),
            rng: thread_rng(),
            open_channels: RefCell::new(HashMap::new()),
            open_remotes: RefCell::new(HashMap::new()),
            txn,
        }
    }
}

type Graph = ::sanakirja::Db<Vertex<ChangeId>, Edge>;
type ChangeSet = ::sanakirja::Db<ChangeId, ApplyTimestamp>;
type RevChangeSet = ::sanakirja::Db<ApplyTimestamp, (ChangeId, Merkle)>;
type ChannelStates = ::sanakirja::Db<Merkle, u64>;

pub type Txn = GenericTxn<
    ::sanakirja::Txn<::sanakirja::Exclusive, Arc<::sanakirja::Env<::sanakirja::Exclusive>>>,
>;
pub type MutTxn<T> =
    GenericTxn<::sanakirja::MutTxn<Arc<::sanakirja::Env<::sanakirja::Exclusive>>, T>>;

/// A transaction, used both for mutable and immutable transactions,
/// depending on type parameter `T`.
///
/// In Sanakirja, both `sanakirja::Txn` and `sanakirja::MutTxn`
/// implement `sanakirja::Transaction`, explaining our implementation
/// of `TxnT` for `Txn<T>` for all `T: sanakirja::Transaction`. This
/// covers both mutable and immutable transactions in a single
/// implementation.
pub struct GenericTxn<T: ::sanakirja::Transaction> {
    #[doc(hidden)]
    pub txn: T,
    #[doc(hidden)]
    pub internal: Db<Hash, ChangeId>,
    #[doc(hidden)]
    pub external: Db<ChangeId, Hash>,
    inodes: Db<Inode, Position<ChangeId>>,
    revinodes: Db<Position<ChangeId>, Inode>,

    tree: Db<UnsafePathId, Inode>,
    revtree: Db<Inode, UnsafePathId>,

    revdep: Db<ChangeId, ChangeId>,
    dep: Db<ChangeId, ChangeId>,

    touched_files: Db<Position<ChangeId>, ChangeId>,
    rev_touched_files: Db<ChangeId, Position<ChangeId>>,

    partials: Db<UnsafeSmallStr, Position<ChangeId>>,
    channels: Db<UnsafeSmallStr, (Graph, ChangeSet, RevChangeSet, ChannelStates, u64, u64)>,
    remotes: Db<UnsafeSmallStr, (Db<u64, (Hash, Merkle)>, Db<Hash, u64>, Db<Merkle, u64>)>,
    rng: ThreadRng,
    open_channels: RefCell<HashMap<SmallString, ChannelRef<Self>>>,
    open_remotes: RefCell<HashMap<SmallString, RemoteRef<Self>>>,
}

/// This is actually safe because the only non-Send fields are
/// `open_channels` and `open_remotes`, but we can't do anything with
/// a `ChannelRef` whose transaction has been moved to another thread.
unsafe impl<T: ::sanakirja::Transaction> Send for GenericTxn<T> {}

#[derive(Debug)]
pub struct DatabaseReport {
    pub refs: usize,
    pub stats: ::sanakirja::Statistics,
}

impl Txn {
    pub fn check_database(&self) -> DatabaseReport {
        let mut refs = HashMap::new();
        self.txn.references(&mut refs, self.internal);
        info!("refs = {:?}", refs);
        self.txn.references(&mut refs, self.external);
        info!("refs = {:?}", refs);
        self.txn.references(&mut refs, self.inodes);
        info!("refs = {:?}", refs);
        self.txn.references(&mut refs, self.revinodes);
        info!("refs = {:?}", refs);
        self.txn.references(&mut refs, self.tree);
        info!("refs = {:?}", refs);
        self.txn.references(&mut refs, self.revtree);
        info!("refs = {:?}", refs);
        self.txn.references(&mut refs, self.revdep);
        info!("refs = {:?}", refs);
        self.txn.references(&mut refs, self.dep);
        info!("refs = {:?}", refs);
        self.txn.references(&mut refs, self.touched_files);
        info!("refs = {:?}", refs);
        self.txn.references(&mut refs, self.rev_touched_files);
        info!("refs = {:?}", refs);
        self.txn.references(&mut refs, self.partials);
        info!("refs = {:?}", refs);
        self.txn.references(&mut refs, self.channels);
        info!("refs = {:?}", refs);
        for x in self.txn.iter(&self.channels, None).unwrap() {
            let (a, (g, c, r, s, _, _)) = x.unwrap();
            info!("channel = {:?}", a);
            self.txn.references(&mut refs, g);
            info!("refs = {:?}", refs);
            self.txn.references(&mut refs, c);
            info!("refs = {:?}", refs);
            self.txn.references(&mut refs, r);
            info!("refs = {:?}", refs);
            self.txn.references(&mut refs, s);
            info!("refs = {:?}", refs);
        }
        self.txn.references(&mut refs, self.remotes);
        info!("refs = {:?}", refs);
        for x in self.txn.iter(&self.remotes, None).unwrap() {
            let (a, (u, v, w)) = x.unwrap();
            info!("remote = {:?}", a);
            self.txn.references(&mut refs, u);
            info!("refs = {:?}", refs);
            self.txn.references(&mut refs, v);
            info!("refs = {:?}", refs);
            self.txn.references(&mut refs, w);
            info!("refs = {:?}", refs);
        }

        let stats = self.txn.statistics();
        let report = DatabaseReport {
            refs: refs.len(),
            stats: stats.clone(),
        };
        let mut channel_roots: Vec<UnsafeDb> = Vec::new();
        for x in self.txn.iter(&self.channels, None).unwrap() {
            let (a, (g, c, r, s, _, _)) = x.unwrap();
            info!("channel: {:?}", a);
            unsafe {
                channel_roots.push(std::mem::transmute(g));
                channel_roots.push(std::mem::transmute(c));
                channel_roots.push(std::mem::transmute(r));
                channel_roots.push(std::mem::transmute(s));
            }
        }
        ::sanakirja::debug_(&self.txn, &channel_roots[..], "debug_sanakirja", true);
        self.txn.check_references(&mut refs);

        info!("stats = {:?}", stats);
        let occupied_pages =
            stats.total_pages - stats.free_pages.len() - stats.bookkeeping_pages.len();
        for i in 1..(stats.total_pages as u64) {
            let p = i * 4096;
            if !refs.contains_key(&p)
                && !stats.free_pages.contains(&p)
                && !stats.bookkeeping_pages.contains(&p)
            {
                panic!("does not contain {:?} ({:?})", i, p);
            }
        }

        // check that there is no intersection.
        for (r, _) in refs.iter() {
            if stats.free_pages.contains(r) {
                panic!("referenced page is free: {:?}", r);
            }
            if stats.bookkeeping_pages.contains(r) {
                panic!("referenced page is a bookkeeping page: {:?}", r);
            }
        }
        for p in stats.free_pages.iter() {
            if stats.bookkeeping_pages.contains(p) {
                panic!("bookkeeping inter free: {:?}", p);
            }
        }

        assert_eq!(1 + refs.len(), occupied_pages);

        report
    }
}

impl<T: ::sanakirja::Transaction> GraphTxnT for GenericTxn<T> {
    type Graph = Db<Vertex<ChangeId>, Edge>;
    type GraphError = SanakirjaError;

    sanakirja_get!(graph, Vertex<ChangeId>, Edge, GraphError);
    fn get_external(&self, p: ChangeId) -> Result<Option<Hash>, TxnErr<Self::GraphError>> {
        if p.is_root() {
            Ok(Some(Hash::None))
        } else if let Ok(x) = self.txn.get(&self.external, p, None) {
            Ok(x)
        } else {
            Err(TxnErr(SanakirjaError::PristineCorrupt))
        }
    }

    fn get_internal(&self, p: Hash) -> Result<Option<ChangeId>, TxnErr<Self::GraphError>> {
        if let Hash::None = p {
            Ok(Some(ChangeId::ROOT))
        } else if let Ok(x) = self.txn.get(&self.internal, p, None) {
            Ok(x)
        } else {
            Err(TxnErr(SanakirjaError::PristineCorrupt))
        }
    }

    type Adj = Adj;

    fn init_adj(
        &self,
        g: &Self::Graph,
        key: Vertex<ChangeId>,
        dest: Position<ChangeId>,
        min_flag: EdgeFlags,
        max_flag: EdgeFlags,
    ) -> Result<Self::Adj, TxnErr<Self::GraphError>> {
        let edge = Edge {
            flag: min_flag,
            dest,
            introduced_by: ChangeId::ROOT,
        };
        if let Ok((cursor, _)) = self.txn.set_cursors(g, Some((key, Some(edge)))) {
            Ok(Adj {
                cursor,
                key,
                min_flag,
                max_flag,
            })
        } else {
            Err(TxnErr(SanakirjaError::PristineCorrupt))
        }
    }

    fn next_adj(
        &self,
        _: &Self::Graph,
        a: &mut Self::Adj,
    ) -> Option<Result<Edge, TxnErr<Self::GraphError>>> {
        next_adj(&self.txn, a)
    }

    fn find_block(
        &self,
        graph: &Self::Graph,
        p: Position<ChangeId>,
    ) -> Result<Vertex<ChangeId>, BlockError<Self::GraphError>> {
        find_block(&self.txn, graph, p)
    }

    fn find_block_end(
        &self,
        graph: &Self::Graph,
        p: Position<ChangeId>,
    ) -> Result<Vertex<ChangeId>, BlockError<Self::GraphError>> {
        find_block_end(&self.txn, graph, p)
    }
}

unsafe fn next_graph<T: ::sanakirja::Transaction>(
    txn: &T,
    cursor: &mut ::sanakirja::Cursor,
) -> Result<Option<(Vertex<ChangeId>, Edge)>, BlockError<SanakirjaError>> {
    match ::sanakirja::next::<_, Vertex<ChangeId>, Edge>(txn, cursor) {
        Ok(x) => Ok(x),
        Err(::sanakirja::CRCError {}) => Err(BlockError::Txn(SanakirjaError::PristineCorrupt)),
    }
}

unsafe fn prev_graph<T: ::sanakirja::Transaction>(
    txn: &T,
    cursor: &mut ::sanakirja::Cursor,
) -> Result<Option<(Vertex<ChangeId>, Edge)>, BlockError<SanakirjaError>> {
    match ::sanakirja::prev::<_, Vertex<ChangeId>, Edge>(txn, cursor) {
        Ok(x) => Ok(x),
        Err(::sanakirja::CRCError {}) => Err(BlockError::Txn(SanakirjaError::PristineCorrupt)),
    }
}

#[doc(hidden)]
pub fn next_adj<T: ::sanakirja::Transaction>(
    txn: &T,
    a: &mut Adj,
) -> Option<Result<Edge, TxnErr<SanakirjaError>>> {
    loop {
        let x: Result<Option<(Vertex<ChangeId>, Edge)>, _> =
            unsafe { ::sanakirja::next(txn, &mut a.cursor) };
        match x {
            Ok(Some((v, e))) => {
                debug!("adjacent iterator: {:?} {:?}", v, e);
                if v == a.key {
                    if e.flag >= a.min_flag {
                        if e.flag <= a.max_flag {
                            return Some(Ok(e));
                        } else {
                            return None;
                        }
                    }
                } else if v > a.key {
                    return None;
                }
            }
            Err(e) => return Some(Err(TxnErr(e.into()))),
            Ok(None) => {
                debug!("adjacent iterator: over");
                return None;
            }
        }
    }
}

#[doc(hidden)]
pub fn find_block<T: ::sanakirja::Transaction>(
    txn: &T,
    graph: &::sanakirja::Db<Vertex<ChangeId>, Edge>,
    p: Position<ChangeId>,
) -> Result<Vertex<ChangeId>, BlockError<SanakirjaError>> {
    if p.change.is_root() {
        return Ok(Vertex::ROOT);
    }
    let key = Vertex {
        change: p.change,
        start: p.pos,
        end: p.pos,
    };
    debug!(target: "libpijul::find_block", "find_block {:?}", key);
    let mut cursor = if let Ok((cursor, _)) = txn.set_cursors(&graph, Some((key, None))) {
        cursor
    } else {
        return Err(BlockError::Txn(SanakirjaError::PristineCorrupt));
    };
    let mut k = if let Some((k, _)) = unsafe { next_graph(txn, &mut cursor)? } {
        k
    } else {
        return Err(BlockError::Block { block: p });
    };
    debug!("k = {:?}", k);
    // The only guarantee here is that k is either the first key
    // >= `key`, or the key just before that. We might need to
    // rewind by one step if key is strictly larger than the
    // result (i.e. if `p` is in the middle of the key).
    while k.change > p.change || (k.change == p.change && k.start > p.pos) {
        debug!(target: "libpijul::find_block", "find_block while {:?}", k);
        if let Some((k_, _)) = unsafe { prev_graph(txn, &mut cursor)? } {
            k = k_
        } else {
            break;
        }
    }
    loop {
        debug!(target: "libpijul::find_block", "find_block loop {:?}", k);
        if k.change == p.change && k.start <= p.pos {
            if k.end > p.pos || (k.start == k.end && k.end == p.pos) {
                return Ok(k);
            }
        } else if k.change > p.change {
            return Err(BlockError::Block { block: p });
        }
        if let Some((k_, _)) = unsafe { next_graph(txn, &mut cursor)? } {
            k = k_
        } else {
            break;
        }
    }
    debug!(target: "libpijul::find_block", "find_block None, {:?}", k);
    Err(BlockError::Block { block: p })
}

#[doc(hidden)]
pub fn find_block_end<T: ::sanakirja::Transaction>(
    txn: &T,
    graph: &::sanakirja::Db<Vertex<ChangeId>, Edge>,
    p: Position<ChangeId>,
) -> Result<Vertex<ChangeId>, BlockError<SanakirjaError>> {
    if p.change.is_root() {
        return Ok(Vertex::ROOT);
    }
    let key = Vertex {
        change: p.change,
        start: p.pos,
        end: p.pos,
    };
    debug!(target: "libpijul::find_block_end", "find_block_end {:?}, p.change.0 = {:?}", key, p.change.0);
    let mut cursor = if let Ok((cursor, _)) = txn.set_cursors(&graph, Some((key, None))) {
        cursor
    } else {
        return Err(BlockError::Txn(SanakirjaError::PristineCorrupt));
    };
    let mut k = if let Some((k, _)) = unsafe { next_graph(txn, &mut cursor)? } {
        k
    } else {
        return Err(BlockError::Block { block: p });
    };
    // The only guarantee here is that k is either the first key
    // before `key`, or the key just before that.
    loop {
        debug!(target: "libpijul::find_block_end", "find_block_end loop {:?} k.change.0 = {:?}", k, k.change.0);
        if k.change < p.change {
            break;
        } else if k.change == p.change {
            // Here we want to create an edge pointing between `p`
            // and its successor. If k.start == p.pos, the only
            // case where that's what we want is if k.start ==
            // k.end.
            if k.start == p.pos && k.end == p.pos {
                return Ok(k);
            } else if k.start < p.pos {
                break;
            }
        }
        if let Some((k_, _)) = unsafe { prev_graph(txn, &mut cursor)? } {
            k = k_
        } else {
            break;
        }
    }
    // We also want k.end >= p.pos, so we just call next() until
    // we have that.
    debug!(target: "libpijul::find_block_end", "find_block_end k(0) = {:?} k.change.0 = {:?}", k, k.change.0);
    while k.change < p.change || (k.change == p.change && p.pos > k.end) {
        if let Some((k_, _)) = unsafe { next_graph(txn, &mut cursor)? } {
            k = k_
        } else {
            break;
        }
    }
    debug!(target: "libpijul::find_block_end", "find_block_end k(1) = {:?}, k.change.0 = {:?}", k, k.change.0);
    if k.change == p.change
        && ((k.start < p.pos && p.pos <= k.end) || (k.start == k.end && k.start == p.pos))
    {
        debug!("ok");
        Ok(k)
    } else {
        Err(BlockError::Block { block: p })
    }
}

pub struct Adj {
    pub cursor: ::sanakirja::Cursor,
    pub key: Vertex<ChangeId>,
    pub min_flag: EdgeFlags,
    pub max_flag: EdgeFlags,
}

impl<T: ::sanakirja::Transaction> GraphIter for GenericTxn<T> {
    type GraphCursor = ::sanakirja::Cursor;

    fn iter_graph(&self, g: &Self::Graph) -> Result<Self::GraphCursor, TxnErr<Self::GraphError>> {
        if let Ok((cursor, _)) = self.txn.set_cursors(&g, None) {
            Ok(cursor)
        } else {
            Err(TxnErr(SanakirjaError::PristineCorrupt))
        }
    }

    fn next_graph(
        &self,
        _: &Self::Graph,
        a: &mut Self::GraphCursor,
    ) -> Option<Result<(Vertex<ChangeId>, Edge), TxnErr<Self::GraphError>>> {
        match unsafe { ::sanakirja::next(&self.txn, a) } {
            Ok(Some(x)) => Some(Ok(x)),
            Ok(None) => None,
            Err(::sanakirja::CRCError {}) => Some(Err(TxnErr(SanakirjaError::PristineCorrupt))),
        }
    }
}

pub struct Channel {
    pub graph: Db<Vertex<ChangeId>, Edge>,
    pub changes: Db<ChangeId, u64>,
    pub revchanges: Db<u64, (ChangeId, Merkle)>,
    pub states: Db<Merkle, u64>,
    pub apply_counter: ApplyTimestamp,
    pub name: SmallString,
    pub last_modified: u64,
}

impl<T: ::sanakirja::Transaction> ChannelTxnT for GenericTxn<T> {
    type Channel = Channel;

    fn graph<'a>(&self, c: &'a Self::Channel) -> &'a Db<Vertex<ChangeId>, Edge> {
        &c.graph
    }
    fn name<'a>(&self, c: &'a Self::Channel) -> &'a str {
        c.name.as_str()
    }
    fn apply_counter(&self, channel: &Self::Channel) -> u64 {
        channel.apply_counter
    }
    fn last_modified(&self, channel: &Self::Channel) -> u64 {
        channel.last_modified
    }
    fn changes<'a>(&self, channel: &'a Self::Channel) -> &'a Self::Changeset {
        &channel.changes
    }
    fn rev_changes<'a>(&self, channel: &'a Self::Channel) -> &'a Self::RevChangeset {
        &channel.revchanges
    }

    type Changeset = ::sanakirja::Db<ChangeId, u64>;
    type RevChangeset = ::sanakirja::Db<u64, (ChangeId, Merkle)>;

    fn get_changeset(
        &self,
        channel: &Self::Changeset,
        c: ChangeId,
    ) -> Result<Option<u64>, TxnErr<Self::GraphError>> {
        if let Ok(x) = self.txn.get(channel, c, None) {
            Ok(x)
        } else {
            Err(TxnErr(SanakirjaError::PristineCorrupt))
        }
    }
    fn get_revchangeset(
        &self,
        revchanges: &Self::RevChangeset,
        c: u64,
    ) -> Result<Option<(ChangeId, Merkle)>, TxnErr<Self::GraphError>> {
        if let Ok(x) = self.txn.get(revchanges, c, None) {
            Ok(x)
        } else {
            Err(TxnErr(SanakirjaError::PristineCorrupt))
        }
    }

    type ChangesetCursor = ::sanakirja::Cursor;

    fn cursor_changeset<'a>(
        &'a self,
        channel: &Self::Changeset,
        pos: Option<ChangeId>,
    ) -> Result<Cursor<Self, &'a Self, Self::ChangesetCursor, ChangeId, u64>, TxnErr<SanakirjaError>>
    {
        if let Ok((cursor, _)) = self.txn.set_cursors(&channel, pos.map(|x| (x, None))) {
            Ok(Cursor {
                cursor,
                txn: self,
                marker: std::marker::PhantomData,
            })
        } else {
            Err(TxnErr(SanakirjaError::PristineCorrupt))
        }
    }

    type RevchangesetCursor = ::sanakirja::Cursor;

    fn cursor_revchangeset_ref<'a, RT: std::ops::Deref<Target = Self>>(
        txn: RT,
        channel: &Self::RevChangeset,
        pos: Option<u64>,
    ) -> Result<
        Cursor<Self, RT, Self::RevchangesetCursor, u64, (ChangeId, Merkle)>,
        TxnErr<SanakirjaError>,
    > {
        if let Ok((cursor, _)) = txn.txn.set_cursors(channel, pos.map(|x| (x, None))) {
            Ok(Cursor {
                cursor,
                txn,
                marker: std::marker::PhantomData,
            })
        } else {
            Err(TxnErr(SanakirjaError::PristineCorrupt))
        }
    }

    fn rev_cursor_revchangeset<'a>(
        &'a self,
        channel: &Self::RevChangeset,
        pos: Option<u64>,
    ) -> Result<
        RevCursor<Self, &'a Self, Self::RevchangesetCursor, u64, (ChangeId, Merkle)>,
        TxnErr<SanakirjaError>,
    > {
        let cursor = if let Some(pos) = pos {
            if let Ok((x, _)) = self.txn.set_cursors(channel, Some((pos, None))) {
                x
            } else {
                return Err(TxnErr(SanakirjaError::PristineCorrupt));
            }
        } else if let Ok(x) = self.txn.set_cursors_last(channel) {
            x
        } else {
            return Err(TxnErr(SanakirjaError::PristineCorrupt));
        };
        Ok(RevCursor {
            cursor,
            txn: self,
            marker: std::marker::PhantomData,
        })
    }

    fn cursor_revchangeset_next(
        &self,
        cursor: &mut Self::RevchangesetCursor,
    ) -> Result<Option<(u64, (ChangeId, Merkle))>, TxnErr<SanakirjaError>> {
        if let Ok(x) = unsafe { ::sanakirja::next(&self.txn, cursor) } {
            Ok(x)
        } else {
            Err(TxnErr(SanakirjaError::PristineCorrupt))
        }
    }
    fn cursor_revchangeset_prev(
        &self,
        cursor: &mut Self::RevchangesetCursor,
    ) -> Result<Option<(u64, (ChangeId, Merkle))>, TxnErr<SanakirjaError>> {
        if let Ok(x) = unsafe { ::sanakirja::prev(&self.txn, cursor) } {
            Ok(x)
        } else {
            Err(TxnErr(SanakirjaError::PristineCorrupt))
        }
    }

    fn cursor_changeset_next(
        &self,
        cursor: &mut Self::ChangesetCursor,
    ) -> Result<Option<(ChangeId, u64)>, TxnErr<SanakirjaError>> {
        if let Ok(x) = unsafe { ::sanakirja::next(&self.txn, cursor) } {
            Ok(x)
        } else {
            Err(TxnErr(SanakirjaError::PristineCorrupt))
        }
    }
    fn cursor_changeset_prev(
        &self,
        cursor: &mut Self::ChangesetCursor,
    ) -> Result<Option<(ChangeId, u64)>, TxnErr<SanakirjaError>> {
        if let Ok(x) = unsafe { ::sanakirja::prev(&self.txn, cursor) } {
            Ok(x)
        } else {
            Err(TxnErr(SanakirjaError::PristineCorrupt))
        }
    }

    type States = ::sanakirja::Db<Merkle, u64>;
    fn states<'a>(&self, channel: &'a Self::Channel) -> &'a Self::States {
        &channel.states
    }
    fn channel_has_state(
        &self,
        channel: &Self::States,
        m: Merkle,
    ) -> Result<Option<u64>, TxnErr<Self::GraphError>> {
        Ok(self.txn.get(channel, m, None)?)
    }
}

impl<T: ::sanakirja::Transaction> DepsTxnT for GenericTxn<T> {
    type DepsError = SanakirjaError;
    type Dep = Db<ChangeId, ChangeId>;
    type Revdep = Db<ChangeId, ChangeId>;

    sanakirja_table_get!(dep, ChangeId, ChangeId, DepsError);
    sanakirja_table_get!(revdep, ChangeId, ChangeId, DepsError);
    sanakirja_cursor_ref!(dep, ChangeId, ChangeId);
    fn iter_dep_ref<RT: std::ops::Deref<Target = Self> + Clone>(
        txn: RT,
        p: ChangeId,
    ) -> Result<super::Cursor<Self, RT, Self::DepCursor, ChangeId, ChangeId>, TxnErr<Self::DepsError>>
    {
        Self::cursor_dep_ref(txn.clone(), &txn.dep, Some((p, None)))
    }

    sanakirja_table_get!(touched_files, Position<ChangeId>, ChangeId, DepsError);
    sanakirja_table_get!(rev_touched_files, ChangeId, Position<ChangeId>, DepsError);

    type Touched_files = Db<Position<ChangeId>, ChangeId>;

    type Rev_touched_files = Db<ChangeId, Position<ChangeId>>;
    sanakirja_iter!(touched_files, Position<ChangeId>, ChangeId);
    sanakirja_iter!(rev_touched_files, ChangeId, Position<ChangeId>);
    fn iter_revdep(
        &self,
        k: ChangeId,
    ) -> Result<
        super::Cursor<Self, &Self, Self::DepCursor, ChangeId, ChangeId>,
        TxnErr<Self::DepsError>,
    > {
        self.cursor_dep(&self.revdep, Some((k, None)))
    }

    fn iter_dep(
        &self,
        k: ChangeId,
    ) -> Result<
        super::Cursor<Self, &Self, Self::DepCursor, ChangeId, ChangeId>,
        TxnErr<Self::DepsError>,
    > {
        self.cursor_dep(&self.dep, Some((k, None)))
    }

    fn iter_touched(
        &self,
        k: Position<ChangeId>,
    ) -> Result<
        super::Cursor<Self, &Self, Self::Touched_filesCursor, Position<ChangeId>, ChangeId>,
        TxnErr<Self::DepsError>,
    > {
        self.cursor_touched_files(&self.touched_files, Some((k, None)))
    }

    fn iter_rev_touched(
        &self,
        k: ChangeId,
    ) -> Result<
        super::Cursor<Self, &Self, Self::Rev_touched_filesCursor, ChangeId, Position<ChangeId>>,
        TxnErr<Self::DepsError>,
    > {
        self.cursor_rev_touched_files(&self.rev_touched_files, Some((k, None)))
    }
}

impl<T: ::sanakirja::Transaction> TreeTxnT for GenericTxn<T> {
    type TreeError = SanakirjaError;
    type Inodes = Db<Inode, Position<ChangeId>>;
    type Revinodes = Db<Position<ChangeId>, Inode>;
    sanakirja_table_get!(inodes, Inode, Position<ChangeId>, TreeError);
    sanakirja_table_get!(revinodes, Position<ChangeId>, Inode, TreeError);
    sanakirja_cursor!(inodes, Inode, Position<ChangeId>);
    #[cfg(debug_assertions)]
    sanakirja_cursor!(revinodes, Position<ChangeId>, Inode);

    type Tree = Db<UnsafePathId, Inode>;
    sanakirja_table_get!(
        tree,
        PathId,
        Inode,
        TreeError,
        (UnsafePathId::from_fileid(key), value),
    );
    sanakirja_iter!(
        tree,
        OwnedPathId,
        Inode,
        if let Some((ref k, ref v)) = pos {
            info!("tree iter {:?} {:?}", k, v);
            Some((UnsafePathId::from_fileid(k.as_file_id()), *v))
        } else {
            None
        },
        map(|(k, v): (UnsafePathId, Inode)| (unsafe { k.to_fileid().to_owned() }, v))
    );
    sanakirja_iter!(
        revtree,
        Inode,
        OwnedPathId,
        if let Some((ref k, ref v)) = pos {
            let v = if let Some(ref v) = *v {
                Some(UnsafePathId::from_fileid(v.as_file_id()))
            } else {
                None
            };
            Some((*k, v))
        } else {
            None
        },
        map(|(k, v): (Inode, UnsafePathId)| (k, unsafe { v.to_fileid().to_owned() }))
    );

    type Revtree = Db<Inode, UnsafePathId>;
    sanakirja_table_get!(
        revtree,
        Inode,
        PathId,
        TreeError,
        (
            key,
            if let Some(value) = value {
                Some(UnsafePathId::from_fileid(value))
            } else {
                None
            }
        ),
        map(|value| unsafe { value.to_fileid() })
    );

    type Partials = Db<UnsafeSmallStr, Position<ChangeId>>;
    sanakirja_cursor!(
        partials,
        SmallString,
        Position<ChangeId>,
        if let Some((ref k, ref v)) = pos {
            Some((UnsafeSmallStr::from_small_str(k.as_small_str()), *v))
        } else {
            None
        },
        map(|(k, v): (UnsafeSmallStr, Position<ChangeId>)| (
            unsafe { k.to_small_str().to_owned() },
            v
        ))
    );
    fn iter_inodes(
        &self,
    ) -> Result<
        super::Cursor<Self, &Self, Self::InodesCursor, Inode, Position<ChangeId>>,
        TxnErr<Self::TreeError>,
    > {
        self.cursor_inodes(&self.inodes, None)
    }

    #[cfg(debug_assertions)]
    fn iter_revinodes(
        &self,
    ) -> Result<
        super::Cursor<Self, &Self, Self::RevinodesCursor, Position<ChangeId>, Inode>,
        TxnErr<SanakirjaError>,
    > {
        self.cursor_revinodes(&self.revinodes, None)
    }

    fn iter_partials<'txn>(
        &'txn self,
        k: &str,
    ) -> Result<
        super::Cursor<Self, &'txn Self, Self::PartialsCursor, SmallString, Position<ChangeId>>,
        TxnErr<SanakirjaError>,
    > {
        let k0 = SmallString::from_str(k);
        self.cursor_partials(&self.partials, Some((k0, None)))
    }
}

impl<T: ::sanakirja::Transaction> GenericTxn<T> {
    #[doc(hidden)]
    pub unsafe fn unsafe_load_channel(
        &self,
        name: SmallString,
    ) -> Result<Option<Channel>, TxnErr<SanakirjaError>> {
        if let Some((channel, changes, revchanges, states, counter, last_modified)) = self.txn.get(
            &self.channels,
            UnsafeSmallStr::from_small_str(name.as_small_str()),
            None,
        )? {
            debug!("unsafe_load_channel: found {:?} {:?}", changes, revchanges);
            Ok(Some(Channel {
                graph: channel,
                changes,
                revchanges,
                apply_counter: counter,
                states,
                name: name.clone(),
                last_modified,
            }))
        } else {
            debug!("unsafe_load_channel: not found");
            Ok(None)
        }
    }
}

impl<T: ::sanakirja::Transaction> TxnT for GenericTxn<T> {
    fn hash_from_prefix(
        &self,
        s: &str,
    ) -> Result<(Hash, ChangeId), super::HashPrefixError<Self::GraphError>> {
        let h = if let Some(h) = Hash::from_prefix(s) {
            h
        } else {
            return Err(super::HashPrefixError::Parse(s.to_string()));
        };
        let mut result = None;
        debug!("h = {:?}", h);
        for x in self
            .txn
            .iter(&self.internal, Some((h, None)))
            .map_err(|e| super::HashPrefixError::Txn(e.into()))?
        {
            let (e, i) = x.map_err(|e| super::HashPrefixError::Txn(e.into()))?;
            debug!("{:?} {:?}", e, i);
            if e < h {
                continue;
            } else {
                let b32 = e.to_base32();
                debug!("{:?}", b32);
                let (b32, _) = b32.split_at(s.len().min(b32.len()));
                if b32 != s {
                    break;
                } else if result.is_none() {
                    result = Some((e, i))
                } else {
                    return Err(super::HashPrefixError::Ambiguous(s.to_string()));
                }
            }
        }
        if let Some(result) = result {
            Ok(result)
        } else {
            Err(super::HashPrefixError::NotFound(s.to_string()))
        }
    }

    fn hash_from_prefix_remote<'txn>(
        &'txn self,
        remote: &RemoteRef<Self>,
        s: &str,
    ) -> Result<Hash, super::HashPrefixError<Self::GraphError>> {
        let remote = remote.borrow();
        let h = if let Some(h) = Hash::from_prefix(s) {
            h
        } else {
            return Err(super::HashPrefixError::Parse(s.to_string()));
        };
        let mut result = None;
        debug!("h = {:?}", h);
        for x in self
            .txn
            .iter(&remote.rev, Some((h, None)))
            .map_err(|e| super::HashPrefixError::Txn(e.into()))?
        {
            let (e, _) = x.map_err(|e| super::HashPrefixError::Txn(e.into()))?;
            debug!("{:?}", e);
            if e < h {
                continue;
            } else {
                let b32 = e.to_base32();
                debug!("{:?}", b32);
                let (b32, _) = b32.split_at(s.len().min(b32.len()));
                if b32 != s {
                    break;
                } else if result.is_none() {
                    result = Some(e)
                } else {
                    return Err(super::HashPrefixError::Ambiguous(s.to_string()));
                }
            }
        }
        if let Some(result) = result {
            Ok(result)
        } else {
            Err(super::HashPrefixError::NotFound(s.to_string()))
        }
    }

    fn load_channel(
        &self,
        name: &str,
    ) -> Result<Option<ChannelRef<Self>>, TxnErr<Self::GraphError>> {
        let name = SmallString::from_str(name);
        match self.open_channels.borrow_mut().entry(name.clone()) {
            Entry::Vacant(v) => {
                if let Some(c) = unsafe { self.unsafe_load_channel(name)? } {
                    Ok(Some(
                        v.insert(ChannelRef {
                            r: Rc::new(RefCell::new(c)),
                        })
                        .clone(),
                    ))
                } else {
                    Ok(None)
                }
            }
            Entry::Occupied(occ) => Ok(Some(occ.get().clone())),
        }
    }

    fn load_remote(&self, name: &str) -> Result<Option<RemoteRef<Self>>, TxnErr<Self::GraphError>> {
        let name = SmallString::from_str(name);
        match self.open_remotes.borrow_mut().entry(name.clone()) {
            Entry::Vacant(v) => {
                if let Some(remote) = self.txn.get(
                    &self.remotes,
                    UnsafeSmallStr::from_small_str(name.as_small_str()),
                    None,
                )? {
                    let r = RemoteRef {
                        db: Rc::new(RefCell::new(Remote {
                            remote: remote.0,
                            rev: remote.1,
                            states: remote.2,
                        })),
                        name: name.clone(),
                    };
                    Ok(Some(v.insert(r).clone()))
                } else {
                    return Ok(None);
                }
            }
            Entry::Occupied(occ) => Ok(Some(occ.get().clone())),
        }
    }

    ///
    type Channels = Db<UnsafeSmallStr, (u64, u64, u64, u64, u64, u64)>;
    sanakirja_cursor!(
        channels,
        SmallString,
        (u64, u64, u64, u64, u64, u64),
        if let Some((ref k, ref v)) = pos {
            Some((UnsafeSmallStr::from_small_str(k.as_small_str()), *v))
        } else {
            None
        },
        map(|(k, v): (UnsafeSmallStr, (u64, u64, u64, u64, u64, u64))| (
            unsafe { k.to_small_str().to_owned() },
            v
        ))
    );
    fn iter_channels<'txn>(
        &'txn self,
        start: &str,
    ) -> Result<ChannelIterator<'txn, Self>, TxnErr<Self::GraphError>> {
        let name = SmallString::from_str(start);
        let name = UnsafeSmallStr::from_small_str(name.as_small_str());
        Ok(ChannelIterator {
            cursor: self.txn.set_cursors(&self.channels, Some((name, None)))?.0,
            txn: self,
        })
    }

    type Remotes = Db<UnsafeSmallStr, (u64, u64, u64)>;
    sanakirja_cursor!(
        remotes,
        SmallString,
        (u64, u64, u64),
        if let Some((ref k, ref v)) = pos {
            Some((UnsafeSmallStr::from_small_str(k.as_small_str()), *v))
        } else {
            None
        },
        map(|(k, v): (UnsafeSmallStr, (u64, u64, u64))| (
            unsafe { k.to_small_str().to_owned() },
            v
        ))
    );
    fn iter_remotes<'txn>(
        &'txn self,
        start: &str,
    ) -> Result<RemotesIterator<'txn, Self>, TxnErr<Self::GraphError>> {
        let name = SmallString::from_str(start);
        let name = UnsafeSmallStr::from_small_str(name.as_small_str());
        Ok(RemotesIterator {
            cursor: self.txn.set_cursors(&self.remotes, Some((name, None)))?.0,
            txn: self,
        })
    }

    type Remote = Db<u64, (Hash, Merkle)>;
    type Revremote = Db<Hash, u64>;
    type Remotestates = Db<Merkle, u64>;
    sanakirja_cursor!(remote, u64, (Hash, Merkle));
    sanakirja_rev_cursor!(remote, u64, (Hash, Merkle));

    fn iter_remote<'txn>(
        &'txn self,
        remote: &Self::Remote,
        k: u64,
    ) -> Result<
        super::Cursor<Self, &'txn Self, Self::RemoteCursor, u64, (Hash, Merkle)>,
        TxnErr<Self::GraphError>,
    > {
        self.cursor_remote(remote, Some((k, None)))
    }

    fn iter_rev_remote<'txn>(
        &'txn self,
        remote: &Self::Remote,
        k: Option<u64>,
    ) -> Result<
        super::RevCursor<Self, &'txn Self, Self::RemoteCursor, u64, (Hash, Merkle)>,
        TxnErr<Self::GraphError>,
    > {
        self.rev_cursor_remote(remote, k.map(|k| (k, None)))
    }

    fn get_remote(
        &mut self,
        name: &str,
    ) -> Result<Option<RemoteRef<Self>>, TxnErr<Self::GraphError>> {
        let name = SmallString::from_str(name);
        match self.open_remotes.borrow_mut().entry(name.clone()) {
            Entry::Vacant(v) => {
                if let Some(remote) = self.txn.get(
                    &self.remotes,
                    UnsafeSmallStr::from_small_str(name.as_small_str()),
                    None,
                )? {
                    let r = RemoteRef {
                        db: Rc::new(RefCell::new(Remote {
                            remote: remote.0,
                            rev: remote.1,
                            states: remote.2,
                        })),
                        name: name.clone(),
                    };
                    v.insert(r);
                } else {
                    return Ok(None);
                }
            }
            Entry::Occupied(_) => {}
        }
        Ok(self.open_remotes.borrow().get(&name).cloned())
    }

    fn last_remote(
        &self,
        remote: &Self::Remote,
    ) -> Result<Option<(u64, (Hash, Merkle))>, TxnErr<Self::GraphError>> {
        Ok(self.txn.rev_iter(remote, None)?.next().transpose()?)
    }

    fn get_remote_state(
        &self,
        remote: &Self::Remote,
        n: u64,
    ) -> Result<Option<(u64, (Hash, Merkle))>, TxnErr<Self::GraphError>> {
        for x in self.txn.iter(remote, Some((n, None)))? {
            let (k, m) = x?;
            if k >= n {
                return Ok(Some((k, m)));
            }
        }
        Ok(None)
    }

    fn remote_has_change(
        &self,
        remote: &RemoteRef<Self>,
        hash: Hash,
    ) -> Result<bool, TxnErr<Self::GraphError>> {
        Ok(self.txn.get(&remote.db.borrow().rev, hash, None)?.is_some())
    }
    fn remote_has_state(
        &self,
        remote: &RemoteRef<Self>,
        m: Merkle,
    ) -> Result<bool, TxnErr<Self::GraphError>> {
        Ok(self.txn.get(&remote.db.borrow().states, m, None)?.is_some())
    }
}

impl GraphMutTxnT for MutTxn<()> {
    fn put_graph(
        &mut self,
        graph: &mut Self::Graph,
        k: Vertex<ChangeId>,
        e: Edge,
    ) -> Result<bool, TxnErr<Self::GraphError>> {
        Ok(self.txn.put(&mut self.rng, graph, k, e)?)
    }

    fn del_graph(
        &mut self,
        graph: &mut Self::Graph,
        k: Vertex<ChangeId>,
        e: Option<Edge>,
    ) -> Result<bool, TxnErr<Self::GraphError>> {
        debug!("del_graph {:?} {:?}", k, e);
        Ok(self.txn.del(&mut self.rng, graph, k, e)?)
    }
    sanakirja_put_del!(internal, Hash, ChangeId, GraphError);
    sanakirja_put_del!(external, ChangeId, Hash, GraphError);

    fn split_block(
        &mut self,
        graph: &mut Self::Graph,
        key: Vertex<ChangeId>,
        pos: ChangePosition,
        buf: &mut Vec<Edge>,
    ) -> Result<(), TxnErr<Self::GraphError>> {
        assert!(pos > key.start);
        assert!(pos < key.end);
        let (mut cursor, _) = self.txn.set_cursors(graph, Some((key, None)))?;
        loop {
            match unsafe { ::sanakirja::next::<_, Vertex<ChangeId>, Edge>(&self.txn, &mut cursor) }
            {
                Ok(Some((k, v))) => {
                    if k > key {
                        break;
                    } else if k < key {
                        continue;
                    }
                    buf.push(v)
                }
                Ok(None) => break,
                Err(::sanakirja::CRCError {}) => {
                    return Err(TxnErr(SanakirjaError::PristineCorrupt))
                }
            }
        }
        for chi in buf.drain(..) {
            assert!(chi.introduced_by != ChangeId::ROOT || chi.flag.contains(EdgeFlags::PSEUDO));
            if chi.flag.contains(EdgeFlags::PARENT | EdgeFlags::BLOCK) {
                put_graph_with_rev(
                    self,
                    graph,
                    chi.flag - EdgeFlags::PARENT,
                    Vertex {
                        change: key.change,
                        start: key.start,
                        end: pos,
                    },
                    Vertex {
                        change: key.change,
                        start: pos,
                        end: key.end,
                    },
                    chi.introduced_by,
                )?;
            }

            self.del_graph(graph, key, Some(chi))?;
            self.put_graph(
                graph,
                if chi.flag.contains(EdgeFlags::PARENT) {
                    Vertex {
                        change: key.change,
                        start: key.start,
                        end: pos,
                    }
                } else {
                    Vertex {
                        change: key.change,
                        start: pos,
                        end: key.end,
                    }
                },
                chi,
            )?;
        }
        Ok(())
    }
}

impl ChannelMutTxnT for MutTxn<()> {
    fn graph_mut(c: &mut Self::Channel) -> &mut Self::Graph {
        &mut c.graph
    }
    fn touch_channel(&mut self, channel: &mut Self::Channel, t: Option<u64>) {
        use std::time::SystemTime;
        if let Some(t) = t {
            channel.last_modified = t
        } else if let Ok(duration) = SystemTime::now().duration_since(SystemTime::UNIX_EPOCH) {
            channel.last_modified = duration.as_secs()
        }
    }

    fn put_changes(
        &mut self,
        channel: &mut Self::Channel,
        p: ChangeId,
        t: ApplyTimestamp,
        h: &Hash,
    ) -> Result<Option<Merkle>, TxnErr<Self::GraphError>> {
        if self.get_changeset(&channel.changes, p)?.is_none() {
            channel.apply_counter += 1;
            debug!("put_changes {:?} {:?}", t, p);
            for i in self.txn.iter(&channel.changes, None).unwrap() {
                debug!("changes {:?}", i);
            }
            let m = if let Some(x) = self.txn.rev_iter(&channel.revchanges, None)?.next() {
                (x?.1).1
            } else {
                Merkle::zero()
            };
            let m = m.next(h);
            assert!(self.get_revchangeset(&channel.revchanges, t)?.is_none());
            assert!(self.txn.put(&mut self.rng, &mut channel.changes, p, t)?);
            assert!(self
                .txn
                .put(&mut self.rng, &mut channel.revchanges, t, (p, m))?);
            Ok(Some(m))
        } else {
            Ok(None)
        }
    }

    fn del_changes(
        &mut self,
        channel: &mut Self::Channel,
        p: ChangeId,
        t: ApplyTimestamp,
    ) -> Result<bool, TxnErr<Self::GraphError>> {
        let mut repl = Vec::new();
        for x in self.txn.iter(&channel.revchanges, Some((t, None)))? {
            let (t_, (p, _)) = x?;
            if t_ >= t {
                repl.push((t_, p))
            }
        }
        let mut m = Merkle::zero();
        for x in self.txn.rev_iter(&channel.revchanges, Some((t, None)))? {
            let (t_, (_, m_)) = x?;
            if t_ < t {
                m = m_;
                break;
            }
        }
        for (t_, p) in repl.iter() {
            debug!("del_changes {:?} {:?}", t_, p);
            self.txn
                .del(&mut self.rng, &mut channel.revchanges, *t_, None)?;
            if *t_ > t {
                m = m.next(&self.get_external(*p)?.unwrap());
                self.txn
                    .put(&mut self.rng, &mut channel.revchanges, *t_, (*p, m))?;
            }
        }
        Ok(self
            .txn
            .del(&mut self.rng, &mut channel.changes, p, Some(t))?)
    }
}

impl DepsMutTxnT for MutTxn<()> {
    sanakirja_put_del!(dep, ChangeId, ChangeId, DepsError);
    sanakirja_put_del!(revdep, ChangeId, ChangeId, DepsError);
    sanakirja_put_del!(touched_files, Position<ChangeId>, ChangeId, DepsError);
    sanakirja_put_del!(rev_touched_files, ChangeId, Position<ChangeId>, DepsError);
}

impl TreeMutTxnT for MutTxn<()> {
    sanakirja_put_del!(inodes, Inode, Position<ChangeId>, TreeError);
    sanakirja_put_del!(revinodes, Position<ChangeId>, Inode, TreeError);

    sanakirja_put_del!(
        tree,
        PathId,
        Inode,
        TreeError,
        UnsafePathId::from_fileid(k),
        v
    );
    sanakirja_put_del!(
        revtree,
        Inode,
        PathId,
        TreeError,
        k,
        UnsafePathId::from_fileid(v)
    );

    fn put_partials(
        &mut self,
        k: &str,
        e: Position<ChangeId>,
    ) -> Result<bool, TxnErr<Self::TreeError>> {
        let k = SmallString::from_str(k);
        Ok(self.txn.put(
            &mut self.rng,
            &mut self.partials,
            UnsafeSmallStr::from_small_str(k.as_small_str()),
            e,
        )?)
    }

    fn del_partials(
        &mut self,
        k: &str,
        e: Option<Position<ChangeId>>,
    ) -> Result<bool, TxnErr<Self::TreeError>> {
        let k = SmallString::from_str(k);
        Ok(self.txn.del(
            &mut self.rng,
            &mut self.partials,
            UnsafeSmallStr::from_small_str(k.as_small_str()),
            e,
        )?)
    }
}

impl MutTxnT for MutTxn<()> {
    fn put_remote(
        &mut self,
        remote: &mut RemoteRef<Self>,
        k: u64,
        v: (Hash, Merkle),
    ) -> Result<bool, Self::GraphError> {
        let mut remote = remote.borrow_mut();
        self.txn.put(&mut self.rng, &mut remote.remote, k, v)?;
        self.txn.put(&mut self.rng, &mut remote.states, v.1, k)?;
        Ok(self.txn.put(&mut self.rng, &mut remote.rev, v.0, k)?)
    }

    fn del_remote(
        &mut self,
        remote: &mut RemoteRef<Self>,
        k: u64,
    ) -> Result<bool, Self::GraphError> {
        let mut remote = remote.borrow_mut();
        if let Some((h, m)) = self.txn.get(&remote.remote, k, None)? {
            self.txn.del(&mut self.rng, &mut remote.rev, h, None)?;
            self.txn.del(&mut self.rng, &mut remote.states, m, None)?;
            Ok(self.txn.del(&mut self.rng, &mut remote.remote, k, None)?)
        } else {
            Ok(false)
        }
    }

    fn open_or_create_channel(&mut self, name: &str) -> Result<ChannelRef<Self>, Self::GraphError> {
        let name = small_string::SmallString::from_str(name);
        let mut commit = None;
        let result = match self.open_channels.borrow_mut().entry(name.clone()) {
            Entry::Vacant(v) => {
                let r = if let Some((
                    graph,
                    changes,
                    revchanges,
                    states,
                    apply_counter,
                    last_modified,
                )) = self.txn.get(
                    &self.channels,
                    UnsafeSmallStr::from_small_str(name.as_small_str()),
                    None,
                )? {
                    ChannelRef {
                        r: Rc::new(RefCell::new(Channel {
                            graph,
                            changes,
                            revchanges,
                            states,
                            apply_counter,
                            name: name.clone(),
                            last_modified,
                        })),
                    }
                } else {
                    let br = ChannelRef {
                        r: Rc::new(RefCell::new(Channel {
                            graph: self.txn.create_db()?,
                            changes: self.txn.create_db()?,
                            revchanges: self.txn.create_db()?,
                            states: self.txn.create_db()?,
                            apply_counter: 0,
                            name: name.clone(),
                            last_modified: 0,
                        })),
                    };
                    commit = Some(br.clone());
                    br
                };
                v.insert(r).clone()
            }
            Entry::Occupied(occ) => occ.get().clone(),
        };
        if let Some(commit) = commit {
            self.put_channel(commit)?;
        }
        Ok(result)
    }

    fn fork(
        &mut self,
        channel: &ChannelRef<Self>,
        new_name: &str,
    ) -> Result<ChannelRef<Self>, ForkError<Self::GraphError>> {
        let channel = channel.r.borrow();
        let name = SmallString::from_str(new_name);
        if self
            .txn
            .get(
                &self.channels,
                UnsafeSmallStr::from_small_str(name.as_small_str()),
                None,
            )
            .map_err(|e| ForkError::Txn(e.into()))?
            .is_none()
        {
            let br = ChannelRef {
                r: Rc::new(RefCell::new(Channel {
                    graph: self
                        .txn
                        .fork(&mut self.rng, &channel.graph)
                        .map_err(|e| ForkError::Txn(e.into()))?,
                    changes: self
                        .txn
                        .fork(&mut self.rng, &channel.changes)
                        .map_err(|e| ForkError::Txn(e.into()))?,
                    revchanges: self
                        .txn
                        .fork(&mut self.rng, &channel.revchanges)
                        .map_err(|e| ForkError::Txn(e.into()))?,
                    states: self
                        .txn
                        .fork(&mut self.rng, &channel.states)
                        .map_err(|e| ForkError::Txn(e.into()))?,
                    name: name.clone(),
                    apply_counter: channel.apply_counter,
                    last_modified: channel.last_modified,
                })),
            };
            self.open_channels.borrow_mut().insert(name, br.clone());
            Ok(br)
        } else {
            Err(super::ForkError::ChannelNameExists(new_name.to_string()))
        }
    }

    fn rename_channel(
        &mut self,
        channel: &mut ChannelRef<Self>,
        new_name: &str,
    ) -> Result<(), ForkError<Self::GraphError>> {
        let name = SmallString::from_str(new_name);
        if self
            .txn
            .get(
                &self.channels,
                UnsafeSmallStr::from_small_str(name.as_small_str()),
                None,
            )
            .map_err(|e| ForkError::Txn(e.into()))?
            .is_none()
        {
            let mut dbs_channels: ::sanakirja::Db<UnsafeSmallStr, (u64, u64, u64, u64, u64, u64)> =
                unsafe { std::mem::transmute(self.channels) };
            self.txn
                .del(
                    &mut self.rng,
                    &mut dbs_channels,
                    UnsafeSmallStr::from_small_str(channel.borrow().name.as_small_str()),
                    None,
                )
                .map_err(|e| ForkError::Txn(e.into()))?;
            self.channels = unsafe { std::mem::transmute(dbs_channels) };
            std::mem::drop(
                self.open_channels
                    .borrow_mut()
                    .remove(&channel.borrow().name)
                    .unwrap(),
            );
            std::cell::RefCell::borrow_mut(&std::rc::Rc::get_mut(&mut channel.r).unwrap()).name =
                name.clone();
            self.open_channels
                .borrow_mut()
                .insert(name, channel.clone());
            Ok(())
        } else {
            Err(ForkError::ChannelNameExists(new_name.to_string()))
        }
    }

    fn drop_channel(&mut self, name: &str) -> Result<bool, Self::GraphError> {
        let name = SmallString::from_str(name);
        self.open_channels.borrow_mut().remove(&name);
        debug!("drop_channel {:?}", name);
        let result = self.txn.del(
            &mut self.rng,
            &mut self.channels,
            UnsafeSmallStr::from_small_str(name.as_small_str()),
            None,
        )?;
        debug!("/drop_channel {:?}: {:?}", name, result);
        Ok(result)
    }

    fn open_or_create_remote(&mut self, name: &str) -> Result<RemoteRef<Self>, Self::GraphError> {
        let name = small_string::SmallString::from_str(name);
        let mut commit = None;
        match self.open_remotes.borrow_mut().entry(name.clone()) {
            Entry::Vacant(v) => {
                let r = if let Some(remote) = self.txn.get(
                    &self.remotes,
                    UnsafeSmallStr::from_small_str(name.as_small_str()),
                    None,
                )? {
                    RemoteRef {
                        db: Rc::new(RefCell::new(Remote {
                            remote: remote.0,
                            rev: remote.1,
                            states: remote.2,
                        })),
                        name: name.clone(),
                    }
                } else {
                    let br = RemoteRef {
                        db: Rc::new(RefCell::new(Remote {
                            remote: self.txn.create_db()?,
                            rev: self.txn.create_db()?,
                            states: self.txn.create_db()?,
                        })),
                        name: name.clone(),
                    };
                    commit = Some(br.clone());
                    br
                };
                v.insert(r);
            }
            Entry::Occupied(_) => {}
        }
        if let Some(commit) = commit {
            self.put_remotes(commit)?;
        }
        Ok(self.open_remotes.borrow().get(&name).unwrap().clone())
    }

    fn drop_remote(&mut self, remote: RemoteRef<Self>) -> Result<bool, Self::GraphError> {
        let name = remote.name.clone();
        let r = self.open_remotes.borrow_mut().remove(&name).unwrap();
        std::mem::drop(remote);
        assert_eq!(Rc::strong_count(&r.db), 1);
        Ok(self.txn.del(
            &mut self.rng,
            &mut self.remotes,
            UnsafeSmallStr::from_small_str(name.as_small_str()),
            None,
        )?)
    }

    fn drop_named_remote(&mut self, name: &str) -> Result<bool, Self::GraphError> {
        let name = SmallString::from_str(name);
        if let Some(r) = self.open_remotes.borrow_mut().remove(&name) {
            assert_eq!(Rc::strong_count(&r.db), 1);
        }
        Ok(self.txn.del(
            &mut self.rng,
            &mut self.remotes,
            UnsafeSmallStr::from_small_str(name.as_small_str()),
            None,
        )?)
    }

    fn commit(mut self) -> Result<(), Self::GraphError> {
        use std::ops::DerefMut;
        {
            let open_channels =
                std::mem::replace(self.open_channels.borrow_mut().deref_mut(), HashMap::new());
            for (name, channel) in open_channels {
                debug!("commit_channel {:?}", name);
                self.commit_channel(channel)?
            }
        }
        {
            let open_remotes =
                std::mem::replace(self.open_remotes.borrow_mut().deref_mut(), HashMap::new());
            for (_, remote) in open_remotes {
                self.commit_remote(remote)?
            }
        }
        self.txn.set_root(Root::Tree as usize, self.tree);
        self.txn.set_root(Root::RevTree as usize, self.revtree);
        self.txn.set_root(Root::Inodes as usize, self.inodes);
        self.txn.set_root(Root::RevInodes as usize, self.revinodes);
        self.txn.set_root(Root::Internal as usize, self.internal);
        self.txn.set_root(Root::External as usize, self.external);
        self.txn.set_root(Root::RevDep as usize, self.revdep);
        self.txn.set_root(Root::Channels as usize, self.channels);
        self.txn.set_root(Root::Remotes as usize, self.remotes);
        self.txn
            .set_root(Root::TouchedFiles as usize, self.touched_files);
        self.txn.set_root(Root::Dep as usize, self.dep);
        self.txn
            .set_root(Root::RevTouchedFiles as usize, self.rev_touched_files);
        self.txn.set_root(Root::Partials as usize, self.partials);

        self.txn.commit()?;
        Ok(())
    }
}

impl Txn {
    pub fn load_const_channel(&self, name: &str) -> Result<Option<Channel>, SanakirjaError> {
        let name = SmallString::from_str(name);
        if let Some((channel, changes, revchanges, states, counter, last_modified)) = self.txn.get(
            &self.channels,
            UnsafeSmallStr::from_small_str(name.as_small_str()),
            None,
        )? {
            Ok(Some(Channel {
                graph: channel,
                changes,
                revchanges,
                states,
                apply_counter: counter,
                name,
                last_modified,
            }))
        } else {
            Ok(None)
        }
    }
}

impl<T> MutTxn<T> {
    fn put_channel(&mut self, channel: ChannelRef<Self>) -> Result<(), SanakirjaError> {
        debug!("Commit_channel.");
        let channel = channel.r.try_borrow()?;
        // Since we are replacing the value, we don't want to
        // decrement its reference counter (which del would do), hence
        // the transmute.
        //
        // This would normally be wrong. The only reason it works is
        // because we know that dbs_channels has never been forked
        // from another database, hence all the reference counts to
        // its elements are 1 (and therefore represented as "not
        // referenced" in Sanakirja).
        let mut dbs_channels: ::sanakirja::Db<UnsafeSmallStr, (u64, u64, u64, u64, u64, u64)> =
            unsafe { std::mem::transmute(self.channels) };

        debug!("Commit_channel, dbs_channels = {:?}", dbs_channels);
        self.txn.del(
            &mut self.rng,
            &mut dbs_channels,
            UnsafeSmallStr::from_small_str(channel.name.as_small_str()),
            None,
        )?;
        debug!("Commit_channel, dbs_channels = {:?}", dbs_channels);
        self.channels = unsafe { std::mem::transmute(dbs_channels) };
        self.txn.put(
            &mut self.rng,
            &mut self.channels,
            UnsafeSmallStr::from_small_str(channel.name.as_small_str()),
            (
                channel.graph,
                channel.changes,
                channel.revchanges,
                channel.states,
                channel.apply_counter,
                channel.last_modified,
            ),
        )?;
        debug!("Commit_channel, self.dbs.channels = {:?}", self.channels);
        Ok(())
    }

    fn commit_channel(&mut self, channel: ChannelRef<Self>) -> Result<(), SanakirjaError> {
        debug!("Commit_channel. This is not too safe.");
        std::mem::drop(
            self.open_channels
                .borrow_mut()
                .remove(&channel.r.borrow().name),
        );
        self.put_channel(channel)
    }

    fn put_remotes(&mut self, remote: RemoteRef<Self>) -> Result<(), SanakirjaError> {
        let mut dbs_remotes: ::sanakirja::Db<UnsafeSmallStr, (u64, u64, u64)> =
            unsafe { std::mem::transmute(self.remotes) };

        debug!("Commit_remote, dbs_remotes = {:?}", dbs_remotes);
        self.txn.del(
            &mut self.rng,
            &mut dbs_remotes,
            UnsafeSmallStr::from_small_str(remote.name.as_small_str()),
            None,
        )?;
        debug!("Commit_remote, dbs_remotes = {:?}", dbs_remotes);
        self.remotes = unsafe { std::mem::transmute(dbs_remotes) };
        let r = remote.db.borrow();
        self.txn.put(
            &mut self.rng,
            &mut self.remotes,
            UnsafeSmallStr::from_small_str(remote.name.as_small_str()),
            (r.remote, r.rev, r.states),
        )?;
        debug!("Commit_remote, self.dbs.remotes = {:?}", self.remotes);
        Ok(())
    }

    fn commit_remote(&mut self, remote: RemoteRef<Self>) -> Result<(), SanakirjaError> {
        std::mem::drop(self.open_remotes.borrow_mut().remove(&remote.name));
        // assert_eq!(Rc::strong_count(&remote.db), 1);
        self.put_remotes(remote)
    }
}

const CHANGE_ID_SIZE: usize = 8;
impl Representable for ChangeId {
    fn alignment() -> Alignment {
        Alignment::B8
    }
    fn onpage_size(&self) -> u16 {
        CHANGE_ID_SIZE as u16
    }
    unsafe fn write_value(&self, p: *mut u8) {
        LittleEndian::write_u64(std::slice::from_raw_parts_mut(p, 8), self.0)
    }
    unsafe fn read_value(p: *const u8) -> Self {
        ChangeId(LittleEndian::read_u64(std::slice::from_raw_parts(p, 8)))
    }
    unsafe fn cmp_value<T>(&self, _: &T, x: Self) -> std::cmp::Ordering {
        self.0.cmp(&x.0)
    }
    type PageOffsets = std::iter::Empty<u64>;
    fn page_offsets(&self) -> Self::PageOffsets {
        std::iter::empty()
    }
}

const VERTEX_SIZE: usize = CHANGE_ID_SIZE + 16;

impl Representable for Vertex<ChangeId> {
    fn alignment() -> Alignment {
        Alignment::B1
    }
    fn onpage_size(&self) -> u16 {
        VERTEX_SIZE as u16
    }
    unsafe fn write_value(&self, p: *mut u8) {
        let p = std::slice::from_raw_parts_mut(p, VERTEX_SIZE);
        LittleEndian::write_u64(p, self.change.0);
        LittleEndian::write_u64(&mut p[CHANGE_ID_SIZE..], self.start.0);
        LittleEndian::write_u64(&mut p[CHANGE_ID_SIZE + 8..], self.end.0);
    }
    unsafe fn read_value(p: *const u8) -> Self {
        let p = std::slice::from_raw_parts(p, VERTEX_SIZE);
        let change = LittleEndian::read_u64(p);
        let start = LittleEndian::read_u64(&p[CHANGE_ID_SIZE..]);
        let end = LittleEndian::read_u64(&p[CHANGE_ID_SIZE + 8..]);
        Vertex {
            change: ChangeId(change),
            start: ChangePosition(start),
            end: ChangePosition(end),
        }
    }
    unsafe fn cmp_value<T>(&self, _: &T, x: Self) -> std::cmp::Ordering {
        self.cmp(&x)
    }
    type PageOffsets = std::iter::Empty<u64>;
    fn page_offsets(&self) -> Self::PageOffsets {
        std::iter::empty()
    }
}

impl Representable for Position<ChangeId> {
    fn alignment() -> Alignment {
        Alignment::B1
    }
    fn onpage_size(&self) -> u16 {
        (CHANGE_ID_SIZE + 8) as u16
    }
    unsafe fn write_value(&self, p: *mut u8) {
        let p = std::slice::from_raw_parts_mut(p, CHANGE_ID_SIZE + 8);
        LittleEndian::write_u64(p, self.change.0);
        LittleEndian::write_u64(&mut p[CHANGE_ID_SIZE..], self.pos.0);
    }
    unsafe fn read_value(p: *const u8) -> Self {
        let p = std::slice::from_raw_parts(p, CHANGE_ID_SIZE + 8);
        let change = LittleEndian::read_u64(p);
        let pos = LittleEndian::read_u64(&p[CHANGE_ID_SIZE..]);
        Position {
            change: ChangeId(change),
            pos: ChangePosition(pos),
        }
    }
    unsafe fn cmp_value<T>(&self, _: &T, x: Self) -> std::cmp::Ordering {
        self.cmp(&x)
    }
    type PageOffsets = std::iter::Empty<u64>;
    fn page_offsets(&self) -> Self::PageOffsets {
        std::iter::empty()
    }
}

impl Representable for Edge {
    fn alignment() -> Alignment {
        Alignment::B1
    }
    fn onpage_size(&self) -> u16 {
        25
    }
    unsafe fn write_value(&self, p: *mut u8) {
        let s = std::slice::from_raw_parts_mut(p, 25);
        s[0] = (*self).flag.bits();
        LittleEndian::write_u64(&mut s[1..], (*self).dest.change.0);
        LittleEndian::write_u64(&mut s[9..], (*self).dest.pos.0);
        LittleEndian::write_u64(&mut s[17..], (*self).introduced_by.0);
    }
    unsafe fn read_value(p: *const u8) -> Self {
        let s = std::slice::from_raw_parts(p, 25);
        Edge {
            flag: if let Some(b) = EdgeFlags::from_bits(s[0]) {
                b
            } else {
                panic!("read_value, edge = {:?}", s);
            },
            dest: Position {
                change: ChangeId(LittleEndian::read_u64(&s[1..])),
                pos: ChangePosition(LittleEndian::read_u64(&s[9..])),
            },
            introduced_by: ChangeId(LittleEndian::read_u64(&s[17..])),
        }
    }
    unsafe fn cmp_value<T>(&self, _: &T, x: Self) -> std::cmp::Ordering {
        let a: &Edge = self;
        let b: &Edge = &x;
        a.cmp(b)
    }
    type PageOffsets = std::iter::Empty<u64>;
    fn page_offsets(&self) -> Self::PageOffsets {
        std::iter::empty()
    }
}

/// An internal "unsafe" version of a [`pristine::PathId`], used to
/// circumvent the absence of associated type constructors in Rust
/// (else this would be borrow on a table).
#[derive(Clone, Copy, Debug)]
pub struct UnsafePathId {
    parent_inode: Inode,
    basename: UnsafeSmallStr,
}
impl UnsafePathId {
    pub fn from_fileid(f: PathId) -> UnsafePathId {
        UnsafePathId {
            parent_inode: f.parent_inode,
            basename: UnsafeSmallStr::from_small_str(f.basename),
        }
    }
    pub unsafe fn to_fileid<'a>(&self) -> PathId<'a> {
        PathId {
            parent_inode: self.parent_inode,
            basename: self.basename.to_small_str(),
        }
    }
}

impl Representable for UnsafePathId {
    fn alignment() -> Alignment {
        Alignment::B1
    }
    fn onpage_size(&self) -> u16 {
        INODE_SIZE + self.basename.onpage_size()
    }
    unsafe fn write_value(&self, p: *mut u8) {
        self.parent_inode.write_value(p);
        self.basename.write_value(p.offset(INODE_SIZE as isize));
    }
    unsafe fn read_value(p: *const u8) -> Self {
        UnsafePathId {
            parent_inode: Inode::read_value(p),
            basename: UnsafeSmallStr::read_value(p.offset(INODE_SIZE as isize)),
        }
    }
    unsafe fn cmp_value<T>(&self, _: &T, x: Self) -> std::cmp::Ordering {
        let a: PathId = self.to_fileid();
        let b: PathId = x.to_fileid();
        a.cmp(&b)
    }
    type PageOffsets = std::iter::Empty<u64>;
    fn page_offsets(&self) -> Self::PageOffsets {
        std::iter::empty()
    }
}

const INODE_SIZE: u16 = 8;
impl Representable for Inode {
    fn alignment() -> Alignment {
        Alignment::B8
    }
    fn onpage_size(&self) -> u16 {
        INODE_SIZE
    }
    unsafe fn write_value(&self, p: *mut u8) {
        LittleEndian::write_u64(std::slice::from_raw_parts_mut(p, 8), self.0)
    }
    unsafe fn read_value(p: *const u8) -> Self {
        Inode(LittleEndian::read_u64(std::slice::from_raw_parts(p, 8)))
    }
    unsafe fn cmp_value<T>(&self, _: &T, x: Self) -> std::cmp::Ordering {
        self.0.cmp(&x.0)
    }
    type PageOffsets = std::iter::Empty<u64>;
    fn page_offsets(&self) -> Self::PageOffsets {
        std::iter::empty()
    }
}

impl Representable for Hash {
    fn alignment() -> Alignment {
        Alignment::B1
    }

    fn onpage_size(&self) -> u16 {
        1 + (match *self {
            Hash::Blake3(_) => 32,
            Hash::None => 0,
        })
    }
    unsafe fn write_value(&self, p: *mut u8) {
        match *self {
            Hash::Blake3(q) => {
                *p = HashAlgorithm::Blake3 as u8;
                std::ptr::copy(q.as_ptr(), p.offset(1), 32)
            }
            Hash::None => *p = HashAlgorithm::None as u8,
        }
    }
    unsafe fn read_value(p: *const u8) -> Self {
        assert!(*p <= HashAlgorithm::Blake3 as u8);
        match std::mem::transmute(*p) {
            HashAlgorithm::Blake3 => {
                let mut h = [0; BLAKE3_BYTES];
                std::ptr::copy(p.offset(1), h.as_mut_ptr(), BLAKE3_BYTES);
                Hash::Blake3(h)
            }
            HashAlgorithm::None => Hash::None,
        }
    }
    unsafe fn cmp_value<T>(&self, _: &T, x: Self) -> std::cmp::Ordering {
        self.cmp(&x)
    }
    type PageOffsets = std::iter::Empty<u64>;
    fn page_offsets(&self) -> Self::PageOffsets {
        std::iter::empty()
    }
}

impl Representable for Merkle {
    fn alignment() -> Alignment {
        Alignment::B1
    }

    fn onpage_size(&self) -> u16 {
        33
    }
    unsafe fn write_value(&self, p: *mut u8) {
        match *self {
            Merkle::Ed25519(q) => {
                *p = MerkleAlgorithm::Ed25519 as u8;
                assert_eq!(*p, 1);
                let q = q.compress();
                let q = q.as_bytes();
                std::ptr::copy(q.as_ptr(), p.offset(1), 32);
            }
        }
    }
    unsafe fn read_value(p: *const u8) -> Self {
        assert_eq!(*p, MerkleAlgorithm::Ed25519 as u8);
        let slice = std::slice::from_raw_parts(p.offset(1), 32);
        Merkle::Ed25519(
            curve25519_dalek::edwards::CompressedEdwardsY::from_slice(slice)
                .decompress()
                .unwrap(),
        )
    }
    unsafe fn cmp_value<T>(&self, _: &T, x: Self) -> std::cmp::Ordering {
        self.to_bytes().cmp(&x.to_bytes())
    }
    type PageOffsets = std::iter::Empty<u64>;
    fn page_offsets(&self) -> Self::PageOffsets {
        std::iter::empty()
    }
}
