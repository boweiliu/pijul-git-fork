#[macro_use]
extern crate log;
#[macro_use]
extern crate serde_derive;
#[macro_use]
extern crate bitflags;
#[macro_use]
extern crate pijul_macros;
#[macro_use]
extern crate thiserror;
#[macro_use]
extern crate lazy_static;

pub mod alive;
mod apply;
pub mod change;
pub mod changestore;
mod diff;
mod find_alive;
pub mod fs;
mod missing_context;
pub mod output;
pub mod path;
pub mod pristine;
pub mod record;
pub mod small_string;
mod unrecord;
mod vector2;
pub mod vertex_buffer;
pub mod working_copy;

#[cfg(test)]
mod tests;

pub const DOT_DIR: &str = ".pijul";

#[derive(Debug, Error)]
pub enum Error {
    #[error("File {:?} already in repository", path)]
    FileAlreadyInRepo { path: String },
    #[error("File {:?} not in repository", path)]
    FileNotInRepo { path: String },
    #[error("Cannot record from unrecorded prefix {:?}", path)]
    UnrecordedPath { path: String },
    #[error("File {:?} not found", path)]
    FileNotFound { path: String },
    #[error("Change not on channel {:?}", change_id)]
    ChangeNotOnChannel { change_id: pristine::ChangeId },
    #[error("Change is depended upon {:?}", change_id)]
    ChangeIsDependedUpon { change_id: pristine::ChangeId },
    #[error("Change not found: {:?}", hash)]
    ChangeNotFound { hash: String },
    #[error("State not found: {:?}", state)]
    StateNotFound { state: pristine::Merkle },
    #[error("Change hash mismatch: {:?} != {:?}", claimed, computed)]
    ChangeHashMismatch {
        claimed: pristine::Hash,
        computed: pristine::Hash,
    },
    #[error("Contents hash mismatch: {:?} != {:?}", claimed, computed)]
    ContentsHashMismatch {
        claimed: pristine::Hash,
        computed: pristine::Hash,
    },
    #[error("Change already on channel: {:?}", hash)]
    ChangeAlreadyOnChannel { hash: pristine::Hash },
    #[error("Dependency missing: {:?}", hash)]
    DependencyMissing { hash: pristine::Hash },
    #[error("Channel name already taken: {:?}", name)]
    ChannelNameExists { name: String },
    #[error("Parse error: {:?}", s)]
    ParseError { s: String },
    #[error("Verify error, public key = {:?}", pk)]
    VerifyError { pk: String },
    #[error("Ambiguous hash prefix: {}", prefix)]
    AmbiguousHashPrefix { prefix: String },
    #[error("Inconsistent references in change")]
    InconsistentChange,
    #[error("Missing change contents: {}", hash)]
    MissingContents { hash: String },
    #[error("Wrong block: {:?}", block)]
    WrongBlock {
        block: pristine::Position<pristine::ChangeId>,
    },
    #[error("Pristine corrupt")]
    PristineCorrupt,
    #[error("Change version mismatch, please run `pijul upgrade`.")]
    VersionMismatch,
    #[error("The repository is locked by another process.")]
    PristineLocked,
}

pub use crate::apply::Workspace as ApplyWorkspace;
pub use crate::apply::{ApplyError, LocalApplyError};
pub use crate::fs::{FsError, WorkingCopyIterator};
pub use crate::output::{Archive, Conflict};
pub use crate::pristine::{
    Base32, ChangeId, ChannelRef, ChannelTxnT, DepsTxnT, EdgeFlags, GraphTxnT, Hash, Inode, Merkle,
    MutTxnT, OwnedPathId, RemoteRef, TreeTxnT, TxnT, Vertex,
};
pub use crate::record::Builder as RecordBuilder;
pub use crate::record::{Algorithm, InodeUpdate};
use std::collections::HashMap;

impl MutTxnTExt for pristine::sanakirja::MutTxn<()> {}
impl TxnTExt for pristine::sanakirja::MutTxn<()> {}
impl TxnTExt for pristine::sanakirja::Txn {}

pub trait MutTxnTExt: pristine::MutTxnT {
    fn apply_change_ws<C: changestore::ChangeStore>(
        &mut self,
        changes: &C,
        channel: &mut pristine::ChannelRef<Self>,
        hash: crate::pristine::Hash,
        workspace: &mut ApplyWorkspace,
    ) -> Result<(u64, pristine::Merkle), crate::apply::ApplyError<C::Error, Self::GraphError>> {
        crate::apply::apply_change_ws(changes, self, channel, hash, workspace)
    }

    fn apply_change_rec_ws<C: changestore::ChangeStore>(
        &mut self,
        changes: &C,
        channel: &mut pristine::ChannelRef<Self>,
        hash: crate::pristine::Hash,
        workspace: &mut ApplyWorkspace,
    ) -> Result<(), crate::apply::ApplyError<C::Error, Self::GraphError>> {
        crate::apply::apply_change_rec_ws(changes, self, channel, hash, workspace, false)
    }

    fn apply_change<C: changestore::ChangeStore>(
        &mut self,
        changes: &C,
        channel: &mut pristine::ChannelRef<Self>,
        hash: pristine::Hash,
    ) -> Result<(u64, pristine::Merkle), crate::apply::ApplyError<C::Error, Self::GraphError>> {
        crate::apply::apply_change(changes, self, channel, hash)
    }

    fn apply_change_rec<C: changestore::ChangeStore>(
        &mut self,
        changes: &C,
        channel: &mut pristine::ChannelRef<Self>,
        hash: pristine::Hash,
    ) -> Result<(), crate::apply::ApplyError<C::Error, Self::GraphError>> {
        crate::apply::apply_change_rec(changes, self, channel, hash, false)
    }

    fn apply_deps_rec<C: changestore::ChangeStore>(
        &mut self,
        changes: &C,
        channel: &mut pristine::ChannelRef<Self>,
        hash: pristine::Hash,
    ) -> Result<(), crate::apply::ApplyError<C::Error, Self::GraphError>> {
        crate::apply::apply_change_rec(changes, self, channel, hash, true)
    }

    fn apply_local_change_ws(
        &mut self,
        channel: &mut pristine::ChannelRef<Self>,
        change: &change::Change,
        hash: pristine::Hash,
        inode_updates: &HashMap<usize, InodeUpdate>,
        workspace: &mut ApplyWorkspace,
    ) -> Result<(u64, pristine::Merkle), crate::apply::LocalApplyError<Self::GraphError>> {
        crate::apply::apply_local_change_ws(self, channel, change, hash, inode_updates, workspace)
    }

    fn apply_local_change(
        &mut self,
        channel: &mut crate::pristine::ChannelRef<Self>,
        change: &crate::change::Change,
        hash: pristine::Hash,
        inode_updates: &HashMap<usize, InodeUpdate>,
    ) -> Result<(u64, pristine::Merkle), crate::apply::LocalApplyError<Self::GraphError>> {
        crate::apply::apply_local_change(self, channel, change, hash, inode_updates)
    }

    fn record<W: crate::working_copy::WorkingCopy, C: crate::changestore::ChangeStore>(
        &mut self,
        builder: &mut RecordBuilder,
        diff_algorithm: Algorithm,
        channel: &mut pristine::ChannelRef<Self>,
        working_copy: &mut W,
        changes: &C,
        prefix: &str,
    ) -> Result<(), crate::record::RecordError<C::Error, W::Error, Self::GraphError>>
    where
        <W as crate::working_copy::WorkingCopy>::Error: 'static,
    {
        builder.record(
            self,
            diff_algorithm,
            &mut channel.borrow_mut(),
            working_copy,
            changes,
            prefix,
        )
    }

    fn record_all<W: crate::working_copy::WorkingCopy, C: crate::changestore::ChangeStore>(
        &mut self,
        diff_algorithm: Algorithm,
        channel: &mut pristine::ChannelRef<Self>,
        working_copy: &mut W,
        changes: &C,
        prefix: &str,
    ) -> Result<record::Recorded, crate::record::RecordError<C::Error, W::Error, Self::GraphError>>
    where
        <W as crate::working_copy::WorkingCopy>::Error: 'static,
    {
        let mut builder = crate::record::Builder::new();
        builder.record(
            self,
            diff_algorithm,
            &mut channel.borrow_mut(),
            working_copy,
            changes,
            prefix,
        )?;
        Ok(builder.finish())
    }

    fn apply_recorded<C: changestore::ChangeStore>(
        &mut self,
        channel: &mut pristine::ChannelRef<Self>,
        recorded: record::Recorded,
        changestore: &C,
    ) -> Result<pristine::Hash, crate::apply::ApplyError<C::Error, Self::GraphError>> {
        let contents_hash = {
            let mut hasher = pristine::Hasher::default();
            hasher.update(&recorded.contents);
            hasher.finish()
        };
        let change = change::LocalChange {
            offsets: change::Offsets::default(),
            hashed: change::Hashed {
                version: change::VERSION,
                contents_hash,
                changes: recorded
                    .actions
                    .into_iter()
                    .map(|rec| rec.globalize(self).unwrap())
                    .collect(),
                metadata: Vec::new(),
                dependencies: Vec::new(),
                extra_known: Vec::new(),
                header: change::ChangeHeader::default(),
            },
            unhashed: None,
            contents: recorded.contents,
        };
        let hash = changestore
            .save_change(&change)
            .map_err(apply::ApplyError::Changestore)?;
        apply::apply_local_change(self, channel, &change, hash, &recorded.updatables)?;
        Ok(hash)
    }

    fn unrecord<C: changestore::ChangeStore>(
        &mut self,
        changes: &C,
        channel: &mut pristine::ChannelRef<Self>,
        hash: &pristine::Hash,
    ) -> Result<bool, unrecord::UnrecordError<C::Error, Self::GraphError>> {
        unrecord::unrecord(self, channel, changes, hash)
    }

    fn output_repository_no_pending<R: working_copy::WorkingCopy, C: changestore::ChangeStore>(
        &mut self,
        repo: &mut R,
        changes: &C,
        channel: &mut pristine::ChannelRef<Self>,
        prefix: &str,
        output_name_conflicts: bool,
        if_modified_since: Option<std::time::SystemTime>,
    ) -> Result<Vec<output::Conflict>, output::OutputError<C::Error, Self::GraphError, R::Error>>
    {
        output::output_repository_no_pending(
            repo,
            changes,
            self,
            channel,
            prefix,
            output_name_conflicts,
            if_modified_since,
        )
    }

    /// Register a file in the working copy, where the file is given by
    /// its path from the root of the repository, where the components of
    /// the path are separated by `/` (example path: `a/b/c`).
    fn add_file(&mut self, path: &str) -> Result<(), fs::FsError<Self::GraphError>> {
        fs::add_inode(self, None, path, false)
    }

    /// Register a directory in the working copy, where the directory is
    /// given by its path from the root of the repository, where the
    /// components of the path are separated by `/` (example path:
    /// `a/b/c`).
    fn add_dir(&mut self, path: &str) -> Result<(), fs::FsError<Self::GraphError>> {
        fs::add_inode(self, None, path, true)
    }

    /// Register a file or directory in the working copy, given by its
    /// path from the root of the repository, where the components of the
    /// path are separated by `/` (example path: `a/b/c`).
    fn add(&mut self, path: &str, is_dir: bool) -> Result<(), fs::FsError<Self::GraphError>> {
        fs::add_inode(self, None, path, is_dir)
    }

    fn move_file(&mut self, a: &str, b: &str) -> Result<(), fs::FsError<Self::GraphError>> {
        fs::move_file(self, a, b)
    }

    fn remove_file(&mut self, a: &str) -> Result<(), fs::FsError<Self::GraphError>> {
        fs::remove_file(self, a)
    }

    #[cfg(feature = "dump")]
    fn channel_from_dump<'a>(
        &'a mut self,
        name: &str,
    ) -> Result<
        pristine::channel_dump::ChannelFromDump<'a, Self>,
        pristine::channel_dump::ChannelDumpError<Self::GraphError>,
    > {
        use pristine::channel_dump::*;
        if self.load_channel(name)?.is_none() {
            let channel = pristine::MutTxnT::open_or_create_channel(self, name)
                .map_err(ChannelDumpError::Txn)?;
            Ok(ChannelFromDump::new(self, channel))
        } else {
            Err(ChannelDumpError::ChannelNameExists(name.to_string()))
        }
    }

    fn archive_with_state<P: changestore::ChangeStore, A: Archive>(
        &mut self,
        changes: &P,
        channel: &mut pristine::ChannelRef<Self>,
        state: pristine::Merkle,
        extra: &[pristine::Hash],
        arch: &mut A,
    ) -> Result<Vec<output::Conflict>, output::ArchiveError<P::Error, Self::GraphError, A::Error>>
    {
        self.archive_prefix_with_state(
            changes,
            channel,
            state,
            extra,
            &mut std::iter::empty(),
            arch,
        )
    }

    /// Warning: this method unrecords changes until finding the
    /// state. If this is not wanted, please fork the channel before
    /// calling.
    fn archive_prefix_with_state<
        'a,
        P: changestore::ChangeStore,
        A: Archive,
        I: Iterator<Item = &'a str>,
    >(
        &mut self,
        changes: &P,
        channel: &mut pristine::ChannelRef<Self>,
        state: pristine::Merkle,
        extra: &[pristine::Hash],
        prefix: &mut I,
        arch: &mut A,
    ) -> Result<Vec<output::Conflict>, output::ArchiveError<P::Error, Self::GraphError, A::Error>>
    {
        let mut unrecord = Vec::new();
        let mut found = false;
        for x in pristine::changeid_rev_log(self, &channel.borrow(), None)? {
            let (_, (h, m)) = x?;
            if m == state {
                found = true;
                break;
            } else {
                unrecord.push(h)
            }
        }
        debug!("unrecord = {:?}", unrecord);
        if found {
            for h in unrecord.drain(..) {
                let h = self.get_external(h)?.unwrap();
                self.unrecord(changes, channel, &h)?;
            }
            for app in extra.iter() {
                self.apply_change_rec(changes, channel, *app)?
            }
            output::archive(changes, self, channel, prefix, arch)
        } else {
            Err(output::ArchiveError::StateNotFound { state })
        }
    }
}

pub trait TxnTExt: pristine::TxnT {
    fn is_directory(&self, inode: pristine::Inode) -> Result<bool, Self::TreeError> {
        fs::is_directory(self, inode).map_err(|e| e.0)
    }

    fn is_tracked(&self, path: &str) -> Result<bool, Self::TreeError> {
        fs::is_tracked(self, path).map_err(|e| e.0)
    }

    fn iter_working_copy(&self) -> WorkingCopyIterator<Self> {
        fs::iter_working_copy(self, pristine::Inode::ROOT)
    }

    fn has_change(
        &self,
        channel: &pristine::ChannelRef<Self>,
        hash: pristine::Hash,
    ) -> Result<Option<u64>, Self::GraphError> {
        if let Some(cid) = pristine::GraphTxnT::get_internal(self, hash).map_err(|e| e.0)? {
            self.get_changeset(self.changes(&channel.borrow()), cid)
                .map_err(|e| e.0)
        } else {
            Ok(None)
        }
    }

    fn is_alive(
        &self,
        channel: &Self::Channel,
        a: pristine::Vertex<pristine::ChangeId>,
    ) -> Result<bool, Self::GraphError> {
        pristine::is_alive(self, self.graph(channel), a).map_err(|e| e.0)
    }

    fn current_state(&self, channel: &Self::Channel) -> Result<pristine::Merkle, Self::GraphError> {
        pristine::current_state(self, channel).map_err(|e| e.0)
    }

    fn log<'channel, 'txn>(
        &'txn self,
        channel: &'channel Self::Channel,
        from: u64,
    ) -> Result<Log<'txn, Self>, Self::GraphError> {
        Ok(Log {
            txn: self,
            iter: pristine::changeid_log(self, channel, from).map_err(|e| e.0)?,
        })
    }

    fn log_for_path<'channel, 'txn>(
        &'txn self,
        channel: &'channel Self::Channel,
        pos: pristine::Position<pristine::ChangeId>,
        from: u64,
    ) -> Result<pristine::PathChangeset<'channel, 'txn, Self>, Self::GraphError> {
        pristine::log_for_path(self, channel, pos, from).map_err(|e| e.0)
    }

    fn rev_log_for_path<'channel, 'txn>(
        &'txn self,
        channel: &'channel Self::Channel,
        pos: pristine::Position<pristine::ChangeId>,
        from: u64,
    ) -> Result<pristine::RevPathChangeset<'channel, 'txn, Self>, Self::DepsError> {
        pristine::rev_log_for_path(self, channel, pos, from).map_err(|e| e.0)
    }

    fn reverse_log<'channel, 'txn>(
        &'txn self,
        channel: &'channel Self::Channel,
        from: Option<u64>,
    ) -> Result<RevLog<'txn, Self>, Self::GraphError> {
        Ok(RevLog {
            txn: self,
            iter: pristine::changeid_rev_log(self, channel, from).map_err(|e| e.0)?,
        })
    }

    fn changeid_reverse_log<'txn>(
        &'txn self,
        channel: &Self::Channel,
        from: Option<u64>,
    ) -> Result<
        pristine::RevCursor<
            Self,
            &'txn Self,
            Self::RevchangesetCursor,
            u64,
            (pristine::ChangeId, pristine::Merkle),
        >,
        Self::GraphError,
    > {
        pristine::changeid_rev_log(self, channel, from).map_err(|e| e.0)
    }

    fn get_changes(
        &self,
        channel: &pristine::ChannelRef<Self>,
        n: u64,
    ) -> Result<Option<(pristine::Hash, pristine::Merkle)>, Self::GraphError> {
        if let Some((h, m)) = self
            .get_revchangeset(self.rev_changes(&channel.borrow()), n)
            .map_err(|e| e.0)?
        {
            Ok(Some((self.get_external(h).map_err(|e| e.0)?.unwrap(), m)))
        } else {
            Ok(None)
        }
    }

    fn get_revchanges(
        &self,
        channel: &pristine::ChannelRef<Self>,
        h: pristine::Hash,
    ) -> Result<Option<u64>, Self::GraphError> {
        if let Some(h) = pristine::GraphTxnT::get_internal(self, h).map_err(|e| e.0)? {
            self.get_changeset(self.changes(&channel.borrow()), h)
                .map_err(|e| e.0)
        } else {
            Ok(None)
        }
    }

    fn touched_files(&self, h: pristine::Hash) -> Result<Option<Touched<Self>>, Self::DepsError> {
        if let Some(id) = pristine::GraphTxnT::get_internal(self, h).map_err(|e| e.0)? {
            Ok(Some(Touched {
                txn: self,
                iter: self.iter_rev_touched_files(id, None).map_err(|e| e.0)?,
                id,
            }))
        } else {
            Ok(None)
        }
    }

    fn find_oldest_path<C: changestore::ChangeStore>(
        &self,
        changes: &C,
        channel: &pristine::ChannelRef<Self>,
        position: pristine::Position<pristine::Hash>,
    ) -> Result<(String, bool), output::FileError<C::Error, Self::GraphError>> {
        let position = pristine::Position {
            change: pristine::GraphTxnT::get_internal(self, position.change)?.unwrap(),
            pos: position.pos,
        };
        fs::find_path(changes, self, &channel.borrow(), false, position)
    }

    fn find_youngest_path<C: changestore::ChangeStore>(
        &self,
        changes: &C,
        channel: &pristine::ChannelRef<Self>,
        position: pristine::Position<pristine::Hash>,
    ) -> Result<(String, bool), output::FileError<C::Error, Self::GraphError>> {
        let position = pristine::Position {
            change: pristine::GraphTxnT::get_internal(self, position.change)?.unwrap(),
            pos: position.pos,
        };
        fs::find_path(changes, self, &channel.borrow(), true, position)
    }

    fn follow_oldest_path<C: changestore::ChangeStore>(
        &self,
        changes: &C,
        channel: &pristine::ChannelRef<Self>,
        path: &str,
    ) -> Result<
        (pristine::Position<pristine::ChangeId>, bool),
        fs::FsErrorC<C::Error, Self::GraphError>,
    > {
        fs::follow_oldest_path(changes, self, &channel.borrow(), path)
    }

    fn output_file<C: changestore::ChangeStore, V: vertex_buffer::VertexBuffer>(
        &self,
        changes: &C,
        channel: &pristine::ChannelRef<Self>,
        v0: pristine::Position<pristine::ChangeId>,
        out: &mut V,
    ) -> Result<(), output::FileError<C::Error, Self::GraphError>> {
        let mut forward = Vec::new();
        let channel = channel.borrow();
        let mut graph = alive::retrieve(self, self.graph(&channel), v0)?;
        alive::output_graph(changes, self, &channel, out, &mut graph, &mut forward)?;
        Ok(())
    }

    fn archive<C: changestore::ChangeStore, A: Archive>(
        &self,
        changes: &C,
        channel: &pristine::ChannelRef<Self>,
        arch: &mut A,
    ) -> Result<Vec<output::Conflict>, output::ArchiveError<C::Error, Self::GraphError, A::Error>>
    {
        output::archive(changes, self, channel, &mut std::iter::empty(), arch)
    }

    fn archive_prefix<'a, C: changestore::ChangeStore, I: Iterator<Item = &'a str>, A: Archive>(
        &self,
        changes: &C,
        channel: &pristine::ChannelRef<Self>,
        prefix: &mut I,
        arch: &mut A,
    ) -> Result<Vec<output::Conflict>, output::ArchiveError<C::Error, Self::GraphError, A::Error>>
    {
        output::archive(changes, self, channel, prefix, arch)
    }

    fn iter_adjacent<'txn>(
        &'txn self,
        graph: &'txn Self::Channel,
        key: Vertex<pristine::ChangeId>,
        min_flag: pristine::EdgeFlags,
        max_flag: pristine::EdgeFlags,
    ) -> Result<pristine::AdjacentIterator<'txn, Self>, pristine::TxnErr<Self::GraphError>> {
        pristine::iter_adjacent(self, self.graph(graph), key, min_flag, max_flag)
    }
}

pub struct Log<'txn, T: pristine::ChannelTxnT> {
    txn: &'txn T,
    iter: pristine::Cursor<
        T,
        &'txn T,
        T::RevchangesetCursor,
        u64,
        (pristine::ChangeId, pristine::Merkle),
    >,
}

impl<'txn, T: pristine::ChannelTxnT> Iterator for Log<'txn, T> {
    type Item = Result<(u64, (pristine::Hash, pristine::Merkle)), T::GraphError>;
    fn next(&mut self) -> Option<Self::Item> {
        match self.iter.next() {
            Some(Ok((n, (c, m)))) => {
                let ext = match self.txn.get_external(c) {
                    Err(pristine::TxnErr(e)) => return Some(Err(e)),
                    Ok(Some(ext)) => ext,
                    Ok(None) => panic!("Unknown change {:?}", c),
                };
                Some(Ok((n, (ext, m))))
            }
            None => None,
            Some(Err(e)) => Some(Err(e.0)),
        }
    }
}

pub struct RevLog<'txn, T: pristine::ChannelTxnT> {
    txn: &'txn T,
    iter: pristine::RevCursor<
        T,
        &'txn T,
        T::RevchangesetCursor,
        u64,
        (pristine::ChangeId, pristine::Merkle),
    >,
}

impl<'txn, T: pristine::ChannelTxnT> Iterator for RevLog<'txn, T> {
    type Item = Result<(u64, (pristine::Hash, pristine::Merkle)), T::GraphError>;
    fn next(&mut self) -> Option<Self::Item> {
        match self.iter.next() {
            Some(Ok((n, (c, m)))) => match self.txn.get_external(c) {
                Ok(Some(ext)) => Some(Ok((n, (ext, m)))),
                Err(e) => Some(Err(e.0)),
                Ok(None) => panic!("Unknown change {:?}", c),
            },
            None => None,
            Some(Err(e)) => Some(Err(e.0)),
        }
    }
}

pub struct Touched<'txn, T: pristine::DepsTxnT> {
    txn: &'txn T,
    iter: pristine::Cursor<
        T,
        &'txn T,
        T::Rev_touched_filesCursor,
        pristine::ChangeId,
        pristine::Position<pristine::ChangeId>,
    >,
    id: pristine::ChangeId,
}

impl<
        'txn,
        T: pristine::DepsTxnT + pristine::GraphTxnT<GraphError = <T as pristine::DepsTxnT>::DepsError>,
    > Iterator for Touched<'txn, T>
{
    type Item = Result<pristine::Position<pristine::Hash>, T::DepsError>;
    fn next(&mut self) -> Option<Self::Item> {
        while let Some(x) = self.iter.next() {
            let (cid, file) = match x {
                Ok(x) => x,
                Err(e) => return Some(Err(e.0)),
            };
            if cid > self.id {
                return None;
            } else if cid == self.id {
                let change = match self.txn.get_external(file.change) {
                    Ok(ext) => ext.unwrap(),
                    Err(e) => return Some(Err(e.0)),
                };
                return Some(Ok(pristine::Position {
                    change,
                    pos: file.pos,
                }));
            }
        }
        None
    }
}

#[doc(hidden)]
#[derive(Debug, Default, Clone)]
pub struct Timers {
    pub alive_output: std::time::Duration,
    pub alive_graph: std::time::Duration,
    pub alive_retrieve: std::time::Duration,
    pub alive_contents: std::time::Duration,
    pub alive_write: std::time::Duration,
    pub record: std::time::Duration,
    pub apply: std::time::Duration,
    pub repair_context: std::time::Duration,
    pub check_cyclic_paths: std::time::Duration,
    pub find_alive: std::time::Duration,
}
use std::sync::Mutex;
lazy_static! {
    pub static ref TIMERS: Mutex<Timers> = Mutex::new(Timers {
        alive_output: std::time::Duration::from_secs(0),
        alive_graph: std::time::Duration::from_secs(0),
        alive_retrieve: std::time::Duration::from_secs(0),
        alive_contents: std::time::Duration::from_secs(0),
        alive_write: std::time::Duration::from_secs(0),
        record: std::time::Duration::from_secs(0),
        apply: std::time::Duration::from_secs(0),
        repair_context: std::time::Duration::from_secs(0),
        check_cyclic_paths: std::time::Duration::from_secs(0),
        find_alive: std::time::Duration::from_secs(0),
    });
}
#[doc(hidden)]
pub fn reset_timers() {
    *TIMERS.lock().unwrap() = Timers::default();
}
#[doc(hidden)]
pub fn get_timers() -> Timers {
    TIMERS.lock().unwrap().clone()
}
