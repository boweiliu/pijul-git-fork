use crate::changestore::ChangeStore;
use crate::path;
use crate::pristine::*;
use std::collections::HashMap;

mod output;
pub use output::*;
mod archive;
pub use archive::*;

#[derive(Debug, Error)]
pub enum OutputError<
    ChangestoreError: std::error::Error + 'static,
    Txn: std::error::Error + 'static,
    W: std::error::Error + 'static,
> {
    #[error("Working copy error: {0}")]
    WorkingCopy(W),
    #[error(transparent)]
    Pristine(#[from] PristineOutputError<ChangestoreError, Txn>),
}

#[derive(Debug, Error)]
pub enum PristineOutputError<ChangestoreError: std::error::Error, Txn: std::error::Error + 'static>
{
    #[error(transparent)]
    Txn(Txn),
    #[error("Changestore error: {0}")]
    Changestore(ChangestoreError),
    #[error(transparent)]
    Io(#[from] std::io::Error),
    #[error(transparent)]
    Fs(#[from] crate::fs::FsError<Txn>),
}

use crate::working_copy::WriteError;

impl<C: std::error::Error, T: std::error::Error + 'static, W: std::error::Error>
    OutputError<C, T, W>
{
    fn from(e: WriteError<Self>) -> Self {
        match e {
            WriteError::Io(e) => OutputError::Pristine(PristineOutputError::Io(e)),
            WriteError::E(e) => e,
        }
    }
}

impl<C: std::error::Error, T: std::error::Error + 'static> From<TxnErr<T>>
    for PristineOutputError<C, T>
{
    fn from(e: TxnErr<T>) -> Self {
        PristineOutputError::Txn(e.0)
    }
}

impl<C: std::error::Error, T: std::error::Error + 'static, W: std::error::Error> From<TxnErr<T>>
    for OutputError<C, T, W>
{
    fn from(e: TxnErr<T>) -> Self {
        OutputError::Pristine(e.into())
    }
}

#[derive(Debug, Error)]
pub enum FileError<ChangestoreError: std::error::Error + 'static, T: std::error::Error + 'static> {
    #[error(transparent)]
    Changestore(ChangestoreError),
    #[error(transparent)]
    Txn(T),
    #[error(transparent)]
    Io(#[from] std::io::Error),
}

impl<C: std::error::Error, T: std::error::Error + 'static> From<FileError<C, T>>
    for PristineOutputError<C, T>
{
    fn from(e: FileError<C, T>) -> Self {
        match e {
            FileError::Changestore(e) => PristineOutputError::Changestore(e),
            FileError::Io(e) => PristineOutputError::Io(e),
            FileError::Txn(t) => PristineOutputError::Txn(t),
        }
    }
}

impl<C: std::error::Error, T: std::error::Error + 'static> From<TxnErr<T>> for FileError<C, T> {
    fn from(e: TxnErr<T>) -> Self {
        FileError::Txn(e.0)
    }
}

#[derive(Debug)]
struct OutputItem {
    parent: Inode,
    path: String,
    meta: InodeMetadata,
    pos: Position<ChangeId>,
    is_zombie: bool,
}

fn collect_children<T: GraphTxnT, P: ChangeStore>(
    txn: &T,
    changes: &P,
    channel: &T::Graph,
    inode_pos: Position<ChangeId>,
    inode: Inode,
    path: &str,
    prefix_basename: Option<&str>,
    files: &mut HashMap<String, Vec<(Vertex<ChangeId>, OutputItem)>>,
) -> Result<(), PristineOutputError<P::Error, T::GraphError>> {
    debug!("path = {:?}", path);
    for e in iter_adjacent(
        txn,
        channel,
        inode_pos.inode_vertex(),
        EdgeFlags::FOLDER,
        EdgeFlags::FOLDER | EdgeFlags::PSEUDO | EdgeFlags::BLOCK,
    )? {
        let e = e?;
        let name_vertex = txn.find_block(channel, e.dest).unwrap();
        let mut name_buf = Vec::new();
        changes
            .get_contents(|h| txn.get_external(h).unwrap(), name_vertex, &mut name_buf)
            .map_err(PristineOutputError::Changestore)?;
        let (perms, basename) = name_buf.as_slice().split_at(2);
        let (perms, basename) = (
            InodeMetadata::from_basename(perms),
            std::str::from_utf8(basename).unwrap(),
        );
        debug!("filename: {:?} {:?}", perms, basename);
        let mut name = path.to_string();
        if let Some(next) = prefix_basename {
            if next != basename {
                continue;
            }
        }
        path::push(&mut name, basename);
        debug!("name_vertex: {:?} {:?}", e, name_vertex);
        let child = if let Some(child) = iter_adjacent(
            txn,
            channel,
            name_vertex,
            EdgeFlags::FOLDER,
            EdgeFlags::FOLDER | EdgeFlags::BLOCK | EdgeFlags::PSEUDO,
        )?
        .next()
        {
            child?
        } else {
            let mut edge = None;
            for e in iter_adjacent(
                txn,
                channel,
                name_vertex,
                EdgeFlags::FOLDER,
                EdgeFlags::all(),
            )? {
                let e = e?;
                if !e.flag.contains(EdgeFlags::PARENT) {
                    edge = Some(e);
                    break;
                }
            }
            let e = edge.unwrap();
            let mut f = std::fs::File::create("debug_output").unwrap();
            debug_root(txn, channel, e.dest.inode_vertex(), &mut f, false).unwrap();
            panic!("no child");
        };

        debug!("child: {:?}", child);
        let v = files.entry(name).or_insert_with(Vec::new);
        v.push((
            name_vertex,
            OutputItem {
                parent: inode,
                path: path.to_string(),
                meta: perms,
                pos: child.dest,
                is_zombie: is_zombie(txn, channel, child.dest)?,
            },
        ));
    }
    Ok(())
}

fn is_zombie<T: GraphTxnT>(
    txn: &T,
    channel: &T::Graph,
    pos: Position<ChangeId>,
) -> Result<bool, TxnErr<T::GraphError>> {
    let f = EdgeFlags::FOLDER | EdgeFlags::PARENT | EdgeFlags::DELETED;
    if let Some(n) =
        iter_adjacent(txn, channel, pos.inode_vertex(), f, f | EdgeFlags::BLOCK)?.next()
    {
        n?;
        Ok(true)
    } else {
        Ok(false)
    }
}
