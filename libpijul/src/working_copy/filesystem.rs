use super::*;
use crate::pristine::InodeMetadata;
use canonical_path::{CanonicalPath, CanonicalPathBuf};
use ignore::WalkBuilder;
use std::borrow::Cow;
use std::path::{Path, PathBuf};

pub struct FileSystem {
    root: PathBuf,
}

pub fn filter_ignore(root_: &CanonicalPath, path: &CanonicalPath, is_dir: bool) -> bool {
    debug!("path = {:?} root = {:?}", path, root_);
    if let Ok(suffix) = path.as_path().strip_prefix(root_.as_path()) {
        debug!("suffix = {:?}", suffix);
        let mut root = root_.as_path().to_path_buf();
        let mut ignore = ignore::gitignore::GitignoreBuilder::new(&root);
        let mut add_root = |root: &mut PathBuf| {
            ignore.add_line(None, crate::DOT_DIR).unwrap();
            root.push(".ignore");
            ignore.add(&root);
            root.pop();
            root.push(".gitignore");
            ignore.add(&root);
            root.pop();
        };
        add_root(&mut root);
        for c in suffix.components() {
            root.push(c);
            add_root(&mut root);
        }
        if let Ok(ig) = ignore.build() {
            let m = ig.matched(suffix, is_dir);
            debug!("m = {:?}", m);
            return !m.is_ignore();
        }
    }
    false
}

/// From a path on the filesystem, return the canonical path (a `PathBuf`), and a
/// prefix relative to the root of the repository (a `String`).
pub fn get_prefix(
    repo_path: Option<&CanonicalPath>,
    prefix: &Path,
) -> Result<(canonical_path::CanonicalPathBuf, String), std::io::Error> {
    let mut p = String::new();
    let repo = if let Some(repo) = repo_path {
        Cow::Borrowed(repo)
    } else {
        Cow::Owned(canonical_path::CanonicalPathBuf::canonicalize(
            std::env::current_dir()?,
        )?)
    };
    debug!("get prefix {:?} {:?}", repo, prefix);
    let prefix_ = CanonicalPathBuf::canonicalize(&repo.as_path().join(&prefix))?;
    debug!("get prefix {:?}", prefix_);
    if let Ok(prefix) = prefix_.as_path().strip_prefix(repo.as_path()) {
        for c in prefix.components() {
            if !p.is_empty() {
                p.push('/');
            }
            let c: &std::path::Path = c.as_ref();
            p.push_str(&c.to_string_lossy())
        }
    }
    Ok((prefix_, p))
}

#[derive(Debug, Error)]
pub enum AddError<T: std::error::Error + 'static> {
    #[error(transparent)]
    Ignore(#[from] ignore::Error),
    #[error(transparent)]
    Io(#[from] std::io::Error),
    #[error(transparent)]
    Fs(#[from] crate::fs::FsError<T>),
}

#[derive(Debug, Error)]
pub enum Error<C: std::error::Error + 'static, T: std::error::Error + 'static> {
    #[error(transparent)]
    Add(#[from] AddError<T>),
    #[error(transparent)]
    Record(#[from] crate::record::RecordError<C, std::io::Error, T>),
}

impl FileSystem {
    pub fn from_root<P: AsRef<Path>>(root: P) -> Self {
        FileSystem {
            root: root.as_ref().to_path_buf(),
        }
    }

    pub fn record_prefixes<
        T: crate::MutTxnTExt + crate::TxnTExt,
        C: crate::changestore::ChangeStore,
        P: AsRef<Path>,
    >(
        &mut self,
        txn: &mut T,
        channel: &mut crate::pristine::ChannelRef<T>,
        changes: &C,
        state: &mut crate::RecordBuilder,
        repo_path: CanonicalPathBuf,
        prefixes: &[P],
        threads: usize,
    ) -> Result<(), Error<C::Error, T::GraphError>> {
        for prefix in prefixes.iter() {
            self.record_prefix(
                txn,
                channel,
                changes,
                state,
                repo_path.clone(),
                prefix.as_ref(),
                threads,
            )?
        }
        if prefixes.is_empty() {
            self.record_prefix(
                txn,
                channel,
                changes,
                state,
                repo_path.clone(),
                Path::new(""),
                threads,
            )?
        }
        Ok(())
    }

    pub fn add_prefix_rec<T: crate::MutTxnTExt + crate::TxnTExt>(
        &self,
        txn: &mut T,
        repo_path: CanonicalPathBuf,
        full: CanonicalPathBuf,
        prefix: &str,
        threads: usize,
    ) -> Result<(), AddError<T::GraphError>> {
        debug!("record_prefix {:?}", prefix);
        debug!("full = {:?}", full);
        let meta = std::fs::metadata(&full)?;
        debug!("meta = {:?}", meta);
        let (sender, receiver) = std::sync::mpsc::sync_channel(100);

        debug!("{:?}", full.as_path().strip_prefix(repo_path.as_path()));
        if !filter_ignore(
            &repo_path.as_canonical_path(),
            &full.as_canonical_path(),
            meta.is_dir(),
        ) {
            return Ok(());
        }
        let t = std::thread::spawn(move || -> Result<(), AddError<T::GraphError>> {
            if meta.is_dir() {
                let mut walk = WalkBuilder::new(&full);
                walk.ignore(true)
                    .git_ignore(true)
                    .filter_entry(|p| {
                        debug!("p.file_name = {:?}", p.file_name());
                        p.file_name() != crate::DOT_DIR
                    })
                    .threads(threads - 1);
                walk.build_parallel().run(|| {
                    Box::new(|entry| {
                        let entry: ignore::DirEntry = if let Ok(entry) = entry {
                            entry
                        } else {
                            return ignore::WalkState::Quit;
                        };
                        let p = entry.path();
                        if let Some(p) = p.file_name() {
                            if let Some(p) = p.to_str() {
                                if p.ends_with("~") || (p.starts_with("#") && p.ends_with("#")) {
                                    return ignore::WalkState::Skip;
                                }
                            }
                        }
                        debug!("entry path = {:?} {:?}", entry.path(), repo_path);
                        if let Ok(entry_path) = CanonicalPathBuf::canonicalize(entry.path()) {
                            if let Ok(path) = entry_path.as_path().strip_prefix(&repo_path) {
                                let is_dir = entry.file_type().unwrap().is_dir();
                                if sender.send((path.to_path_buf(), is_dir)).is_err() {
                                    return ignore::WalkState::Quit;
                                }
                            } else {
                                debug!("entry = {:?}", entry.path());
                            }
                        }
                        ignore::WalkState::Continue
                    })
                })
            } else {
                debug!("filter_ignore ok");
                let path = full.as_path().strip_prefix(&repo_path.as_path()).unwrap();
                sender.send((path.to_path_buf(), false)).unwrap();
            }
            Ok(())
        });

        while let Ok((path, is_dir)) = receiver.recv() {
            info!("Adding {:?}", path);
            let path_str = path.to_str().unwrap();
            match txn.add(path_str, is_dir) {
                Ok(()) => {}
                Err(crate::fs::FsError::AlreadyInRepo(_)) => {}
                Err(e) => return Err(e.into()),
            }
        }

        if let Ok(t) = t.join() {
            t?
        }
        Ok(())
    }

    pub fn record_prefix<
        T: crate::MutTxnTExt + crate::TxnTExt,
        C: crate::changestore::ChangeStore,
    >(
        &mut self,
        txn: &mut T,
        channel: &mut crate::pristine::ChannelRef<T>,
        changes: &C,
        state: &mut crate::RecordBuilder,
        repo_path: CanonicalPathBuf,
        prefix: &Path,
        threads: usize,
    ) -> Result<(), Error<C::Error, T::GraphError>> {
        if let Ok((full, prefix)) = get_prefix(Some(repo_path.as_ref()), prefix) {
            self.add_prefix_rec(txn, repo_path, full, &prefix, threads)?;
            debug!("recording from prefix {:?}", prefix);
            txn.record(
                state,
                crate::Algorithm::default(),
                channel,
                self,
                changes,
                &prefix,
            )?;
            debug!("recorded");
        }
        Ok(())
    }

    fn path(&self, file: &str) -> PathBuf {
        let mut path = self.root.clone();
        path.extend(crate::path::components(file));
        path
    }
}

impl WorkingCopy for FileSystem {
    type Error = std::io::Error;
    fn create_dir_all(&mut self, file: &str) -> Result<(), Self::Error> {
        Ok(std::fs::create_dir_all(&self.path(file))?)
    }
    fn file_metadata(&self, file: &str) -> Result<InodeMetadata, Self::Error> {
        let attr = std::fs::metadata(&self.path(file))?;
        let permissions = permissions(&attr).unwrap_or(0o755);
        debug!("permissions = {:?}", permissions);
        Ok(InodeMetadata::new(permissions & 0o777, attr.is_dir()))
    }
    fn read_file(&self, file: &str, buffer: &mut Vec<u8>) -> Result<(), Self::Error> {
        use std::io::Read;
        let mut f = std::fs::File::open(&self.path(file))?;
        f.read_to_end(buffer)?;
        Ok(())
    }
    fn modified_time(&self, file: &str) -> Result<std::time::SystemTime, Self::Error> {
        let attr = std::fs::metadata(&self.path(file))?;
        Ok(attr.modified()?)
    }

    fn remove_path(&mut self, path: &str) -> Result<(), Self::Error> {
        let path = self.path(path);
        if let Ok(meta) = std::fs::metadata(&path) {
            if let Err(e) = if meta.is_dir() {
                std::fs::remove_dir_all(&path)
            } else {
                std::fs::remove_file(&path)
            } {
                error!("while deleting {:?}: {:?}", path, e);
            }
        }
        Ok(())
    }
    fn rename(&mut self, former: &str, new: &str) -> Result<(), Self::Error> {
        let former = self.path(former);
        let new = self.path(new);
        if let Some(p) = new.parent() {
            std::fs::create_dir_all(p)?
        }
        if let Err(e) = std::fs::rename(&former, &new) {
            error!("while renaming {:?} to {:?}: {:?}", former, new, e)
        }
        Ok(())
    }
    #[cfg(not(windows))]
    fn set_permissions(&mut self, name: &str, permissions: u16) -> Result<(), Self::Error> {
        use std::os::unix::fs::PermissionsExt;
        let name = self.path(name);
        debug!("set_permissions: {:?}", name);
        let metadata = std::fs::metadata(&name)?;
        let mut current = metadata.permissions();
        debug!(
            "setting mode for {:?} to {:?} (currently {:?})",
            name, permissions, current
        );
        current.set_mode(permissions as u32);
        std::fs::set_permissions(name, current)?;
        Ok(())
    }
    #[cfg(windows)]
    fn set_permissions(&mut self, _name: &str, _permissions: u16) -> Result<(), Self::Error> {
        Ok(())
    }
    fn write_file<A, E: std::error::Error, F: FnOnce(&mut dyn std::io::Write) -> Result<A, E>>(
        &mut self,
        file: &str,
        writer: F,
    ) -> Result<A, WriteError<E>> {
        let path = self.path(file);
        if let Some(p) = path.parent() {
            std::fs::create_dir_all(p).map_err(WriteError::Io)?
        }
        std::fs::remove_file(&path).unwrap_or(());
        let mut file =
            std::io::BufWriter::new(std::fs::File::create(&path).map_err(WriteError::Io)?);
        writer(&mut file).map_err(WriteError::E)
    }
}

#[cfg(not(windows))]
fn permissions(attr: &std::fs::Metadata) -> Option<usize> {
    use std::os::unix::fs::PermissionsExt;
    Some(attr.permissions().mode() as usize)
}
#[cfg(windows)]
fn permissions(_: &std::fs::Metadata) -> Option<usize> {
    None
}
