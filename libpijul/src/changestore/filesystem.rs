use super::*;
use crate::change::{Change, ChangeFile};
use crate::pristine::{Base32, ChangeId, Hash, Vertex};
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex, MutexGuard};

const CHANGE_CACHE_SIZE: usize = 100;

/// A file system change store.
#[derive(Clone)]
pub struct FileSystem(Arc<FileSystem_>);

struct FileSystem_ {
    change_cache: Mutex<lru_cache::LruCache<ChangeId, Arc<Mutex<ChangeFile<'static>>>>>,
    changes_dir: PathBuf,
}

#[derive(Debug, Error)]
pub enum Error {
    #[error(transparent)]
    Io(#[from] std::io::Error),
    #[error(transparent)]
    Utf8(#[from] std::str::Utf8Error),
    #[error(transparent)]
    ChangeFile(#[from] crate::change::ChangeError),
    #[error(transparent)]
    Persist(#[from] tempfile::PersistError),
}

pub fn push_filename(changes_dir: &mut PathBuf, hash: &Hash) {
    let h32 = hash.to_base32();
    let (a, b) = h32.split_at(2);
    changes_dir.push(a);
    changes_dir.push(b);
    changes_dir.set_extension("change");
}

pub fn pop_filename(changes_dir: &mut PathBuf) {
    changes_dir.pop();
    changes_dir.pop();
}

impl FileSystem {
    pub fn filename(&self, hash: &Hash) -> PathBuf {
        let mut path = self.0.changes_dir.clone();
        push_filename(&mut path, hash);
        path
    }

    pub fn has_change(&self, hash: &Hash) -> bool {
        std::fs::metadata(&self.filename(hash)).is_ok()
    }

    /// Construct a `FileSystem`, starting from the root of the
    /// repository (i.e. the parent of the `.pijul` directory).
    pub fn from_root<P: AsRef<Path>>(root: P) -> Self {
        let dot_pijul = root.as_ref().join(crate::DOT_DIR);
        let changes_dir = dot_pijul.join("changes");
        Self::from_changes(changes_dir)
    }

    /// Construct a `FileSystem`, starting from the root of the
    /// repository (i.e. the parent of the `.pijul` directory).
    pub fn from_changes(changes_dir: PathBuf) -> Self {
        std::fs::create_dir_all(&changes_dir).unwrap();
        FileSystem(Arc::new(FileSystem_ {
            changes_dir,
            change_cache: Mutex::new(lru_cache::LruCache::new(CHANGE_CACHE_SIZE)),
        }))
    }

    fn load<F: Fn(ChangeId) -> Option<Hash>>(
        &self,
        hash: F,
        change: ChangeId,
    ) -> Result<
        MutexGuard<lru_cache::LruCache<ChangeId, Arc<Mutex<ChangeFile<'static>>>>>,
        crate::change::ChangeError,
    > {
        let mut cache = self.0.change_cache.lock().unwrap();
        if !cache.contains_key(&change) {
            let h = hash(change).unwrap();
            let path = self.filename(&h);
            let p = crate::change::ChangeFile::open(h, &path.to_str().unwrap())?;
            cache.insert(change, Arc::new(Mutex::new(p)));
        }
        Ok(cache)
    }

    pub fn save_from_buf(
        &self,
        buf: &[u8],
        hash: &Hash,
        change_id: Option<ChangeId>,
    ) -> Result<(), crate::change::ChangeError> {
        Change::check_from_buffer(buf, hash)?;
        self.save_from_buf_unchecked(buf, hash, change_id)?;
        Ok(())
    }

    pub fn save_from_buf_unchecked(
        &self,
        buf: &[u8],
        hash: &Hash,
        change_id: Option<ChangeId>,
    ) -> Result<(), std::io::Error> {
        let mut f = tempfile::NamedTempFile::new_in(&self.0.changes_dir)?;
        let file_name = self.filename(hash);
        use std::io::Write;
        f.write_all(buf)?;
        debug!("file_name = {:?}", file_name);
        std::fs::create_dir_all(file_name.parent().unwrap())?;
        f.persist(file_name)?;
        if let Some(ref change_id) = change_id {
            let mut cache = self.0.change_cache.lock().unwrap();
            cache.remove(change_id);
        }
        Ok(())
    }
}

impl ChangeStore for FileSystem {
    type Error = Error;
    fn has_contents(&self, hash: Hash, change_id: Option<ChangeId>) -> bool {
        if let Some(ref change_id) = change_id {
            let mut cache = self.0.change_cache.lock().unwrap();
            let mut poisoned = false;
            if let Some(c) = cache.get_mut(change_id) {
                if let Ok(l) = c.lock() {
                    return l.has_contents();
                } else {
                    poisoned = true
                }
            }
            if poisoned {
                cache.remove(change_id);
            }
        }
        let path = self.filename(&hash);
        if let Ok(p) = crate::change::ChangeFile::open(hash, &path.to_str().unwrap()) {
            p.has_contents()
        } else {
            false
        }
    }

    fn get_header(&self, h: &Hash) -> Result<ChangeHeader, Self::Error> {
        let path = self.filename(h);
        let p = crate::change::ChangeFile::open(*h, &path.to_str().unwrap())?;
        Ok(p.hashed().header.clone())
    }

    fn get_contents<F: Fn(ChangeId) -> Option<Hash>>(
        &self,
        hash: F,
        key: Vertex<ChangeId>,
        buf: &mut Vec<u8>,
    ) -> Result<usize, Self::Error> {
        buf.resize((key.end.0 - key.start.0) as usize, 0);
        if key.end <= key.start || key.is_root() {
            return Ok(0);
        }
        let mut cache = self.load(hash, key.change)?;
        let p = cache.get_mut(&key.change).unwrap();
        let mut p = p.lock().unwrap();
        let n = p.read_contents(key.start.0, buf)?;
        Ok(n)
    }
    fn get_contents_ext(
        &self,
        key: Vertex<Option<Hash>>,
        buf: &mut Vec<u8>,
    ) -> Result<usize, Self::Error> {
        if let Some(change) = key.change {
            buf.resize((key.end.0 - key.start.0) as usize, 0);
            if key.end <= key.start {
                return Ok(0);
            }
            let path = self.filename(&change);
            let mut p = crate::change::ChangeFile::open(change, &path.to_str().unwrap())?;
            let n = p.read_contents(key.start.0, buf)?;
            Ok(n)
        } else {
            Ok(0)
        }
    }
    fn change_deletes_position<F: Fn(ChangeId) -> Option<Hash>>(
        &self,
        hash: F,
        change: ChangeId,
        pos: Position<Option<Hash>>,
    ) -> Result<Vec<Hash>, Self::Error> {
        let mut cache = self.load(hash, change)?;
        let p = cache.get_mut(&change).unwrap();
        let p = p.lock().unwrap();
        let mut v = Vec::new();
        for c in p.hashed().changes.iter() {
            for c in c.iter() {
                v.extend(c.deletes_pos(pos).into_iter())
            }
        }
        Ok(v)
    }
    fn save_change(&self, p: &Change) -> Result<Hash, Self::Error> {
        let mut f = tempfile::NamedTempFile::new_in(&self.0.changes_dir)?;
        let hash = {
            let w = std::io::BufWriter::new(&mut f);
            p.serialize(w)?
        };
        let file_name = self.filename(&hash);
        std::fs::create_dir_all(file_name.parent().unwrap())?;
        debug!("file_name = {:?}", file_name);
        f.persist(file_name)?;
        Ok(hash)
    }
    fn del_change(&self, hash: &Hash) -> Result<bool, Self::Error> {
        let file_name = self.filename(hash);
        debug!("file_name = {:?}", file_name);
        let result = std::fs::remove_file(&file_name).is_ok();
        std::fs::remove_dir(file_name.parent().unwrap()).unwrap_or(()); // fails silently if there are still changes with the same 2-letter prefix.
        Ok(result)
    }
    fn get_change(&self, h: &Hash) -> Result<Change, Self::Error> {
        let file_name = self.filename(h);
        let file_name = file_name.to_str().unwrap();
        debug!("file_name = {:?}", file_name);
        Ok(Change::deserialize(&file_name, Some(h))?)
    }
}
