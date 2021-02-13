use super::*;
use crate::pristine::InodeMetadata;
use std::collections::HashMap;
use std::time::SystemTime;

#[derive(Debug)]
pub struct Memory {
    pub files: FileTree,
    pub last_modified: SystemTime,
}

#[derive(Debug, Default)]
pub struct FileTree {
    children: HashMap<String, Inode>,
}
#[derive(Debug)]
enum Inode {
    File {
        meta: InodeMetadata,
        last_modified: SystemTime,
        contents: Vec<u8>,
    },
    Directory {
        meta: InodeMetadata,
        last_modified: SystemTime,
        children: FileTree,
    },
}

impl Default for Memory {
    fn default() -> Self {
        Self {
            files: FileTree::default(),
            last_modified: SystemTime::now(),
        }
    }
}

impl Memory {
    pub fn new() -> Self {
        Self::default()
    }
    pub fn list_files(&self) -> Vec<String> {
        let mut result = Vec::new();
        let mut current_files = vec![(String::new(), &self.files)];
        let mut next_files = Vec::new();
        loop {
            if current_files.is_empty() {
                break;
            }
            for (path, tree) in current_files.iter() {
                for (name, inode) in tree.children.iter() {
                    let mut path = path.clone();
                    crate::path::push(&mut path, name);
                    match inode {
                        Inode::File { .. } => {
                            result.push(path);
                        }
                        Inode::Directory { ref children, .. } => {
                            result.push(path.clone());
                            next_files.push((path, children))
                        }
                    }
                }
            }
            std::mem::swap(&mut current_files, &mut next_files);
            next_files.clear();
        }
        result
    }

    pub fn add_file(&mut self, file: &str, file_contents: Vec<u8>) {
        let file_meta = InodeMetadata::new(0o644, false);
        let last = SystemTime::now();
        self.add_inode(
            file,
            Inode::File {
                meta: file_meta,
                last_modified: last,
                contents: file_contents,
            },
        )
    }

    pub fn add_dir(&mut self, file: &str) {
        let file_meta = InodeMetadata::new(0o755, true);
        let last = SystemTime::now();
        self.add_inode(
            file,
            Inode::Directory {
                meta: file_meta,
                last_modified: last,
                children: FileTree {
                    children: HashMap::new(),
                },
            },
        )
    }

    fn add_inode(&mut self, file: &str, inode: Inode) {
        let mut file_tree = &mut self.files;
        let last = SystemTime::now();
        self.last_modified = last;
        let file = file.split('/').filter(|c| !c.is_empty());
        let mut p = file.peekable();
        while let Some(f) = p.next() {
            if p.peek().is_some() {
                let entry = file_tree
                    .children
                    .entry(f.to_string())
                    .or_insert(Inode::Directory {
                        meta: InodeMetadata::new(0o755, true),
                        children: FileTree {
                            children: HashMap::new(),
                        },
                        last_modified: last,
                    });
                match *entry {
                    Inode::Directory {
                        ref mut children, ..
                    } => file_tree = children,
                    _ => panic!("Not a directory"),
                }
            } else {
                file_tree.children.insert(f.to_string(), inode);
                break;
            }
        }
    }

    fn get_file(&self, file: &str) -> Option<&Inode> {
        debug!("get_file {:?}", file);
        debug!("repo = {:?}", self);
        let mut t = Some(&self.files);
        let mut inode = None;
        let it = file.split('/').filter(|c| !c.is_empty());
        for c in it {
            debug!("c = {:?}", c);
            inode = t.take().unwrap().children.get(c);
            debug!("inode = {:?}", inode);
            match inode {
                Some(Inode::Directory { ref children, .. }) => t = Some(children),
                _ => break,
            }
        }
        inode
    }

    fn get_file_mut<'a>(&'a mut self, file: &str) -> Option<&'a mut Inode> {
        debug!("get_file_mut {:?}", file);
        debug!("repo = {:?}", self);
        let mut t = Some(&mut self.files);
        let mut it = file.split('/').filter(|c| !c.is_empty()).peekable();
        self.last_modified = SystemTime::now();
        while let Some(c) = it.next() {
            debug!("c = {:?}", c);
            let inode_ = t.take().unwrap().children.get_mut(c);
            debug!("inode = {:?}", inode_);
            if it.peek().is_none() {
                return inode_;
            }
            match inode_ {
                Some(Inode::Directory {
                    ref mut children, ..
                }) => t = Some(children),
                _ => return None,
            }
        }
        None
    }

    fn remove_path_(&mut self, path: &str) -> Option<Inode> {
        debug!("remove_path {:?}", path);
        debug!("repo = {:?}", self);
        let mut t = Some(&mut self.files);
        let mut it = path.split('/').filter(|c| !c.is_empty());
        let mut c = it.next().unwrap();
        self.last_modified = SystemTime::now();
        loop {
            debug!("c = {:?}", c);
            let next_c = it.next();
            let t_ = t.take().unwrap();
            let next_c = if let Some(next_c) = next_c {
                next_c
            } else {
                return t_.children.remove(c);
            };
            let inode = t_.children.get_mut(c);
            c = next_c;
            debug!("inode = {:?}", inode);
            match inode {
                Some(Inode::Directory {
                    ref mut children, ..
                }) => t = Some(children),
                _ => return None,
            }
        }
    }
}

#[derive(Debug, Error)]
pub enum Error {
    #[error("Path not found: {path}")]
    NotFound { path: String },
}

impl WorkingCopy for Memory {
    type Error = Error;
    fn create_dir_all(&mut self, file: &str) -> Result<(), Self::Error> {
        if self.get_file(file).is_none() {
            let last = SystemTime::now();
            self.add_inode(
                file,
                Inode::Directory {
                    meta: InodeMetadata::new(0o755, true),
                    children: FileTree {
                        children: HashMap::new(),
                    },
                    last_modified: last,
                },
            );
        }
        Ok(())
    }
    fn file_metadata(&self, file: &str) -> Result<InodeMetadata, Self::Error> {
        match self.get_file(file) {
            Some(Inode::Directory { meta, .. }) => Ok(*meta),
            Some(Inode::File { meta, .. }) => Ok(*meta),
            None => Err(Error::NotFound {
                path: file.to_string(),
            }),
        }
    }
    fn read_file(&self, file: &str, buffer: &mut Vec<u8>) -> Result<(), Self::Error> {
        match self.get_file(file) {
            Some(Inode::Directory { .. }) => panic!("Not a file: {:?}", file),
            Some(Inode::File { ref contents, .. }) => {
                buffer.extend(contents);
                Ok(())
            }
            None => Err(Error::NotFound {
                path: file.to_string(),
            }),
        }
    }
    fn modified_time(&self, _file: &str) -> Result<std::time::SystemTime, Self::Error> {
        Ok(self.last_modified)
    }

    fn remove_path(&mut self, path: &str) -> Result<(), Self::Error> {
        self.remove_path_(path);
        Ok(())
    }

    fn rename(&mut self, old: &str, new: &str) -> Result<(), Self::Error> {
        debug!("rename {:?} to {:?}", old, new);
        if let Some(inode) = self.remove_path_(old) {
            self.add_inode(new, inode)
        }
        Ok(())
    }
    fn set_permissions(&mut self, file: &str, permissions: u16) -> Result<(), Self::Error> {
        debug!("set_permissions {:?}", file);
        match self.get_file_mut(file) {
            Some(Inode::File { ref mut meta, .. }) => {
                *meta = InodeMetadata::new(permissions as usize, false);
            }
            Some(Inode::Directory { ref mut meta, .. }) => {
                *meta = InodeMetadata::new(permissions as usize, true);
            }
            None => panic!("file not found: {:?}", file),
        }
        Ok(())
    }
    fn write_file<A, E: std::error::Error, F: FnOnce(&mut dyn std::io::Write) -> Result<A, E>>(
        &mut self,
        file: &str,
        writer: F,
    ) -> Result<A, WriteError<E>> {
        match self.get_file_mut(file) {
            Some(Inode::File {
                ref mut contents, ..
            }) => {
                contents.clear();
                writer(contents).map_err(WriteError::E)
            }
            None => {
                let mut contents = Vec::new();
                let last_modified = SystemTime::now();
                let a = writer(&mut contents).map_err(WriteError::E)?;
                self.add_inode(
                    file,
                    Inode::File {
                        meta: InodeMetadata::new(0o644, false),
                        contents,
                        last_modified,
                    },
                );
                Ok(a)
            }
            _ => panic!("not a file: {:?}", file),
        }
    }
}
