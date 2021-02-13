use super::inode::*;
use crate::small_string::*;

/// A key in the file tree, i.e. a directory (`parent_inode`) and the
/// name of the child (file or directory).
#[doc(hidden)]
#[derive(Debug, Hash, Eq, PartialEq, Clone, PartialOrd, Ord)]
pub struct OwnedPathId {
    /// The parent of this path.
    pub parent_inode: Inode,
    /// Name of the file.
    pub basename: SmallString,
}

impl OwnedPathId {
    pub fn as_file_id(&self) -> PathId {
        PathId {
            parent_inode: self.parent_inode,
            basename: self.basename.as_small_str(),
        }
    }
}

/// A borrow on a [`OwnedPathId`](struct.OwnedPathId.html).
#[derive(Debug, Eq, PartialEq, Ord, PartialOrd, Clone, Copy)]
#[doc(hidden)]
pub struct PathId<'a> {
    pub parent_inode: Inode,
    pub basename: SmallStr<'a>,
}

impl<'a> PathId<'a> {
    /// Make an owned version of this `PathId`.
    pub fn to_owned(&self) -> OwnedPathId {
        OwnedPathId {
            parent_inode: self.parent_inode.clone(),
            basename: self.basename.to_owned(),
        }
    }
}
