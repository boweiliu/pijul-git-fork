/// A unique identifier for files or directories in the actual
/// file system, to map "files from the graph" to real files.
#[derive(Clone, Copy, PartialEq, PartialOrd, Eq, Ord, Hash)]
pub struct Inode(pub(in crate::pristine) u64);

impl std::fmt::Debug for Inode {
    fn fmt(&self, fmt: &mut std::fmt::Formatter) -> std::fmt::Result {
        use byteorder::{ByteOrder, LittleEndian};
        let mut b = [0; 8];
        LittleEndian::write_u64(&mut b, self.0);
        write!(fmt, "Inode({})", data_encoding::BASE32_NOPAD.encode(&b))
    }
}

impl Inode {
    pub const ROOT: Inode = Inode(0);
    pub fn is_root(&self) -> bool {
        *self == Inode::ROOT
    }
    pub(crate) fn random() -> Self {
        Inode(rand::random())
    }
}
