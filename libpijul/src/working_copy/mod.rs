use crate::pristine::InodeMetadata;

#[cfg(feature = "ondisk-repos")]
pub mod filesystem;
#[cfg(feature = "ondisk-repos")]
pub use filesystem::FileSystem;

pub mod memory;
pub use memory::Memory;

#[derive(Debug, Error)]
pub enum WriteError<E: std::error::Error + 'static> {
    #[error(transparent)]
    E(E),
    #[error(transparent)]
    Io(#[from] std::io::Error),
}

pub trait WorkingCopy {
    type Error: std::error::Error;
    fn create_dir_all(&mut self, path: &str) -> Result<(), Self::Error>;
    fn file_metadata(&self, file: &str) -> Result<InodeMetadata, Self::Error>;
    fn read_file(&self, file: &str, buffer: &mut Vec<u8>) -> Result<(), Self::Error>;
    fn modified_time(&self, file: &str) -> Result<std::time::SystemTime, Self::Error>;
    fn remove_path(&mut self, name: &str) -> Result<(), Self::Error>;
    fn rename(&mut self, former: &str, new: &str) -> Result<(), Self::Error>;
    fn set_permissions(&mut self, name: &str, permissions: u16) -> Result<(), Self::Error>;
    fn write_file<A, E: std::error::Error, F: FnOnce(&mut dyn std::io::Write) -> Result<A, E>>(
        &mut self,
        file: &str,
        writer: F,
    ) -> Result<A, WriteError<E>>;
}
