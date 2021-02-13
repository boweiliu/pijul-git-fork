use fs2::FileExt;
use std::fs::OpenOptions;
use std::path::Path;

pub struct TxnLock {
    file: std::fs::File,
}

pub struct MutTxnLock {
    file: std::fs::File,
}

pub async fn mut_txn<P: AsRef<Path>>(file: P) -> Result<MutTxnLock, anyhow::Error> {
    let file = OpenOptions::new().write(true).create(true).open(file)?;
    file.lock_exclusive()?;
    Ok(MutTxnLock { file })
}

pub async fn txn<P: AsRef<Path>>(file: P) -> Result<TxnLock, anyhow::Error> {
    let file = OpenOptions::new().write(true).create(true).open(file)?;
    file.lock_shared()?;
    Ok(TxnLock { file })
}

impl MutTxnLock {
    pub async fn commit(&mut self) -> Result<(), anyhow::Error> {
        Ok(self.file.unlock()?)
    }
}

impl Drop for MutTxnLock {
    fn drop(&mut self) {
        self.file.unlock().unwrap_or(())
    }
}

impl Drop for TxnLock {
    fn drop(&mut self) {
        self.file.unlock().unwrap_or(())
    }
}
