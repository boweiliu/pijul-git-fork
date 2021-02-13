use anyhow::bail;
use std::path::Path;
use tokio::io::{AsyncReadExt, AsyncWriteExt};
use tokio::net::UnixStream;

pub struct TxnLock {
    _stream: UnixStream,
}

pub struct MutTxnLock {
    stream: UnixStream,
}

const TXN_BEGIN: u8 = 0;
const MUT_TXN_BEGIN: u8 = 1;
const COMMIT: u8 = 2;
const ACK: u8 = 3;

async fn start_stream_if_needed(file: &Path) -> Result<UnixStream, std::io::Error> {
    if let Ok(stream) = UnixStream::connect(file).await {
        Ok(stream)
    } else {
        let cmd = std::env::args().next().unwrap();
        let mut process = tokio::process::Command::new(&cmd)
            .args(&["lock", file.to_str().unwrap()])
            .stdout(std::process::Stdio::piped())
            .stdin(std::process::Stdio::piped())
            .stderr(std::process::Stdio::piped())
            .spawn()?;
        let s = process.stdout.as_mut().unwrap();
        if let Err(e) = s.read_exact(&mut [0u8]).await {
            process.wait().await?;
            return Err(e);
        }
        UnixStream::connect(file).await
    }
}

pub async fn mut_txn<P: AsRef<Path>>(file: P) -> Result<MutTxnLock, anyhow::Error> {
    let mut stream = start_stream_if_needed(file.as_ref()).await?;
    stream.writable().await?;
    stream.write_all(&[MUT_TXN_BEGIN]).await?;
    let mut t = [0u8];
    stream.read_exact(&mut t).await?;
    if t[0] == ACK {
        Ok(MutTxnLock { stream })
    } else {
        bail!("Pristine locked")
    }
}

pub async fn txn<P: AsRef<Path>>(file: P) -> Result<TxnLock, anyhow::Error> {
    let mut stream = start_stream_if_needed(file.as_ref()).await?;
    stream.writable().await?;
    stream.write_all(&[TXN_BEGIN]).await?;
    let mut t = [0u8];
    stream.read_exact(&mut t).await?;
    if t[0] == ACK {
        Ok(TxnLock { _stream: stream })
    } else {
        bail!("Pristine locked")
    }
}

impl MutTxnLock {
    pub async fn commit(&mut self) -> Result<(), anyhow::Error> {
        self.stream.write_all(&[COMMIT]).await?;
        Ok(())
    }
}
