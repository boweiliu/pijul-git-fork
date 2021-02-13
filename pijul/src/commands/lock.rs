use clap::Clap;
use fs2::FileExt;
use std::fs::OpenOptions;
use std::path::PathBuf;
use std::sync::Arc;
use tokio::io::{AsyncReadExt, AsyncWriteExt};
use tokio::net::UnixListener;
use tokio::sync::{mpsc, watch, Mutex};

#[derive(Clap, Debug)]
pub struct Lock {
    path: PathBuf,
}

const COMMIT: u8 = 2;
const ACK: u8 = 3;
const LOCKED: u8 = 4;

impl Lock {
    pub async fn run(self) -> Result<(), anyhow::Error> {
        if let Some(p) = self.path.parent() {
            std::fs::create_dir_all(p)?
        }
        self.run_socket().await
    }

    async fn run_socket(self) -> Result<(), anyhow::Error> {
        let lock = self.path.with_extension("lock");
        let file = OpenOptions::new().write(true).create(true).open(&lock)?;
        if file.try_lock_exclusive().is_err() {
            return Ok(());
        }
        std::fs::remove_file(&self.path).unwrap_or(());
        let listener = UnixListener::bind(&self.path);
        println!();
        let listener = if let Ok(listener) = listener {
            listener
        } else {
            return Ok(());
        };
        let (tx, active_at_last_commit) = watch::channel(0);
        let (done_tx, mut done_rx) = mpsc::channel(1);
        let file = Arc::new(self.path);
        let locks = Locks {
            n_clients: Arc::new(Mutex::new(0usize)),
            muttxn: Arc::new(Mutex::new(())),
            tx: Arc::new(tx),
            active_at_last_commit,
            file: file.clone(),
            clock: Arc::new(Mutex::new(0usize)),
            txn_counter: Arc::new(Mutex::new(0usize)),
            done_tx,
        };
        loop {
            tokio::select! {
                x = tokio::time::timeout(std::time::Duration::from_secs(1), listener.accept()) => {
                    match x {
                        Err(_) => {
                            if *locks.n_clients.lock().await == 0 {
                                break
                            }
                        }
                        Ok(Ok((stream, _))) => {
                            accept(stream, locks.clone()).await
                        }
                        Ok(Err(_)) => break
                    }
                },
                _ = done_rx.recv() => {
                    break
                }
            }
        }
        std::fs::remove_file(file.as_ref()).unwrap_or(());
        Ok(())
    }
}

#[derive(Clone)]
struct Locks {
    n_clients: Arc<Mutex<usize>>,
    file: Arc<PathBuf>,
    muttxn: Arc<Mutex<()>>,
    clock: Arc<Mutex<usize>>,
    txn_counter: Arc<Mutex<usize>>,
    active_at_last_commit: watch::Receiver<usize>,
    tx: Arc<watch::Sender<usize>>,
    done_tx: mpsc::Sender<()>,
}

async fn accept(mut stream: tokio::net::UnixStream, mut locks: Locks) {
    *locks.n_clients.lock().await += 1;
    tokio::spawn(async move {
        let mut t = [0u8];
        while let Ok(n) = stream.read(&mut t).await {
            if n == 0 {
                break;
            }
            if t[0] == 1 {
                // muttxn
                let lock = if let Ok(guard) = locks.muttxn.try_lock() {
                    guard
                } else {
                    stream.write_all(&[LOCKED]).await.unwrap_or(());
                    locks.muttxn.lock().await
                };
                while *locks.active_at_last_commit.borrow() > 0 {
                    stream.write_all(&[LOCKED]).await.unwrap_or(());
                    locks.active_at_last_commit.changed().await.unwrap();
                }
                stream.write_all(&[ACK]).await.unwrap_or(());
                if let Ok(n) = stream.read(&mut t).await {
                    if n == 0 {
                        break;
                    }
                    if t[0] == COMMIT {
                        // commit
                        let mut clock = locks.clock.lock().await;
                        *clock += 1;
                        let counter = *locks.txn_counter.lock().await;
                        locks.tx.send(counter).unwrap();
                    }
                }
                std::mem::drop(lock)
            } else {
                // txn
                *locks.txn_counter.lock().await += 1;
                let start_date = *locks.clock.lock().await;
                stream.write_all(&[ACK]).await.unwrap_or(());
                let n = stream.read(&mut t).await.unwrap_or(0);
                if n == 0 {
                    break;
                }
                *locks.txn_counter.lock().await -= 1;
                if start_date < *locks.clock.lock().await {
                    let last = *locks.active_at_last_commit.borrow();
                    locks.tx.send(last - 1).unwrap();
                }
            }
        }
        if *locks.n_clients.lock().await == 1 {
            tokio::time::sleep(std::time::Duration::from_secs(1)).await;
            if *locks.n_clients.lock().await == 1 {
                locks.done_tx.send(()).await.unwrap();
                return;
            }
        }
        *locks.n_clients.lock().await -= 1
    });
}
