use std::io::Write;
use std::path::PathBuf;

use anyhow::bail;
use libpijul::DOT_DIR;
use log::debug;

#[cfg(not(unix))]
mod basic_lock;
#[cfg(unix)]
mod unix_lock;

mod lock {
    #[cfg(not(unix))]
    pub use super::basic_lock::*;
    #[cfg(unix)]
    pub use super::unix_lock::*;
    use std::path::Path;
    pub enum Lock {
        Txn(TxnLock),
        MutTxn(MutTxnLock),
    }

    impl Lock {
        pub async fn mut_txn_lock<P: AsRef<Path>>(p: P) -> Result<Self, anyhow::Error> {
            let pp = p.as_ref().join("db_lock");
            Ok(Lock::MutTxn(mut_txn(&pp).await?))
        }
        pub async fn txn_lock<P: AsRef<Path>>(p: P) -> Result<Self, anyhow::Error> {
            let pp = p.as_ref().join("db_lock");
            Ok(Lock::Txn(txn(&pp).await?))
        }

        pub async fn commit(&mut self) -> Result<(), anyhow::Error> {
            match self {
                Lock::MutTxn(m) => m.commit().await,
                _ => Ok(()),
            }
        }
    }
}
use crate::{config, current_dir};

pub struct Repository {
    pub lock: lock::Lock,
    pub pristine: libpijul::pristine::sanakirja::Pristine,
    pub changes: libpijul::changestore::filesystem::FileSystem,
    pub working_copy: libpijul::working_copy::filesystem::FileSystem,
    pub config: config::Config,
    pub path: PathBuf,
    pub changes_dir: PathBuf,
}

pub const PRISTINE_DIR: &str = "pristine";
pub const CHANGES_DIR: &str = "changes";
pub const CONFIG_FILE: &str = "config";

impl Repository {
    pub fn save_config(&self) -> Result<(), anyhow::Error> {
        let config = toml::to_string(&self.config)?;
        let mut file = std::fs::File::create(&self.path.join(DOT_DIR).join(CONFIG_FILE))?;
        file.write_all(config.as_bytes())?;
        Ok(())
    }

    fn find_root_(cur: Option<PathBuf>, dot_dir: &str) -> Result<PathBuf, anyhow::Error> {
        let mut cur = if let Some(cur) = cur {
            cur
        } else {
            current_dir()?
        };
        cur.push(dot_dir);
        loop {
            debug!("{:?}", cur);
            if std::fs::metadata(&cur).is_err() {
                cur.pop();
                if cur.pop() {
                    cur.push(DOT_DIR);
                } else {
                    bail!("No Pijul repository found")
                }
            } else {
                break;
            }
        }
        Ok(cur)
    }

    pub async fn find_root(cur: Option<PathBuf>) -> Result<Self, anyhow::Error> {
        Self::find_root_with_dot_dir(cur, DOT_DIR, true).await
    }

    pub async unsafe fn find_root_immutable(cur: Option<PathBuf>) -> Result<Self, anyhow::Error> {
        Self::find_root_with_dot_dir(cur, DOT_DIR, false).await
    }

    pub async fn find_root_with_dot_dir(
        cur: Option<PathBuf>,
        dot_dir: &str,
        mutable: bool,
    ) -> Result<Self, anyhow::Error> {
        let cur = Self::find_root_(cur, dot_dir)?;
        let mut pristine_dir = cur.clone();
        pristine_dir.push(PRISTINE_DIR);
        let mut changes_dir = cur.clone();
        changes_dir.push(CHANGES_DIR);
        let mut working_copy_dir = cur.clone();
        working_copy_dir.pop();
        let config_path = cur.join(CONFIG_FILE);
        let config = if let Ok(config) = std::fs::read(&config_path) {
            if let Ok(toml) = toml::from_slice(&config) {
                toml
            } else {
                bail!("Could not read configuration file at {:?}", config_path)
            }
        } else {
            config::Config::default()
        };
        Ok(Repository {
            lock: if mutable {
                lock::Lock::mut_txn_lock(&pristine_dir).await?
            } else {
                lock::Lock::txn_lock(&pristine_dir).await?
            },
            pristine: unsafe {
                libpijul::pristine::sanakirja::Pristine::new_nolock(&pristine_dir)?
            },
            working_copy: libpijul::working_copy::filesystem::FileSystem::from_root(
                &working_copy_dir,
            ),
            changes: libpijul::changestore::filesystem::FileSystem::from_root(&working_copy_dir),
            config,
            path: working_copy_dir,
            changes_dir,
        })
    }

    pub async fn init(path: Option<std::path::PathBuf>) -> Result<Self, anyhow::Error> {
        let cur = if let Some(path) = path {
            path
        } else {
            current_dir()?
        };
        let mut pristine_dir = cur.clone();
        pristine_dir.push(DOT_DIR);
        pristine_dir.push(PRISTINE_DIR);
        if std::fs::metadata(&pristine_dir).is_err() {
            std::fs::create_dir_all(&pristine_dir)?;
            let mut changes_dir = cur.clone();
            changes_dir.push(DOT_DIR);
            changes_dir.push(CHANGES_DIR);
            Ok(Repository {
                lock: lock::Lock::mut_txn_lock(&pristine_dir).await?,
                pristine: unsafe {
                    libpijul::pristine::sanakirja::Pristine::new_nolock(&pristine_dir)?
                },
                working_copy: libpijul::working_copy::filesystem::FileSystem::from_root(&cur),
                changes: libpijul::changestore::filesystem::FileSystem::from_root(&cur),
                config: config::Config::default(),
                path: cur,
                changes_dir,
            })
        } else {
            bail!("Already in a repository")
        }
    }
}
