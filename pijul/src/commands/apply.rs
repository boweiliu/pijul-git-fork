use std::collections::{HashMap, HashSet};
use std::path::PathBuf;

use anyhow::bail;
use clap::Clap;
use libpijul::changestore::ChangeStore;
use libpijul::{DepsTxnT, GraphTxnT, MutTxnT, MutTxnTExt, TxnT};

use crate::repository::Repository;

#[derive(Clap, Debug)]
pub struct Apply {
    /// Set the repository where this command should run. Defaults to the first ancestor of the current directory that contains a `.pijul` directory.
    #[clap(long = "repository")]
    repo_path: Option<PathBuf>,
    /// Apply change to this channel
    #[clap(long = "channel")]
    channel: Option<String>,
    /// Only apply the dependencies of the change, not the change itself. Only applicable for a single change.
    #[clap(long = "deps-only")]
    deps_only: bool,
    /// The change that need to be applied. If this value is missing, read the change in text format on the standard input.
    change: Vec<String>,
}

impl Apply {
    pub async fn run(self) -> Result<(), anyhow::Error> {
        let mut repo = Repository::find_root(self.repo_path).await?;
        let mut txn = repo.pristine.mut_txn_begin();
        let channel_name = repo.config.get_current_channel(self.channel.as_deref());
        let mut channel = if let Some(channel) = txn.load_channel(&channel_name)? {
            channel
        } else {
            txn.open_or_create_channel(&channel_name)?
        };
        let mut hashes = Vec::new();
        for ch in self.change.iter() {
            hashes.push(if let Ok(h) = txn.hash_from_prefix(ch) {
                h.0
            } else {
                let change = libpijul::change::Change::deserialize(&ch, None)?;
                repo.changes.save_change(&change)?
            })
        }
        if hashes.is_empty() {
            let mut change = std::io::BufReader::new(std::io::stdin());
            let change = libpijul::change::Change::read(&mut change, &mut HashMap::new())?;
            hashes.push(repo.changes.save_change(&change)?)
        }
        if self.deps_only {
            if hashes.len() > 1 {
                bail!("--deps-only is only applicable to a single change")
            }
            txn.apply_deps_rec(&repo.changes, &mut channel, hashes.pop().unwrap())?;
        } else {
            for hash in hashes.drain(..) {
                txn.apply_change_rec(&repo.changes, &mut channel, hash)?;
            }
        }

        let mut touched = HashSet::new();
        for d in hashes.iter() {
            if let Some(int) = txn.get_internal(*d)? {
                for inode in txn.iter_rev_touched(int)? {
                    let (int_, inode) = inode?;
                    if int_ < int {
                        continue;
                    } else if int_ > int {
                        break;
                    }
                    touched.insert(inode);
                }
            }
        }

        for i in touched {
            let (path, _) =
                libpijul::fs::find_path(&repo.changes, &txn, &channel.borrow(), false, i)?;
            txn.output_repository_no_pending(
                &mut repo.working_copy,
                &repo.changes,
                &mut channel,
                &path,
                true,
                None,
            )?;
        }
        txn.commit()?;
        repo.lock.commit().await?;
        Ok(())
    }
}
