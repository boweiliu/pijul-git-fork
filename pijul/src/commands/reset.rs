use std::collections::HashSet;
use std::path::PathBuf;

use anyhow::bail;
use canonical_path::CanonicalPathBuf;
use clap::Clap;
use libpijul::pristine::{ChangeId, ChannelMutTxnT, Position};
use libpijul::{ChannelTxnT, DepsTxnT, MutTxnT, MutTxnTExt, TxnT, TxnTExt};
use log::debug;

use crate::repository::Repository;

#[derive(Clap, Debug)]
pub struct Reset {
    /// Set the repository where this command should run. Defaults to the first ancestor of the current directory that contains a `.pijul` directory.
    #[clap(long = "repository")]
    pub repo_path: Option<PathBuf>,
    /// Reset the working copy to this channel, and change the current channel to this channel.
    #[clap(long = "channel")]
    pub channel: Option<String>,
    /// Print this file to the standard output, without modifying the repository (works for a single file only).
    #[clap(long = "dry-run")]
    pub dry_run: bool,
    /// Only reset these files
    pub files: Vec<PathBuf>,
}

impl Reset {
    pub async fn run(self) -> Result<(), anyhow::Error> {
        self.reset(true).await
    }

    pub async fn switch(self) -> Result<(), anyhow::Error> {
        self.reset(false).await
    }

    async fn reset(self, overwrite_changes: bool) -> Result<(), anyhow::Error> {
        let has_repo_path = self.repo_path.is_some();
        let mut repo = Repository::find_root(self.repo_path).await?;
        let mut txn = repo.pristine.mut_txn_begin();
        let channel_name = repo.config.get_current_channel(self.channel.as_deref());
        let repo_path = CanonicalPathBuf::canonicalize(&repo.path)?;
        let mut channel = if let Some(channel) = txn.load_channel(&channel_name)? {
            channel
        } else {
            bail!("No such channel: {:?}", channel_name)
        };
        if self.dry_run {
            if self.files.len() != 1 {
                bail!("reset --dry-run needs exactly one file");
            }
            let (pos, _ambiguous) = if has_repo_path {
                let root = std::fs::canonicalize(repo.path.join(&self.files[0]))?;
                let path = root.strip_prefix(&repo_path)?.to_str().unwrap();
                txn.follow_oldest_path(&repo.changes, &channel, &path)?
            } else {
                let mut root = crate::current_dir()?;
                root.push(&self.files[0]);
                let root = std::fs::canonicalize(&root)?;
                let path = root.strip_prefix(&repo_path)?.to_str().unwrap();
                txn.follow_oldest_path(&repo.changes, &channel, &path)?
            };
            txn.output_file(
                &repo.changes,
                &channel,
                pos,
                &mut libpijul::vertex_buffer::Writer::new(std::io::stdout()),
            )?;
        } else {
            let current_channel = repo.config.get_current_channel(None);
            if self.channel.as_deref() == Some(current_channel) {
                if !overwrite_changes {
                    return Ok(());
                }
            } else if self.channel.is_some() {
                if let Some(mut channel) = txn.load_channel(current_channel)? {
                    let mut state = libpijul::RecordBuilder::new();
                    txn.record(
                        &mut state,
                        libpijul::Algorithm::default(),
                        &mut channel,
                        &mut repo.working_copy,
                        &repo.changes,
                        "",
                    )?;
                    let rec = state.finish();
                    debug!("actions = {:?}", rec.actions);
                    if !rec.actions.is_empty() {
                        bail!("Cannot change channel, as there are unrecorded changes.")
                    }
                }
            }

            let now = std::time::Instant::now();
            if self.files.is_empty() {
                if self.channel.is_none() || self.channel.as_deref() == Some(current_channel) {
                    let last_modified = last_modified(&txn, &channel.borrow());
                    txn.output_repository_no_pending(
                        &mut repo.working_copy,
                        &repo.changes,
                        &mut channel,
                        "",
                        true,
                        Some(last_modified),
                    )?;
                    txn.touch_channel(&mut channel.borrow_mut(), None);
                    txn.commit()?;
                    repo.lock.commit().await?;
                    return Ok(());
                }
                let mut inodes = HashSet::new();
                if let Some(cur) = txn.load_channel(current_channel)? {
                    let mut changediff = HashSet::new();
                    let (a, b, s) = libpijul::pristine::last_common_state(
                        &txn,
                        &cur.borrow(),
                        &channel.borrow(),
                    )?;
                    debug!("last common state {:?}", s);
                    changes_after(&txn, &cur.borrow(), a, &mut changediff, &mut inodes)?;
                    changes_after(&txn, &channel.borrow(), b, &mut changediff, &mut inodes)?;
                }

                if self.channel.is_some() {
                    repo.config.current_channel = self.channel;
                    repo.save_config()?;
                }

                for pos in inodes.iter() {
                    let (path, _) = libpijul::fs::find_path(
                        &repo.changes,
                        &txn,
                        &channel.borrow(),
                        false,
                        *pos,
                    )?;
                    debug!("resetting {:?}", path);
                    txn.output_repository_no_pending(
                        &mut repo.working_copy,
                        &repo.changes,
                        &mut channel,
                        &path,
                        true,
                        None,
                    )?;
                }
            } else {
                for root in self.files.iter() {
                    let root = std::fs::canonicalize(&root)?;
                    let path = root.strip_prefix(&repo_path)?.to_str().unwrap();
                    txn.output_repository_no_pending(
                        &mut repo.working_copy,
                        &repo.changes,
                        &mut channel,
                        &path,
                        true,
                        None,
                    )?;
                }
            }
            txn.commit()?;
            repo.lock.commit().await?;
            debug!("now = {:?}", now.elapsed());
        }
        let locks = libpijul::TIMERS.lock().unwrap();
        debug!(
            "retrieve: {:?}, graph: {:?}, output: {:?}",
            locks.alive_retrieve, locks.alive_graph, locks.alive_output,
        );
        Ok(())
    }
}

fn changes_after<T: ChannelTxnT + DepsTxnT>(
    txn: &T,
    chan: &T::Channel,
    from: u64,
    changediff: &mut HashSet<ChangeId>,
    inodes: &mut HashSet<Position<ChangeId>>,
) -> Result<(), anyhow::Error> {
    for x in libpijul::pristine::changeid_log(txn, chan, from)? {
        let (n, (u, _)) = x?;
        debug!("{:?} {:?} {:?}", n, u, from);
        if n <= from {
            continue;
        }
        if changediff.insert(u) {
            for y in txn.iter_rev_touched_files(u, None)? {
                let (uu, pos) = y?;
                if uu < u {
                    continue;
                } else if uu > u {
                    break;
                }
                inodes.insert(pos);
            }
        }
    }
    Ok(())
}

fn last_modified<T: ChannelTxnT>(txn: &T, channel: &T::Channel) -> std::time::SystemTime {
    std::time::SystemTime::UNIX_EPOCH + std::time::Duration::from_secs(txn.last_modified(channel))
}
