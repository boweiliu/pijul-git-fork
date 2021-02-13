use std::path::PathBuf;

use super::{make_changelist, parse_changelist};
use anyhow::{anyhow, bail};
use clap::Clap;
use libpijul::changestore::ChangeStore;
use libpijul::*;
use log::debug;

use crate::repository::Repository;

#[derive(Clap, Debug)]
pub struct Unrecord {
    /// Set the repository where this command should run. Defaults to the first ancestor of the current directory that contains a `.pijul` directory.
    #[clap(long = "repository")]
    repo_path: Option<PathBuf>,
    /// Unrecord changes from this channel instead of the current channel
    #[clap(long = "channel")]
    channel: Option<String>,
    /// Also undo the changes in the working copy (preserving unrecorded changes if there are any)
    #[clap(long = "reset")]
    reset: bool,
    /// Show N changes in a text editor if no <change-id>s were given.
    /// Defaults to the value
    /// of `unrecord_changes` in your global configuration.
    #[clap(long = "show-changes", value_name = "N", conflicts_with("change-id"))]
    show_changes: Option<usize>,
    /// The hash of a change (unambiguous prefixes are accepted)
    #[clap(multiple = true)]
    change_id: Vec<String>,
}

impl Unrecord {
    pub async fn run(self) -> Result<(), anyhow::Error> {
        let mut repo = Repository::find_root(self.repo_path).await?;
        debug!("{:?}", repo.config);
        let channel_name = repo.config.get_current_channel(self.channel.as_deref());
        let mut txn = repo.pristine.mut_txn_begin();
        if let Some(mut channel) = txn.load_channel(channel_name)? {
            let pending_hash = if self.reset {
                super::pending(&mut txn, &mut channel, &mut repo)?
            } else {
                None
            };

            let mut hashes = Vec::new();

            if self.change_id.is_empty() {
                // No change ids were given, present a list for choosing
                // The number can be set in the global config or passed as a command-line option
                let number_of_changes = if let Some(n) = self.show_changes {
                    n
                } else {
                    let cfg = crate::config::Global::load()?;
                    cfg.unrecord_changes.ok_or_else(|| {
                        anyhow!(
                            "Can't determine how many changes to show. \
                            Please set the `unrecord_changes` option in \
                            your global config or run `pijul unrecord` \
                            with the `--show-changes` option."
                        )
                    })?
                };
                let hashes_ = txn
                    .reverse_log(&channel.borrow(), None)?
                    .map(|h| (h.unwrap().1).0)
                    .take(number_of_changes)
                    .collect::<Vec<_>>();
                let o = make_changelist(&repo.changes, &hashes_, "unrecord")?;
                for h in parse_changelist(&edit::edit_bytes(&o[..])?).iter() {
                    hashes.push((*h, txn.get_internal(*h)?.unwrap()))
                }
            } else {
                for c in self.change_id.iter() {
                    let (hash, cid) = txn.hash_from_prefix(c)?;
                    hashes.push((hash, cid))
                }
            };
            let channel_ = channel.borrow();
            let mut changes = Vec::new();
            for (hash, change_id) in hashes {
                let n = txn
                    .get_changeset(txn.changes(&channel_), change_id)
                    .unwrap();
                changes.push((hash, change_id, n));
            }
            std::mem::drop(channel_);
            changes.sort_by(|a, b| b.2.cmp(&a.2));
            for (hash, change_id, _) in changes {
                let channel_ = channel.borrow();
                for p in txn.iter_revdep(change_id)? {
                    let (p, d) = p?;
                    if p < change_id {
                        continue;
                    } else if p > change_id {
                        break;
                    }
                    if txn.get_changeset(txn.changes(&channel_), d)?.is_some() {
                        let dep = txn.get_external(d)?.unwrap();
                        if Some(dep) == pending_hash {
                            bail!(
                                "Cannot unrecord change {} because unrecorded changes depend on it",
                                hash.to_base32()
                            );
                        } else {
                            bail!(
                                "Cannot unrecord change {} because {} depend on it",
                                hash.to_base32(),
                                dep.to_base32()
                            );
                        }
                    }
                }
                std::mem::drop(channel_);
                txn.unrecord(&repo.changes, &mut channel, &hash)?;
            }
            if self.reset {
                txn.output_repository_no_pending(
                    &mut repo.working_copy,
                    &repo.changes,
                    &mut channel,
                    "",
                    true,
                    None,
                )?;
            }
            if let Some(h) = pending_hash {
                txn.unrecord(&repo.changes, &mut channel, &h)?;
                if cfg!(feature = "keep-changes") {
                    repo.changes.del_change(&h)?;
                }
            }
        }
        txn.commit()?;
        repo.lock.commit().await?;
        Ok(())
    }
}
