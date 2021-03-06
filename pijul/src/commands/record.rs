use std::collections::{HashMap, HashSet};
use std::io::Write;
use std::path::PathBuf;

use anyhow::bail;
use canonical_path::{CanonicalPath, CanonicalPathBuf};
use chrono::Utc;
use clap::Clap;
use libpijul::change::*;
use libpijul::changestore::*;
use libpijul::pristine::ChannelMutTxnT;
use libpijul::{Base32, ChannelRef, ChannelTxnT, MutTxnT, MutTxnTExt, TxnT, TxnTExt};
use log::{debug, error};
use serde_derive::{Deserialize, Serialize};
use thrussh_keys::PublicKeyBase64;

use crate::repository::*;

#[derive(Clap, Debug)]
pub struct Record {
    /// Record all paths that have changed
    #[clap(short = 'a', long = "all")]
    pub all: bool,
    /// Set the change message
    #[clap(short = 'm', long = "message")]
    pub message: Option<String>,
    /// Set the author field
    #[clap(long = "author")]
    pub author: Option<String>,
    /// Record the change in this channel instead of the current channel
    #[clap(long = "channel")]
    pub channel: Option<String>,
    /// Set the repository where this command should run. Defaults to the first ancestor of the current directory that contains a `.pijul` directory.
    #[clap(long = "repository")]
    pub repo_path: Option<PathBuf>,
    /// Set the timestamp field
    #[clap(long = "timestamp")]
    pub timestamp: Option<i64>,
    /// Sign the change with the default key
    #[clap(short = 'S')]
    pub sign: bool,
    #[clap(long = "tag")]
    pub tag: bool,
    /// Ignore missing (deleted) files
    #[clap(long = "ignore-missing")]
    pub ignore_missing: bool,
    #[clap(long = "working-copy")]
    pub working_copy: Option<String>,
    /// Amend this change instead of creating a new change
    #[clap(long = "amend")]
    #[allow(clippy::option_option)]
    pub amend: Option<Option<String>>,
    /// Paths in which to record the changes
    pub prefixes: Vec<PathBuf>,
}

impl Record {
    pub async fn run(self) -> Result<(), anyhow::Error> {
        let mut repo = Repository::find_root(self.repo_path.clone()).await?;
        let mut stdout = std::io::stdout();
        let mut stderr = std::io::stderr();

        for h in repo.config.hooks.record.iter() {
            h.run()?
        }
        let mut txn = repo.pristine.mut_txn_begin();
        let mut channel =
            txn.open_or_create_channel(repo.config.get_current_channel(self.channel.as_deref()))?;
        let sign = self.sign;

        let mut extra = Vec::new();
        for h in repo.config.extra_dependencies.iter() {
            let (h, c) = txn.hash_from_prefix(h)?;
            if txn
                .get_changeset(txn.changes(&channel.borrow()), c)?
                .is_none()
            {
                bail!(
                    "Change {:?} (from .pijul/config) is not on channel {:?}",
                    h,
                    channel.borrow().name
                )
            }
            extra.push(h)
        }

        let header = if let Some(ref amend) = self.amend {
            let h = if let Some(ref hash) = amend {
                txn.hash_from_prefix(hash)?.0
            } else if let Some(h) = txn.reverse_log(&channel.borrow(), None)?.next() {
                (h?.1).0
            } else {
                return Ok(());
            };
            let header = if let Some(message) = self.message.clone() {
                ChangeHeader {
                    message,
                    ..repo.changes.get_header(&h)?
                }
            } else {
                repo.changes.get_header(&h)?
            };

            txn.unrecord(&repo.changes, &mut channel, &h)?;
            header
        } else {
            self.header()
        };
        let no_prefixes =
            self.prefixes.is_empty() && !self.ignore_missing && self.working_copy.is_none();
        let (repo_path, mut working_copy) = if let Some(ref w) = self.working_copy {
            (
                CanonicalPathBuf::canonicalize(w)?,
                Some(libpijul::working_copy::filesystem::FileSystem::from_root(w)),
            )
        } else {
            (CanonicalPathBuf::canonicalize(&repo.path)?, None)
        };
        let result = self.record(
            &mut txn,
            &mut channel,
            working_copy.as_mut().unwrap_or(&mut repo.working_copy),
            &repo.changes,
            repo_path,
            header,
            &extra,
        )?;
        if let Some((mut change, updates, hash, oldest)) = result {
            let hash = hash.unwrap();
            if sign {
                let mut key_path = dirs_next::home_dir().unwrap().join(".ssh");
                match sign_hash(&mut key_path, hash).await? {
                    Some((pk, signature)) if !signature.is_empty() => {
                        let sig = toml::Value::try_from(vec![Signature {
                            public_key: pk,
                            timestamp: change.header.timestamp,
                            signature,
                        }])?;
                        let mut toml = toml::map::Map::new();
                        toml.insert("signatures".to_string(), sig);
                        change.unhashed = Some(toml.into());
                        let hash2 = repo.changes.save_change(&change).unwrap();
                        assert_eq!(hash2, hash);
                    }
                    _ => {
                        bail!("Could not sign the change");
                    }
                }
            }
            txn.apply_local_change(&mut channel, &change, hash, &updates)?;
            writeln!(stdout, "Hash: {}", hash.to_base32())?;
            let oldest = if let Ok(t) = oldest.duration_since(std::time::SystemTime::UNIX_EPOCH) {
                t.as_secs() as u64
            } else {
                0
            };
            if no_prefixes {
                txn.touch_channel(&mut channel.borrow_mut(), Some(oldest));
            }
            txn.commit()?;
            repo.lock.commit().await?;
        } else {
            if no_prefixes {
                let now = std::time::SystemTime::now();
                txn.touch_channel(&mut channel.borrow_mut(), None);
                txn.commit()?;
                repo.lock.commit().await?;
                debug!("commit: {:?}", now.elapsed());
            }
            writeln!(stderr, "Nothing to record")?;
        }
        Ok(())
    }

    fn header(&self) -> ChangeHeader {
        let authors = if let Some(ref a) = self.author {
            vec![libpijul::change::Author {
                name: a.clone(),
                full_name: None,
                email: None,
            }]
        } else if let Ok(global) = crate::config::Global::load() {
            vec![global.author]
        } else {
            Vec::new()
        };
        ChangeHeader {
            message: self.message.clone().unwrap_or_else(String::new),
            authors,
            description: None,
            timestamp: if let Some(t) = self.timestamp {
                chrono::DateTime::from_utc(chrono::NaiveDateTime::from_timestamp(t, 0), chrono::Utc)
            } else {
                Utc::now()
            },
        }
    }

    fn fill_relative_prefixes(&mut self) -> Result<(), anyhow::Error> {
        let cwd = std::env::current_dir()?;
        for p in self.prefixes.iter_mut() {
            if p.is_relative() {
                *p = cwd.join(&p);
            }
        }
        Ok(())
    }

    fn record<T: TxnTExt + MutTxnTExt, C: ChangeStore>(
        mut self,
        txn: &mut T,
        channel: &mut ChannelRef<T>,
        working_copy: &mut libpijul::working_copy::FileSystem,
        changes: &C,
        repo_path: CanonicalPathBuf,
        header: ChangeHeader,
        extra_deps: &[libpijul::Hash],
    ) -> Result<
        Option<(
            Change,
            HashMap<usize, libpijul::InodeUpdate>,
            Option<libpijul::Hash>,
            std::time::SystemTime,
        )>,
        anyhow::Error,
    > {
        let mut state = libpijul::RecordBuilder::new();
        if self.ignore_missing {
            state.ignore_missing = true;
        }
        if self.prefixes.is_empty() {
            if self.ignore_missing {
                for f in ignore::Walk::new(&repo_path) {
                    let f = f?;
                    if f.metadata()?.is_file() {
                        let p = CanonicalPath::new(f.path())?;
                        let p = p.as_path().strip_prefix(&repo_path).unwrap();
                        txn.record(
                            &mut state,
                            libpijul::Algorithm::default(),
                            channel,
                            working_copy,
                            changes,
                            p.to_str().unwrap(),
                        )?
                    }
                }
            } else {
                txn.record(
                    &mut state,
                    libpijul::Algorithm::default(),
                    channel,
                    working_copy,
                    changes,
                    "",
                )?
            }
        } else {
            self.fill_relative_prefixes()?;
            working_copy.record_prefixes(
                txn,
                channel,
                changes,
                &mut state,
                repo_path,
                &self.prefixes,
                num_cpus::get(),
            )?;
        }
        let mut rec = state.finish();
        if rec.actions.is_empty() {
            return Ok(None);
        }
        let actions = rec
            .actions
            .into_iter()
            .map(|rec| rec.globalize(txn).unwrap())
            .collect();
        let mut change =
            LocalChange::make_change(txn, channel, actions, rec.contents, header, Vec::new())?;

        let current: HashSet<_> = change.dependencies.iter().cloned().collect();
        for dep in extra_deps.iter() {
            if !current.contains(dep) {
                change.dependencies.push(*dep)
            }
        }

        let file_name = |local: &Local, _| -> String { format!("{}:{}", local.path, local.line) };
        debug!("has_binary = {:?}", rec.has_binary_files);
        let mut change = if self.all {
            change
        } else if rec.has_binary_files {
            bail!("Cannot record a binary change interactively. Please use -a.")
        } else {
            let mut o = Vec::new();
            change.write(changes, None, file_name, true, &mut o)?;

            let mut with_errors: Option<Vec<u8>> = None;
            let change = loop {
                let mut bytes = if let Some(ref o) = with_errors {
                    edit::edit_bytes(&o[..])?
                } else {
                    edit::edit_bytes(&o[..])?
                };
                if bytes.iter().all(|c| (*c as char).is_whitespace()) {
                    bail!("Empty change")
                }
                let mut change = std::io::BufReader::new(std::io::Cursor::new(&bytes));
                if let Ok(change) =
                    Change::read_and_deps(&mut change, &mut rec.updatables, txn, channel)
                {
                    break change;
                }

                let mut err = SYNTAX_ERROR.as_bytes().to_vec();
                err.append(&mut bytes);
                with_errors = Some(err)
            };
            if change.changes.is_empty() {
                bail!("Empty change")
            }
            change
        };

        let current: HashSet<_> = change.dependencies.iter().cloned().collect();
        for dep in extra_deps.iter() {
            if !current.contains(dep) {
                change.dependencies.push(*dep)
            }
        }

        if change.header.message.trim().is_empty() {
            bail!("No change message")
        }
        debug!("saving change");
        let hash = changes.save_change(&change).unwrap();
        debug!("saved");
        Ok(Some((
            change,
            rec.updatables,
            Some(hash),
            rec.oldest_change,
        )))
    }
}

#[derive(Debug, Serialize, Deserialize)]
struct Signature {
    public_key: String,
    timestamp: chrono::DateTime<chrono::Utc>,
    signature: String,
}

async fn sign_hash(
    key_path: &mut PathBuf,
    hash: libpijul::Hash,
) -> Result<Option<(String, String)>, anyhow::Error> {
    let to_sign = hash.to_bytes();
    match thrussh_keys::agent::client::AgentClient::connect_env().await {
        Ok(agent) => {
            let mut agent = Some(agent);
            for k in &["id_ed25519.pub", "id_rsa.pub"] {
                key_path.push(k);
                if let Ok(key) = thrussh_keys::load_public_key(&key_path) {
                    debug!("key");
                    if let Some(a) = agent.take() {
                        debug!("authenticate future");
                        if let (_, Ok(sig)) = a.sign_request_base64(&key, &to_sign).await {
                            key_path.pop();
                            let key = key.public_key_base64();
                            return Ok(Some((key, sig)));
                        }
                    }
                }
                key_path.pop();
            }
        }
        Err(e) => {
            error!("{:?}", e);
        }
    }
    for k in &["id_ed25519", "id_rsa"] {
        key_path.push(k);
        if let Some(k) = crate::remote::ssh::load_secret_key(&key_path, k) {
            key_path.pop();
            let pk = k.public_key_base64();
            return Ok(Some((pk, k.sign_detached(&to_sign)?.to_base64())));
        } else {
            key_path.pop();
        }
    }
    Ok(None)
}

const SYNTAX_ERROR: &str = "# Syntax errors, please try again.
# Alternatively, you may delete the entire file (including this
# comment to abort).
";
