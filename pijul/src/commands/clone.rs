use std::path::PathBuf;

use crate::repository::*;
use anyhow::bail;
use clap::Clap;
use libpijul::{MutTxnT, MutTxnTExt};
use log::debug;

#[derive(Clap, Debug)]
pub struct Clone {
    /// Only download changes with alive contents
    #[clap(long = "lazy")]
    lazy: bool,
    /// Set the remote channel
    #[clap(long = "channel", default_value = crate::DEFAULT_CHANNEL)]
    channel: String,
    /// Clone this change and its dependencies
    #[clap(long = "change", conflicts_with = "state")]
    change: Option<String>,
    /// Clone this state
    #[clap(long = "state", conflicts_with = "change")]
    state: Option<String>,
    /// Clone this path only
    #[clap(long = "path", multiple(true))]
    partial_paths: Vec<String>,
    /// Do not check certificates (HTTPS remotes only, this option might be dangerous)
    #[clap(short = 'k')]
    no_cert_check: bool,
    /// Clone this remote
    remote: String,
    /// Path where to clone the repository.
    /// If missing, the inferred name of the remote repository is used.
    path: Option<PathBuf>,
}

impl Clone {
    pub async fn run(self) -> Result<(), anyhow::Error> {
        let mut remote =
            crate::remote::unknown_remote(None, &self.remote, &self.channel, self.no_cert_check)
                .await?;

        let path = if let Some(path) = self.path {
            if path.is_relative() {
                let mut p = std::env::current_dir()?;
                p.push(path);
                p
            } else {
                path
            }
        } else if let Some(path) = remote.repo_name()? {
            let mut p = std::env::current_dir()?;
            p.push(path);
            p
        } else {
            bail!("Could not infer repository name from {:?}", self.remote)
        };
        debug!("path = {:?}", path);

        let repo_path = RepoPath::new(path.clone());
        let repo_path_ = path.clone();
        ctrlc::set_handler(move || {
            std::fs::remove_dir_all(&repo_path_).unwrap_or(());
            std::process::exit(130)
        })
        .unwrap_or(());

        let mut repo = Repository::init(Some(path)).await?;
        let mut txn = repo.pristine.mut_txn_begin();
        let mut channel = txn.open_or_create_channel(&self.channel)?;
        if let Some(ref change) = self.change {
            let h = change.parse()?;
            remote
                .clone_tag(&mut repo, &mut txn, &mut channel, &[h])
                .await?
        } else if let Some(ref state) = self.state {
            let h = state.parse()?;
            remote
                .clone_state(&mut repo, &mut txn, &mut channel, h, self.lazy)
                .await?
        } else {
            remote
                .clone_channel(
                    &mut repo,
                    &mut txn,
                    &mut channel,
                    self.lazy,
                    &self.partial_paths,
                )
                .await?;
        }
        let progress = indicatif::ProgressBar::new_spinner();
        progress.set_style(
            indicatif::ProgressStyle::default_spinner().template("{spinner} Outputting repository"),
        );
        progress.enable_steady_tick(100);
        txn.output_repository_no_pending(
            &mut repo.working_copy,
            &repo.changes,
            &mut channel,
            "",
            true,
            None,
        )?;
        remote.finish().await?;
        txn.commit()?;
        repo.lock.commit().await?;
        progress.set_style(
            indicatif::ProgressStyle::default_spinner().template("✓ Outputting repository"),
        );
        progress.finish();
        repo.config.current_channel = Some(self.channel);
        if let crate::remote::RemoteRepo::Local(ref l) = remote {
            repo.config.default_remote = std::fs::canonicalize(&l.root)?
                .to_str()
                .map(|x| x.to_string());
        } else {
            repo.config.default_remote = Some(self.remote);
        }
        repo.save_config()?;
        std::mem::forget(repo_path);
        Ok(())
    }
}

#[derive(Debug, Clone)]
struct RepoPath {
    path: PathBuf,
    remove_dir: bool,
    remove_dot: bool,
}

impl RepoPath {
    fn new(path: PathBuf) -> Self {
        RepoPath {
            remove_dir: std::fs::metadata(&path).is_err(),
            remove_dot: std::fs::metadata(&path.join(libpijul::DOT_DIR)).is_err(),
            path,
        }
    }
    fn remove(&self) {
        if self.remove_dir {
            std::fs::remove_dir_all(&self.path).unwrap_or(());
        } else if self.remove_dot {
            std::fs::remove_dir_all(&self.path.join(libpijul::DOT_DIR)).unwrap_or(());
        }
    }
}

impl Drop for RepoPath {
    fn drop(&mut self) {
        self.remove()
    }
}
