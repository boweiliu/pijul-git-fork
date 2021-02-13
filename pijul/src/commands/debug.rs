use std::path::PathBuf;

use crate::repository::Repository;
use anyhow::bail;
use clap::Clap;
use libpijul::{TxnT, TxnTExt};

#[derive(Clap, Debug)]
pub struct Debug {
    #[clap(long = "repository")]
    repo_path: Option<PathBuf>,
    #[clap(long = "channel")]
    channel: Option<String>,
    root: Option<String>,
}

impl Debug {
    pub async fn run(self) -> Result<(), anyhow::Error> {
        let repo = Repository::find_root(self.repo_path).await?;
        let txn = repo.pristine.txn_begin()?;
        libpijul::pristine::debug_inodes(&txn);
        libpijul::pristine::debug_revinodes(&txn);
        libpijul::pristine::debug_tree_print(&txn);
        libpijul::pristine::debug_revtree_print(&txn);
        let channel_name = repo.config.get_current_channel(self.channel.as_deref());
        let channel = if let Some(channel) = txn.load_channel(&channel_name)? {
            channel
        } else {
            bail!("No such channel: {:?}", channel_name)
        };
        if let Some(root) = self.root {
            let (pos, _) = txn
                .follow_oldest_path(&repo.changes, &channel, &root)
                .unwrap();
            libpijul::pristine::debug_root(
                &txn,
                &channel.borrow().graph,
                pos.inode_vertex(),
                std::io::stdout(),
                true,
            )?;
        } else {
            let channel = channel.borrow();
            libpijul::pristine::debug(&txn, &channel.graph, std::io::stdout())?;
        }
        libpijul::pristine::check_alive_debug(&repo.changes, &txn, &channel.borrow(), 0)?;
        eprintln!("{:#?}", txn.check_database());
        Ok(())
    }
}
