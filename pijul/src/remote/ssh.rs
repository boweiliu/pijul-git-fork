use std::collections::HashSet;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::pin::Pin;
use std::sync::Arc;
use std::time::{Duration, SystemTime};

use anyhow::bail;
use byteorder::{BigEndian, ReadBytesExt};
use indicatif::ProgressBar;
use lazy_static::lazy_static;
use libpijul::pristine::Position;
use libpijul::{Base32, ChannelRef, Hash, Merkle, MutTxnT, MutTxnTExt, TxnTExt};
use log::{debug, error};
use regex::Regex;
use thrussh::client::Session;
use tokio::sync::Mutex;

use super::{parse_line, RemoteRef};
use crate::repository::Repository;

pub struct Ssh {
    pub h: thrussh::client::Handle<SshClient>,
    pub c: thrussh::client::Channel,
    pub channel: String,
    pub remote_cmd: String,
    pub path: String,
    pub is_running: bool,
    pub name: String,
    state: Arc<Mutex<State>>,
    has_errors: Arc<Mutex<bool>>,
}

lazy_static! {
    static ref ADDRESS: Regex = Regex::new(
        r#"(ssh://)?((?P<user>[^@]+)@)?((?P<host>(\[([^\]]+)\])|([^:/]+)))((:(?P<port>\d+)/)|:|/)(?P<path>.+)"#
    )
        .unwrap();

    static ref PROGRESS: Arc<Mutex<Option<ProgressBar>>> = Arc::new(Mutex::new(None));
}

#[derive(Debug)]
pub struct Remote<'a> {
    addr: &'a str,
    host: &'a str,
    path: &'a str,
    config: thrussh_config::Config,
}

pub fn ssh_remote(addr: &str) -> Option<Remote> {
    let cap = ADDRESS.captures(addr)?;
    debug!("ssh_remote: {:?}", cap);
    let host = cap.name("host").unwrap().as_str();

    let mut config =
        thrussh_config::parse_home(&host).unwrap_or(thrussh_config::Config::default(host));
    if let Some(port) = cap.name("port").map(|x| x.as_str().parse().unwrap()) {
        config.port = port
    }
    if let Some(u) = cap.name("user") {
        config.user.clear();
        config.user.push_str(u.as_str());
    }
    let path = cap.name("path").unwrap().as_str();
    Some(Remote {
        addr,
        host,
        path,
        config,
    })
}

impl<'a> Remote<'a> {
    pub async fn connect(&mut self, name: &str, channel: &str) -> Result<Ssh, anyhow::Error> {
        let mut home = dirs_next::home_dir().unwrap();
        home.push(".ssh");
        home.push("known_hosts");
        let state = Arc::new(Mutex::new(State::None));
        let has_errors = Arc::new(Mutex::new(false));
        let client = SshClient {
            addr: self.config.host_name.clone(),
            known_hosts: home,
            last_window_adjustment: SystemTime::now(),
            state: state.clone(),
            has_errors: has_errors.clone(),
        };
        let stream = self.config.stream().await?;
        let config = Arc::new(thrussh::client::Config::default());
        let mut h = thrussh::client::connect_stream(config, stream, client).await?;

        let mut key_path = dirs_next::home_dir().unwrap().join(".ssh");

        // First try agent auth
        let authenticated = self
            .auth_agent(&mut h, &mut key_path)
            .await
            .unwrap_or(false)
            || self.auth_pk(&mut h, &mut key_path).await
            || self.auth_password(&mut h).await?;

        if !authenticated {
            bail!("Not authenticated")
        }

        let c = h.channel_open_session().await?;
        let remote_cmd = if let Ok(cmd) = std::env::var("REMOTE_PIJUL") {
            cmd
        } else {
            "pijul".to_string()
        };
        Ok(Ssh {
            h,
            c,
            channel: channel.to_string(),
            remote_cmd,
            path: self.path.to_string(),
            is_running: false,
            name: name.to_string(),
            state,
            has_errors,
        })
    }

    async fn auth_agent(
        &self,
        h: &mut thrussh::client::Handle<SshClient>,
        key_path: &mut PathBuf,
    ) -> Result<bool, anyhow::Error> {
        let mut authenticated = false;
        let mut agent = thrussh_keys::agent::client::AgentClient::connect_env().await?;
        let identities = if let Some(ref file) = self.config.identity_file {
            key_path.push(file);
            key_path.set_extension("pub");
            let k = thrussh_keys::load_public_key(&key_path);
            key_path.pop();
            if let Ok(k) = k {
                vec![k]
            } else {
                return Ok(false);
            }
        } else {
            agent.request_identities().await?
        };
        debug!("identities = {:?}", identities);
        let mut agent = Some(agent);
        for key in identities {
            debug!("Trying key {:?}", key);
            debug!("fingerprint = {:?}", key.fingerprint());
            if let Some(a) = agent.take() {
                debug!("authenticate future");
                match h.authenticate_future(&self.config.user, key, a).await {
                    (a, Ok(auth)) => {
                        authenticated = auth;
                        agent = Some(a);
                    }
                    (a, Err(e)) => {
                        agent = Some(a);
                        debug!("not auth {:?}", e);
                        if let thrussh::AgentAuthError::Key(e) = e {
                            debug!("error: {:?}", e);
                            writeln!(std::io::stderr(), "Failed to sign with agent")?;
                        }
                    }
                }
            }
            if authenticated {
                return Ok(true);
            }
        }
        Ok(false)
    }

    async fn auth_pk(
        &self,
        h: &mut thrussh::client::Handle<SshClient>,
        key_path: &mut PathBuf,
    ) -> bool {
        let mut authenticated = false;
        let mut keys = Vec::new();
        if let Some(ref file) = self.config.identity_file {
            keys.push(file.as_str())
        } else {
            keys.push("id_ed25519");
            keys.push("id_rsa");
        }
        for k in keys.iter() {
            key_path.push(k);
            let k = if let Some(k) = load_secret_key(&key_path, k) {
                k
            } else {
                key_path.pop();
                continue;
            };
            if let Ok(auth) = h
                .authenticate_publickey(&self.config.user, Arc::new(k))
                .await
            {
                authenticated = auth
            }
            key_path.pop();
            if authenticated {
                return true;
            }
        }
        false
    }

    async fn auth_password(
        &self,
        h: &mut thrussh::client::Handle<SshClient>,
    ) -> Result<bool, thrussh::Error> {
        let pass = rpassword::read_password_from_tty(Some(&format!(
            "Password for {}@{}: ",
            self.config.user, self.config.host_name
        )))?;
        h.authenticate_password(self.config.user.to_string(), &pass)
            .await
    }
}

pub fn load_secret_key(key_path: &Path, k: &str) -> Option<thrussh_keys::key::KeyPair> {
    match thrussh_keys::load_secret_key(&key_path, None) {
        Ok(k) => Some(k),
        Err(e) => {
            if let thrussh_keys::Error::KeyIsEncrypted = e {
                let pass = if let Ok(pass) =
                    rpassword::read_password_from_tty(Some(&format!("Password for key {:?}: ", k)))
                {
                    pass
                } else {
                    return None;
                };
                if pass.is_empty() {
                    return None;
                }
                if let Ok(k) = thrussh_keys::load_secret_key(&key_path, Some(pass.as_bytes())) {
                    return Some(k);
                }
            }
            None
        }
    }
}

pub struct SshClient {
    addr: String,
    known_hosts: PathBuf,
    last_window_adjustment: SystemTime,
    state: Arc<Mutex<State>>,
    has_errors: Arc<Mutex<bool>>,
}

enum State {
    None,
    State {
        sender: Option<tokio::sync::oneshot::Sender<Option<(u64, Merkle)>>>,
    },
    Changes {
        sender: Option<tokio::sync::mpsc::Sender<Hash>>,
        remaining_len: usize,
        file: std::fs::File,
        path: PathBuf,
        hashes: Vec<libpijul::pristine::Hash>,
        current: usize,
    },
    Changelist {
        sender: tokio::sync::mpsc::Sender<Option<super::ListLine>>,
    },
    Channel {
        sender: tokio::sync::mpsc::Sender<Vec<u8>>,
    },
    Archive {
        sender: Option<tokio::sync::oneshot::Sender<u64>>,
        len: u64,
        conflicts: u64,
        len_n: u64,
        w: Box<dyn Write + Send>,
    },
}

type BoxFuture<T> = Pin<Box<dyn futures::future::Future<Output = T> + Send>>;

impl thrussh::client::Handler for SshClient {
    type Error = anyhow::Error;
    type FutureBool = futures::future::Ready<Result<(Self, bool), anyhow::Error>>;
    type FutureUnit = BoxFuture<Result<(Self, Session), anyhow::Error>>;

    fn finished_bool(self, b: bool) -> Self::FutureBool {
        futures::future::ready(Ok((self, b)))
    }
    fn finished(self, session: Session) -> Self::FutureUnit {
        Box::pin(async move { Ok((self, session)) })
    }
    fn check_server_key(
        self,
        server_public_key: &thrussh_keys::key::PublicKey,
    ) -> Self::FutureBool {
        let mut it = self.addr.split(':');
        let addr = it.next().unwrap();
        let port = it.next().unwrap_or("22").parse().unwrap();
        match thrussh_keys::check_known_hosts_path(addr, port, server_public_key, &self.known_hosts)
        {
            Ok(e) => {
                if e {
                    futures::future::ready(Ok((self, true)))
                } else {
                    match learn(addr, port, server_public_key) {
                        Ok(x) => futures::future::ready(Ok((self, x))),
                        Err(e) => futures::future::ready(Err(e)),
                    }
                }
            }
            Err(e) => {
                error!("Key changed for {:?}", self.addr);
                futures::future::ready(Err(e.into()))
            }
        }
    }

    fn adjust_window(&mut self, _channel: thrussh::ChannelId, target: u32) -> u32 {
        let elapsed = self.last_window_adjustment.elapsed().unwrap();
        self.last_window_adjustment = SystemTime::now();
        if target >= 10_000_000 {
            return target;
        }
        if elapsed < Duration::from_secs(2) {
            target * 2
        } else if elapsed > Duration::from_secs(8) {
            target / 2
        } else {
            target
        }
    }

    fn channel_eof(
        self,
        _channel: thrussh::ChannelId,
        session: thrussh::client::Session,
    ) -> Self::FutureUnit {
        Box::pin(async move {
            *self.state.lock().await = State::None;
            Ok((self, session))
        })
    }

    fn exit_status(
        self,
        channel: thrussh::ChannelId,
        exit_status: u32,
        session: thrussh::client::Session,
    ) -> Self::FutureUnit {
        session.send_channel_msg(channel, thrussh::ChannelMsg::ExitStatus { exit_status });
        Box::pin(async move {
            *self.state.lock().await = State::None;
            *self.has_errors.lock().await = true;
            Ok((self, session))
        })
    }

    fn extended_data(
        self,
        channel: thrussh::ChannelId,
        ext: u32,
        data: &[u8],
        session: thrussh::client::Session,
    ) -> Self::FutureUnit {
        debug!("extended data {:?}, {:?}", std::str::from_utf8(data), ext);
        if ext == 0 {
            self.data(channel, data, session)
        } else {
            let data = data.to_vec();
            Box::pin(async move {
                *PROGRESS.lock().await = None;
                *super::SPINNER.lock().await = None;
                *self.has_errors.lock().await = true;
                let stderr = std::io::stderr();
                let mut handle = stderr.lock();
                handle.write_all(&data)?;
                Ok((self, session))
            })
        }
    }

    fn data(
        self,
        channel: thrussh::ChannelId,
        data: &[u8],
        session: thrussh::client::Session,
    ) -> Self::FutureUnit {
        debug!("data {:?} {:?}", channel, data.len());
        let data = data.to_vec();
        Box::pin(async move {
            match *self.state.lock().await {
                State::State { ref mut sender } => {
                    debug!("state: State");
                    if let Some(sender) = sender.take() {
                        // If we can't parse `data` (for example if the
                        // remote returns the standard "-\n"), this
                        // returns None.
                        let mut s = std::str::from_utf8(&data).unwrap().split(' ');
                        debug!("s = {:?}", s);
                        if let (Some(n), Some(m)) = (s.next(), s.next()) {
                            let n = n.parse().unwrap();
                            sender
                                .send(Some((n, Merkle::from_base32(m.trim().as_bytes()).unwrap())))
                                .unwrap_or(());
                        } else {
                            sender.send(None).unwrap_or(());
                        }
                    }
                }
                State::Changes {
                    ref mut sender,
                    ref mut remaining_len,
                    ref mut file,
                    ref mut path,
                    ref hashes,
                    ref mut current,
                } => {
                    debug!("state changes");
                    let mut p = 0;
                    while p < data.len() {
                        if *remaining_len == 0 {
                            *remaining_len = (&data[p..]).read_u64::<BigEndian>().unwrap() as usize;
                            p += 8;
                            debug!("remaining_len = {:?}", remaining_len);
                        }
                        if data.len() >= p + *remaining_len {
                            file.write_all(&data[p..p + *remaining_len])?;
                            // We have enough data to write the
                            // file, write it and move to the next
                            // file.
                            p += *remaining_len;
                            *remaining_len = 0;
                            file.flush()?;
                            let mut final_path = path.clone();
                            final_path.set_extension("change");
                            debug!("moving {:?} to {:?}", path, final_path);
                            std::fs::rename(&path, &final_path)?;
                            debug!("sending");
                            if let Some(ref mut sender) = sender {
                                if sender.send(hashes[*current]).await.is_err() {
                                    break;
                                }
                            }
                            debug!("sent");
                            *current += 1;
                            if *current < hashes.len() {
                                // If we're still waiting for
                                // another change.
                                libpijul::changestore::filesystem::pop_filename(path);
                                libpijul::changestore::filesystem::push_filename(
                                    path,
                                    &hashes[*current],
                                );
                                std::fs::create_dir_all(&path.parent().unwrap())?;
                                path.set_extension("tmp");
                                debug!("creating file {:?}", path);
                                *file = std::fs::File::create(&path)?;
                            } else {
                                // Else, just finish.
                                debug!("dropping channel");
                                std::mem::drop(sender.take());
                                break;
                            }
                        } else {
                            // not enough data, we need more.
                            file.write_all(&data[p..])?;
                            file.flush()?;
                            *remaining_len -= data.len() - p;
                            debug!("need more data");
                            break;
                        }
                    }
                    debug!("finished, {:?} {:?}", p, data.len());
                }
                State::Changelist { ref mut sender } => {
                    debug!("state changelist");
                    if &data[..] == b"\n" {
                        debug!("log done");
                        sender.send(None).await.unwrap_or(())
                    } else if let Ok(data) = std::str::from_utf8(&data) {
                        for l in data.lines() {
                            if !l.is_empty() {
                                debug!("line = {:?}", l);
                                sender.send(parse_line(l).ok()).await.unwrap_or(())
                            } else {
                                sender.send(None).await.unwrap_or(());
                            }
                        }
                    }
                }
                State::Channel { ref mut sender } => {
                    debug!("state channel");
                    sender.send(data).await?
                }
                State::Archive {
                    ref mut sender,
                    ref mut w,
                    ref mut len,
                    ref mut len_n,
                    ref mut conflicts,
                } => {
                    debug!("state archive");
                    let mut off = 0;
                    while *len_n < 16 && off < data.len() {
                        if *len_n < 8 {
                            *len = (*len << 8) | (data[off] as u64);
                        } else {
                            *conflicts = (*conflicts << 8) | (data[off] as u64);
                        }
                        *len_n += 1;
                        off += 1;
                    }
                    if *len_n >= 16 {
                        w.write_all(&data[off..])?;
                        *len -= (data.len() - off) as u64;
                        if *len == 0 {
                            if let Some(sender) = sender.take() {
                                sender.send(*conflicts).unwrap_or(())
                            }
                        }
                    }
                }
                State::None => {
                    debug!("None state");
                }
            }
            Ok((self, session))
        })
    }
}

fn learn(addr: &str, port: u16, pk: &thrussh_keys::key::PublicKey) -> Result<bool, anyhow::Error> {
    if port == 22 {
        print!(
            "Unknown key for {:?}, fingerprint {:?}. Learn it (y/N)? ",
            addr,
            pk.fingerprint()
        );
    } else {
        print!(
            "Unknown key for {:?}:{}, fingerprint {:?}. Learn it (y/N)? ",
            addr,
            port,
            pk.fingerprint()
        );
    }
    std::io::stdout().flush()?;
    let mut buffer = String::new();
    std::io::stdin().read_line(&mut buffer)?;
    let buffer = buffer.trim();
    if buffer == "Y" || buffer == "y" {
        thrussh_keys::learn_known_hosts(addr, port, pk)?;
        Ok(true)
    } else {
        Ok(false)
    }
}

impl Ssh {
    pub async fn finish(&mut self) -> Result<(), anyhow::Error> {
        self.c.eof().await?;
        while let Some(msg) = self.c.wait().await {
            debug!("msg = {:?}", msg);
            match msg {
                thrussh::ChannelMsg::WindowAdjusted { .. } => {}
                thrussh::ChannelMsg::Eof => {}
                thrussh::ChannelMsg::ExitStatus { exit_status } => {
                    if exit_status != 0 {
                        bail!("Remote exited with status {:?}", exit_status)
                    }
                }
                msg => error!("wrong message {:?}", msg),
            }
        }
        Ok(())
    }

    pub async fn get_state(
        &mut self,
        mid: Option<u64>,
    ) -> Result<Option<(u64, Merkle)>, anyhow::Error> {
        debug!("get_state");
        let (sender, receiver) = tokio::sync::oneshot::channel();
        *self.state.lock().await = State::State {
            sender: Some(sender),
        };
        self.run_protocol().await?;
        if let Some(mid) = mid {
            self.c
                .data(format!("state {} {}\n", self.channel, mid).as_bytes())
                .await?;
        } else {
            self.c
                .data(format!("state {}\n", self.channel).as_bytes())
                .await?;
        }
        Ok(receiver.await?)
    }

    pub async fn archive<W: std::io::Write + Send + 'static>(
        &mut self,
        prefix: Option<String>,
        state: Option<(Merkle, &[Hash])>,
        w: W,
    ) -> Result<u64, anyhow::Error> {
        debug!("archive");
        let (sender, receiver) = tokio::sync::oneshot::channel();
        *self.state.lock().await = State::Archive {
            sender: Some(sender),
            len: 0,
            conflicts: 0,
            len_n: 0,
            w: Box::new(w),
        };
        self.run_protocol().await?;
        if let Some((ref state, ref extra)) = state {
            let mut cmd = format!("archive {} {}", self.channel, state.to_base32(),);
            for e in extra.iter() {
                cmd.push_str(&format!(" {}", e.to_base32()));
            }
            if let Some(ref p) = prefix {
                cmd.push_str(" :");
                cmd.push_str(p)
            }
            cmd.push('\n');
            self.c.data(cmd.as_bytes()).await?;
        } else {
            self.c
                .data(
                    format!(
                        "archive {}{}{}\n",
                        self.channel,
                        if prefix.is_some() { " :" } else { "" },
                        prefix.unwrap_or_else(String::new)
                    )
                    .as_bytes(),
                )
                .await?;
        }
        let conflicts = receiver.await.unwrap_or(0);
        Ok(conflicts)
    }

    pub async fn run_protocol(&mut self) -> Result<(), anyhow::Error> {
        if !self.is_running {
            self.is_running = true;
            debug!("run_protocol");
            self.c
                .exec(
                    true,
                    format!(
                        "{} protocol --version {} --repository {}",
                        self.remote_cmd,
                        crate::PROTOCOL_VERSION,
                        self.path
                    ),
                )
                .await?;
            debug!("waiting for a message");
            while let Some(msg) = self.c.wait().await {
                debug!("msg = {:?}", msg);
                match msg {
                    thrussh::ChannelMsg::Success => break,
                    thrussh::ChannelMsg::WindowAdjusted { .. } => {}
                    thrussh::ChannelMsg::Eof => {}
                    thrussh::ChannelMsg::ExitStatus { exit_status } => {
                        if exit_status != 0 {
                            bail!("Remote exited with status {:?}", exit_status)
                        }
                    }
                    _ => {}
                }
            }
            debug!("run_protocol done");
        }
        Ok(())
    }

    pub async fn download_changelist<T: MutTxnT>(
        &mut self,
        txn: &mut T,
        remote: &mut RemoteRef<T>,
        from: u64,
        paths: &[String],
    ) -> Result<HashSet<Position<Hash>>, anyhow::Error> {
        let (sender, mut receiver) = tokio::sync::mpsc::channel(10);
        *self.state.lock().await = State::Changelist { sender };
        self.run_protocol().await?;
        debug!("download_changelist");
        let mut command = Vec::new();
        write!(command, "changelist {} {}", self.channel, from).unwrap();
        for p in paths {
            write!(command, " {:?}", p).unwrap()
        }
        command.push(b'\n');
        self.c.data(&command[..]).await?;
        debug!("waiting ssh, command: {:?}", std::str::from_utf8(&command));
        let mut result = HashSet::new();
        while let Some(Some(m)) = receiver.recv().await {
            match m {
                super::ListLine::Change { n, h, m } => {
                    txn.put_remote(remote, n, (h, m))?;
                }
                super::ListLine::Position(pos) => {
                    result.insert(pos);
                }
                super::ListLine::Error(err) => {
                    bail!(err)
                }
            }
        }
        if *self.has_errors.lock().await {
            bail!("Remote sent an error")
        }
        debug!("no msg, result = {:?}", result);
        Ok(result)
    }

    pub async fn upload_changes(
        &mut self,
        mut local: PathBuf,
        to_channel: Option<&str>,
        changes: &[Hash],
    ) -> Result<(), anyhow::Error> {
        self.run_protocol().await?;
        debug!("upload_changes");
        let progress = ProgressBar::new(changes.len() as u64);
        progress.set_style(
            indicatif::ProgressStyle::default_bar()
                .template("  Uploading changes   {wide_bar} {pos:>5}/{len}"),
        );
        let progress = super::PROGRESS.add(progress);
        *PROGRESS.lock().await = Some(progress);
        for c in changes {
            debug!("{:?}", c);
            libpijul::changestore::filesystem::push_filename(&mut local, &c);
            let mut change_file = std::fs::File::open(&local)?;
            let change_len = change_file.metadata()?.len();
            let mut change = thrussh::CryptoVec::new_zeroed(change_len as usize);
            use std::io::Read;
            change_file.read_exact(&mut change[..])?;
            let to_channel = if let Some(t) = to_channel {
                t
            } else {
                self.channel.as_str()
            };
            self.c
                .data(format!("apply {} {} {}\n", to_channel, c.to_base32(), change_len).as_bytes())
                .await?;
            self.c.data(&change[..]).await?;
            if let Some(ref mut progress) = *PROGRESS.lock().await {
                progress.inc(1);
            }
            libpijul::changestore::filesystem::pop_filename(&mut local);
        }
        if let Some(ref mut progress) = *PROGRESS.lock().await {
            progress.set_style(
                indicatif::ProgressStyle::default_bar()
                    .template("✓ Uploading changes {pos:>5}/{len}"),
            );
            progress.finish();
        }
        Ok(())
    }

    pub async fn download_changes(
        &mut self,
        c: &[libpijul::pristine::Hash],
        sender: &mut tokio::sync::mpsc::Sender<libpijul::pristine::Hash>,
        changes_dir: &mut PathBuf,
        full: bool,
    ) -> Result<(), anyhow::Error> {
        self.download_changes_(c, Some(sender), changes_dir, full)
            .await
    }

    async fn download_changes_(
        &mut self,
        c: &[libpijul::pristine::Hash],
        mut sender: Option<&mut tokio::sync::mpsc::Sender<libpijul::pristine::Hash>>,
        changes_dir: &mut PathBuf,
        full: bool,
    ) -> Result<(), anyhow::Error> {
        if c.is_empty() {
            return Ok(());
        }
        let (sender_, mut recv) = tokio::sync::mpsc::channel(100);
        let mut path = changes_dir.clone();
        libpijul::changestore::filesystem::push_filename(&mut path, &c[0]);
        std::fs::create_dir_all(&path.parent().unwrap())?;
        path.set_extension("tmp");
        let file = std::fs::File::create(&path)?;
        *self.state.lock().await = State::Changes {
            sender: Some(sender_),
            remaining_len: 0,
            path,
            file,
            hashes: c.to_vec(),
            current: 0,
        };
        self.run_protocol().await?;
        for c in c {
            debug!("download_change {:?} {:?}", c, full);
            if full {
                self.c
                    .data(format!("change {}\n", c.to_base32()).as_bytes())
                    .await?;
            } else {
                self.c
                    .data(format!("partial {}\n", c.to_base32()).as_bytes())
                    .await?;
            }
        }
        let progress = ProgressBar::new(c.len() as u64);
        progress.set_style(
            indicatif::ProgressStyle::default_bar()
                .template("  Downloading changes {wide_bar} {pos:>5}/{len}"),
        );
        *PROGRESS.lock().await = Some(progress);
        while let Some(_hash) = recv.recv().await {
            debug!("received hash {:?}", _hash);
            if let Some(ref mut progress) = *PROGRESS.lock().await {
                progress.inc(1);
            }
            if let Some(ref mut sender) = sender {
                if sender.send(_hash).await.is_err() {
                    if let Some(ref mut progress) = *PROGRESS.lock().await {
                        progress.abandon();
                    }
                    break;
                }
            }
        }
        if let Some(ref mut progress) = *PROGRESS.lock().await {
            if !progress.is_finished() {
                progress.set_style(
                    indicatif::ProgressStyle::default_bar()
                        .template("✓ Downloading changes {pos:>5}/{len}"),
                );
                progress.finish();
            }
        }
        debug!("done downloading");
        Ok(())
    }

    pub async fn clone_channel<T: TxnTExt + MutTxnTExt>(
        &mut self,
        repo: &mut Repository,
        txn: &mut T,
        channel: &mut ChannelRef<T>,
        lazy: bool,
    ) -> Result<(), anyhow::Error> {
        let (sender, mut recv) = tokio::sync::mpsc::channel(10);
        *self.state.lock().await = State::Channel { sender };
        self.run_protocol().await?;
        debug!("clone channel");
        self.c
            .data(format!("channel {}\n", self.channel).as_bytes())
            .await?;

        let progress = indicatif::ProgressBar::new_spinner();
        progress.set_style(
            indicatif::ProgressStyle::default_spinner().template("{spinner} Cloning channel"),
        );
        progress.enable_steady_tick(100);
        *PROGRESS.lock().await = Some(progress);
        let from_dump_alive = {
            let mut from_dump =
                libpijul::pristine::channel_dump::ChannelFromDump::new(txn, channel.clone());
            debug!("receiving channel");
            while let Some(msg) = recv.recv().await {
                debug!("msg = {:?}", msg.len());
                if from_dump.read(&msg)? {
                    debug!("break");
                    break;
                }
            }
            debug!("from dump done");
            from_dump.alive
        };
        if let Some(ref mut progress) = *PROGRESS.lock().await {
            progress.set_style(
                indicatif::ProgressStyle::default_spinner().template("✓ Cloning channel"),
            );
            progress.finish();
        }
        let channel_ = channel.borrow();
        debug!("cloned, now downloading changes");
        let mut hashes = Vec::new();
        if lazy {
            for &ch in from_dump_alive.iter() {
                let h = txn.get_external(ch)?.unwrap();
                hashes.push(h);
            }
        } else {
            for h in txn.log(&channel_, 0)? {
                hashes.push((h?.1).0);
            }
        }
        std::mem::drop(channel_);
        debug!("hashes = {:#?}", hashes);
        self.download_changes_(&hashes, None, &mut repo.changes_dir, true)
            .await?;
        txn.output_repository_no_pending(
            &mut repo.working_copy,
            &repo.changes,
            channel,
            "",
            true,
            None,
        )?;
        Ok(())
    }
}
