use super::*;
use crate::working_copy::WorkingCopy;

#[test]
fn rollback_conflict_resolution_simple() -> Result<(), anyhow::Error> {
    env_logger::try_init().unwrap_or(());

    let mut repo = working_copy::memory::Memory::new();
    let changes = changestore::memory::Memory::new();

    let env = pristine::sanakirja::Pristine::new_anon()?;

    let mut txn = env.mut_txn_begin();

    let mut channela = txn.open_or_create_channel("main")?;

    // Create a simple conflict between axb and ayb
    repo.add_file("file", b"a\nb\n".to_vec());
    txn.add_file("file")?;
    record_all(&mut repo, &changes, &mut txn, &mut channela, "")?;

    let mut channelb = txn.fork(&channela, "other")?;

    repo.write_file::<_, std::io::Error, _>("file", |w| {
        w.write_all(b"a\nx\nb\n")?;
        Ok(())
    })?;
    let ha = record_all(&mut repo, &changes, &mut txn, &mut channela, "")?;

    repo.write_file::<_, std::io::Error, _>("file", |w| {
        w.write_all(b"a\ny\nb\n")?;
        Ok(())
    })?;
    let hb = record_all(&mut repo, &changes, &mut txn, &mut channelb, "")?;

    apply::apply_change(&changes, &mut txn, &mut channelb, ha)?;
    apply::apply_change(&changes, &mut txn, &mut channela, hb)?;

    debug_to_file(&txn, &channela.borrow(), "debuga")?;
    debug_to_file(&txn, &channelb.borrow(), "debugb")?;

    output::output_repository_no_pending(&mut repo, &changes, &mut txn, &mut channela, "", true)?;
    let mut buf = Vec::new();
    repo.read_file("file", &mut buf)?;
    debug!("{}", std::str::from_utf8(&buf).unwrap());

    // Solve the conflict.
    let conflict: Vec<_> = std::str::from_utf8(&buf)?.lines().collect();
    repo.write_file::<_, std::io::Error, _>("file", |w| {
        for l in conflict.iter().filter(|l| l.len() == 1) {
            writeln!(w, "{}", l)?
        }
        Ok(())
    })?;

    buf.clear();
    repo.read_file("file", &mut buf)?;
    debug!("{}", std::str::from_utf8(&buf).unwrap());
    let resb = record_all(&mut repo, &changes, &mut txn, &mut channela, "")?;
    debug_to_file(&txn, &channela.borrow(), "debugres")?;

    let p_inv = changes.get_change(&resb).unwrap().inverse(
        &resb,
        crate::change::ChangeHeader {
            authors: vec![],
            message: "rollback".to_string(),
            description: None,
            timestamp: chrono::Utc::now(),
        },
        Vec::new(),
    );
    let h_inv = changes.save_change(&p_inv)?;
    apply::apply_change(&changes, &mut txn, &mut channela, h_inv)?;
    debug_to_file(&txn, &channela.borrow(), "debug")?;

    Ok(())
}

#[test]
fn rollback_conflict_resolution_swap() -> Result<(), anyhow::Error> {
    env_logger::try_init().unwrap_or(());

    let mut repo = working_copy::memory::Memory::new();
    let changes = changestore::memory::Memory::new();

    let env = pristine::sanakirja::Pristine::new_anon()?;

    let mut txn = env.mut_txn_begin();

    let mut channela = txn.open_or_create_channel("main")?;

    // Create a simple conflict between axb and ayb
    repo.add_file("file", b"a\nb\n".to_vec());
    txn.add_file("file")?;
    record_all(&mut repo, &changes, &mut txn, &mut channela, "")?;

    let mut channelb = txn.fork(&channela, "other")?;

    repo.write_file::<_, std::io::Error, _>("file", |w| {
        w.write_all(b"a\nx\nb\n")?;
        Ok(())
    })?;
    let ha = record_all(&mut repo, &changes, &mut txn, &mut channela, "")?;

    repo.write_file::<_, std::io::Error, _>("file", |w| {
        w.write_all(b"a\ny\nb\n")?;
        Ok(())
    })?;
    let hb = record_all(&mut repo, &changes, &mut txn, &mut channelb, "")?;

    apply::apply_change(&changes, &mut txn, &mut channelb, ha)?;
    apply::apply_change(&changes, &mut txn, &mut channela, hb)?;

    debug_to_file(&txn, &channela.borrow(), "debuga")?;
    debug_to_file(&txn, &channelb.borrow(), "debugb")?;

    output::output_repository_no_pending(&mut repo, &changes, &mut txn, &mut channela, "", true)?;
    let mut buf = Vec::new();
    repo.read_file("file", &mut buf)?;
    debug!("{}", std::str::from_utf8(&buf).unwrap());

    // Solve the conflict.
    let conflict: Vec<_> = std::str::from_utf8(&buf)?.lines().collect();
    repo.write_file::<_, std::io::Error, _>("file", |w| {
        for l in conflict.iter().filter(|l| l.len() == 1) {
            writeln!(w, "{}", l)?
        }
        Ok(())
    })?;

    buf.clear();
    repo.read_file("file", &mut buf)?;
    debug!("{}", std::str::from_utf8(&buf).unwrap());
    let resb = record_all(&mut repo, &changes, &mut txn, &mut channelb, "")?;
    debug_to_file(&txn, &channelb.borrow(), "debugres")?;

    let p_inv = changes.get_change(&resb).unwrap().inverse(
        &resb,
        crate::change::ChangeHeader {
            authors: vec![],
            message: "rollback".to_string(),
            description: None,
            timestamp: chrono::Utc::now(),
        },
        Vec::new(),
    );
    let h_inv = changes.save_change(&p_inv)?;
    apply::apply_change(&changes, &mut txn, &mut channelb, h_inv)?;
    debug_to_file(&txn, &channelb.borrow(), "debug")?;

    Ok(())
}
