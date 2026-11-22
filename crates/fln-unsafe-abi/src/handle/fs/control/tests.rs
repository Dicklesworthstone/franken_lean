use super::{FileIoError, Obj, control_result_transport};
use crate::shadow::{self, EventKind};
use crate::tests::lock;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicUsize, Ordering};

static SERIAL: AtomicUsize = AtomicUsize::new(0);

fn path(label: &str) -> PathBuf {
    std::env::temp_dir().join(format!(
        "fln-file-controls-{}-{}-{label}",
        std::process::id(),
        SERIAL.fetch_add(1, Ordering::Relaxed)
    ))
}

fn field(packet: &Obj, index: usize) -> Obj {
    assert_eq!(packet.header().tag, 0);
    assert_eq!(packet.header().other, 7);
    packet.try_ctor_child(index).unwrap()
}

fn payload(result: Result<Obj, FileIoError>) -> Obj {
    let packet = result.unwrap();
    assert_eq!(field(&packet, 1).unbox(), 1);
    field(&packet, 0)
}

fn open(path: &Path, mode: usize) -> Obj {
    let handle = payload(Obj::try_file_open(
        &Obj::mk_string(path.to_str().unwrap()),
        &Obj::mk_nat(mode),
        &Obj::mk_nat(0),
    ));
    assert!(handle.is_file_handle());
    handle
}

fn unit(result: Result<Obj, FileIoError>) {
    assert_eq!(payload(result).unbox(), 0);
}

fn no_leaks() {
    let (events, live) = shadow::disable_and_drain();
    assert_eq!(live, 0, "every Handle and control result must settle");
    assert!(events.iter().all(|event| !matches!(
        event.kind,
        EventKind::DoubleRelease | EventKind::ForeignPointer
    )));
}

#[test]
fn file_controls_keep_native_cursor_and_truncation_semantics() {
    let _guard = lock();
    let path = path("cursor-λ");
    std::fs::write(&path, "original suffix").unwrap();
    shadow::enable();
    {
        let world = Obj::mk_nat(0);
        let handle = open(&path, 3);
        let alias = handle.clone_ref();
        let before = handle.header().rc;
        unit(handle.try_file_put_str(&Obj::mk_string("longer replacement"), &world));
        // fseek, unlike truncate, flushes pending output.
        unit(alias.try_file_rewind(&world));
        assert_eq!(std::fs::read(&path).unwrap(), b"longer replacement");
        unit(handle.try_file_put_str(&Obj::mk_string("λ"), &world));
        unit(handle.try_file_flush(&world));
        unit(alias.try_file_truncate(&world));
        assert_eq!(std::fs::read(&path).unwrap(), "λ".as_bytes());
        unit(handle.try_file_rewind(&world));
        let line = handle.try_file_get_line(&world, 100, 100).unwrap();
        let string = field(&line, 0);
        let (size, _, _, bytes) = string.try_string_view().unwrap();
        assert_eq!(&bytes[..size - 1], "λ".as_bytes());
        assert_eq!(handle.header().rc, before);
    }
    no_leaks();
}

#[test]
fn file_controls_reject_inputs_before_effects_and_preserve_read_only_errors() {
    let _guard = lock();
    let path = path("preconditions");
    shadow::enable();
    {
        let world = Obj::mk_nat(0);
        let wrong_world = Obj::mk_nat(1);
        let handle = open(&path, 1);
        unit(handle.try_file_put_str(&Obj::mk_string("pending"), &world));
        for result in [
            handle.try_file_rewind(&wrong_world),
            handle.try_file_truncate(&wrong_world),
            handle.try_file_lock(true, &wrong_world),
            handle.try_file_try_lock(false, &wrong_world),
            handle.try_file_unlock(&wrong_world),
        ] {
            assert!(matches!(result, Err(FileIoError::InvalidWorld)));
        }
        assert!(std::fs::read(&path).unwrap().is_empty());
        for invalid in [
            Obj::mk_nat(0),
            Obj::mk_string("Handle lookalike"),
            Obj::mk_ctor(0, vec![], &[]),
            Obj::mk_ref(Obj::mk_nat(0)),
        ] {
            for result in [
                invalid.try_file_rewind(&world),
                invalid.try_file_truncate(&world),
                invalid.try_file_lock(true, &world),
                invalid.try_file_try_lock(false, &world),
                invalid.try_file_unlock(&world),
            ] {
                assert!(matches!(result, Err(FileIoError::InvalidHandle)));
            }
        }
        unit(handle.try_file_flush(&world));
        let reader = open(&path, 0);
        unit(reader.try_file_rewind(&world));
        let error = reader.try_file_truncate(&world).unwrap();
        assert_eq!(field(&error, 1).unbox(), 0);
        assert_eq!(std::fs::read(&path).unwrap(), b"pending");
    }
    no_leaks();
}

#[test]
fn file_locks_preserve_shared_exclusive_contention_and_aliases() {
    let _guard = lock();
    let path = path("locks");
    std::fs::write(&path, "lock target").unwrap();
    shadow::enable();
    {
        let world = Obj::mk_nat(0);
        let first = open(&path, 3);
        let second = open(&path, 3);
        let alias = first.clone_ref();
        let before = first.header().rc;
        unit(first.try_file_lock(false, &world));
        assert_eq!(payload(second.try_file_try_lock(false, &world)).unbox(), 1);
        assert_eq!(payload(second.try_file_try_lock(true, &world)).unbox(), 0);
        unit(alias.try_file_unlock(&world));
        assert_eq!(payload(second.try_file_try_lock(true, &world)).unbox(), 1);
        assert_eq!(payload(first.try_file_try_lock(true, &world)).unbox(), 0);
        unit(second.try_file_unlock(&world));
        assert_eq!(payload(first.try_file_try_lock(true, &world)).unbox(), 1);
        unit(alias.try_file_unlock(&world));
        unit(alias.try_file_unlock(&world));
        assert_eq!(first.header().rc, before);
    }
    no_leaks();
    assert_eq!(std::fs::read(path).unwrap(), b"lock target");
}

#[test]
fn file_locks_are_visible_to_independent_processes_and_release_on_last_drop() {
    let _guard = lock();
    let path = path("process-lock");
    std::fs::write(&path, "unchanged").unwrap();
    let probe = |blocked: bool| {
        let result = std::process::Command::new(std::env::current_exe().unwrap())
            .args([
                "--exact",
                "handle::fs::control::tests::file_lock_child_process_probe",
                "--nocapture",
            ])
            .env("FLN_HANDLE_LOCK_PROBE", &path)
            .env("FLN_HANDLE_LOCK_BLOCKED", if blocked { "1" } else { "0" })
            .output()
            .unwrap();
        assert!(
            result.status.success(),
            "child lock probe: {} {}",
            String::from_utf8_lossy(&result.stdout),
            String::from_utf8_lossy(&result.stderr)
        );
        assert!(String::from_utf8_lossy(&result.stdout).contains("1 passed"));
    };
    shadow::enable();
    {
        let world = Obj::mk_nat(0);
        let handle = open(&path, 3);
        let alias = handle.clone_ref();
        unit(handle.try_file_lock(true, &world));
        probe(true);
        drop(handle);
        probe(true);
        unit(alias.try_file_unlock(&world));
        probe(false);
        unit(alias.try_file_lock(true, &world));
        probe(true);
    }
    no_leaks();
    probe(false);
}

#[test]
fn file_lock_child_process_probe() {
    let Some(path) = std::env::var_os("FLN_HANDLE_LOCK_PROBE") else {
        return;
    };
    let file = std::fs::OpenOptions::new()
        .read(true)
        .write(true)
        .open(path)
        .unwrap();
    let result = file.try_lock();
    if std::env::var("FLN_HANDLE_LOCK_BLOCKED").unwrap() == "1" {
        assert!(matches!(result, Err(std::fs::TryLockError::WouldBlock)));
    } else {
        result.unwrap();
        file.unlock().unwrap();
    }
}

#[test]
fn file_control_transport_refuses_malformed_boolean_and_unit_payloads() {
    let _guard = lock();
    shadow::enable();
    {
        for value in 0..=2 {
            let result = Obj::mk_ctor(0, vec![Obj::mk_nat(value)], &[]);
            assert_eq!(control_result_transport(&result, true).is_some(), value < 2);
            assert_eq!(
                control_result_transport(&result, false).is_some(),
                value == 0
            );
        }
        for malformed in [
            Obj::mk_nat(0),
            Obj::mk_ctor(0, vec![], &[]),
            Obj::mk_ctor(0, vec![Obj::mk_string("true")], &[]),
            Obj::mk_ctor(0, vec![Obj::mk_nat(1), Obj::mk_nat(0)], &[]),
            Obj::mk_ctor(2, vec![Obj::mk_nat(1)], &[]),
        ] {
            assert!(control_result_transport(&malformed, true).is_none());
        }
    }
    no_leaks();
}
