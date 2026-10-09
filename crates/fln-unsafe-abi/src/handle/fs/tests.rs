use super::{FileIoError, Obj, file_result_transport};
use crate::shadow::{self, EventKind};
use crate::tests::lock;
use std::path::PathBuf;
use std::sync::atomic::{AtomicUsize, Ordering};

static SERIAL: AtomicUsize = AtomicUsize::new(0);

fn path(label: &str) -> PathBuf {
    std::env::temp_dir().join(format!(
        "fln-file-io-{}-{}-{label}",
        std::process::id(),
        SERIAL.fetch_add(1, Ordering::Relaxed)
    ))
}

fn text(value: &Obj) -> String {
    let (size, _, _, bytes) = value.try_string_view().unwrap();
    String::from_utf8(bytes[..size - 1].to_vec()).unwrap()
}

fn field(value: &Obj, index: usize) -> Obj {
    assert_eq!(value.header().tag, 0);
    assert_eq!(value.header().other, 7);
    assert_eq!(value.byte_size(), size_of::<[usize; 8]>());
    value.try_ctor_child(index).unwrap()
}

fn open(path: &std::path::Path, mode: usize) -> Obj {
    Obj::try_file_open(
        &Obj::mk_string(path.to_str().unwrap()),
        &Obj::mk_nat(mode),
        &Obj::mk_nat(0),
    )
    .unwrap()
}

fn handle(opened: &Obj) -> Obj {
    assert_eq!(field(opened, 1).unbox(), 1);
    let result = field(opened, 0);
    assert!(result.is_file_handle());
    result
}

fn no_leaks() {
    let (events, live) = shadow::disable_and_drain();
    assert_eq!(live, 0, "every file/result reference must settle");
    let faults: Vec<_> = events
        .iter()
        .filter(|event| {
            matches!(
                event.kind,
                EventKind::DoubleRelease | EventKind::ForeignPointer
            )
        })
        .collect();
    assert!(faults.is_empty(), "ownership faults: {faults:?}");
}

#[test]
fn file_io_preserves_borrows_aliases_unicode_nuls_and_finalizes_the_last_handle() {
    let _guard = lock();
    let path = path("aliases");
    shadow::enable();
    {
        let opened = open(&path, 1);
        let original = handle(&opened);
        let alias = original.clone_ref();
        drop(opened);
        drop(original);
        for source in ["first\n", "λ🙂\0tail"] {
            let input = Obj::mk_string(source);
            let before = (alias.header().rc, input.header().rc);
            let result = alias.try_file_put_str(&input, &Obj::mk_nat(0)).unwrap();
            assert_eq!(field(&result, 1).unbox(), 1);
            assert_eq!(field(&result, 0).unbox(), 0);
            assert_eq!((alias.header().rc, input.header().rc), before);
            assert_eq!(text(&input), source);
        }
    }
    no_leaks();
    assert_eq!(std::fs::read(path).unwrap(), "first\nλ🙂\0tail".as_bytes());
}

#[test]
fn file_io_modes_keep_truncate_append_exclusive_and_read_only_semantics() {
    let _guard = lock();
    let path = path("modes");
    std::fs::write(&path, "old content").unwrap();
    for (mode, content, expected) in [
        (1, "first", "first"),
        (4, "!", "first!"),
        (3, "XY", "XYrst!"),
    ] {
        {
            let opened = open(&path, mode);
            let handle = handle(&opened);
            assert_eq!(
                field(
                    &handle
                        .try_file_put_str(&Obj::mk_string(content), &Obj::mk_nat(0))
                        .unwrap(),
                    1
                )
                .unbox(),
                1
            );
        }
        assert_eq!(std::fs::read_to_string(&path).unwrap(), expected);
    }
    let exclusive = open(&path, 2);
    assert_eq!(field(&exclusive, 1).unbox(), 0);
    assert_eq!(field(&exclusive, 3).unbox(), 17); // EEXIST, measured Linux contract.
    assert_eq!(text(&field(&exclusive, 5)), path.to_str().unwrap());
    assert_eq!(std::fs::read(&path).unwrap(), b"XYrst!");
    let created = path.with_extension("exclusive-new");
    drop(open(&created, 2));
    assert!(created.exists());
    let opened = open(&path, 0);
    let handle = handle(&opened);
    let failed = handle
        .try_file_put_str(&Obj::mk_string("refused"), &Obj::mk_nat(0))
        .unwrap();
    assert_eq!(field(&failed, 1).unbox(), 0);
    assert_eq!(field(&failed, 2).unbox(), 12);
    assert_eq!(field(&failed, 3).unbox(), crate::stdio::EBADF as usize);
    assert_eq!(field(&failed, 4).unbox(), 0);
    assert_eq!(std::fs::read(&path).unwrap(), b"XYrst!");
}

#[test]
fn file_io_rejects_invalid_inputs_before_effects_and_keeps_filename_nul_as_error() {
    let _guard = lock();
    let path = path("preconditions");
    std::fs::write(&path, "untouched").unwrap();
    let filename = Obj::mk_string(path.to_str().unwrap());
    assert!(matches!(
        Obj::try_file_open(&filename, &Obj::mk_nat(5), &Obj::mk_nat(0)),
        Err(FileIoError::InvalidMode)
    ));
    assert!(matches!(
        Obj::try_file_open(&filename, &Obj::mk_nat(1), &Obj::mk_nat(1)),
        Err(FileIoError::InvalidWorld)
    ));
    assert!(matches!(
        Obj::try_file_open(&Obj::mk_nat(0), &Obj::mk_nat(1), &Obj::mk_nat(0)),
        Err(FileIoError::InvalidFilename)
    ));
    let with_nul = format!("{}\0ignored", path.display());
    let error =
        Obj::try_file_open(&Obj::mk_string(&with_nul), &Obj::mk_nat(1), &Obj::mk_nat(0)).unwrap();
    assert_eq!(field(&error, 1).unbox(), 0);
    assert_eq!(field(&error, 2).unbox(), 12);
    assert_eq!(field(&error, 4).unbox(), 1);
    assert_eq!(text(&field(&error, 5)), with_nul);
    assert_eq!(text(&field(&error, 6)), "string contains NUL bytes");
    assert_eq!(std::fs::read(&path).unwrap(), b"untouched");
    let opened = open(&path, 3);
    let handle = handle(&opened);
    assert!(matches!(
        handle.try_file_put_str(&Obj::mk_string("bad"), &Obj::mk_nat(1)),
        Err(FileIoError::InvalidWorld)
    ));
    assert!(matches!(
        handle.try_file_put_str(&Obj::mk_ctor(0, vec![], &[]), &Obj::mk_nat(0)),
        Err(FileIoError::InvalidString)
    ));
    for other in [
        Obj::mk_nat(0),
        Obj::mk_ref(Obj::mk_nat(0)),
        Obj::mk_external_counting(),
        Obj::mk_closure(2, vec![]),
    ] {
        assert!(!other.is_file_handle());
        assert!(matches!(
            other.try_file_put_str(&Obj::mk_string("bad"), &Obj::mk_nat(0)),
            Err(FileIoError::InvalidHandle)
        ));
    }
    drop(handle);
    drop(opened);
    assert_eq!(std::fs::read(path).unwrap(), b"untouched");
}

#[test]
fn file_io_transport_refuses_fake_handles_logical_results_and_malformed_errors() {
    let _guard = lock();
    for payload in [
        Obj::mk_nat(0),
        Obj::mk_external_counting(),
        Obj::mk_ref(Obj::mk_nat(42)),
    ] {
        assert!(file_result_transport(&Obj::mk_ctor(0, vec![payload], &[]), true).is_none());
    }
    let logical = Obj::mk_ctor(0, vec![Obj::mk_nat(0), Obj::mk_nat(0)], &[]);
    assert!(file_result_transport(&logical, false).is_none());
    let malformed = Obj::mk_ctor(1, vec![Obj::mk_ctor(10, vec![Obj::mk_nat(0)], &[])], &[]);
    assert!(file_result_transport(&malformed, true).is_none());
    let missing = path("absent-parent").join("missing");
    let error = open(&missing, 0);
    assert_eq!(field(&error, 1).unbox(), 0);
    assert_eq!(field(&error, 2).unbox(), 11);
    assert_eq!(field(&error, 4).unbox(), 1);
    assert_eq!(text(&field(&error, 5)), missing.to_str().unwrap());
}

#[test]
fn file_io_is_not_swallowed_by_an_active_stdout_capture() {
    let _guard = lock();
    let path = path("capture-isolation");
    let capture = crate::handle::stdout_capture::StdoutCapture::begin(1).unwrap();
    {
        let opened = open(&path, 1);
        let handle = handle(&opened);
        let result = handle
            .try_file_put_str(&Obj::mk_string("file λ🙂\0\n"), &Obj::mk_nat(0))
            .unwrap();
        assert_eq!(field(&result, 1).unbox(), 1);
    }
    let output = capture.finish();
    assert_eq!(output.error, None);
    assert!(output.bytes.is_empty());
    assert_eq!(std::fs::read(path).unwrap(), "file λ🙂\0\n".as_bytes());
}

// Test-only OS fixtures: raw descriptors are uniquely owned and every path
// transfers them to FILE or closes them. No production native callback escapes.
// UNSAFE-LEDGER: FLN-UL-0635
#[allow(unsafe_code)]
unsafe extern "C" {
    fn close(fd: i32) -> i32;
    fn pipe(fds: *mut i32) -> i32;
    fn fdopen(fd: i32, mode: *const core::ffi::c_char) -> *mut core::ffi::c_void;
    fn signal(signum: i32, handler: usize) -> usize;
}

#[test]
fn file_io_failed_fdopen_closes_the_owned_descriptor_and_preserves_errno() {
    use std::os::fd::IntoRawFd;
    let _guard = lock();
    let path = path("fdopen-failure");
    let descriptor = std::fs::File::create(&path).unwrap().into_raw_fd();
    let filename = Obj::mk_string(path.to_str().unwrap());
    // SAFETY: descriptor is uniquely transferred; null models fdopen failure
    // after real open. The second close observes EBADF, never another owner.
    // UNSAFE-LEDGER: FLN-UL-0636
    #[allow(unsafe_code)]
    unsafe {
        let result = Obj(crate::stdio::finish_handle_open(
            descriptor,
            core::ptr::null_mut(),
            22,
            filename.0,
        ));
        let error = file_result_transport(&result, true).unwrap();
        assert_eq!(field(&error, 3).unbox(), 22);
        assert_eq!(text(&field(&error, 5)), path.to_str().unwrap());
        assert_eq!(close(descriptor), -1);
        assert_eq!(crate::stdio::errno(), crate::stdio::EBADF);
    }
    assert!(path.exists(), "the already-created file is not rolled back");
}

#[test]
fn file_io_initializes_sigpipe_without_default_streams() {
    const NAME: &str = "handle::fs::tests::file_io_initializes_sigpipe_without_default_streams";
    if std::env::var_os("FLN_FILE_SIGPIPE_CHILD").is_none() {
        let output = std::process::Command::new(std::env::current_exe().unwrap())
            .args(["--exact", NAME, "--nocapture", "--test-threads=1"])
            .env("FLN_FILE_SIGPIPE_CHILD", "1")
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "child status {:?}\n{}\n{}",
            output.status,
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
        assert!(String::from_utf8_lossy(&output.stdout).contains("1 passed"));
        return;
    }
    // SAFETY: isolated child resets only its own signal policy, closes the
    // pipe reader, and transfers its uniquely owned writer to native Handle.
    // The safe write must establish SIG_IGN before fwrite can raise SIGPIPE.
    // UNSAFE-LEDGER: FLN-UL-0637
    #[allow(unsafe_code)]
    unsafe {
        signal(13, 0); // Linux SIGPIPE, SIG_DFL.
        let mut descriptors = [-1; 2];
        assert_eq!(pipe(descriptors.as_mut_ptr()), 0);
        assert_eq!(close(descriptors[0]), 0);
        let file = fdopen(descriptors[1], c"w".as_ptr());
        assert!(!file.is_null());
        let handle = Obj(crate::stdio::io_wrap_handle(file));
        let result = handle
            .try_file_put_str(&Obj::mk_string(&"x".repeat(128 * 1024)), &Obj::mk_nat(0))
            .unwrap();
        assert_eq!(field(&result, 1).unbox(), 0);
        assert_eq!(field(&result, 3).unbox(), 32); // EPIPE.
        assert!(!text(&field(&result, 6)).is_empty());
    }
}
