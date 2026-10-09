use super::{FileReadError, Obj};
use crate::shadow::{self, EventKind};
use crate::tests::lock;
use std::path::PathBuf;
use std::sync::atomic::{AtomicUsize, Ordering};

static SERIAL: AtomicUsize = AtomicUsize::new(0);
fn path(label: &str) -> PathBuf {
    std::env::temp_dir().join(format!(
        "fln-get-line-{}-{}-{label}",
        std::process::id(),
        SERIAL.fetch_add(1, Ordering::Relaxed)
    ))
}
fn open(path: &std::path::Path, mode: usize) -> Obj {
    let result = Obj::try_file_open(
        &Obj::mk_string(path.to_str().unwrap()),
        &Obj::mk_nat(mode),
        &Obj::mk_nat(0),
    )
    .unwrap();
    assert_eq!(result.try_ctor_child(1).unwrap().unbox(), 1);
    result.try_ctor_child(0).unwrap()
}
fn text(value: &Obj) -> String {
    let (size, _, chars, bytes) = value.try_string_view().unwrap();
    let text = std::str::from_utf8(&bytes[..size - 1]).unwrap();
    assert_eq!(chars, text.chars().count());
    text.to_owned()
}
fn line(handle: &Obj, input: usize, output: usize) -> Result<String, FileReadError> {
    let packet = handle.try_file_get_line(&Obj::mk_nat(0), input, output)?;
    assert_eq!(packet.header().other, 7);
    assert_eq!(
        packet.try_ctor_child(1).unwrap().unbox(),
        1,
        "logical IO success"
    );
    Ok(text(&packet.try_ctor_child(0).unwrap()))
}
fn no_leaks() {
    let (events, live) = shadow::disable_and_drain();
    assert_eq!(live, 0);
    let faults: Vec<_> = events
        .iter()
        .filter(|e| matches!(e.kind, EventKind::DoubleRelease | EventKind::ForeignPointer))
        .collect();
    assert!(faults.is_empty(), "ownership faults: {faults:?}");
}

#[test]
fn bounded_get_line_preserves_lines_lossy_recovery_tail_eof_aliases_and_borrows() {
    let _guard = lock();
    let path = path("lines");
    let mut input = "first\r\nλ🙂\0\n".as_bytes().to_vec();
    input.extend_from_slice(&[0xff, 0x80, 0x80, b'X', b'\n']);
    input.extend_from_slice(b"tail");
    std::fs::write(&path, input).unwrap();
    shadow::enable();
    {
        let handle = open(&path, 0);
        let alias = handle.clone_ref();
        let before = handle.header().rc;
        assert_eq!(line(&handle, 64, 64).unwrap(), "first\r\n");
        assert_eq!(line(&alias, 64, 64).unwrap(), "λ🙂\0\n");
        assert_eq!(line(&handle, 64, 64).unwrap(), "�X\n");
        assert_eq!(handle.header().rc, before);
        drop(handle);
        assert_eq!(
            line(&alias, 4, 4).unwrap(),
            "tail",
            "exact input cap at EOF succeeds"
        );
        assert_eq!(line(&alias, 0, 0).unwrap(), "");
        assert_eq!(line(&alias, 0, 0).unwrap(), "");
    }
    no_leaks();
}

#[test]
fn bounded_get_line_reports_consumed_input_and_output_caps_and_releases_the_lock() {
    let _guard = lock();
    let path = path("caps");
    std::fs::write(&path, b"abX\nnext\n\xffA\nok\n").unwrap();
    let handle = open(&path, 0);
    assert_eq!(
        line(&handle, 2, 10),
        Err(FileReadError::InputLimit {
            limit: 2,
            observed: 3,
            bytes_consumed: 3
        })
    );
    assert!(
        lock_available_elsewhere(&handle),
        "resource stop must release FILE lock"
    );
    assert_eq!(line(&handle, 1, 1).unwrap(), "\n");
    assert_eq!(
        line(&handle, 5, 5).unwrap(),
        "next\n",
        "exact newline cap succeeds"
    );
    assert_eq!(
        line(&handle, 3, 4),
        Err(FileReadError::OutputLimit {
            limit: 4,
            observed: 5,
            bytes_consumed: 3
        })
    );
    assert!(lock_available_elsewhere(&handle));
    assert_eq!(line(&handle, 3, 3).unwrap(), "ok\n");
    assert_eq!(line(&handle, 0, 0).unwrap(), "");
    let path = path.with_extension("zero");
    std::fs::write(&path, b"Z\n").unwrap();
    let handle = open(&path, 0);
    assert_eq!(
        line(&handle, 0, 0),
        Err(FileReadError::InputLimit {
            limit: 0,
            observed: 1,
            bytes_consumed: 1
        })
    );
    assert_eq!(line(&handle, 1, 1).unwrap(), "\n");
}

#[test]
fn bounded_get_line_refuses_bad_world_without_reading_and_returns_real_io_error() {
    let _guard = lock();
    let path = path("errors");
    std::fs::write(&path, b"still here\n").unwrap();
    let handle = open(&path, 0);
    assert!(matches!(
        handle.try_file_get_line(&Obj::mk_nat(1), 100, 100),
        Err(FileReadError::InvalidWorld)
    ));
    assert_eq!(line(&handle, 100, 100).unwrap(), "still here\n");
    for value in [
        Obj::mk_nat(0),
        Obj::mk_external_counting(),
        Obj::mk_ref(Obj::mk_nat(0)),
    ] {
        assert!(matches!(
            value.try_file_get_line(&Obj::mk_nat(0), 100, 100),
            Err(FileReadError::InvalidHandle)
        ));
    }
    let write = open(&path, 4);
    let error = write.try_file_get_line(&Obj::mk_nat(0), 100, 100).unwrap();
    assert_eq!(error.try_ctor_child(1).unwrap().unbox(), 0);
    assert_eq!(error.try_ctor_child(2).unwrap().unbox(), 12);
    assert_eq!(
        error.try_ctor_child(3).unwrap().unbox(),
        crate::stdio::EBADF as usize
    );
    assert_eq!(error.try_ctor_child(4).unwrap().unbox(), 0);
    assert!(!text(&error.try_ctor_child(6).unwrap()).is_empty());
    assert!(lock_available_elsewhere(&write));
}

#[test]
fn bounded_get_line_exact_recovery_matches_pinned_raw_constructor_with_expansion_limits() {
    let _guard = lock();
    let cases: &[(&[u8], &str)] = &[
        (&[0xff, 0x80, 0x80, b'\n'], "�\n"),
        (&[0xc0, 0x80, b'A'], "�A"),
        (&[0xed, 0xa0, 0x80, b'\n'], "�\n"),
        (&[0xf0, 0x9f], "�"),
        (&[0xc2, b'X'], "�X"),
        (&[0xe2, 0x82, b'Y'], "�Y"),
        (&[0x80, 0x80, b'Z'], "�Z"),
        ("λ🙂\0\n".as_bytes(), "λ🙂\0\n"),
    ];
    for (index, (bytes, expected)) in cases.iter().enumerate() {
        let path = path(&format!("recovery-{index}"));
        std::fs::write(&path, bytes).unwrap();
        let handle = open(&path, 0);
        assert_eq!(
            line(&handle, bytes.len(), expected.len()).unwrap(),
            *expected
        );
        // SAFETY: raw constructor receives exactly this borrowed byte slice;
        // its owned result is immediately wrapped and settled by Obj.
        // UNSAFE-LEDGER: FLN-UL-0646
        #[allow(unsafe_code)]
        let raw = unsafe {
            Obj(crate::export::mk_string_from_bytes_impl(
                bytes.as_ptr().cast(),
                bytes.len(),
            ))
        };
        assert_eq!(text(&raw), *expected);
        let handle = open(&path, 0);
        assert_eq!(
            line(&handle, bytes.len(), expected.len() - 1),
            Err(FileReadError::OutputLimit {
                limit: expected.len() - 1,
                observed: expected.len(),
                bytes_consumed: bytes.len(),
            })
        );
    }
}

#[test]
fn bounded_get_line_preserves_unrepresentable_errno_counts_and_rejects_fake_string_results() {
    let _guard = lock();
    for code in [2, 4] {
        assert!(matches!(crate::stdio::checked_get_line_error(code, 7),
            Err(crate::stdio::FileReadFailure::Unrepresentable { errno, bytes_consumed: 7 }) if errno == code));
    }
    let wrong = Obj::mk_ctor(0, vec![Obj::mk_nat(0)], &[]);
    assert!(super::super::string_result_transport(&wrong).is_none());
    let logical = Obj::mk_ctor(0, vec![Obj::mk_string("x"), Obj::mk_nat(0)], &[]);
    assert!(super::super::string_result_transport(&logical).is_none());
    let malformed = Obj::mk_ctor(1, vec![Obj::mk_ctor(10, vec![], &[])], &[]);
    assert!(super::super::string_result_transport(&malformed).is_none());
}

// Test-only lock observations, in a separate thread so recursive flockfile
// acquisition on the reading thread cannot hide an unreleased resource lock.
// UNSAFE-LEDGER: FLN-UL-0643
#[allow(unsafe_code)]
unsafe extern "C" {
    fn ftrylockfile(file: *mut core::ffi::c_void) -> i32;
    fn funlockfile(file: *mut core::ffi::c_void);
}

fn lock_available_elsewhere(handle: &Obj) -> bool {
    assert!(handle.is_file_handle());
    // SAFETY: exact Handle owns FILE through the joined child; only libc's
    // documented cross-thread FILE lock operation runs there, and a successful
    // test lock is released before the child returns. No Obj crosses threads.
    // UNSAFE-LEDGER: FLN-UL-0645
    #[allow(unsafe_code)]
    unsafe {
        let (_, file) = crate::object::external_fields(handle.0);
        let address = file as usize;
        std::thread::spawn(move || {
            let file = address as *mut core::ffi::c_void;
            if ftrylockfile(file) == 0 {
                funlockfile(file);
                true
            } else {
                false
            }
        })
        .join()
        .unwrap()
    }
}
