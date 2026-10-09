//! The bounded Golem stdout door: observable bytes, borrowed ownership,
//! hostile callbacks, and packed-native/error-transport separation.

use super::{Obj, StdioPutStrError, stdio_result_transport};
use crate::layout::LeanObject;
use crate::shadow::{self, EventKind};
use crate::tests::lock;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicUsize, Ordering};

static SERIAL: AtomicUsize = AtomicUsize::new(0);
static FOREIGN_CALLS: AtomicUsize = AtomicUsize::new(0);

fn capture_path(label: &str) -> PathBuf {
    std::env::temp_dir().join(format!(
        "fln-bounded-stdout-{}-{}-{label}",
        std::process::id(),
        SERIAL.fetch_add(1, Ordering::Relaxed),
    ))
}

fn initialize_stdout() {
    crate::stdio::initialize_streams();
    // Each test has a fresh thread-local slot. Seed it before enabling the
    // allocation shadow: the process-initial stream is persistent and was
    // allocated outside this test's tracked lifetime. Its lazy TLS retain
    // would otherwise be reported as RC traffic on an unregistered pointer.
    drop(Obj::stdio_stdout().expect("native process stdout"));
}

fn stream_for_file(path: &Path, mode: u8) -> Obj {
    let filename = Obj::mk_string(path.to_str().expect("test path is UTF-8"));
    // SAFETY: the filename is canonical and borrowed by Handle.mk. The native
    // result is owned; the cloned Handle is consumed by stream_of_handle.
    // UNSAFE-LEDGER: FLN-UL-0622
    #[allow(unsafe_code)]
    unsafe {
        let opened = Obj(crate::stdio::prim_handle_mk(filename.0, mode));
        assert_eq!(opened.header().tag, 0, "test file opens");
        let handle = opened.try_ctor_child(0).expect("native IO.Result payload");
        Obj(crate::stdio::stream_of_handle(handle.into_raw()))
    }
}

struct StdoutRestore(Option<Obj>);

impl StdoutRestore {
    fn install(stream: Obj) -> Self {
        Self(Some(Obj(crate::stdio::get_set_stdout(stream.into_raw()))))
    }
}

impl Drop for StdoutRestore {
    fn drop(&mut self) {
        if let Some(previous) = self.0.take() {
            drop(Obj(crate::stdio::get_set_stdout(previous.into_raw())));
        }
    }
}

fn no_leaks() {
    let (events, live) = shadow::disable_and_drain();
    assert_eq!(live, 0, "all temporary stream/transport references settle");
    let faults = events
        .iter()
        .filter(|event| {
            matches!(
                event.kind,
                EventKind::DoubleRelease | EventKind::ForeignPointer
            )
        })
        .collect::<Vec<_>>();
    assert!(faults.is_empty(), "ownership faults: {faults:?}");
}

fn text(value: &Obj) -> String {
    let (size, _, _, bytes) = value.try_string_view().expect("transport String");
    String::from_utf8(bytes[..size - 1].to_vec()).expect("transport UTF-8")
}

fn packet(value: &Obj) -> (usize, usize, usize, usize, String, String) {
    assert_eq!(value.header().tag, 0);
    assert_eq!(value.header().other, 6);
    assert_eq!(value.byte_size(), 7 * size_of::<usize>());
    (
        value.try_ctor_child(0).unwrap().unbox(),
        value.try_ctor_child(1).unwrap().unbox(),
        value.try_ctor_child(2).unwrap().unbox(),
        value.try_ctor_child(3).unwrap().unbox(),
        text(&value.try_ctor_child(4).unwrap()),
        text(&value.try_ctor_child(5).unwrap()),
    )
}

#[test]
fn bounded_stdout_writes_current_stream_bytes_and_retains_borrowed_inputs() {
    let _guard = lock();
    initialize_stdout();
    let path = capture_path("utf8");
    shadow::enable();
    {
        let _restore = StdoutRestore::install(stream_for_file(&path, 1));
        let stream = Obj::stdio_stdout().unwrap();
        let callback = stream.try_ctor_child(4).unwrap();
        assert!(callback.is_stdio_put_str_closure());
        assert_eq!(std::fs::metadata(&path).unwrap().len(), 0);
        let world = Obj::mk_nat(0);
        for line in ["first\n", "λ🙂\0tail\n"] {
            let input = Obj::mk_string(line);
            let callback_rc = callback.header().rc;
            let input_rc = input.header().rc;
            let result = callback.try_stdio_put_str(&input, &world).unwrap();
            assert_eq!(packet(&result), (1, 0, 0, 0, String::new(), String::new()));
            assert_eq!(callback.header().rc, callback_rc);
            assert_eq!(input.header().rc, input_rc);
            assert_eq!(text(&input), line);
        }
    }
    no_leaks();
    // The temporary stream's final Handle reference has closed/flushed it.
    assert_eq!(
        std::fs::read(path).unwrap(),
        "first\nλ🙂\0tail\n".as_bytes()
    );
}

#[test]
fn bounded_stdout_reports_real_write_failure_in_neutral_error_transport() {
    let _guard = lock();
    initialize_stdout();
    let path = capture_path("read-only");
    std::fs::write(&path, "untouched").unwrap();
    shadow::enable();
    {
        let _restore = StdoutRestore::install(stream_for_file(&path, 0));
        let callback = Obj::stdio_stdout().unwrap().try_ctor_child(4).unwrap();
        let input = Obj::mk_string("must fail");
        let result = callback.try_stdio_put_str(&input, &Obj::mk_nat(0)).unwrap();
        let (success, tag, code, has_filename, filename, details) = packet(&result);
        assert_eq!(
            (success, tag, code, has_filename),
            (0, 12, crate::stdio::EBADF as usize, 0)
        );
        assert!(filename.is_empty());
        assert!(!details.is_empty());
    }
    no_leaks();
    assert_eq!(std::fs::read(path).unwrap(), b"untouched");
}

extern "C" fn foreign_put_str(
    _capture: *mut LeanObject,
    _text: *mut LeanObject,
    _world: *mut LeanObject,
) -> *mut LeanObject {
    FOREIGN_CALLS.fetch_add(1, Ordering::SeqCst);
    crate::tagged::boxi(0)
}

fn malformed_known_callback(arity: u16, captures: Vec<Obj>) -> Obj {
    let canonical = Obj::stdio_stdout().unwrap().try_ctor_child(4).unwrap();
    // SAFETY: canonical is a live native closure. The mutated callback is
    // freshly allocated with every capture initialized; it is inspected only,
    // never dispatched through the unchecked generic native apply machinery.
    // UNSAFE-LEDGER: FLN-UL-0623
    #[allow(unsafe_code)]
    unsafe {
        let (target, _, _, _) = crate::object::closure_fields(canonical.0);
        let callback = crate::object::alloc_closure(target, arity, captures.len() as u16);
        for (index, capture) in captures.into_iter().enumerate() {
            crate::object::closure_set(callback, index, capture.into_raw());
        }
        Obj(callback)
    }
}

#[test]
fn bounded_stdout_refuses_foreign_targets_wrong_captures_and_bad_inputs_before_write() {
    let _guard = lock();
    initialize_stdout();
    let path = capture_path("refused");
    FOREIGN_CALLS.store(0, Ordering::SeqCst);
    shadow::enable();
    {
        let _restore = StdoutRestore::install(stream_for_file(&path, 1));
        let stream = Obj::stdio_stdout().unwrap();
        let callback = stream.try_ctor_child(4).unwrap();
        let input = Obj::mk_string("must not be written");
        let world = Obj::mk_nat(0);
        for wrong in [
            Obj::mk_nat(0),
            Obj::mk_string("not callable"),
            Obj::mk_closure(3, vec![Obj::mk_nat(0)]),
            Obj::mk_closure_fn3(foreign_put_str, vec![Obj::mk_nat(0)]),
            malformed_known_callback(4, vec![Obj::mk_nat(0)]),
            malformed_known_callback(3, Vec::new()),
            malformed_known_callback(3, vec![Obj::mk_nat(0), Obj::mk_nat(0)]),
            malformed_known_callback(3, vec![Obj::mk_nat(0)]),
            malformed_known_callback(3, vec![Obj::mk_external_counting()]),
        ] {
            assert!(!wrong.is_stdio_put_str_closure());
            assert!(wrong.try_stdio_put_str(&input, &world).is_err());
        }
        for field in [0, 1, 2, 3, 5] {
            let other = stream.try_ctor_child(field).unwrap();
            assert!(!other.is_stdio_put_str_closure());
            assert!(other.try_stdio_put_str(&input, &world).is_err());
        }
        assert!(
            callback
                .try_stdio_put_str(&Obj::mk_nat(42), &world)
                .is_err()
        );
        assert!(callback.try_stdio_put_str(&input, &Obj::mk_nat(1)).is_err());
        assert!(
            callback
                .try_stdio_put_str(&input, &Obj::mk_ctor(0, Vec::new(), &[]))
                .is_err()
        );
        let bad_string = Obj::mk_string("wrong terminator");
        bad_string.plant_string_terminator(b'x');
        assert!(callback.try_stdio_put_str(&bad_string, &world).is_err());
        bad_string.plant_string_terminator(0);
    }
    no_leaks();
    assert_eq!(FOREIGN_CALLS.load(Ordering::SeqCst), 0);
    assert!(std::fs::read(path).unwrap().is_empty());
}

fn io_error(error: Obj) -> Obj {
    Obj::mk_ctor(1, vec![error], &[])
}

#[test]
fn bounded_stdout_getter_refuses_golem_foreign_malformed_and_mixed_stream_overrides() {
    let _guard = lock();
    initialize_stdout();
    FOREIGN_CALLS.store(0, Ordering::SeqCst);
    let first_path = capture_path("getter-first");
    let second_path = capture_path("getter-second");
    shadow::enable();
    {
        let native = stream_for_file(&first_path, 1);
        let other = stream_for_file(&second_path, 1);
        let _restore = StdoutRestore::install(native.clone_ref());
        let fields = || {
            (0..6)
                .map(|index| native.try_ctor_child(index).unwrap())
                .collect::<Vec<_>>()
        };
        let check = |stream| {
            let _restore = StdoutRestore::install(stream);
            assert!(Obj::stdio_stdout().is_none());
        };
        check(Obj::mk_nat(0));
        check(Obj::mk_string("not a stream"));
        check(Obj::mk_ctor(1, fields(), &[]));
        check(Obj::mk_ctor(0, fields().into_iter().take(5).collect(), &[]));
        check(Obj::mk_ctor(0, fields(), &[0; 8]));
        for index in 0..6 {
            let mut override_fields = fields();
            override_fields[index] = Obj::mk_closure(3, vec![Obj::mk_nat(0)]);
            check(Obj::mk_ctor(0, override_fields, &[]));
            let mut wrong_native_method = fields();
            wrong_native_method[index] = native.try_ctor_child((index + 1) % 6).unwrap();
            check(Obj::mk_ctor(0, wrong_native_method, &[]));
        }
        for wrong_put_str in [
            Obj::mk_closure_fn3(foreign_put_str, vec![Obj::mk_nat(0)]),
            malformed_known_callback(4, vec![Obj::mk_nat(0)]),
            malformed_known_callback(3, Vec::new()),
            malformed_known_callback(3, vec![Obj::mk_external_counting()]),
        ] {
            let mut override_fields = fields();
            override_fields[4] = wrong_put_str;
            check(Obj::mk_ctor(0, override_fields, &[]));
        }
        let mut mixed = fields();
        mixed[4] = other.try_ctor_child(4).unwrap();
        check(Obj::mk_ctor(0, mixed, &[]));
        assert!(
            Obj::stdio_stdout().is_some(),
            "native override survives rejected nested overrides"
        );
        {
            let _restore = StdoutRestore::install(other);
            assert!(
                Obj::stdio_stdout().is_some(),
                "another complete native Handle stream is supported"
            );
        }
    }
    no_leaks();
    assert_eq!(FOREIGN_CALLS.load(Ordering::SeqCst), 0);
    assert!(std::fs::read(first_path).unwrap().is_empty());
    assert!(std::fs::read(second_path).unwrap().is_empty());
}

#[test]
fn bounded_stdout_refuses_decoder_errors_that_require_an_unavailable_filename() {
    let _guard = lock();
    shadow::enable();
    {
        // This tests completion of an already performed write. A positive
        // byte count must survive; no assertion here claims absent output.
        for failure in [
            (crate::stdio::EINTR, 0),
            (crate::stdio::EINTR, 3),
            (crate::stdio::ENOENT, 2),
        ] {
            assert_eq!(
                crate::stdio::checked_put_str_result(Err(failure)),
                Err(failure)
            );
        }
        let (raw, written) = crate::stdio::checked_put_str_result(Ok(4)).unwrap();
        assert_eq!(written, 4);
        let ok = Obj(raw);
        assert_eq!(packet(&stdio_result_transport(&ok).unwrap()).0, 1);
        let (raw, written) =
            crate::stdio::checked_put_str_result(Err((crate::stdio::EBADF, 2))).unwrap();
        assert_eq!(written, 2);
        let error = Obj(raw);
        let (success, tag, code, has_filename, filename, _) =
            packet(&stdio_result_transport(&error).unwrap());
        assert_eq!(
            (success, tag, code, has_filename),
            (0, 12, crate::stdio::EBADF as usize, 0)
        );
        assert!(filename.is_empty());
        let callback = Obj::mk_nat(0);
        assert!(matches!(
            callback.try_stdio_put_str(&Obj::mk_string("untouched"), &Obj::mk_nat(0)),
            Err(StdioPutStrError::InvalidCallback),
        ));
        assert!(matches!(
            callback.try_stdio_put_str(&Obj::mk_nat(0), &Obj::mk_nat(0)),
            Err(StdioPutStrError::InvalidString),
        ));
        assert!(matches!(
            callback.try_stdio_put_str(&Obj::mk_string("untouched"), &Obj::mk_nat(1)),
            Err(StdioPutStrError::InvalidWorld),
        ));
    }
    no_leaks();
}

#[test]
fn bounded_stdout_transport_decodes_all_pinned_native_error_shapes() {
    let _guard = lock();
    shadow::enable();
    {
        let code = 0xfedc_ba98_u32;
        for tag in 0..=18 {
            for has_filename in [false, true] {
                let filename = Obj::mk_string("λ.txt");
                let details = Obj::mk_string("details 🙂");
                let (native, expected_filename, expected_details, expected_code) = match tag {
                    0 | 12..=16 => {
                        let option = if has_filename {
                            Obj::mk_ctor(1, vec![filename], &[])
                        } else {
                            Obj::mk_nat(0)
                        };
                        (
                            Obj::mk_ctor(tag, vec![option, details], &code.to_ne_bytes()),
                            has_filename,
                            "details 🙂",
                            code,
                        )
                    }
                    1..=9 => (
                        Obj::mk_ctor(tag, vec![details], &code.to_ne_bytes()),
                        false,
                        "details 🙂",
                        code,
                    ),
                    10 | 11 => (
                        Obj::mk_ctor(tag, vec![filename, details], &code.to_ne_bytes()),
                        true,
                        "details 🙂",
                        code,
                    ),
                    17 => (Obj::mk_nat(17), false, "", 0),
                    18 => (
                        Obj::mk_ctor(tag, vec![details], &[]),
                        false,
                        "details 🙂",
                        0,
                    ),
                    _ => unreachable!(),
                };
                let transport = stdio_result_transport(&io_error(native)).unwrap();
                let actual = packet(&transport);
                assert_eq!(actual.0, 0);
                assert_eq!(actual.1, usize::from(tag));
                assert_eq!(actual.2, expected_code as usize);
                assert_eq!(actual.3, usize::from(expected_filename));
                assert_eq!(actual.4, if expected_filename { "λ.txt" } else { "" });
                assert_eq!(actual.5, expected_details);
            }
        }
    }
    no_leaks();
}

#[test]
fn bounded_stdout_transport_refuses_logical_results_and_malformed_native_errors() {
    let _guard = lock();
    shadow::enable();
    {
        for result in [
            Obj::mk_nat(0),
            Obj::mk_ctor(0, vec![Obj::mk_nat(0), Obj::mk_nat(0)], &[]),
            Obj::mk_ctor(0, vec![Obj::mk_ctor(0, Vec::new(), &[])], &[]),
            Obj::mk_ctor(0, vec![Obj::mk_nat(1)], &[]),
            Obj::mk_ctor(2, vec![Obj::mk_nat(0)], &[]),
            io_error(Obj::mk_nat(0)),
            io_error(Obj::mk_ctor(17, Vec::new(), &[])),
            io_error(Obj::mk_ctor(19, vec![Obj::mk_string("bad tag")], &[])),
            io_error(Obj::mk_ctor(1, vec![Obj::mk_string("missing code")], &[])),
            io_error(Obj::mk_ctor(
                1,
                vec![Obj::mk_nat(42)],
                &42_u32.to_ne_bytes(),
            )),
            io_error(Obj::mk_ctor(
                18,
                vec![Obj::mk_string("extra code")],
                &42_u32.to_ne_bytes(),
            )),
            io_error(Obj::mk_ctor(
                12,
                vec![Obj::mk_nat(1), Obj::mk_string("bad option")],
                &42_u32.to_ne_bytes(),
            )),
            io_error(Obj::mk_ctor(
                12,
                vec![
                    Obj::mk_ctor(1, vec![Obj::mk_nat(7)], &[]),
                    Obj::mk_string("bad filename"),
                ],
                &42_u32.to_ne_bytes(),
            )),
            io_error(Obj::mk_ctor(
                10,
                vec![Obj::mk_nat(0), Obj::mk_string("missing filename")],
                &42_u32.to_ne_bytes(),
            )),
        ] {
            assert!(stdio_result_transport(&result).is_none());
        }
    }
    no_leaks();
}
