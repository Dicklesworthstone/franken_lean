use super::{StdoutCapture, StdoutCaptureError};
use crate::handle::{Obj, StdioPutStrError};

fn stdout() -> Obj {
    Obj::stdio_stdout().unwrap().try_ctor_child(4).unwrap()
}

fn stderr() -> Obj {
    Obj::stdio_stderr().unwrap().try_ctor_child(4).unwrap()
}

fn write(callback: &Obj, text: &str) -> Result<Obj, StdioPutStrError> {
    callback.try_stdio_put_str(&Obj::mk_string(text), &Obj::mk_nat(0))
}

#[test]
fn evaluation_capture_orders_both_streams_and_native_diagnostics() {
    let _lock = crate::tests::lock();
    let output = stdout();
    let error = stderr();
    let output_rc = output.header().rc;
    let error_rc = error.header().rc;
    let scope = StdoutCapture::begin_evaluation(1024).unwrap();
    write(&output, "out: λ\0").unwrap();
    write(&error, "err: 🙂\n").unwrap();
    crate::trace_message(b"trace: \xff");
    assert!(crate::stdio::panic_message_via_stream(b"panic line"));
    write(&output, "tail").unwrap();
    let captured = scope.finish();
    assert_eq!(captured.error, None);
    assert_eq!(
        captured.bytes,
        "out: λ\0err: 🙂\ntrace: �\npanic line\ntail".as_bytes()
    );
    assert_eq!(output.header().rc, output_rc);
    assert_eq!(error.header().rc, error_rc);
}

#[test]
fn evaluation_capture_mixed_nested_scopes_restore_each_selected_stream() {
    let _lock = crate::tests::lock();
    let output = stdout();
    let error = stderr();
    let outer = StdoutCapture::begin_evaluation(100).unwrap();
    write(&output, "outer:").unwrap();
    let inner = StdoutCapture::begin(100).unwrap();
    write(&output, "inner").unwrap();
    write(&error, "stderr").unwrap();
    crate::trace_message(b" trace");
    assert_eq!(outer.finish().bytes, b"outer:stderr trace\n");
    write(&output, " still").unwrap();
    assert_eq!(inner.finish().bytes, b"inner still");

    let outer = StdoutCapture::begin_evaluation(100).unwrap();
    assert!(
        std::panic::catch_unwind(|| {
            let _inner = StdoutCapture::begin_evaluation(100).unwrap();
            crate::trace_message(b"discarded with inner");
            panic!("evaluation capture unwind control");
        })
        .is_err()
    );
    write(&error, "restored").unwrap();
    crate::trace_message(b" trace");
    assert_eq!(outer.finish().bytes, b"restored trace\n");
}

struct RestoreStderr(Option<Obj>);

impl RestoreStderr {
    fn install(stream: Obj) -> Self {
        Self(Some(Obj(crate::stdio::get_set_stderr(stream.into_raw()))))
    }
}

impl Drop for RestoreStderr {
    fn drop(&mut self) {
        if let Some(previous) = self.0.take() {
            drop(Obj(crate::stdio::get_set_stderr(previous.into_raw())));
        }
    }
}

#[test]
fn evaluation_capture_invalid_stderr_does_not_install_a_partial_scope() {
    let _lock = crate::tests::lock();
    let output = stdout();
    let outer = StdoutCapture::begin(100).unwrap();
    {
        let _restore = RestoreStderr::install(Obj::mk_nat(0));
        assert!(matches!(
            StdoutCapture::begin_evaluation(100),
            Err(StdoutCaptureError::InvalidStderr)
        ));
        assert!(!super::diagnostic_if_captured(b"invalid stream"));
        write(&output, "outer remains").unwrap();
    }
    assert_eq!(outer.finish().bytes, b"outer remains");
    let next = StdoutCapture::begin_evaluation(100).unwrap();
    crate::trace_message(b"stderr restored");
    assert_eq!(next.finish().bytes, b"stderr restored\n");
}

#[test]
fn evaluation_capture_lossy_diagnostics_use_exact_atomic_bounds() {
    let _lock = crate::tests::lock();
    for (input, expected, escaped) in [
        (b"x\xffy".as_slice(), "x�y\n", 7),
        (b"\xe2\x82".as_slice(), "�\n", 5),
        (b"\xf0\x28\x8c\x28".as_slice(), "�(�(\n", 10),
        (b"\xff\0".as_slice(), "�\0\n", 11),
        (b"".as_slice(), "\n", 2),
    ] {
        let scope = StdoutCapture::begin_evaluation(escaped).unwrap();
        assert!(crate::stdio::panic_message_via_stream(input));
        let captured = scope.finish();
        assert_eq!(captured.error, None);
        assert_eq!(captured.bytes, expected.as_bytes());

        let refused = StdoutCapture::begin_evaluation(escaped - 1).unwrap();
        assert!(crate::stdio::panic_message_via_stream(input));
        let captured = refused.finish();
        assert!(captured.bytes.is_empty());
        assert_eq!(
            captured.error,
            Some(StdoutCaptureError::Limit {
                limit: escaped - 1,
                requested: escaped,
            })
        );
    }
    let message = vec![0xff; 128 * 1024];
    let scope = StdoutCapture::begin_evaluation(5).unwrap();
    assert!(crate::stdio::panic_message_via_stream(&message));
    let captured = scope.finish();
    assert!(captured.bytes.is_empty());
    assert_eq!(
        captured.error,
        Some(StdoutCaptureError::Limit {
            limit: 5,
            requested: 3 * message.len() + 2,
        })
    );
}

#[test]
fn evaluation_capture_limit_is_sticky_and_native_diagnostics_do_not_leak() {
    const CHILD: &str = "FLN_EVALUATION_CAPTURE_LIMIT_CHILD";
    if std::env::var_os(CHILD).is_none() {
        let child = std::process::Command::new(std::env::current_exe().unwrap())
            .args([
                "--exact",
                "handle::stdout_capture::evaluation_tests::evaluation_capture_limit_is_sticky_and_native_diagnostics_do_not_leak",
                "--nocapture",
                "--test-threads=1",
            ])
            .env(CHILD, "1")
            .env("LEAN_BACKTRACE", "0")
            .env_remove("LEAN_ABORT_ON_PANIC")
            .output()
            .unwrap();
        assert!(
            child.status.success(),
            "child failed: stdout={} stderr={}",
            String::from_utf8_lossy(&child.stdout),
            String::from_utf8_lossy(&child.stderr)
        );
        assert!(
            child.stderr.is_empty(),
            "capture failure leaked native stderr: {}",
            String::from_utf8_lossy(&child.stderr)
        );
        return;
    }

    let _lock = crate::tests::lock();
    let scope = StdoutCapture::begin_evaluation(7).unwrap();
    write(&stdout(), "ok").unwrap();
    crate::trace_message(b"\xff\0");
    crate::report_panic(b"must remain captured after the limit");
    let error = StdoutCaptureError::Limit {
        limit: 7,
        requested: 13,
    };
    assert!(matches!(
        write(&stderr(), "later"),
        Err(StdioPutStrError::Capture(actual)) if actual == error
    ));
    let captured = scope.finish();
    assert_eq!(captured.bytes, b"ok");
    assert_eq!(captured.error, Some(error));
}
