use super::{StdoutCapture, StdoutCaptureError};
use crate::handle::{Obj, StdioPutStrError};

fn callback() -> Obj {
    Obj::stdio_stdout().unwrap().try_ctor_child(4).unwrap()
}

fn write(callback: &Obj, text: &str) -> Result<Obj, StdioPutStrError> {
    callback.try_stdio_put_str(&Obj::mk_string(text), &Obj::mk_nat(0))
}

#[test]
fn captured_native_result_requires_a_sink_and_preserves_borrowed_inputs() {
    let _lock = crate::tests::lock();
    let callback = callback();
    let text = Obj::mk_string("λ\0🙂\n");
    let world = Obj::mk_nat(0);
    let references = (callback.header().rc, text.header().rc);
    assert!(matches!(
        callback.try_captured_stdio_put_str(&text, &world),
        Err(StdioPutStrError::Capture(
            StdoutCaptureError::ScopeUnavailable
        ))
    ));
    let capture = StdoutCapture::begin_isolated(8, true).unwrap();
    let result = callback.try_captured_stdio_put_str(&text, &world).unwrap();
    assert!(native_result_is_ok_unit(&result));
    assert_eq!((callback.header().rc, text.header().rc), references);
    assert_eq!(capture.finish().bytes, "λ\0🙂\n".as_bytes());
}

fn native_result_is_ok_unit(value: &Obj) -> bool {
    // Observe the same one-field result that lean_io_result_mk_ok emits;
    // the live compiled-IR fixture independently consumes this ABI on Golem.
    value.header().tag == 0
        && value.header().other == 1
        && value
            .try_ctor_child(0)
            .is_some_and(|unit| unit.is_scalar() && unit.unbox() == 0)
}

#[test]
fn captured_native_result_retains_prefix_and_refuses_invalid_inputs() {
    let _lock = crate::tests::lock();
    let callback = callback();
    let capture = StdoutCapture::begin_isolated(2, true).unwrap();
    for (text, world) in [
        (Obj::mk_nat(0), Obj::mk_nat(0)),
        (Obj::mk_string("bad"), Obj::mk_nat(1)),
    ] {
        assert!(callback.try_captured_stdio_put_str(&text, &world).is_err());
    }
    callback
        .try_captured_stdio_put_str(&Obj::mk_string("ok"), &Obj::mk_nat(0))
        .unwrap();
    assert!(matches!(
        callback.try_captured_stdio_put_str(&Obj::mk_string("x"), &Obj::mk_nat(0)),
        Err(StdioPutStrError::Capture(StdoutCaptureError::Limit {
            limit: 2,
            requested: 3
        }))
    ));
    let output = capture.finish();
    assert_eq!(output.bytes, b"ok");
    assert!(output.error.is_some());
}

#[test]
fn capture_keeps_utf8_nuls_and_thread_sinks_independent() {
    let _lock = crate::tests::lock();
    let threads: Vec<_> = (0..3)
        .map(|index| {
            std::thread::spawn(move || {
                let scope = StdoutCapture::begin(1024).unwrap();
                let callback = callback();
                let value = format!("thread{index}: λ🙂\0tail\n");
                let original = callback.header().rc;
                let result = write(&callback, &value).unwrap();
                assert_eq!(result.try_ctor_child(0).unwrap().unbox(), 1);
                assert_eq!(callback.header().rc, original);
                let output = scope.finish();
                assert_eq!(output.error, None);
                assert_eq!(output.bytes, value.as_bytes());
                value
            })
        })
        .collect();
    for (index, thread) in threads.into_iter().enumerate() {
        assert!(
            thread
                .join()
                .unwrap()
                .starts_with(&format!("thread{index}:"))
        );
    }
}

#[test]
fn capture_nested_finish_drop_and_unwind_restore_only_their_scope() {
    let _lock = crate::tests::lock();
    let callback = callback();
    let outer = StdoutCapture::begin(100).unwrap();
    write(&callback, "outer").unwrap();
    let inner = StdoutCapture::begin(100).unwrap();
    write(&callback, "inner").unwrap();
    assert_eq!(outer.finish().bytes, b"outer");
    write(&callback, " stays").unwrap();
    assert_eq!(inner.finish().bytes, b"inner stays");
    let outer = StdoutCapture::begin(100).unwrap();
    let inner = StdoutCapture::begin(100).unwrap();
    drop(outer);
    write(&callback, "drop-safe").unwrap();
    assert_eq!(inner.finish().bytes, b"drop-safe");
    let outer = StdoutCapture::begin(100).unwrap();
    assert!(
        std::panic::catch_unwind(|| {
            let _inner = StdoutCapture::begin(100).unwrap();
            panic!("capture unwind control");
        })
        .is_err()
    );
    write(&callback, "restored").unwrap();
    assert_eq!(outer.finish().bytes, b"restored");
}

#[test]
fn capture_limits_refuse_whole_write_and_retain_accepted_prefix() {
    let _lock = crate::tests::lock();
    let callback = callback();
    let scope = StdoutCapture::begin(7).unwrap();
    write(&callback, "ok").unwrap();
    let error = StdoutCaptureError::Limit {
        limit: 7,
        requested: 8,
    };
    assert!(
        matches!(write(&callback, "\0"), Err(StdioPutStrError::Capture(actual)) if actual == error)
    );
    assert!(
        matches!(write(&callback, "z"), Err(StdioPutStrError::Capture(actual)) if actual == error)
    );
    let output = scope.finish();
    assert_eq!(output.bytes, b"ok");
    assert_eq!(output.error, Some(error));
    let exact = StdoutCapture::begin(8).unwrap();
    write(&callback, "ok\0").unwrap();
    assert_eq!(exact.finish().bytes, b"ok\0");
}

#[test]
fn capture_oversized_aliased_text_can_retry_without_consuming_its_bytes() {
    let _lock = crate::tests::lock();
    let callback = callback();
    let text = "λ🙂\0".repeat(64 * 1024);
    let value = Obj::mk_string(&text);
    let alias = value.clone_ref();
    let original_references = value.header().rc;
    // Each pair of Unicode characters occupies six unchanged UTF-8 bytes;
    // the NUL contributes six escaped bytes to the existing capture policy.
    let escaped_bytes = 12 * 64 * 1024;
    let scope = StdoutCapture::begin(32).unwrap();
    write(&callback, "prefix").unwrap();
    let expected = StdoutCaptureError::Limit {
        limit: 32,
        requested: escaped_bytes + 6,
    };
    assert!(matches!(
        callback.try_stdio_put_str(&value, &Obj::mk_nat(0)),
        Err(StdioPutStrError::Capture(error)) if error == expected
    ));
    assert_eq!(value.header().rc, original_references);
    let captured = scope.finish();
    assert_eq!(captured.bytes, b"prefix");
    assert_eq!(captured.error, Some(expected));

    let retry = StdoutCapture::begin(escaped_bytes).unwrap();
    let result = callback.try_stdio_put_str(&alias, &Obj::mk_nat(0)).unwrap();
    assert_eq!(result.try_ctor_child(0).unwrap().unbox(), 1);
    let captured = retry.finish();
    assert_eq!(captured.error, None);
    assert_eq!(captured.bytes, text.as_bytes());
    assert_eq!(value.header().rc, original_references);
    let (size, _, _, bytes) = value.try_borrow_string_view().unwrap();
    assert_eq!(&bytes[..size - 1], text.as_bytes());
}

#[test]
fn capture_never_accepts_invalid_callback_string_or_world() {
    let _lock = crate::tests::lock();
    let scope = StdoutCapture::begin(100).unwrap();
    let callback = callback();
    assert!(matches!(
        write(&Obj::mk_nat(0), "not written"),
        Err(StdioPutStrError::InvalidCallback)
    ));
    assert!(matches!(
        callback.try_stdio_put_str(&Obj::mk_nat(1), &Obj::mk_nat(0)),
        Err(StdioPutStrError::InvalidString)
    ));
    assert!(matches!(
        callback.try_stdio_put_str(&Obj::mk_string("not written"), &Obj::mk_nat(1)),
        Err(StdioPutStrError::InvalidWorld)
    ));
    let result = scope.finish();
    assert!(result.bytes.is_empty());
    assert_eq!(result.error, None);
}

#[test]
fn isolated_capture_validates_both_streams_and_keeps_raw_byte_order() {
    let _lock = crate::tests::lock();
    let stdout = callback();
    let stderr = Obj::stdio_stderr().unwrap().try_ctor_child(4).unwrap();
    let outer = StdoutCapture::begin_isolated(100, true).unwrap();
    let inner = StdoutCapture::begin_isolated(11, true).unwrap();
    write(&stdout, "λ\0").unwrap();
    write(&stderr, "🙂").unwrap();
    assert!(crate::stdio::panic_message_via_stream(b"end"));
    let result = inner.finish();
    assert_eq!(result.error, None);
    assert_eq!(result.bytes, "λ\0🙂end\n".as_bytes());
    assert_eq!(StdoutCapture::current_error(), None);

    // A stdout-only inner scope leaves stderr with its previous owner.
    let inner = StdoutCapture::begin_isolated(1, false).unwrap();
    write(&stderr, "outer-stderr").unwrap();
    write(&stdout, "x").unwrap();
    assert_eq!(inner.finish().bytes, b"x");
    assert_eq!(outer.finish().bytes, b"outer-stderr");
    assert_eq!(
        StdoutCapture::append_current("no physical write"),
        Err(StdoutCaptureError::ScopeUnavailable)
    );
}

#[test]
fn isolated_diagnostic_limit_retains_prefix_and_restores_outer_capture() {
    let _lock = crate::tests::lock();
    let stdout = callback();
    let outer = StdoutCapture::begin(100).unwrap();
    let inner = StdoutCapture::begin_isolated(4, true).unwrap();
    write(&stdout, "ok").unwrap();
    let expected = StdoutCaptureError::Limit {
        limit: 4,
        requested: 6,
    };
    assert!(crate::stdio::panic_message_via_stream(b"bad"));
    assert_eq!(StdoutCapture::current_error(), Some(expected));
    assert!(matches!(
        write(&stdout, "x"),
        Err(StdioPutStrError::Capture(error)) if error == expected
    ));
    let result = inner.finish();
    assert_eq!(result.bytes, b"ok");
    assert_eq!(result.error, Some(expected));
    assert_eq!(StdoutCapture::current_error(), None);
    // The outer JSON allowance still counts escaped bytes, independently of
    // the inner raw-byte allowance and without replaying either stream.
    StdoutCapture::append_current("\0\n").unwrap();
    write(&stdout, "after").unwrap();
    let result = outer.finish();
    assert_eq!(result.error, None);
    assert_eq!(result.bytes, b"\0\nafter");

    let scope = StdoutCapture::begin_isolated(5, true).unwrap();
    assert!(crate::stdio::panic_message_via_stream(b"x\xff"));
    let result = scope.finish();
    assert_eq!(result.error, None);
    assert_eq!(result.bytes, "x\u{fffd}\n".as_bytes());
    let scope = StdoutCapture::begin_isolated(4, true).unwrap();
    assert!(crate::stdio::panic_message_via_stream(b"x\xff"));
    let result = scope.finish();
    assert!(result.bytes.is_empty());
    assert_eq!(
        result.error,
        Some(StdoutCaptureError::Limit {
            limit: 4,
            requested: 5,
        })
    );
}
