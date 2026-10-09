use super::{StdoutCapture, StdoutCaptureError};
use crate::handle::{Obj, StdioPutStrError};

fn callback() -> Obj {
    Obj::stdio_stdout().unwrap().try_ctor_child(4).unwrap()
}

fn write(callback: &Obj, text: &str) -> Result<Obj, StdioPutStrError> {
    callback.try_stdio_put_str(&Obj::mk_string(text), &Obj::mk_nat(0))
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
