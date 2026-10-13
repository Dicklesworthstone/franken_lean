//! The stderr getter uses the same complete native-stream gate as stdin/stdout.
use super::Obj;
use crate::tests::lock;

struct Restore(Option<Obj>);
impl Restore {
    fn install(stream: Obj) -> Self {
        Self(Some(Obj(crate::stdio::get_set_stderr(stream.into_raw()))))
    }
}
impl Drop for Restore {
    fn drop(&mut self) {
        if let Some(previous) = self.0.take() {
            drop(Obj(crate::stdio::get_set_stderr(previous.into_raw())));
        }
    }
}

#[test]
fn stderr_getter_refuses_non_native_tls_and_restores_its_scope() {
    let _lock = lock();
    let original = Obj::stdio_stderr().unwrap();
    assert_eq!(original.header().other, 6);
    for bad in [
        Obj::mk_nat(0),
        Obj::mk_string("not a stream"),
        Obj::mk_ctor(0, (0..6).map(|_| Obj::mk_nat(0)).collect(), &[]),
        Obj::mk_closure(1, vec![]),
    ] {
        {
            let _restore = Restore::install(bad);
            assert!(Obj::stdio_stderr().is_none());
            assert!(Obj::stdio_stdin().is_some());
            assert!(Obj::stdio_stdout().is_some());
        }
        let restored = Obj::stdio_stderr().unwrap();
        assert!(
            restored
                .try_ctor_child(4)
                .unwrap()
                .is_stdio_put_str_closure()
        );
    }
}

#[test]
fn stderr_callbacks_keep_the_selected_stream_after_tls_restore() {
    let _lock = lock();
    let stdout = Obj::stdio_stdout().unwrap();
    let callback =
        {
            let _restore = Restore::install(stdout);
            let stderr = Obj::stdio_stderr().unwrap();
            assert!((0..6).all(|i| {
                stderr.try_ctor_child(i).unwrap().is_stdio_put_str_closure() == (i == 4)
            }));
            stderr.try_ctor_child(4).unwrap()
        };
    let capture = super::stdout_capture::StdoutCapture::begin(1024).unwrap();
    let text = Obj::mk_string("stderr alias: λ🙂\0tail\n");
    let before = text.header().rc;
    let result = callback.try_stdio_put_str(&text, &Obj::mk_nat(0)).unwrap();
    assert_eq!(result.try_ctor_child(0).unwrap().unbox(), 1);
    assert_eq!(text.header().rc, before);
    let output = capture.finish();
    assert_eq!(output.error, None);
    assert_eq!(output.bytes, "stderr alias: λ🙂\0tail\n".as_bytes());
}
