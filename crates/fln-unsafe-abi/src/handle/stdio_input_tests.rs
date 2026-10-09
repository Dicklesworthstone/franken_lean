use super::{Obj, fs::FileReadError};
use crate::tests::lock;
use std::path::Path;
use std::sync::atomic::{AtomicUsize, Ordering};

static FOREIGN_CALLS: AtomicUsize = AtomicUsize::new(0);
extern "C" fn foreign_read(
    _: *mut crate::layout::LeanObject,
    _: *mut crate::layout::LeanObject,
) -> *mut crate::layout::LeanObject {
    FOREIGN_CALLS.fetch_add(1, Ordering::SeqCst);
    crate::tagged::boxi(0)
}

fn malformed(callback: &Obj, arity: u16, captures: Vec<Obj>) -> Obj {
    // SAFETY: the canonical callback is live; a fresh closure is fully
    // initialized for observation only, never sent to generic native apply.
    // UNSAFE-LEDGER: FLN-UL-0649
    #[allow(unsafe_code)]
    unsafe {
        let (target, _, _, _) = crate::object::closure_fields(callback.0);
        let value = crate::object::alloc_closure(target, arity, captures.len() as u16);
        for (index, capture) in captures.into_iter().enumerate() {
            crate::object::closure_set(value, index, capture.into_raw());
        }
        Obj(value)
    }
}

struct Restore(Option<Obj>);
impl Restore {
    fn install(stream: Obj) -> Self {
        Self(Some(Obj(crate::stdio::get_set_stdin(stream.into_raw()))))
    }
}
impl Drop for Restore {
    fn drop(&mut self) {
        if let Some(previous) = self.0.take() {
            drop(Obj(crate::stdio::get_set_stdin(previous.into_raw())));
        }
    }
}
fn stream(path: &Path, mode: usize) -> Obj {
    let opened = Obj::try_file_open(
        &Obj::mk_string(path.to_str().unwrap()),
        &Obj::mk_nat(mode),
        &Obj::mk_nat(0),
    )
    .unwrap();
    assert_eq!(opened.try_ctor_child(1).unwrap().unbox(), 1);
    let handle = opened.try_ctor_child(0).unwrap();
    // SAFETY: successful guarded open supplies one owned exact Handle;
    // stream_of_handle consumes it into six fully initialized native closures.
    // UNSAFE-LEDGER: FLN-UL-0648
    #[allow(unsafe_code)]
    unsafe {
        Obj(crate::stdio::stream_of_handle(handle.into_raw()))
    }
}
fn text(packet: &Obj) -> String {
    assert_eq!(packet.header().other, 7);
    assert_eq!(packet.try_ctor_child(1).unwrap().unbox(), 1);
    let value = packet.try_ctor_child(0).unwrap();
    let (size, _, _, bytes) = value.try_string_view().unwrap();
    String::from_utf8(bytes[..size - 1].to_vec()).unwrap()
}
fn read(callback: &Obj) -> Obj {
    callback
        .try_stdio_get_line(&Obj::mk_nat(0), 1024, 1024)
        .unwrap()
        .unwrap()
}
fn path(label: &str) -> std::path::PathBuf {
    std::env::temp_dir().join(format!(
        "fln-stdin-{}-{}-{label}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos()
    ))
}

#[test]
fn stdin_callbacks_retain_shared_cursor_after_tls_restore_and_preserve_borrows() {
    let _lock = lock();
    drop(Obj::stdio_stdin().unwrap());
    let file = path("cursor");
    std::fs::write(&file, "λ🙂\0first\r\nsecond\ntail").unwrap();
    let callback = {
        let _restore = Restore::install(stream(&file, 0));
        let stdin = Obj::stdio_stdin().unwrap();
        assert!((0..6).all(|index| {
            stdin
                .try_ctor_child(index)
                .unwrap()
                .is_stdio_get_line_closure()
                == (index == 3)
        }));
        stdin.try_ctor_child(3).unwrap()
    };
    let alias = callback.clone_ref();
    let before = callback.header().rc;
    assert!(matches!(
        callback.try_stdio_get_line(&Obj::mk_nat(1), 1024, 1024),
        Err(FileReadError::InvalidWorld)
    ));
    assert_eq!(text(&read(&callback)), "λ🙂\0first\r\n");
    assert_eq!(callback.header().rc, before);
    assert_eq!(text(&read(&alias)), "second\n");
    assert_eq!(text(&read(&callback)), "tail");
    assert_eq!(text(&read(&alias)), "");
    assert_eq!(text(&read(&callback)), "");
}

#[test]
fn stdin_getter_and_read_preconditions_refuse_before_cursor_effects() {
    let _lock = lock();
    drop(Obj::stdio_stdin().unwrap());
    let first = path("first");
    let second = path("second");
    std::fs::write(&first, b"unchanged\n").unwrap();
    std::fs::write(&second, b"other\n").unwrap();
    let native = stream(&first, 0);
    let other = stream(&second, 0);
    FOREIGN_CALLS.store(0, Ordering::SeqCst);
    for value in [
        Obj::mk_nat(0),
        Obj::mk_string("not a stream"),
        Obj::mk_ctor(0, Vec::new(), &[]),
    ] {
        let _restore = Restore::install(value);
        assert!(Obj::stdio_stdin().is_none());
    }
    let canonical = native.try_ctor_child(3).unwrap();
    for value in [
        Obj::mk_closure_fn2(foreign_read, vec![Obj::mk_nat(0)]),
        malformed(&canonical, 3, vec![Obj::mk_nat(0)]),
        malformed(&canonical, 2, vec![]),
        // Live closures retain an open argument slot. The two-capture mutant
        // therefore has arity three; the arity-two zero-capture case above
        // independently exercises the fixed-count refusal.
        malformed(&canonical, 3, vec![Obj::mk_nat(0), Obj::mk_nat(0)]),
        malformed(&canonical, 2, vec![Obj::mk_nat(0)]),
        malformed(&canonical, 2, vec![Obj::mk_external_counting()]),
    ] {
        assert!(!value.is_stdio_get_line_closure());
        assert!(
            value
                .try_stdio_get_line(&Obj::mk_nat(0), 1024, 1024)
                .unwrap()
                .is_none()
        );
    }
    assert_eq!(FOREIGN_CALLS.load(Ordering::SeqCst), 0);
    for index in 0..6 {
        let mut fields: Vec<_> = (0..6).map(|i| native.try_ctor_child(i).unwrap()).collect();
        fields[index] = other.try_ctor_child(index).unwrap();
        let _restore = Restore::install(Obj::mk_ctor(0, fields, &[]));
        assert!(
            Obj::stdio_stdin().is_none(),
            "different captured Handle in field {index}"
        );
    }
    for index in [0, 1, 2, 4, 5] {
        let callback = native.try_ctor_child(index).unwrap();
        assert!(!callback.is_stdio_get_line_closure());
        assert!(
            callback
                .try_stdio_get_line(&Obj::mk_nat(0), 1024, 1024)
                .unwrap()
                .is_none()
        );
    }
    for value in [
        Obj::mk_nat(0),
        Obj::mk_closure(2, vec![Obj::mk_nat(0)]),
        Obj::mk_external_counting(),
    ] {
        assert!(!value.is_stdio_get_line_closure());
        assert!(
            value
                .try_stdio_get_line(&Obj::mk_nat(0), 1024, 1024)
                .unwrap()
                .is_none()
        );
    }
    assert_eq!(
        text(&read(&native.try_ctor_child(3).unwrap())),
        "unchanged\n"
    );
    let write_only = stream(&first, 4).try_ctor_child(3).unwrap();
    let error = read(&write_only);
    assert_eq!(error.try_ctor_child(1).unwrap().unbox(), 0);
    assert_eq!(error.try_ctor_child(2).unwrap().unbox(), 12);
    assert_eq!(error.try_ctor_child(3).unwrap().unbox(), 9);
}

#[test]
fn stdin_callback_resource_failure_retains_the_consumed_cursor() {
    let _lock = lock();
    let file = path("budget");
    std::fs::write(&file, b"abcd\nnext\n").unwrap();
    let callback = stream(&file, 0).try_ctor_child(3).unwrap();
    assert_eq!(
        callback
            .try_stdio_get_line(&Obj::mk_nat(0), 2, 100)
            .err()
            .unwrap(),
        FileReadError::InputLimit {
            limit: 2,
            observed: 3,
            bytes_consumed: 3
        }
    );
    assert_eq!(text(&read(&callback)), "d\n");
    assert_eq!(text(&read(&callback)), "next\n");
}
