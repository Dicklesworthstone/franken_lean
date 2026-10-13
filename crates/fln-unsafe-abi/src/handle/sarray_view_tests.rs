use crate::handle::Obj;
use crate::layout::LeanSarrayObject;
use crate::shadow::{self, EventKind};
use crate::tests::lock;
use std::mem::offset_of;

#[test]
fn borrowed_sarray_view_aliases_only_initialized_storage() {
    let _guard = lock();
    shadow::enable();
    {
        for (width, data) in [(1, &b""[..]), (1, &b"a\0\xffz"[..]), (4, &b"12345678"[..])] {
            let value = Obj::mk_sarray(width, data);
            let alias = value.clone_ref();
            let references = value.header().rc;
            let (elem, size, capacity, first) = value.try_borrow_sarray_view().unwrap();
            let second = value.try_borrow_sarray_view().unwrap().3;
            let aliased = alias.try_borrow_sarray_view().unwrap().3;
            assert_eq!(
                (elem, size, capacity),
                (
                    width,
                    data.len() / usize::from(width),
                    data.len() / usize::from(width)
                )
            );
            assert_eq!(first, data);
            assert_eq!(first.as_ptr(), second.as_ptr());
            assert_eq!(first.as_ptr(), aliased.as_ptr());
            assert_eq!(
                first.as_ptr() as usize,
                value.identity_token() + offset_of!(LeanSarrayObject, m_data)
            );
            assert_eq!(value.header().rc, references);
            let mut copy = value.try_sarray_view().unwrap().3;
            assert_eq!(copy, data);
            if !copy.is_empty() {
                assert_ne!(copy.as_ptr(), first.as_ptr());
                copy[0] ^= 0xff;
                assert_eq!(first, data, "the copying observer remains independent");
                value.plant_sarray_size(size - 1);
                let (elem, shorter, cap, live) = value.try_borrow_sarray_view().unwrap();
                assert_eq!((elem, shorter, cap), (width, size - 1, capacity));
                assert_eq!(live, &data[..data.len() - usize::from(width)]);
                value.restore_sarray_size(size);
            }
            drop(value);
            assert_eq!(alias.try_borrow_sarray_view().unwrap().3, data);
        }
    }
    let (events, live) = shadow::disable_and_drain();
    assert_eq!(live, 0);
    assert!(events.iter().all(|event| !matches!(
        event.kind,
        EventKind::DoubleRelease | EventKind::ForeignPointer
    )));
}

#[test]
fn borrowed_sarray_view_refuses_categories_and_hostile_headers() {
    let _guard = lock();
    for value in [
        Obj::mk_nat(1),
        Obj::mk_string("bytes"),
        Obj::mk_array(vec![Obj::mk_nat(1)]),
        Obj::mk_ctor(0, vec![Obj::mk_nat(1)], &[]),
    ] {
        assert!(value.try_borrow_sarray_view().is_none());
        assert!(value.try_sarray_view().is_none());
    }
    let value = Obj::mk_sarray(2, b"abcd");
    value.plant_sarray_size(3);
    assert!(value.try_borrow_sarray_view().is_none());
    assert!(value.try_sarray_view().is_none());
    value.restore_sarray_size(2);
    value.plant_sarray_elem(0);
    assert!(value.try_borrow_sarray_view().is_none());
    assert!(value.try_sarray_view().is_none());
    value.plant_sarray_elem(2);
    assert_eq!(
        value.try_borrow_sarray_view(),
        Some((2, 2, 2, &b"abcd"[..]))
    );
}
