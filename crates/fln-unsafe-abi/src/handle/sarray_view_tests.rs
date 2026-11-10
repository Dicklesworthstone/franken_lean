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

#[test]
fn owned_float_array_push_preserves_bits_capacity_and_shared_snapshots() {
    let _guard = lock();
    shadow::enable();
    {
        let bits = [
            0,
            (-0.0f64).to_bits(),
            1.25f64.to_bits(),
            f64::INFINITY.to_bits(),
            f64::NEG_INFINITY.to_bits(),
            0x7ff8_0000_0000_0123,
        ];
        let mut value = Obj::mk_sarray(8, &[]);
        let mut reused_capacity = false;
        for index in 0..96 {
            let (_, size, capacity, _) = value.try_borrow_sarray_view().unwrap();
            let identity = value.identity_token();
            value = value
                .try_float_array_push(f64::from_bits(bits[index % bits.len()]))
                .unwrap_or_else(|_| panic!("valid FloatArray"));
            if size < capacity {
                assert_eq!(value.identity_token(), identity);
                reused_capacity = true;
            }
        }
        assert!(
            reused_capacity,
            "native pushes must retain geometric spare capacity"
        );
        let snapshot = value.clone_ref();
        let original = snapshot.try_borrow_sarray_view().unwrap().3.to_vec();
        value = value
            .try_float_array_push(f64::from_bits(1))
            .unwrap_or_else(|_| panic!("shared FloatArray"));
        assert_ne!(value.identity_token(), snapshot.identity_token());
        assert_eq!(snapshot.try_borrow_sarray_view().unwrap().3, original);
        let (width, size, _, bytes) = value.try_borrow_sarray_view().unwrap();
        assert_eq!((width, size), (8, 97));
        for (index, word) in bytes.chunks_exact(8).enumerate() {
            let expected = if index == 96 {
                1
            } else {
                bits[index % bits.len()]
            };
            assert_eq!(u64::from_ne_bytes(word.try_into().unwrap()), expected);
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
fn owned_float_array_push_refuses_wrong_widths_and_hostile_headers() {
    let _guard = lock();
    for value in [
        Obj::mk_nat(0),
        Obj::mk_string("float array"),
        Obj::mk_array(Vec::new()),
        Obj::mk_sarray(1, &[0; 8]),
        Obj::mk_sarray(4, &[0; 8]),
        Obj::mk_sarray(16, &[0; 16]),
    ] {
        let identity = value.identity_token();
        let result = value.try_float_array_push(1.0);
        let Err(original) = result else {
            panic!("wrong FloatArray representation was accepted");
        };
        assert_eq!(original.identity_token(), identity);
    }
    let value = Obj::mk_sarray(8, &1.0f64.to_ne_bytes());
    let identity = value.identity_token();
    value.plant_sarray_size(2);
    let Err(original) = value.try_float_array_push(2.0) else {
        panic!("inconsistent FloatArray header was accepted");
    };
    assert_eq!(original.identity_token(), identity);
    original.restore_sarray_size(1);
    assert_eq!(
        original.try_borrow_sarray_view().unwrap().3,
        &1.0f64.to_ne_bytes()
    );
}
