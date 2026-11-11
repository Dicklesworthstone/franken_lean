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
        for (index, word) in bytes.as_chunks::<8>().0.iter().enumerate() {
            let expected = if index == 96 {
                1
            } else {
                bits[index % bits.len()]
            };
            assert_eq!(u64::from_ne_bytes(*word), expected);
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

#[test]
fn owned_sarray_updates_reuse_storage_and_preserve_shared_snapshots() {
    let _guard = lock();
    shadow::enable();
    {
        for width in [1u8, 8] {
            let initial = vec![0; 256 * usize::from(width)];
            let mut array = Obj::mk_sarray(width, &initial);
            let identity = array.identity_token();
            for index in 0..256 {
                let value = (0x7ff8_0000_0000_0000u64 | index as u64).to_ne_bytes();
                array = array
                    .try_sarray_set(index, &value[..usize::from(width)])
                    .unwrap_or_else(|_| panic!("a checked element update must succeed"));
                assert_eq!(array.identity_token(), identity);
            }
            let snapshot = array.clone_ref();
            let before = snapshot.try_borrow_sarray_view().unwrap().3.to_vec();
            let replacement = vec![0x55; usize::from(width)];
            let array = array
                .try_sarray_set(0, &replacement)
                .unwrap_or_else(|_| panic!("shared scalar arrays must copy"));
            assert_ne!(array.identity_token(), snapshot.identity_token());
            assert_eq!(snapshot.try_borrow_sarray_view().unwrap().3, before);
            let bytes = array.try_borrow_sarray_view().unwrap().3;
            assert_eq!(&bytes[..usize::from(width)], replacement);
            assert_eq!(&bytes[usize::from(width)..], &before[usize::from(width)..]);

            // A replacement may itself borrow the old array through an alias.
            // The copy must precede the write without invalidating that borrow.
            let replacement_owner = array.clone_ref();
            let array = array
                .try_sarray_set(
                    1,
                    &replacement_owner.try_borrow_sarray_view().unwrap().3[..usize::from(width)],
                )
                .unwrap_or_else(|_| panic!("borrowed replacement bytes remain live"));
            assert_ne!(array.identity_token(), replacement_owner.identity_token());
            assert_eq!(
                &array.try_borrow_sarray_view().unwrap().3
                    [usize::from(width)..2 * usize::from(width)],
                replacement
            );
        }
        let array = Obj::mk_sarray(1, &[])
            .try_byte_array_push(4)
            .unwrap_or_else(|_| panic!("byte push"));
        let capacity = array.try_borrow_sarray_view().unwrap().2;
        let snapshot = array.clone_ref();
        let updated = array
            .try_sarray_set(0, &[9])
            .unwrap_or_else(|_| panic!("shared byte update"));
        assert_eq!(updated.try_borrow_sarray_view().unwrap().2, capacity);
        assert_eq!(snapshot.try_borrow_sarray_view().unwrap().3, &[4]);
    }
    let (events, live) = shadow::disable_and_drain();
    assert_eq!(live, 0);
    assert!(events.iter().all(|event| !matches!(
        event.kind,
        EventKind::DoubleRelease | EventKind::ForeignPointer
    )));
}

#[test]
fn owned_sarray_updates_refuse_invalid_layouts_bounds_and_widths() {
    let _guard = lock();
    for value in [
        Obj::mk_nat(0),
        Obj::mk_string("bytes"),
        Obj::mk_array(Vec::new()),
    ] {
        let identity = value.identity_token();
        let Err(original) = value.try_sarray_set(0, &[1]) else {
            panic!("a non-scalar-array cannot be mutated");
        };
        assert_eq!(original.identity_token(), identity);
    }
    for (index, bytes) in [
        (0, &[][..]),
        (0, &[1, 2][..]),
        (1, &[1][..]),
        (usize::MAX, &[1][..]),
    ] {
        let value = Obj::mk_sarray(1, &[7]);
        let identity = value.identity_token();
        let Err(original) = value.try_sarray_set(index, bytes) else {
            panic!("invalid width or index was accepted");
        };
        assert_eq!(original.identity_token(), identity);
        assert_eq!(original.try_borrow_sarray_view().unwrap().3, &[7]);
    }
    let array = Obj::mk_sarray(8, &1.25f64.to_ne_bytes());
    array.plant_sarray_size(2);
    let Err(original) = array.try_sarray_set(0, &(-0.0f64).to_ne_bytes()) else {
        panic!("an inconsistent header was accepted");
    };
    original.restore_sarray_size(1);
    assert_eq!(
        original.try_borrow_sarray_view().unwrap().3,
        &1.25f64.to_ne_bytes()
    );
    original.plant_sarray_elem(0);
    let Err(original) = original.try_sarray_set(0, &[]) else {
        panic!("zero-width elements were accepted");
    };
    original.plant_sarray_elem(8);
    assert_eq!(
        original.try_borrow_sarray_view().unwrap().3,
        &1.25f64.to_ne_bytes()
    );
    assert!(!super::sarray_allocation_fits(0, 0));
    assert!(!super::sarray_allocation_fits(8, usize::MAX));
    assert!(!super::sarray_allocation_fits(1, isize::MAX as usize));
}

#[test]
fn owned_byte_array_slice_copy_reuses_capacity_and_preserves_aliases() {
    let _guard = lock();
    shadow::enable();
    {
        let source = Obj::mk_sarray(1, b"ABCDE");
        let mut destination = Obj::mk_sarray(1, &[]);
        for byte in b"123" {
            destination = destination
                .try_byte_array_push(*byte)
                .unwrap_or_else(|_| panic!("byte push"));
        }
        let identity = destination.identity_token();
        let capacity = destination.try_borrow_sarray_view().unwrap().2;
        assert_eq!(capacity, 6);
        destination = destination
            .try_byte_array_copy_slice(&source, 1, 1, 2, true)
            .unwrap_or_else(|_| panic!("bounded copy"));
        assert_eq!(destination.identity_token(), identity);
        assert_eq!(destination.try_borrow_sarray_view().unwrap().3, b"1BC");
        destination = destination
            .try_byte_array_copy_slice(&source, 2, usize::MAX, usize::MAX, false)
            .unwrap_or_else(|_| panic!("clamped copy"));
        assert_eq!(destination.identity_token(), identity);
        assert_eq!(destination.try_borrow_sarray_view().unwrap().3, b"1BCCDE");
        let snapshot = destination.clone_ref();
        destination = destination
            .try_byte_array_copy_slice(&source, 0, 0, 2, false)
            .unwrap_or_else(|_| panic!("shared destination copy"));
        assert_ne!(destination.identity_token(), snapshot.identity_token());
        assert_eq!(destination.try_borrow_sarray_view().unwrap().2, capacity);
        assert_eq!(destination.try_borrow_sarray_view().unwrap().3, b"ABCCDE");
        assert_eq!(snapshot.try_borrow_sarray_view().unwrap().3, b"1BCCDE");
        assert_eq!(source.try_borrow_sarray_view().unwrap().3, b"ABCDE");

        let source_alias = destination.clone_ref();
        destination = destination
            .try_byte_array_copy_slice(&source_alias, 0, 1, 4, true)
            .unwrap_or_else(|_| panic!("overlapping logical source and destination"));
        assert_eq!(destination.try_borrow_sarray_view().unwrap().3, b"AABCCE");
        assert_eq!(source_alias.try_borrow_sarray_view().unwrap().3, b"ABCCDE");

        for exact in [false, true] {
            let copied = Obj::mk_sarray(1, b"x")
                .try_byte_array_copy_slice(&source, 0, usize::MAX, usize::MAX, exact)
                .unwrap_or_else(|_| panic!("growing copy"));
            let (_, size, capacity, bytes) = copied.try_borrow_sarray_view().unwrap();
            assert_eq!((size, capacity), (6, if exact { 6 } else { 12 }));
            assert_eq!(bytes, b"xABCDE");
        }
        let identity = destination.identity_token();
        let destination = destination
            .try_byte_array_copy_slice(&source, usize::MAX, usize::MAX, usize::MAX, true)
            .unwrap_or_else(|_| panic!("a source offset past the end is a no-op"));
        assert_eq!(destination.identity_token(), identity);
        assert_eq!(destination.try_borrow_sarray_view().unwrap().3, b"AABCCE");
    }
    let (events, live) = shadow::disable_and_drain();
    assert_eq!(live, 0);
    assert!(events.iter().all(|event| !matches!(
        event.kind,
        EventKind::DoubleRelease | EventKind::ForeignPointer
    )));
}

#[test]
fn owned_byte_array_slice_copy_refuses_invalid_carriers_before_transfer() {
    let _guard = lock();
    for invalid in [
        Obj::mk_nat(0),
        Obj::mk_string("bytes"),
        Obj::mk_sarray(8, &[0; 8]),
    ] {
        let identity = invalid.identity_token();
        let source = Obj::mk_sarray(1, b"abc");
        let Err(original) = invalid.try_byte_array_copy_slice(&source, 0, 0, 1, false) else {
            panic!("invalid destination was accepted");
        };
        assert_eq!(original.identity_token(), identity);
        let destination = Obj::mk_sarray(1, b"xyz");
        let Err(destination) = destination.try_byte_array_copy_slice(&original, 0, 0, 1, false)
        else {
            panic!("invalid source was accepted");
        };
        assert_eq!(destination.try_borrow_sarray_view().unwrap().3, b"xyz");
    }
    let source = Obj::mk_sarray(1, b"abc");
    source.plant_sarray_size(4);
    let Err(destination) =
        Obj::mk_sarray(1, b"xyz").try_byte_array_copy_slice(&source, 0, 0, 1, false)
    else {
        panic!("an inconsistent source header was accepted");
    };
    source.restore_sarray_size(3);
    assert_eq!(source.try_borrow_sarray_view().unwrap().3, b"abc");
    destination.plant_sarray_size(4);
    let Err(destination) = destination.try_byte_array_copy_slice(&source, 0, 0, 1, false) else {
        panic!("an inconsistent destination header was accepted");
    };
    destination.restore_sarray_size(3);
    assert_eq!(destination.try_borrow_sarray_view().unwrap().3, b"xyz");
}
