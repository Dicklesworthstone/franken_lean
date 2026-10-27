use super::*;
use fln_core::outcome::InconclusiveCause;

const ROW: &str = "extern:String.ofByteArray";

fn assert_text(value: &Obj, expected: &str) {
    let (size, capacity, characters, bytes) = value
        .try_borrow_string_view()
        .expect("canonical native String");
    assert_eq!(size, expected.len() + 1);
    assert!(capacity >= size);
    assert_eq!(characters, expected.chars().count());
    assert_eq!(&bytes[..size - 1], expected.as_bytes());
    assert_eq!(bytes[size - 1], 0);
}

#[test]
fn byte_array_string_conversion_rejects_wrong_carriers_and_element_widths() {
    for value in [
        Obj::mk_nat(0),
        Obj::mk_string("bytes"),
        Obj::mk_array(vec![]),
        Obj::mk_ctor(0, vec![], &[]),
    ] {
        let kind = value_kind(&value);
        assert!(matches!(string_from_byte_array(&value, 8),
            Err(IntrinsicFailure::Refused(VmRefusal::TypeMismatch {
                operation: "String.ofByteArray", argument: 0, expected: "ByteArray", actual,
            })) if actual == kind));
    }
    for width in [2, 4, 8] {
        let value = Obj::mk_sarray(width, b"abcdefgh");
        let alias = value.clone_ref();
        let references = value.header().rc;
        assert!(matches!(
            string_from_byte_array(&value, 8),
            Err(IntrinsicFailure::Refused(VmRefusal::InvalidByteArrayObject))
        ));
        assert_eq!(value.header().rc, references);
        assert_eq!(alias.try_borrow_sarray_view().unwrap().3, b"abcdefgh");
    }
}

#[test]
fn byte_array_string_conversion_bounds_bytes_before_utf8_and_allocation() {
    let exact = Obj::mk_sarray(1, "é\0".as_bytes());
    let converted = match string_from_byte_array(&exact, 3) {
        Ok(result) => result.into_object(),
        _ => panic!("the exact UTF-8 byte allowance must fit"),
    };
    assert_text(&converted, "é\0");
    for (bytes, limit) in [(&b"\xff"[..], 0), (&b"ok\xff"[..], 2)] {
        let input = Obj::mk_sarray(1, bytes);
        assert!(matches!(string_from_byte_array(&input, limit),
            Err(IntrinsicFailure::StringBytesResource {
                operation: "String.ofByteArray",
                error: strings::ResourceError::OutputLimit { allowed, observed },
            })
                if allowed == limit as u64 && observed == bytes.len() as u64));
    }
    let oversized = Obj::mk_sarray(1, &vec![b'x'; MAX_STRING_CONVERSION_BYTES + 1]);
    let error = match invoke_intrinsic(
        IntrinsicImplementation::for_row(ROW),
        ROW,
        vec![oversized],
        1024,
    ) {
        Err(IntrinsicFailure::StringBytesResource {
            operation: "String.ofByteArray",
            error,
        }) => error,
        _ => panic!("real dispatch must enforce the production byte ceiling"),
    };
    assert!(
        matches!(string_bytes_exhausted("String.ofByteArray", error, "test"), Stop::Inconclusive(inconclusive)
        if matches!(&inconclusive.cause, InconclusiveCause::ResourceExhausted { usage }
            if usage.reason == ResourceReason::Memory { limit_bytes: MAX_STRING_CONVERSION_BYTES as u64 }
                && usage.allowed == MAX_STRING_CONVERSION_BYTES as u64
                && usage.observed == MAX_STRING_CONVERSION_BYTES as u64 + 1))
    );
}

#[test]
fn string_byte_array_output_budget_counts_payload_bytes_without_the_sentinel() {
    let text = Obj::mk_string("é");
    let result = string_to_byte_array(&text, 2)
        .unwrap_or_else(|_| panic!("two UTF-8 bytes must fit the exact output budget"));
    assert_eq!(
        result.value.try_borrow_sarray_view().unwrap().3,
        b"\xc3\xa9"
    );
    assert!(matches!(
        string_to_byte_array(&text, 1),
        Err(IntrinsicFailure::StringBytesResource {
            operation: "String.toByteArray",
            error: strings::ResourceError::OutputLimit {
                allowed: 1,
                observed: 2,
            },
        })
    ));
    let empty = string_to_byte_array(&Obj::mk_string(""), 0)
        .unwrap_or_else(|_| panic!("an empty String needs no payload bytes"));
    assert_eq!(empty.value.try_borrow_sarray_view().unwrap().3, b"");
    assert!(matches!(
        string_to_byte_array(&Obj::mk_nat(0), 0),
        Err(IntrinsicFailure::Refused(VmRefusal::TypeMismatch { .. }))
    ));
}

#[test]
fn string_byte_array_conversion_dispatch_preserves_typed_memory_stops() {
    for row in ["extern:String.toByteArray", "extern:String.toUTF8"] {
        let oversized = Obj::mk_string(&"x".repeat(MAX_STRING_CONVERSION_BYTES + 1));
        let error = match invoke_intrinsic(
            IntrinsicImplementation::for_row(row),
            row,
            vec![oversized],
            1024,
        ) {
            Err(IntrinsicFailure::StringBytesResource {
                operation: "String.toByteArray",
                error,
            }) => error,
            _ => panic!("real dispatch must enforce the conversion output ceiling"),
        };
        assert!(matches!(
            string_bytes_exhausted("String.toByteArray", error, "test"),
            Stop::Inconclusive(inconclusive)
                if matches!(&inconclusive.cause, InconclusiveCause::ResourceExhausted { usage }
                    if usage.reason == ResourceReason::Memory {
                        limit_bytes: MAX_STRING_CONVERSION_BYTES as u64,
                    } && usage.allowed == MAX_STRING_CONVERSION_BYTES as u64
                        && usage.observed == MAX_STRING_CONVERSION_BYTES as u64 + 1)
        ));
    }
}
