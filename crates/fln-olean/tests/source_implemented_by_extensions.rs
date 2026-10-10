//! Pinned parametric-attribute payloads are data, independent of execution.
#![forbid(unsafe_code)]
use fln_core::name::Name;
use fln_olean::region::OpaqueExtensionBlock;
use fln_olean::source_extensions::{
    DecodeLimits, IMPLEMENTED_BY_EXTENSION, ImplementedByEntry, decode,
};
use fln_rt::convert::inject_name;
use fln_rt::obj::Obj;
use fln_rt::region::{audit, compact};

fn n(label: &str) -> Name {
    Name::from_components(label.split('.'))
}
fn pair(source: &Name, target: &Name) -> Obj {
    Obj::mk_ctor(0, vec![inject_name(source), inject_name(target)], &[])
}
fn block(value: &Obj) -> OpaqueExtensionBlock {
    OpaqueExtensionBlock {
        name: n(IMPLEMENTED_BY_EXTENSION),
        entries: vec![compact(value, 0).unwrap()],
    }
}

#[test]
fn declaration_and_target_names_retain_order_and_structural_identity() {
    let source = Name::num(n("source"), 3);
    let target = Name::str(n("target"), "3");
    let value = block(&pair(&source, &target));
    let decoded = decode(std::slice::from_ref(&value), DecodeLimits::default()).unwrap();
    assert_eq!(
        decoded.implemented_by,
        [ImplementedByEntry {
            declaration: source,
            implementation: target
        }]
    );
    assert!(decoded.uninterpreted.is_empty());
    let mut lookalike = value;
    lookalike.name = Name::str(Name::anonymous(), IMPLEMENTED_BY_EXTENSION);
    let decoded = decode(&[lookalike], DecodeLimits::default()).unwrap();
    assert!(decoded.implemented_by.is_empty());
    assert_eq!(decoded.uninterpreted.len(), 1);
    assert!(
        decode(&[], DecodeLimits::default())
            .unwrap()
            .implemented_by
            .is_empty()
    );
}

#[test]
fn wrong_pair_shapes_anonymous_names_and_bad_later_rows_refuse_atomically() {
    for malformed in [
        Obj::mk_nat(0),
        Obj::mk_ctor(1, vec![inject_name(&n("a")), inject_name(&n("b"))], &[]),
        Obj::mk_ctor(0, vec![inject_name(&n("a"))], &[]),
        Obj::mk_ctor(0, vec![inject_name(&n("a")), Obj::mk_string("b")], &[]),
        pair(&Name::anonymous(), &n("b")),
        pair(&n("a"), &Name::anonymous()),
    ] {
        let mut prefixed = block(&pair(&n("a"), &n("b")));
        prefixed.entries.extend(block(&malformed).entries);
        assert!(decode(&[prefixed], DecodeLimits::default()).is_err());
    }
}

#[test]
fn row_bytes_and_objects_share_the_decoders_cumulative_limits() {
    let mut repeated = block(&pair(&n("a"), &n("b")));
    let bytes = repeated.entries[0].len();
    let objects = audit(&repeated.entries[0], 0).unwrap().objects;
    repeated.entries.push(repeated.entries[0].clone());
    assert_eq!(
        decode(std::slice::from_ref(&repeated), DecodeLimits::default())
            .unwrap()
            .implemented_by
            .len(),
        2
    );
    for limits in [
        DecodeLimits {
            max_entries: 1,
            ..DecodeLimits::default()
        },
        DecodeLimits {
            max_bytes: 2 * bytes - 1,
            ..DecodeLimits::default()
        },
        DecodeLimits {
            max_objects: 2 * objects - 1,
            ..DecodeLimits::default()
        },
    ] {
        assert!(
            decode(std::slice::from_ref(&repeated), limits)
                .unwrap_err()
                .is_resource()
        );
    }
}
