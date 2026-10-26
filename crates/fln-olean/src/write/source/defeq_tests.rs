//! Persistent flags are data. These tests do not grant theorem authority.
use super::*;
use crate::source_extensions::{self, DecodeLimits};

fn n(s: &str) -> Name {
    Name::from_components(s.split('.'))
}
fn encode(names: Vec<Name>, budget: WriteBudget) -> WResult<EncodedModule> {
    encode_module_with_source_metadata(
        tests::input(),
        &SourceMetadata {
            defeq: names,
            ..Default::default()
        },
        tests::header(),
        budget,
    )
}
fn blocks(bytes: &[u8]) -> Vec<crate::region::OpaqueExtensionBlock> {
    let view = crate::region::OleanView::parse(bytes).unwrap();
    view.extension_payloads(crate::region::WalkBudget::default(), 1024 * 1024)
        .unwrap()
}

#[test]
fn exported_defeq_includes_backward_tags_in_the_pins_quick_order() {
    let names = vec![
        n("z"),
        n("A.x"),
        Name::num(n("hidden"), 3),
        n("hidden.3"),
        n("a"),
    ];
    let mut expected = names.clone();
    expected.sort_by(Name::quick_cmp);
    assert_ne!(names, expected);
    let encoded = encode(names, WriteBudget::default()).unwrap();
    let blocks = blocks(&encoded.bytes);
    assert_eq!(
        blocks.iter().map(|b| b.name.clone()).collect::<Vec<_>>(),
        [
            n(source_extensions::DEFEQ_EXTENSION),
            n(source_extensions::BACKWARD_DEFEQ_EXTENSION)
        ]
    );
    let decoded = source_extensions::decode(&blocks, DecodeLimits::default()).unwrap();
    assert_eq!(decoded.defeq, expected);
    assert_eq!(decoded.backward_defeq, expected);
    assert!(decoded.uninterpreted.is_empty());
    let again = encode(decoded.defeq, WriteBudget::default()).unwrap();
    assert_eq!(encoded.bytes, again.bytes);
}

#[test]
fn backward_only_metadata_does_not_become_default_defeq() {
    let encoded = encode_module_with_source_metadata(
        tests::input(),
        &SourceMetadata {
            backward_defeq: vec![n("onlyBackward")],
            ..Default::default()
        },
        tests::header(),
        WriteBudget::default(),
    )
    .unwrap();
    let blocks = blocks(&encoded.bytes);
    assert_eq!(blocks.len(), 1);
    assert_eq!(
        blocks[0].name,
        n(source_extensions::BACKWARD_DEFEQ_EXTENSION)
    );
    let decoded = source_extensions::decode(&blocks, DecodeLimits::default()).unwrap();
    assert!(decoded.defeq.is_empty());
    assert_eq!(decoded.backward_defeq, [n("onlyBackward")]);
}

#[test]
fn strict_and_backward_only_tags_union_without_promoting_generated_equations() {
    let metadata = SourceMetadata {
        defeq: vec![n("strict")],
        backward_defeq: vec![n("f.eq_1"), n("strict")],
        ..Default::default()
    };
    let encoded = encode_module_with_source_metadata(
        tests::input(),
        &metadata,
        tests::header(),
        WriteBudget::default(),
    )
    .unwrap();
    let decoded =
        source_extensions::decode(&blocks(&encoded.bytes), DecodeLimits::default()).unwrap();
    assert_eq!(decoded.defeq, [n("strict")]);
    let mut expected = vec![n("strict"), n("f.eq_1")];
    expected.sort_by(Name::quick_cmp);
    assert_eq!(decoded.backward_defeq, expected);
    for names in [vec![Name::anonymous()], vec![n("strict"), n("strict")]] {
        assert!(matches!(
            encode_module_with_source_metadata(
                tests::input(),
                &SourceMetadata {
                    backward_defeq: names,
                    ..metadata.clone()
                },
                tests::header(),
                WriteBudget::default(),
            ),
            Err(WriteError::Contract { .. })
        ));
    }
}

#[test]
fn malformed_later_tag_and_duplicate_blocks_do_not_expose_a_prefix() {
    let encoded = encode(vec![n("first"), n("second")], WriteBudget::default()).unwrap();
    let valid = blocks(&encoded.bytes);
    let mut bad = valid.clone();
    let duplicate = bad[0].entries[0].clone();
    bad[0].entries.push(duplicate);
    assert!(source_extensions::decode(&bad, DecodeLimits::default()).is_err());
    let mut bad = valid.clone();
    bad[0].entries[1] = b"not a compacted Name".to_vec();
    assert!(source_extensions::decode(&bad, DecodeLimits::default()).is_err());
    let mut bad = valid.clone();
    bad.push(valid[0].clone());
    assert!(source_extensions::decode(&bad, DecodeLimits::default()).is_err());
    for names in [vec![Name::anonymous()], vec![n("same"), n("same")]] {
        assert!(matches!(
            encode(names, WriteBudget::default()),
            Err(WriteError::Contract { .. })
        ));
    }
}

#[test]
fn both_tag_arrays_share_writer_and_reader_budgets() {
    let full = encode(vec![n("a")], WriteBudget::default()).unwrap();
    for budget in [
        WriteBudget {
            max_objects: 0,
            ..Default::default()
        },
        WriteBudget {
            max_bytes: full.report.file_bytes - 1,
            ..Default::default()
        },
    ] {
        assert!(matches!(
            encode(vec![n("a")], budget),
            Err(WriteError::Budget { .. })
        ));
    }
    let blocks = blocks(&full.bytes);
    for limits in [
        DecodeLimits {
            max_entries: 1,
            ..Default::default()
        },
        DecodeLimits {
            max_bytes: 0,
            ..Default::default()
        },
        DecodeLimits {
            max_objects: 0,
            ..Default::default()
        },
    ] {
        assert!(source_extensions::decode(&blocks, limits).is_err());
    }
    assert!(
        source_extensions::decode(
            &blocks,
            DecodeLimits {
                max_entries: 2,
                ..Default::default()
            }
        )
        .is_ok()
    );
}
