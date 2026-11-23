//! Two independent pin tag arrays use the same metered Name codec.
use super::*;
use crate::region::{OleanView, WalkBudget};
use crate::source_extensions::{self, DecodeLimits};

fn n(text: &str) -> Name {
    Name::from_components(text.split('.'))
}

#[test]
fn eliminator_tags_preserve_structural_identities_and_independent_sorted_sets() {
    let metadata = SourceMetadata {
        elab_as_elim: vec![
            n("Payload.right.elim"),
            n("ordinaryElim"),
            n("Payload.left.elim"),
        ],
        sparse_cases_on: vec![n("Payload.right.elim"), n("Payload.left.elim")],
        ..SourceMetadata::default()
    };
    for version in crate::format::OLEAN_ACCEPTED_VERSIONS {
        let mut header = super::tests::header();
        header.version = *version;
        let encoded = encode_module_with_source_metadata(
            super::tests::input(),
            &metadata,
            header,
            WriteBudget::default(),
        )
        .unwrap();
        let exact = WriteBudget {
            max_objects: encoded.report.runtime_objects,
            max_bytes: encoded.report.file_bytes,
        };
        assert_eq!(
            encode_module_with_source_metadata(super::tests::input(), &metadata, header, exact)
                .unwrap()
                .bytes,
            encoded.bytes
        );
        for budget in [
            WriteBudget {
                max_objects: exact.max_objects - 1,
                ..exact
            },
            WriteBudget {
                max_bytes: exact.max_bytes - 1,
                ..exact
            },
        ] {
            assert!(matches!(
                encode_module_with_source_metadata(
                    super::tests::input(),
                    &metadata,
                    header,
                    budget
                ),
                Err(WriteError::Budget { .. })
            ));
        }
        let blocks = OleanView::parse(&encoded.bytes)
            .unwrap()
            .extension_payloads(WalkBudget::default(), 4 << 20)
            .unwrap();
        assert_eq!(blocks.len(), 2);
        assert!(
            blocks
                .iter()
                .any(|block| block.name == source_extensions::sparse_cases_on_extension_name())
        );
        let decoded = source_extensions::decode(&blocks, DecodeLimits::default()).unwrap();
        let mut elab = metadata.elab_as_elim.clone();
        elab.sort_by(Name::quick_cmp);
        let mut sparse = metadata.sparse_cases_on.clone();
        sparse.sort_by(Name::quick_cmp);
        assert_eq!(decoded.elab_as_elim, elab);
        assert_eq!(decoded.sparse_cases_on, sparse);
        assert!(
            decoded.aux_recursors.is_empty(),
            "tag families do not fabricate aux-recursion classification"
        );
        assert!(decoded.uninterpreted.is_empty());
        let payloads: Vec<_> = blocks.iter().flat_map(|block| &block.entries).collect();
        let exact = DecodeLimits {
            max_bytes: payloads.iter().map(|bytes| bytes.len()).sum(),
            max_objects: payloads
                .iter()
                .map(|bytes| fln_rt::region::audit(bytes, 0).unwrap().objects)
                .sum(),
            max_entries: payloads.len(),
            max_indices: 0,
            max_keys: 0,
        };
        assert_eq!(source_extensions::decode(&blocks, exact).unwrap(), decoded);
        for limits in [
            DecodeLimits {
                max_bytes: exact.max_bytes - 1,
                ..exact
            },
            DecodeLimits {
                max_objects: exact.max_objects - 1,
                ..exact
            },
            DecodeLimits {
                max_entries: exact.max_entries - 1,
                ..exact
            },
        ] {
            assert!(
                source_extensions::decode(&blocks, limits)
                    .unwrap_err()
                    .is_resource()
            );
        }
    }
}

#[test]
fn each_eliminator_tag_only_module_is_retained_and_invalid_name_sets_refuse() {
    for sparse in [false, true] {
        for names in [
            vec![n("owned")],
            vec![Name::anonymous()],
            vec![n("owned"), n("owned")],
        ] {
            let metadata = if sparse {
                SourceMetadata {
                    sparse_cases_on: names.clone(),
                    ..SourceMetadata::default()
                }
            } else {
                SourceMetadata {
                    elab_as_elim: names.clone(),
                    ..SourceMetadata::default()
                }
            };
            let result = encode_module_with_source_metadata(
                super::tests::input(),
                &metadata,
                super::tests::header(),
                WriteBudget::default(),
            );
            if names == [n("owned")] {
                let bytes = result.unwrap().bytes;
                let blocks = OleanView::parse(&bytes)
                    .unwrap()
                    .extension_payloads(WalkBudget::default(), 4 << 20)
                    .unwrap();
                assert_eq!(blocks.len(), 1);
                let decoded = source_extensions::decode(&blocks, DecodeLimits::default()).unwrap();
                assert_eq!(
                    if sparse {
                        decoded.sparse_cases_on
                    } else {
                        decoded.elab_as_elim
                    },
                    names
                );
            } else {
                assert!(matches!(result, Err(WriteError::Contract { .. })));
            }
        }
    }
}
