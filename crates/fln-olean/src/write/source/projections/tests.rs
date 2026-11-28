use super::*;
use crate::region::{OleanView, OpaqueExtensionBlock, WalkBudget};
use crate::source_extensions::{self, DecodeError, DecodeLimits};
use fln_rt::convert::inject_name;
use fln_rt::region::compact;

fn n(text: &str) -> Name {
    Name::from_components(text.split('.'))
}

fn rows() -> Vec<ProjectionEntry> {
    vec![
        ProjectionEntry {
            declaration: n("Class.value"),
            constructor: n("Class.mk"),
            num_params: 2,
            field_index: 1,
            from_class: true,
        },
        ProjectionEntry {
            declaration: Name::str(Name::num(n("_private.Projections"), 0), "Record.proof"),
            constructor: n("Record.mk"),
            num_params: 1,
            field_index: 0,
            from_class: false,
        },
    ]
}

fn encode(rows: Vec<ProjectionEntry>, version: u8, budget: WriteBudget) -> WResult<EncodedModule> {
    encode_module_with_source_metadata(
        ModuleWriteInput {
            is_module: false,
            imports: &[],
            constants: &[],
            extra_const_names: &[],
        },
        &SourceMetadata {
            projections: rows,
            ..Default::default()
        },
        OleanWriteHeader {
            version,
            flags: 1,
            lean_version: format::PIN_TAG.strip_prefix('v').unwrap(),
            githash: format::PIN_COMMIT,
            base_addr: 2 * format::REGION_ALIGN as u64,
        },
        budget,
    )
}

#[test]
fn projection_maps_preserve_creation_flags_and_exact_writer_decoder_budgets() {
    for &version in format::OLEAN_ACCEPTED_VERSIONS {
        let encoded = encode(rows(), version, WriteBudget::default()).unwrap();
        let blocks = OleanView::parse(&encoded.bytes)
            .unwrap()
            .extension_payloads(WalkBudget::default(), 1 << 20)
            .unwrap();
        assert_eq!(
            blocks.len(),
            1,
            "metadata-only modules must retain the projection map"
        );
        assert_eq!(blocks[0].name, n(source_extensions::PROJECTION_EXTENSION));
        let mut expected = rows();
        expected.sort_by(|left, right| left.declaration.quick_cmp(&right.declaration));
        let decoded = source_extensions::decode(&blocks, DecodeLimits::default()).unwrap();
        assert_eq!(decoded.projections, expected);
        assert!(decoded.uninterpreted.is_empty());
        let exact = WriteBudget {
            max_bytes: encoded.report.file_bytes,
            max_objects: encoded.report.runtime_objects,
        };
        assert_eq!(encode(rows(), version, exact).unwrap().bytes, encoded.bytes);
        for budget in [
            WriteBudget {
                max_bytes: exact.max_bytes - 1,
                ..exact
            },
            WriteBudget {
                max_objects: exact.max_objects - 1,
                ..exact
            },
        ] {
            assert!(matches!(
                encode(rows(), version, budget),
                Err(WriteError::Budget { .. })
            ));
        }
        let exact = DecodeLimits {
            max_bytes: blocks[0].entries.iter().map(Vec::len).sum(),
            max_objects: blocks[0]
                .entries
                .iter()
                .map(|entry| fln_rt::region::audit(entry, 0).unwrap().objects)
                .sum(),
            max_entries: blocks[0].entries.len(),
            max_indices: 0,
            max_keys: 0,
        };
        assert_eq!(
            source_extensions::decode(&blocks, exact)
                .unwrap()
                .projections,
            expected
        );
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
fn projection_writer_refuses_anonymous_and_duplicate_declarations() {
    let row = rows().remove(0);
    for malformed in [
        vec![ProjectionEntry {
            declaration: Name::anonymous(),
            ..row.clone()
        }],
        vec![ProjectionEntry {
            constructor: Name::anonymous(),
            ..row.clone()
        }],
        vec![row.clone(), row],
    ] {
        assert!(matches!(
            encode(malformed, 2, WriteBudget::default()),
            Err(WriteError::Contract { .. })
        ));
    }
}

fn wire(declaration: &Name, constructor: &Name, flag: &[u8]) -> Obj {
    let info = Obj::mk_ctor(
        0,
        vec![inject_name(constructor), Obj::mk_nat(2), Obj::mk_nat(1)],
        flag,
    );
    Obj::mk_ctor(0, vec![inject_name(declaration), info], &[])
}

#[test]
fn malformed_projection_rows_and_duplicate_entries_expose_no_prefix() {
    let good = wire(&n("Good.value"), &n("Good.mk"), &[1]);
    let malformed = [
        wire(&Name::anonymous(), &n("Bad.mk"), &[0]),
        wire(&n("Bad.value"), &Name::anonymous(), &[0]),
        wire(&n("Bad.value"), &n("Bad.mk"), &[2]),
        wire(&n("Bad.value"), &n("Bad.mk"), &[]),
        Obj::mk_ctor(1, vec![inject_name(&n("Bad.value")), Obj::mk_nat(0)], &[]),
        good.clone_ref(),
    ];
    for row in malformed {
        let blocks = [OpaqueExtensionBlock {
            name: n(source_extensions::PROJECTION_EXTENSION),
            entries: vec![compact(&good, 0).unwrap(), compact(&row, 0).unwrap()],
        }];
        assert!(matches!(
            source_extensions::decode(&blocks, DecodeLimits::default()),
            Err(DecodeError::Shape { .. })
        ));
    }
}
