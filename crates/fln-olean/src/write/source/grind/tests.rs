use super::*;
use crate::region::{OleanView, OpaqueExtensionBlock, WalkBudget};
use crate::source_extensions::{self, DecodeError, DecodeLimits, Decoder};
use fln_rt::convert::{inject_expr, inject_name};
use fln_rt::native_heap::NativeHeap;
use fln_rt::region::compact;

fn n(text: &str) -> Name {
    Name::from_components(text.split('.'))
}
fn input() -> ModuleWriteInput<'static> {
    ModuleWriteInput {
        is_module: false,
        imports: &[],
        constants: &[],
        extra_const_names: &[],
    }
}
fn header(version: u8) -> OleanWriteHeader<'static> {
    OleanWriteHeader {
        version,
        flags: 1,
        lean_version: crate::format::PIN_TAG.strip_prefix('v').unwrap(),
        githash: crate::format::PIN_COMMIT,
        base_addr: 2 * crate::format::REGION_ALIGN as u64,
    }
}
fn row() -> GrindPatternEntry {
    let u = Level::param(n("u"));
    let mut data = KVMap::new();
    data.insert(
        n(source_extensions::GRIND_GROUND_PATTERN_ANNOTATION),
        DataValue::OfBool(true),
    );
    let ground = Expr::mdata(data, Expr::const_(n("a"), vec![]));
    let first = Expr::app(
        Expr::app(
            Expr::const_(n("f"), vec![u.clone()]),
            Expr::bvar(2).unwrap(),
        ),
        ground,
    );
    let second = Expr::app(
        Expr::app(
            Expr::const_(n("g"), vec![u.clone()]),
            Expr::const_(n(source_extensions::GRIND_DONT_CARE), vec![]),
        ),
        Expr::bvar(1).unwrap(),
    );
    GrindPatternEntry {
        declaration: n("rule"),
        proof: Expr::const_(n("rule"), vec![u]),
        num_params: 3,
        patterns: vec![first, second],
        symbols: vec![n("f"), n("a"), n("g")],
    }
}
fn blocks(rows: &[Obj]) -> Vec<OpaqueExtensionBlock> {
    vec![OpaqueExtensionBlock {
        name: n(source_extensions::GRIND_EXTENSION),
        entries: rows.iter().map(|row| compact(row, 0).unwrap()).collect(),
    }]
}
fn expression(expr: &Expr) -> Obj {
    let mut heap = NativeHeap::new();
    let handle = heap.alloc(expr.clone());
    inject_expr(&heap, handle).unwrap()
}
fn list(values: Vec<Obj>) -> Obj {
    values.into_iter().rev().fold(Obj::mk_nat(0), |tail, head| {
        Obj::mk_ctor(1, vec![head, tail], &[])
    })
}

// Independent pin shape: EMatchTheorem has eight object fields and one Bool.
// These literal slots are also checked against the real Reference fixture below.
fn fields(row: &GrindPatternEntry) -> Vec<Obj> {
    vec![
        Obj::mk_array(vec![]),
        expression(&row.proof),
        Obj::mk_nat(row.num_params as usize),
        list(row.patterns.iter().map(expression).collect()),
        list(
            row.symbols
                .iter()
                .map(|symbol| Obj::mk_ctor(2, vec![inject_name(symbol)], &[]))
                .collect(),
        ),
        Obj::mk_ctor(0, vec![inject_name(&row.declaration)], &[]),
        Obj::mk_nat(9),
        Obj::mk_nat(0),
    ]
}
fn wire(fields: Vec<Obj>, scalars: &[u8]) -> Obj {
    let theorem = Obj::mk_ctor(0, fields, scalars);
    let entry = Obj::mk_ctor(3, vec![theorem], &[]);
    Obj::mk_ctor(0, vec![entry], &[])
}
fn replace_field(index: usize, value: Obj) -> Obj {
    let mut fields = fields(&row());
    fields[index] = value;
    wire(fields, &[0])
}

#[test]
fn grind_wire_keeps_groups_gadgets_universes_and_duplicates_under_shared_budgets() {
    let metadata = SourceMetadata {
        grind_patterns: vec![row(), row()],
        ..SourceMetadata::default()
    };
    for version in crate::format::OLEAN_ACCEPTED_VERSIONS {
        let encoded = encode_module_with_source_metadata(
            input(),
            &metadata,
            header(*version),
            WriteBudget::default(),
        )
        .unwrap();
        let exact_write = WriteBudget {
            max_bytes: encoded.report.file_bytes,
            max_objects: encoded.report.runtime_objects,
        };
        assert_eq!(
            encode_module_with_source_metadata(input(), &metadata, header(*version), exact_write)
                .unwrap()
                .bytes,
            encoded.bytes,
        );
        for budget in [
            WriteBudget {
                max_bytes: exact_write.max_bytes - 1,
                ..exact_write
            },
            WriteBudget {
                max_objects: exact_write.max_objects - 1,
                ..exact_write
            },
        ] {
            assert!(matches!(
                encode_module_with_source_metadata(input(), &metadata, header(*version), budget),
                Err(WriteError::Budget { .. }),
            ));
        }
        let blocks = OleanView::parse(&encoded.bytes)
            .unwrap()
            .extension_payloads(WalkBudget::default(), 4 << 20)
            .unwrap();
        assert_eq!(
            blocks.len(),
            1,
            "grind-only artifacts must retain their journal"
        );
        let payloads = &blocks[0].entries;
        let exact_decode = DecodeLimits {
            max_bytes: payloads.iter().map(Vec::len).sum(),
            max_objects: payloads
                .iter()
                .map(|bytes| fln_rt::region::audit(bytes, 0).unwrap().objects)
                .sum(),
            max_entries: metadata
                .grind_patterns
                .iter()
                .map(|row| 1 + row.patterns.len() + row.symbols.len())
                .sum(),
            max_indices: 0,
            max_keys: metadata
                .grind_patterns
                .iter()
                .map(|row| row.symbols.len())
                .sum(),
        };
        let decoded = source_extensions::decode(&blocks, exact_decode).unwrap();
        assert_eq!(
            decoded.grind_patterns,
            metadata
                .grind_patterns
                .iter()
                .cloned()
                .map(Some)
                .collect::<Vec<_>>()
        );
        assert_eq!(decoded.grind_deferred, 0);
        assert!(decoded.uninterpreted.is_empty());
        for limits in [
            DecodeLimits {
                max_bytes: exact_decode.max_bytes - 1,
                ..exact_decode
            },
            DecodeLimits {
                max_objects: exact_decode.max_objects - 1,
                ..exact_decode
            },
            DecodeLimits {
                max_entries: exact_decode.max_entries - 1,
                ..exact_decode
            },
            DecodeLimits {
                max_keys: exact_decode.max_keys - 1,
                ..exact_decode
            },
        ] {
            assert!(
                source_extensions::decode(&blocks, limits)
                    .unwrap_err()
                    .is_resource()
            );
        }
        let mut decoder = Decoder::new(exact_decode);
        decoder.decode(&blocks).unwrap();
        assert!(decoder.decode(&blocks).unwrap_err().is_resource());
    }
}

#[test]
fn mixed_grind_blocks_preserve_physical_row_windows_and_deferred_accounting() {
    let global = |entry| Obj::mk_ctor(0, vec![entry], &[]);
    let scoped_entry = Obj::mk_ctor(3, vec![Obj::mk_ctor(0, fields(&row()), &[0])], &[]);
    let mut deferred = vec![
        global(Obj::mk_ctor(0, vec![inject_name(&n("extRule"))], &[])),
        global(Obj::mk_ctor(1, vec![inject_name(&n("congrRule"))], &[])),
        global(Obj::mk_ctor(2, vec![inject_name(&n("Cases"))], &[1])),
        global(Obj::mk_ctor(
            4,
            vec![Obj::mk_ctor(
                0,
                vec![
                    Obj::mk_array(vec![]),
                    expression(&row().proof),
                    list(vec![Obj::mk_ctor(2, vec![inject_name(&n("f"))], &[])]),
                    Obj::mk_ctor(0, vec![inject_name(&n("rule"))], &[]),
                ],
                &[],
            )],
            &[],
        )),
        Obj::mk_ctor(1, vec![inject_name(&n("Mode")), scoped_entry], &[]),
        replace_field(6, Obj::mk_ctor(0, vec![], &[0])),
        replace_field(6, Obj::mk_nat(4)),
        replace_field(7, list(vec![Obj::mk_ctor(4, vec![Obj::mk_nat(1)], &[])])),
        replace_field(0, Obj::mk_array(vec![inject_name(&n("u"))])),
        replace_field(5, Obj::mk_ctor(1, vec![inject_name(&n("localProof"))], &[])),
        replace_field(
            4,
            list(vec![Obj::mk_ctor(
                3,
                vec![inject_name(&n("Box")), Obj::mk_nat(0)],
                &[],
            )]),
        ),
        replace_field(
            1,
            expression(&Expr::app(row().proof, Expr::const_(n("a"), vec![]))),
        ),
    ];
    deferred.push(wire(fields(&row()), &[1]));
    let expected_deferred = deferred.len();
    let mut rows = vec![wire(fields(&row()), &[0])];
    rows.extend(deferred);
    rows.push(wire(fields(&row()), &[0]));
    let decoded = source_extensions::decode(&blocks(&rows), DecodeLimits::default()).unwrap();
    assert_eq!(decoded.grind_patterns.len(), expected_deferred + 2);
    assert_eq!(decoded.grind_patterns.first(), Some(&Some(row())));
    assert_eq!(decoded.grind_patterns.last(), Some(&Some(row())));
    assert!(
        decoded.grind_patterns[1..=expected_deferred]
            .iter()
            .all(Option::is_none)
    );
    assert_eq!(decoded.grind_deferred, expected_deferred);
    assert_eq!(
        decoded.uninterpreted,
        [n(source_extensions::GRIND_EXTENSION)]
    );
}

#[test]
fn malformed_supported_grind_rows_refuse_without_publishing_a_valid_prefix() {
    let mut short = fields(&row());
    short.pop();
    let wrong_proof = expression(&Expr::const_(n("someOtherRule"), vec![]));
    let bad_patterns = list(vec![expression(&Expr::bvar(3).unwrap())]);
    let duplicate_symbols = list(vec![
        Obj::mk_ctor(2, vec![inject_name(&n("f"))], &[]),
        Obj::mk_ctor(2, vec![inject_name(&n("f"))], &[]),
    ]);
    for invalid in [
        Obj::mk_nat(0),
        wire(short, &[0]),
        wire(fields(&row()), &[]),
        wire(fields(&row()), &[2]),
        replace_field(1, wrong_proof),
        replace_field(3, Obj::mk_nat(1)),
        replace_field(3, Obj::mk_nat(0)),
        replace_field(3, bad_patterns),
        replace_field(4, Obj::mk_nat(0)),
        replace_field(4, duplicate_symbols),
        replace_field(6, Obj::mk_ctor(9, vec![], &[])),
    ] {
        let mut decoder = Decoder::new(DecodeLimits::default());
        let result = decoder.decode(&blocks(&[wire(fields(&row()), &[0]), invalid]));
        assert!(
            matches!(result, Err(DecodeError::Shape { .. })),
            "{result:?}"
        );
        assert!(
            decoder
                .decode(&blocks(&[wire(fields(&row()), &[0])]))
                .is_err()
        );
    }
}

#[test]
fn grind_writer_rejects_unbound_patterns_and_forged_proof_or_symbol_metadata() {
    let original = row();
    let invalid = [
        GrindPatternEntry {
            declaration: Name::anonymous(),
            ..original.clone()
        },
        GrindPatternEntry {
            proof: Expr::const_(n("different"), vec![]),
            ..original.clone()
        },
        GrindPatternEntry {
            patterns: vec![],
            ..original.clone()
        },
        GrindPatternEntry {
            patterns: vec![Expr::bvar(3).unwrap()],
            ..original.clone()
        },
        GrindPatternEntry {
            symbols: vec![],
            ..original.clone()
        },
        GrindPatternEntry {
            symbols: vec![Name::anonymous()],
            ..original.clone()
        },
        GrindPatternEntry {
            symbols: vec![n("f"), n("f")],
            ..original
        },
    ];
    for row in invalid {
        assert!(matches!(
            encode_module_with_source_metadata(
                input(),
                &SourceMetadata {
                    grind_patterns: vec![row],
                    ..SourceMetadata::default()
                },
                header(crate::format::OLEAN_ACCEPTED_VERSIONS[0]),
                WriteBudget::default()
            ),
            Err(WriteError::Contract { .. }),
        ));
    }
}

#[test]
fn actual_reference_grind_journal_decodes_original_proof_and_ordered_user_groups() {
    // Generated by the SUITE.lock pin from the adjacent prelude-only source.
    // Its two rows are independent of this writer and include a trailing proof binder.
    let bytes = include_bytes!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/tests/fixtures/grind_patterns/reference.olean"
    ));
    let blocks = OleanView::parse(bytes)
        .unwrap()
        .extension_payloads(WalkBudget::default(), 4 << 20)
        .unwrap();
    let decoded = source_extensions::decode(&blocks, DecodeLimits::default()).unwrap();
    let expected: Vec<_> = ["trigger", "other"]
        .into_iter()
        .map(|symbol| {
            Some(GrindPatternEntry {
                declaration: n("rule"),
                proof: Expr::const_(n("rule"), vec![]),
                num_params: 2,
                patterns: vec![Expr::app(
                    Expr::const_(n(symbol), vec![]),
                    Expr::bvar(1).unwrap(),
                )],
                symbols: vec![n(symbol)],
            })
        })
        .collect();
    assert_eq!(decoded.grind_patterns, expected);
    assert_eq!(decoded.grind_deferred, 0);
    assert!(
        !decoded
            .uninterpreted
            .contains(&n(source_extensions::GRIND_EXTENSION))
    );
}
