//! Pinned simp journals and independently constructed hostile entry shapes.
#![forbid(unsafe_code)]
use fln_core::expr::{Expr, FVarId, Literal, MVarId, NatLit};
use fln_core::level::{LMVarId, Level};
use fln_core::name::Name;
use fln_olean::region::{OleanView, OpaqueExtensionBlock, WalkBudget};
use fln_olean::source_extensions::{
    DecodeError, DecodeLimits, DiscrTreeKey, SIMP_EXTENSION, SimpEntry, SimpKind, SimpTheorem,
    decode,
};
use fln_olean::write::source::{SourceMetadata, encode_module_with_source_metadata};
use fln_olean::write::{
    EncodedModule, ModuleWriteInput, OleanWriteHeader, WriteBudget, WriteError,
};
use fln_rt::convert::{inject_expr, inject_name};
use fln_rt::obj::Obj;
use fln_rt::region::compact;

fn n(text: &str) -> Name {
    Name::from_components(text.split('.'))
}
fn theorem(origin: &Name, proof: &Expr, post: u8, inverse: u8, perm: u8) -> Obj {
    let mut heap = fln_rt::native_heap::NativeHeap::new();
    let handle = heap.alloc(proof.clone());
    let origin = Obj::mk_ctor(0, vec![inject_name(origin)], &[post, inverse]);
    let theorem = Obj::mk_ctor(
        0,
        vec![
            Obj::mk_array(vec![]),
            Obj::mk_array(vec![]),
            inject_expr(&heap, handle).unwrap(),
            Obj::mk_nat(700),
            origin,
        ],
        &[post, perm, 0, 1],
    );
    Obj::mk_ctor(0, vec![theorem], &[])
}
fn block(entries: &[Obj]) -> Vec<OpaqueExtensionBlock> {
    vec![OpaqueExtensionBlock {
        name: n(SIMP_EXTENSION),
        entries: entries
            .iter()
            .map(|entry| compact(entry, 0).unwrap())
            .collect(),
    }]
}
fn global(entry: Obj) -> Obj {
    Obj::mk_ctor(0, vec![entry], &[])
}

#[test]
fn pinned_prelude_simp_journal_retains_actual_proofs_and_origins() {
    let public = include_bytes!("../../fln-conformance/fixtures/tag_attributes/prelude.olean");
    let server =
        include_bytes!("../../fln-conformance/fixtures/tag_attributes/prelude.olean.server");
    let private =
        include_bytes!("../../fln-conformance/fixtures/tag_attributes/prelude.olean.private");
    let blocks = OleanView::parse_with_dependencies(private, &[public, server])
        .unwrap()
        .extension_payloads(WalkBudget::default(), 32 << 20)
        .unwrap();
    let decoded = decode(&blocks, DecodeLimits::default()).unwrap();
    assert!(
        !decoded.simps.is_empty(),
        "fixture must exercise actual simp entries"
    );
    let mut theorems = 0;
    let mut auxiliaries = 0;
    for entry in &decoded.simps {
        if let SimpKind::Theorem(theorem) = &entry.kind {
            theorems += 1;
            assert!(theorem.level_params.is_empty());
            let fln_core::expr::ExprNode::Const { name, levels } = theorem.proof.node() else {
                panic!("global simp proof must name its admitted lemma");
            };
            assert!(levels.is_empty());
            auxiliaries += usize::from(*name != theorem.origin);
        }
    }
    assert_eq!((decoded.simps.len(), theorems, auxiliaries), (3, 1, 0));
    assert_eq!(decoded.simps[0].kind, SimpKind::Unfold(n("Eq.ndrec")));
    let SimpKind::Theorem(rule) = &decoded.simps[1].kind else {
        panic!("id_eq theorem");
    };
    assert_eq!(rule.origin, n("id_eq"));
    assert_eq!(rule.priority, 1000);
    assert_eq!(
        rule.keys,
        [
            DiscrTreeKey::Const(n("id"), 2),
            DiscrTreeKey::Star,
            DiscrTreeKey::Star,
        ]
    );
    assert!(rule.post && rule.reflexive && rule.backward_reflexive);
    assert!(!rule.origin_reverse && !rule.permutation);
    assert_eq!(decoded.simps[2].kind, SimpKind::Unfold(n("Eq.ndrec_symm")));
    assert!(!decoded.uninterpreted.contains(&n(SIMP_EXTENSION)));
    for &version in fln_olean::format::OLEAN_ACCEPTED_VERSIONS {
        let encoded = write_simps(decoded.simps.clone(), version, WriteBudget::default()).unwrap();
        let blocks = OleanView::parse(&encoded.bytes)
            .unwrap()
            .extension_payloads(WalkBudget::default(), 1 << 20)
            .unwrap();
        assert_eq!(
            decode(&blocks, DecodeLimits::default()).unwrap().simps,
            decoded.simps
        );
    }
}

#[test]
fn inverse_origin_does_not_reverse_or_replace_the_auxiliary_proof() {
    let origin = n("Library.rule");
    let auxiliary = Name::num(n("_private.Library"), 17);
    let proof = Expr::const_(auxiliary, vec![]);
    let entry = global(theorem(&origin, &proof, 1, 1, 0));
    let decoded = decode(&block(&[entry]), DecodeLimits::default()).unwrap();
    let SimpKind::Theorem(theorem) = &decoded.simps[0].kind else {
        panic!("theorem entry");
    };
    assert_eq!(theorem.origin, origin);
    assert_eq!(theorem.proof, proof);
    assert!(theorem.origin_reverse && theorem.post && theorem.backward_reflexive);
    assert!(!theorem.permutation && !theorem.reflexive);
    assert_eq!(theorem.priority, 700);
}

#[test]
fn scope_unfolding_and_equation_groups_keep_journal_order() {
    let theorem = theorem(&n("rule"), &Expr::const_(n("rule"), vec![]), 0, 0, 1);
    let scoped = Obj::mk_ctor(1, vec![inject_name(&n("Feature")), theorem], &[]);
    let unfold = global(Obj::mk_ctor(1, vec![inject_name(&n("function"))], &[]));
    let equations = global(Obj::mk_ctor(
        2,
        vec![
            inject_name(&n("function")),
            Obj::mk_array(vec![
                inject_name(&n("function.eq_1")),
                inject_name(&n("function.eq_2")),
            ]),
        ],
        &[],
    ));
    let result = decode(
        &block(&[scoped, unfold, equations]),
        DecodeLimits::default(),
    )
    .unwrap();
    assert_eq!(result.simps[0].scope, Some(n("Feature")));
    assert!(matches!(&result.simps[0].kind, SimpKind::Theorem(t) if !t.post && t.permutation));
    assert_eq!(result.simps[1].kind, SimpKind::Unfold(n("function")));
    assert_eq!(
        result.simps[2].kind,
        SimpKind::UnfoldTheorems {
            declaration: n("function"),
            theorems: vec![n("function.eq_1"), n("function.eq_2")]
        }
    );
}

#[test]
fn bad_flags_scope_tags_and_local_proofs_refuse_without_a_prefix() {
    let good = global(theorem(
        &n("rule"),
        &Expr::const_(n("rule"), vec![]),
        1,
        0,
        0,
    ));
    for bad in [
        global(theorem(
            &n("rule"),
            &Expr::const_(n("rule"), vec![]),
            2,
            0,
            0,
        )),
        global(theorem(
            &n("rule"),
            &Expr::const_(n("rule"), vec![]),
            1,
            2,
            0,
        )),
        global(theorem(
            &n("rule"),
            &Expr::const_(n("rule"), vec![]),
            1,
            0,
            2,
        )),
        global(theorem(&n("rule"), &Expr::bvar(0).unwrap(), 1, 0, 0)),
        Obj::mk_ctor(2, vec![Obj::mk_nat(0)], &[]),
        global(Obj::mk_ctor(3, vec![inject_name(&n("rule"))], &[])),
        global(Obj::mk_ctor(1, vec![inject_name(&Name::anonymous())], &[])),
    ] {
        assert!(decode(&block(&[good.clone_ref(), bad]), DecodeLimits::default()).is_err());
    }
    let inner = good.ctor_child(0).ctor_child(0);
    let fields = (0..5).map(|i| inner.ctor_child(i)).collect();
    let phase_mismatch = global(Obj::mk_ctor(
        0,
        vec![Obj::mk_ctor(0, fields, &[0, 0, 0, 1])],
        &[],
    ));
    assert!(matches!(
        decode(&block(&[phase_mismatch]), DecodeLimits::default()),
        Err(DecodeError::Shape { .. })
    ));
}

#[test]
fn simp_entries_and_index_cells_share_cumulative_limits() {
    let group = global(Obj::mk_ctor(
        2,
        vec![
            inject_name(&n("function")),
            Obj::mk_array(vec![inject_name(&n("eq1")), inject_name(&n("eq2"))]),
        ],
        &[],
    ));
    let blocks = block(&[group.clone_ref(), group]);
    let defaults = DecodeLimits::default();
    for limits in [
        DecodeLimits {
            max_bytes: blocks[0].entries[0].len(),
            ..defaults
        },
        DecodeLimits {
            max_objects: 0,
            ..defaults
        },
        DecodeLimits {
            max_entries: 1,
            ..defaults
        },
        DecodeLimits {
            max_indices: 3,
            ..defaults
        },
    ] {
        assert!(matches!(
            decode(&blocks, limits),
            Err(DecodeError::Limit { .. })
        ));
    }
    assert_eq!(
        decode(
            &blocks,
            DecodeLimits {
                max_indices: 4,
                ..defaults
            }
        )
        .unwrap()
        .simps
        .len(),
        2
    );
}

fn write_simps(
    simp: Vec<SimpEntry>,
    version: u8,
    budget: WriteBudget,
) -> Result<EncodedModule, WriteError> {
    encode_module_with_source_metadata(
        ModuleWriteInput {
            is_module: false,
            imports: &[],
            constants: &[],
            extra_const_names: &[],
        },
        &SourceMetadata {
            simp,
            ..SourceMetadata::default()
        },
        OleanWriteHeader {
            version,
            flags: 1,
            lean_version: fln_olean::format::PIN_TAG.strip_prefix('v').unwrap(),
            githash: fln_olean::format::PIN_COMMIT,
            base_addr: 2 * fln_olean::format::REGION_ALIGN as u64,
        },
        budget,
    )
}

fn writer_theorem() -> SimpTheorem {
    use DiscrTreeKey::*;
    SimpTheorem {
        proof: Expr::const_(
            Name::num(n("_private.Library"), 17),
            vec![Level::param(n("u"))],
        ),
        level_params: vec![n("u")],
        origin: n("Library.rule"),
        origin_reverse: false,
        priority: 1000,
        post: true,
        permutation: false,
        reflexive: false,
        backward_reflexive: false,
        keys: vec![
            Const(n("head"), 7),
            Star,
            Other,
            Lit(Literal::Nat(NatLit::from_limbs_le(vec![0, 1]))),
            Lit(Literal::Str("λ".into())),
            FVar(n("x"), 1),
            Star,
            Arrow,
            Const(n("Type"), 0),
            Proj(n("Structure"), 2, 1),
            Const(n("structureValue"), 0),
            Star,
        ],
    }
}

#[test]
fn writer_preserves_all_keys_flags_oriented_proofs_scopes_and_journal_order() {
    let mut rows = Vec::new();
    for flags in 0..32u32 {
        let mut theorem = writer_theorem();
        theorem.priority -= flags;
        theorem.post = flags & 1 != 0;
        theorem.origin_reverse = flags & 2 != 0;
        theorem.permutation = flags & 4 != 0;
        theorem.reflexive = flags & 8 != 0;
        theorem.backward_reflexive = flags & 16 != 0;
        rows.push(SimpEntry {
            scope: (flags % 2 == 0).then(|| n("Feature.Nested")),
            kind: SimpKind::Theorem(theorem),
        });
    }
    rows.push(SimpEntry {
        scope: None,
        kind: SimpKind::Unfold(n("function")),
    });
    rows.push(SimpEntry {
        scope: Some(n("Feature")),
        kind: SimpKind::UnfoldTheorems {
            declaration: n("function"),
            theorems: vec![n("function.eq_2"), n("function.eq_1")],
        },
    });
    for &version in fln_olean::format::OLEAN_ACCEPTED_VERSIONS {
        let encoded = write_simps(rows.clone(), version, WriteBudget::default()).unwrap();
        let blocks = OleanView::parse(&encoded.bytes)
            .unwrap()
            .extension_payloads(WalkBudget::default(), 1 << 20)
            .unwrap();
        let decoded = decode(&blocks, DecodeLimits::default()).unwrap();
        assert_eq!(decoded.simps, rows);
        assert!(decoded.namespaces.contains(&n("Feature")));
        assert!(decoded.namespaces.contains(&n("Feature.Nested")));
        assert!(decoded.uninterpreted.is_empty());
        assert_eq!(
            write_simps(rows.clone(), version, WriteBudget::default())
                .unwrap()
                .bytes,
            encoded.bytes
        );
    }
}

#[test]
fn malformed_simp_keys_are_decoded_and_key_budget_is_cumulative() {
    let with_keys = |keys| {
        let inner = theorem(&n("rule"), &Expr::const_(n("rule"), vec![]), 1, 0, 0).ctor_child(0);
        let mut fields: Vec<_> = (0..5).map(|index| inner.ctor_child(index)).collect();
        fields[0] = Obj::mk_array(keys);
        global(Obj::mk_ctor(
            0,
            vec![Obj::mk_ctor(0, fields, &[1, 0, 0, 1])],
            &[],
        ))
    };
    let good = with_keys(vec![
        Obj::mk_ctor(4, vec![inject_name(&n("head")), Obj::mk_nat(1)], &[]),
        Obj::mk_nat(0),
    ]);
    let blocks = block(&[good.clone_ref(), good.clone_ref()]);
    assert_eq!(
        decode(
            &blocks,
            DecodeLimits {
                max_keys: 4,
                ..DecodeLimits::default()
            }
        )
        .unwrap()
        .simps
        .len(),
        2
    );
    assert!(matches!(
        decode(
            &blocks,
            DecodeLimits {
                max_keys: 3,
                ..DecodeLimits::default()
            }
        ),
        Err(DecodeError::Limit { .. })
    ));
    for key in [
        Obj::mk_nat(7),
        Obj::mk_nat(4),
        Obj::mk_ctor(4, vec![inject_name(&n("head"))], &[]),
        Obj::mk_ctor(
            4,
            vec![inject_name(&Name::anonymous()), Obj::mk_nat(0)],
            &[],
        ),
    ] {
        assert!(matches!(
            decode(
                &block(&[good.clone_ref(), with_keys(vec![key])]),
                DecodeLimits::default()
            ),
            Err(DecodeError::Shape { .. })
        ));
    }
}

#[test]
fn writer_refuses_local_proofs_malformed_paths_and_invalid_names() {
    for defect in 0..11 {
        let mut theorem = writer_theorem();
        match defect {
            0 => theorem.origin = Name::anonymous(),
            1 => theorem.proof = Expr::bvar(0).unwrap(),
            2 => theorem.proof = Expr::fvar(FVarId(n("local"))),
            3 => theorem.proof = Expr::mvar(MVarId(n("meta"))),
            4 => theorem.proof = Expr::const_(n("rule"), vec![Level::mvar(LMVarId(n("level")))]),
            5 => theorem.keys.clear(),
            6 => theorem.keys = vec![DiscrTreeKey::Const(n("head"), 1)],
            7 => theorem.keys = vec![DiscrTreeKey::Star, DiscrTreeKey::Other],
            8 => theorem.keys = vec![DiscrTreeKey::Const(Name::anonymous(), 0)],
            9 => theorem.level_params = vec![n("u"), n("u")],
            _ => theorem.level_params = vec![Name::anonymous()],
        }
        assert!(
            matches!(
                write_simps(
                    vec![SimpEntry {
                        scope: None,
                        kind: SimpKind::Theorem(theorem)
                    }],
                    2,
                    WriteBudget::default()
                ),
                Err(WriteError::Contract { .. })
            ),
            "defect {defect}"
        );
    }
    for row in [
        SimpEntry {
            scope: Some(Name::anonymous()),
            kind: SimpKind::Unfold(n("function")),
        },
        SimpEntry {
            scope: None,
            kind: SimpKind::Unfold(Name::anonymous()),
        },
        SimpEntry {
            scope: None,
            kind: SimpKind::UnfoldTheorems {
                declaration: Name::anonymous(),
                theorems: vec![],
            },
        },
        SimpEntry {
            scope: None,
            kind: SimpKind::UnfoldTheorems {
                declaration: n("function"),
                theorems: vec![Name::anonymous()],
            },
        },
        SimpEntry {
            scope: None,
            kind: SimpKind::UnfoldTheorems {
                declaration: n("function"),
                theorems: vec![n("eq"), n("eq")],
            },
        },
    ] {
        assert!(matches!(
            write_simps(vec![row], 2, WriteBudget::default()),
            Err(WriteError::Contract { .. })
        ));
    }
}

#[test]
fn simp_writer_charges_all_objects_and_bytes_to_the_module_budget() {
    let rows = vec![SimpEntry {
        scope: Some(n("Feature")),
        kind: SimpKind::Theorem(writer_theorem()),
    }];
    for &version in fln_olean::format::OLEAN_ACCEPTED_VERSIONS {
        let output = write_simps(rows.clone(), version, WriteBudget::default()).unwrap();
        let exact = WriteBudget {
            max_bytes: output.report.file_bytes,
            max_objects: output.report.runtime_objects,
        };
        assert_eq!(
            write_simps(rows.clone(), version, exact).unwrap().bytes,
            output.bytes
        );
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
                write_simps(rows.clone(), version, budget),
                Err(WriteError::Budget { .. })
            ));
        }
    }
}
