//! Pinned simp journals and independently constructed hostile entry shapes.
#![forbid(unsafe_code)]
use fln_core::expr::Expr;
use fln_core::name::Name;
use fln_olean::region::{OleanView, OpaqueExtensionBlock, WalkBudget};
use fln_olean::source_extensions::{DecodeError, DecodeLimits, SIMP_EXTENSION, SimpKind, decode};
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
    assert_eq!(rule.key_count, 3);
    assert!(rule.post && rule.reflexive && rule.backward_reflexive);
    assert!(!rule.origin_reverse && !rule.permutation);
    assert_eq!(decoded.simps[2].kind, SimpKind::Unfold(n("Eq.ndrec_symm")));
    assert!(!decoded.uninterpreted.contains(&n(SIMP_EXTENSION)));
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
