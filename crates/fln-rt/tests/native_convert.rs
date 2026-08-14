//! `native_convert` — the named suite for fln-lld's lazy converter membrane
//! (`fln_rt::convert`).
//!
//! # The laws proven here
//!
//! Laziness (a Conversion dropped without projecting allocates nothing),
//! structural fidelity (round-trip: project then inject mirrors the Compat
//! structure exactly — the no-claim boundary made executable), the R10 dedup
//! law (two structurally equal graphs share one native handle; a shared
//! subgraph projects once), the typed failure families (malformed shapes and
//! out-of-subset constructors refused with family and tag), the declarations
//! themselves (all five fields non-blank, so a review can diff them), and the
//! membrane tripwire (the converter is the only module naming both heaps'
//! types in code).

#![forbid(unsafe_code)]

use fln_core::expr::{BinderInfo, Expr, ExprNode, Literal, MVarId, NatLit};
use fln_core::level::{LMVarId, Level};
use fln_core::name::Name;
use fln_core::options::{DataValue, KVMap, SyntaxHandle};
use fln_rt::convert::{Conversion, ConvertError, INJECT_DECL, PROJECT_DECL, inject_expr};
use fln_rt::native_heap::NativeHeap;
use fln_unsafe_abi::handle::Obj;

fn name_component_count(name: &Name) -> usize {
    let mut cursor = name.clone();
    let mut count = 0;
    while !cursor.is_anonymous() {
        count += 1;
        cursor = cursor.parent();
    }
    count
}

fn mk_name(parts: &[&str]) -> Obj {
    let mut out = Obj::mk_ctor(0, Vec::new(), &[]);
    for part in parts {
        out = Obj::mk_ctor(1, vec![out, Obj::mk_string(part)], &[]);
    }
    out
}

fn mk_level_succ(depth: u32) -> Obj {
    let mut out = Obj::mk_ctor(0, Vec::new(), &[]); // zero
    for _ in 0..depth {
        out = Obj::mk_ctor(1, vec![out], &[]);
    }
    out
}

// ---------------------------------------------------------------------------
// Laziness
// ---------------------------------------------------------------------------

#[test]
fn a_conversion_dropped_without_projecting_allocates_nothing() {
    let heap = NativeHeap::new();
    let conversion = Conversion::new();
    let (projected, dedup) = conversion.finish();
    assert_eq!((projected, dedup), (0, 0));
    assert_eq!(
        heap.live(),
        0,
        "laziness: no inspection, no projection, no allocation"
    );
}

// ---------------------------------------------------------------------------
// Structural fidelity: the round-trip law
// ---------------------------------------------------------------------------

#[test]
fn project_then_inject_mirrors_the_structure_exactly() {
    let mut heap = NativeHeap::new();
    // app(sort(succ(succ(zero))), lit(nat 42))
    let sort = Obj::mk_ctor(3, vec![mk_level_succ(2)], &[]);
    let lit = Obj::mk_ctor(9, vec![Obj::mk_ctor(0, vec![Obj::mk_nat(42)], &[])], &[]);
    let app = Obj::mk_ctor(5, vec![sort, lit], &[]);

    let mut conversion = Conversion::new();
    let handle = conversion
        .project_expr(&mut heap, &app)
        .expect("projection succeeds");
    let back = inject_expr(&heap, handle).expect("injection succeeds");

    // Structural mirror, read back through the membrane: tag and shape.
    assert_eq!(back.obj_tag(), 5, "app tag preserved");
    let back_sort = back.ctor_child(0);
    assert_eq!(back_sort.obj_tag(), 3, "sort tag preserved");
    let back_level = back_sort.ctor_child(0);
    assert_eq!(back_level.obj_tag(), 1, "succ tag preserved");
    let back_lit = back.ctor_child(1);
    assert_eq!(back_lit.obj_tag(), 9, "lit tag preserved");
    let back_nat = back_lit.ctor_child(0).ctor_child(0);
    assert!(back_nat.is_scalar());
    assert_eq!(back_nat.unbox(), 42, "the payload is byte-exact");
}

#[test]
fn a_multibyte_string_literal_projects_every_scalar() {
    let mut heap = NativeHeap::new();
    // "héllo" is 5 scalars and 6 UTF-8 bytes. Slicing the buffer with
    // m_length drops the last character.
    let text = Obj::mk_string("héllo");
    let lit = Obj::mk_ctor(9, vec![Obj::mk_ctor(1, vec![text], &[])], &[]);
    let mut conversion = Conversion::new();
    let handle = conversion
        .project_expr(&mut heap, &lit)
        .expect("a well-formed multi-byte string must project");
    let expr = heap.get(handle).expect("the handle resolves");
    assert!(
        matches!(
            expr.node(),
            ExprNode::Lit {
                literal: Literal::Str(value)
            } if value == "héllo"
        ),
        "projection must keep every UTF-8 scalar, not m_length bytes"
    );
}

#[test]
fn injected_nat_literals_use_the_small_nat_ceiling_not_usize_max() {
    let mut heap = NativeHeap::new();

    let zero = heap.alloc(Expr::lit(Literal::Nat(NatLit::from_u64(0))));
    let back_zero = inject_expr(&heap, zero).expect("zero injects");
    let zero_payload = back_zero.ctor_child(0).ctor_child(0);
    assert!(
        zero_payload.is_scalar(),
        "Nat 0 is a tagged scalar, not mpz"
    );
    assert_eq!(zero_payload.unbox(), 0);

    let just_over = heap.alloc(Expr::lit(Literal::Nat(NatLit::from_u64(
        (usize::MAX >> 1) as u64 + 1,
    ))));
    let back_wide =
        inject_expr(&heap, just_over).expect("a Nat just above the tagged ceiling must not panic");
    let wide_payload = back_wide.ctor_child(0).ctor_child(0);
    assert!(
        !wide_payload.is_scalar(),
        "2^63 is a nonnegative mpz, not mk_nat"
    );
    let (_, size, limbs) = wide_payload.mpz_view();
    assert!(size > 0);
    assert_eq!(limbs, &[(usize::MAX >> 1) as u64 + 1]);
}

#[test]
fn const_names_and_levels_round_trip() {
    let mut heap = NativeHeap::new();
    // const Foo.bar [succ zero, param u]
    let levels = Obj::mk_ctor(
        1,
        vec![
            mk_level_succ(1),
            Obj::mk_ctor(
                1,
                vec![
                    Obj::mk_ctor(4, vec![mk_name(&["u"])], &[]),
                    Obj::mk_ctor(0, Vec::new(), &[]),
                ],
                &[],
            ),
        ],
        &[],
    );
    let konst = Obj::mk_ctor(4, vec![mk_name(&["Foo", "bar"]), levels], &[]);
    let mut conversion = Conversion::new();
    let handle = conversion
        .project_expr(&mut heap, &konst)
        .expect("projection");
    let back = inject_expr(&heap, handle).expect("injection");
    assert_eq!(back.obj_tag(), 4);
    let back_name = back.ctor_child(0);
    assert_eq!(back_name.obj_tag(), 1, "a str name node");
    let back_leaf = back_name.ctor_child(1);
    let (size, _, _, bytes) = back_leaf.string_view();
    assert_eq!(
        &bytes[..size - 1],
        b"bar",
        "the leaf name is the UTF-8 payload"
    );
    let expected = Name::from_components(["Foo", "bar"]).hash();
    assert_eq!(
        back_name.ctor_scalar_u64(16),
        expected,
        "injected Name.str carries the cached hash, as olean write does"
    );
}

#[test]
fn an_ill_typed_but_well_formed_structure_converts() {
    // The no-claim boundary, executable: app(sort 0, sort 0) is ill-typed
    // (Prop is not a function) and converts fine — well-typedness is the
    // kernel's judgment, never the converter's.
    let mut heap = NativeHeap::new();
    let sort0 = Obj::mk_ctor(3, vec![Obj::mk_ctor(0, Vec::new(), &[])], &[]);
    let app = Obj::mk_ctor(5, vec![sort0.clone_ref(), sort0], &[]);
    let mut conversion = Conversion::new();
    conversion
        .project_expr(&mut heap, &app)
        .expect("the converter does not judge types");
}

// ---------------------------------------------------------------------------
// The R10 dedup law
// ---------------------------------------------------------------------------

#[test]
fn structurally_equal_graphs_share_one_handle() {
    let mut heap = NativeHeap::new();
    let mk = || {
        Obj::mk_ctor(
            5,
            vec![
                Obj::mk_ctor(3, vec![mk_level_succ(1)], &[]),
                Obj::mk_ctor(9, vec![Obj::mk_ctor(0, vec![Obj::mk_nat(7)], &[])], &[]),
            ],
            &[],
        )
    };
    let first_graph = mk();
    let second_graph = mk();
    let mut conversion = Conversion::new();
    let first = conversion
        .project_expr(&mut heap, &first_graph)
        .expect("first");
    let second = conversion
        .project_expr(&mut heap, &second_graph)
        .expect("second");
    assert_eq!(
        first, second,
        "structurally equal terms share one native handle (upstream's hash-consing)"
    );
    assert_eq!(
        conversion.dedup_hits(),
        1,
        "the second projection allocated nothing"
    );
}

#[test]
fn a_shared_subgraph_projects_once_across_separate_conversions() {
    let mut heap = NativeHeap::new();
    let graph = Obj::mk_ctor(9, vec![Obj::mk_ctor(0, vec![Obj::mk_nat(3)], &[])], &[]);
    let first = Conversion::new()
        .project_expr(&mut heap, &graph)
        .expect("first conversion");
    let second = Conversion::new()
        .project_expr(&mut heap, &graph)
        .expect("a second, independent conversion");
    assert_eq!(
        first, second,
        "the dedup is the heap's interning, so it survives the conversion scope"
    );
    assert_eq!(heap.live(), 1);
}

// ---------------------------------------------------------------------------
// The typed failure families
// ---------------------------------------------------------------------------

#[test]
fn an_out_of_subset_constructor_is_refused_with_family_and_tag() {
    let mut heap = NativeHeap::new();
    // Expr tags 0..=11 are the Lean inventory. Tag 12 is not a constructor.
    let unknown = Obj::mk_ctor(12, Vec::new(), &[]);
    let mut conversion = Conversion::new();
    match conversion.project_expr(&mut heap, &unknown) {
        Err(ConvertError::UnsupportedConstructor { family, tag }) => {
            assert_eq!(family, "expr");
            assert_eq!(tag, 12);
        }
        other => panic!("an unknown Expr tag must be refused typed, got {other:?}"),
    }
}

#[test]
fn a_malformed_shape_is_refused_with_its_reason() {
    let mut heap = NativeHeap::new();
    let scalar = Obj::mk_nat(5);
    let mut conversion = Conversion::new();
    match conversion.project_expr(&mut heap, &scalar) {
        Err(ConvertError::MalformedCompat { family, .. }) => {
            assert_eq!(family, "expr");
        }
        other => panic!("a bare scalar is malformed as an expr, got {other:?}"),
    }
}

#[test]
fn a_numeric_name_component_is_the_stored_u64_not_the_parent_pointer() {
    let mut heap = NativeHeap::new();
    let name = Obj::mk_ctor(2, vec![mk_name(&["foo"])], &7u64.to_le_bytes());
    let levels = Obj::mk_ctor(0, Vec::new(), &[]);
    let konst = Obj::mk_ctor(4, vec![name, levels], &[]);
    let mut conversion = Conversion::new();
    let handle = conversion
        .project_expr(&mut heap, &konst)
        .expect("Name.num must project without panicking");
    let expr = heap.get(handle).expect("the handle resolves");
    let ExprNode::Const { name, .. } = expr.node() else {
        panic!("expected a const");
    };
    assert_eq!(
        name.to_display_string(),
        "foo.7",
        "the component is the scalar after the parent pointer, not byte 0"
    );

    let native = Name::num(Name::from_components(["foo"]), 7);
    let injected_handle = heap.alloc(Expr::const_(native, Vec::new()));
    let injected = inject_expr(&heap, injected_handle).expect("injecting Name.num");
    let mut conversion = Conversion::new();
    let back = conversion
        .project_expr(&mut heap, &injected)
        .expect("round-trip Name.num");
    let ExprNode::Const { name, .. } = heap.get(back).expect("handle").node() else {
        panic!("expected a const");
    };
    assert_eq!(name.to_display_string(), "foo.7");
    assert_eq!(
        injected.ctor_child(0).header().other,
        2,
        "injected Name.num is Lean's two object children, not an inline u64"
    );
    assert!(
        injected.ctor_child(0).ctor_child(1).is_scalar(),
        "the Name.num component is a boxed Nat"
    );
    assert_eq!(injected.ctor_child(0).ctor_child(1).unbox(), 7);
}

#[test]
fn a_negative_mpz_nat_literal_is_refused_as_negative() {
    let mut heap = NativeHeap::new();
    let lit = Obj::mk_ctor(
        9,
        vec![Obj::mk_ctor(0, vec![Obj::mk_mpz(&[1], true)], &[])],
        &[],
    );
    let mut conversion = Conversion::new();
    match conversion.project_expr(&mut heap, &lit) {
        Err(ConvertError::MalformedCompat { family, reason }) => {
            assert_eq!(family, "literal");
            assert!(
                reason.contains("negative"),
                "the sign lives in _mp_size, not _mp_alloc; got {reason}"
            );
        }
        other => panic!("a negative mpz Nat must be refused as negative, got {other:?}"),
    }
}

#[test]
fn a_bvar_index_wider_than_u32_is_overflow_not_a_wrapped_index() {
    let mut heap = NativeHeap::new();
    let wide = u64::from(u32::MAX) + 5;
    let bvar = Obj::mk_ctor(0, Vec::new(), &wide.to_le_bytes());
    let mut conversion = Conversion::new();
    match conversion.project_expr(&mut heap, &bvar) {
        Err(ConvertError::NativeOverflow { family }) => assert_eq!(family, "expr"),
        other => panic!("a u64 index above u32::MAX must not wrap into a live bvar, got {other:?}"),
    }
}

#[test]
fn a_nat_literal_whose_payload_is_not_mpz_is_malformed_not_a_panic() {
    let mut heap = NativeHeap::new();
    let lit = Obj::mk_ctor(
        9,
        vec![Obj::mk_ctor(0, vec![Obj::mk_string("not-a-nat")], &[])],
        &[],
    );
    let mut conversion = Conversion::new();
    match conversion.project_expr(&mut heap, &lit) {
        Err(ConvertError::MalformedCompat { family, reason }) => {
            assert_eq!(family, "literal");
            assert!(
                reason.contains("mpz"),
                "a non-mpz boxed Nat payload must name mpz, got {reason}"
            );
        }
        other => panic!("a string posing as a Nat payload must be malformed, got {other:?}"),
    }
}

#[test]
fn a_name_str_whose_text_is_not_a_string_is_malformed_not_a_panic() {
    let mut heap = NativeHeap::new();
    let name = Obj::mk_ctor(1, vec![mk_name(&[]), Obj::mk_ctor(0, Vec::new(), &[])], &[]);
    let levels = Obj::mk_ctor(0, Vec::new(), &[]);
    let konst = Obj::mk_ctor(4, vec![name, levels], &[]);
    let mut conversion = Conversion::new();
    match conversion.project_expr(&mut heap, &konst) {
        Err(ConvertError::MalformedCompat { family, reason }) => {
            assert_eq!(family, "string");
            assert!(
                reason.contains("string"),
                "Name.str's second child must be a string object, got {reason}"
            );
        }
        other => panic!("a ctor posing as a Name.str text must be malformed, got {other:?}"),
    }
}

#[test]
fn lean_box0_nullary_constructors_project_as_anonymous_zero_and_nil() {
    let mut heap = NativeHeap::new();
    // Lean Name.anonymous / Level.zero / List.nil are lean_box(0).
    let name = Obj::mk_nat(0);
    let levels = Obj::mk_nat(0);
    let konst = Obj::mk_ctor(4, vec![name, levels], &[]);
    let mut conversion = Conversion::new();
    let handle = conversion
        .project_expr(&mut heap, &konst)
        .expect("Lean-true nullary names and lists must project");
    let ExprNode::Const { name, levels } = heap.get(handle).expect("handle").node() else {
        panic!("expected a const");
    };
    assert!(name.is_anonymous(), "box(0) is Name.anonymous");
    assert!(levels.is_empty(), "box(0) is List.nil");

    let sort = Obj::mk_ctor(3, vec![Obj::mk_nat(0)], &[]);
    let mut conversion = Conversion::new();
    let handle = conversion
        .project_expr(&mut heap, &sort)
        .expect("Lean-true Level.zero must project");
    let ExprNode::Sort { level } = heap.get(handle).expect("handle").node() else {
        panic!("expected a sort");
    };
    assert!(level.is_zero(), "box(0) is Level.zero");
}

#[test]
fn inject_emits_lean_box0_for_anonymous_zero_and_nil() {
    let mut heap = NativeHeap::new();
    let handle = heap.alloc(Expr::const_(Name::anonymous(), Vec::new()));
    let back = inject_expr(&heap, handle).expect("anonymous const injects");
    assert!(
        back.ctor_child(0).is_scalar() && back.ctor_child(0).unbox() == 0,
        "injected Name.anonymous is lean_box(0)"
    );
    assert!(
        back.ctor_child(1).is_scalar() && back.ctor_child(1).unbox() == 0,
        "injected List.nil is lean_box(0)"
    );

    let sort = heap.alloc(Expr::sort(Level::zero()));
    let back_sort = inject_expr(&heap, sort).expect("sort 0 injects");
    assert!(
        back_sort.ctor_child(0).is_scalar() && back_sort.ctor_child(0).unbox() == 0,
        "injected Level.zero is lean_box(0)"
    );

    let succ = Level::zero().succ().expect("succ packs");
    let sort_succ = heap.alloc(Expr::sort(succ.clone()));
    let back_succ = inject_expr(&heap, sort_succ).expect("sort succ injects");
    assert_eq!(
        back_succ.ctor_child(0).ctor_scalar_u64(8),
        succ.data().0,
        "injected Level.succ carries Level.Data after its child"
    );
}

#[test]
fn a_bvar_with_no_scalar_bytes_is_malformed_not_a_panic() {
    let mut heap = NativeHeap::new();
    let bvar = Obj::mk_ctor(0, Vec::new(), &[]);
    let mut conversion = Conversion::new();
    match conversion.project_expr(&mut heap, &bvar) {
        Err(ConvertError::MalformedCompat { family, reason }) => {
            assert_eq!(family, "expr");
            assert!(
                reason.contains("scalar"),
                "a bvar without an index word must name the missing scalar, got {reason}"
            );
        }
        other => panic!("a 0-byte bvar must be malformed, got {other:?}"),
    }
}

#[test]
fn a_short_constructor_is_malformed_not_a_panic() {
    let mut heap = NativeHeap::new();
    // Expr.app needs two children; zero fields used to assert in ctor_child.
    let app = Obj::mk_ctor(5, Vec::new(), &[]);
    let mut conversion = Conversion::new();
    match conversion.project_expr(&mut heap, &app) {
        Err(ConvertError::MalformedCompat { family, reason }) => {
            assert_eq!(family, "expr");
            assert!(
                reason.contains("fields"),
                "a short ctor must name the missing field, got {reason}"
            );
        }
        other => panic!("a 0-field app must be malformed, got {other:?}"),
    }
}

#[test]
fn a_lean_true_two_child_name_num_projects_the_nat_child() {
    let mut heap = NativeHeap::new();
    let name = Obj::mk_ctor(2, vec![mk_name(&["foo"]), Obj::mk_nat(7)], &[]);
    let levels = Obj::mk_ctor(0, Vec::new(), &[]);
    let konst = Obj::mk_ctor(4, vec![name, levels], &[]);
    let mut conversion = Conversion::new();
    let handle = conversion
        .project_expr(&mut heap, &konst)
        .expect("Lean Name.num is two object children, not an inline u64");
    let ExprNode::Const { name, .. } = heap.get(handle).expect("handle").node() else {
        panic!("expected a const");
    };
    assert_eq!(name.to_display_string(), "foo.7");
}

#[test]
fn a_stored_name_hash_that_disagrees_with_the_children_is_malformed() {
    let mut heap = NativeHeap::new();
    let name = Obj::mk_ctor(
        2,
        vec![mk_name(&["foo"]), Obj::mk_nat(7)],
        &0xDEAD_BEEF_u64.to_le_bytes(),
    );
    let levels = Obj::mk_ctor(0, Vec::new(), &[]);
    let konst = Obj::mk_ctor(4, vec![name, levels], &[]);
    match Conversion::new().project_expr(&mut heap, &konst) {
        Err(ConvertError::MalformedCompat { family, reason }) => {
            assert_eq!(family, "name");
            assert!(
                reason.contains("Name.hash"),
                "a hostile hash word must name Name.hash, got {reason}"
            );
        }
        other => panic!("mismatched Name.hash must be malformed, got {other:?}"),
    }
}

#[test]
fn a_lean_true_bvar_nat_child_projects() {
    let mut heap = NativeHeap::new();
    let bvar = Obj::mk_ctor(0, vec![Obj::mk_nat(3)], &[]);
    let mut conversion = Conversion::new();
    let handle = conversion
        .project_expr(&mut heap, &bvar)
        .expect("Lean bvar is a Nat child, not only an inline u64");
    let ExprNode::BVar { idx } = heap.get(handle).expect("handle").node() else {
        panic!("expected a bvar");
    };
    assert_eq!(*idx, 3);
}

#[test]
fn inject_emits_a_nat_child_for_bvar() {
    let mut heap = NativeHeap::new();
    let handle = heap.alloc(Expr::bvar(4).expect("bvar 4 packs"));
    let back = inject_expr(&heap, handle).expect("bvar injects");
    assert_eq!(back.header().other, 1, "Lean bvar has one Nat child");
    assert!(back.ctor_child(0).is_scalar());
    assert_eq!(back.ctor_child(0).unbox(), 4);
    let native = Expr::bvar(4).expect("bvar 4 packs");
    assert_eq!(
        back.ctor_scalar_u64(8),
        native.data().0,
        "injected bvar carries Expr.Data after the Nat child"
    );
}

#[test]
fn inject_and_project_round_trip_lam_forall_let_mvar_proj_and_mdata() {
    let mut heap = NativeHeap::new();
    let ty = Expr::sort(Level::zero());
    let body = Expr::bvar(0).expect("bvar 0 packs");
    let lam = Expr::lam(
        Name::from_components(["x"]),
        ty.clone(),
        body.clone(),
        BinderInfo::Implicit,
    );
    let forall = Expr::forall_e(
        Name::from_components(["y"]),
        ty.clone(),
        body.clone(),
        BinderInfo::InstImplicit,
    );
    let let_e = Expr::let_e(
        Name::from_components(["z"]),
        ty.clone(),
        Expr::lit(Literal::Nat(NatLit::from_u64(1))),
        body.clone(),
        true,
    );
    let mvar = Expr::mvar(MVarId(Name::from_components(["m"])));
    let proj = Expr::proj(Name::from_components(["Pair"]), 1, body.clone());
    let metadata = KVMap::from_entries(vec![(
        Name::from_components(["note"]),
        DataValue::OfString("hi".to_string()),
    )]);
    let mdata = Expr::mdata(metadata, body);

    for native in [lam, forall, let_e, mvar, proj, mdata] {
        let handle = heap.alloc(native.clone());
        let injected = inject_expr(&heap, handle).expect("binder/mdata/proj inject");
        let back = Conversion::new()
            .project_expr(&mut heap, &injected)
            .expect("binder/mdata/proj project");
        let restored = heap.get(back).expect("handle");
        assert_eq!(
            restored.hash(),
            native.hash(),
            "injected Lean-true packing must project to the same term"
        );
    }

    let lam = Expr::lam(
        Name::from_components(["x"]),
        ty,
        Expr::bvar(0).expect("bvar 0 packs"),
        BinderInfo::Implicit,
    );
    let handle = heap.alloc(lam.clone());
    let injected = inject_expr(&heap, handle).expect("lam inject");
    assert_eq!(injected.header().other, 3, "Lean lam has three children");
    assert_eq!(
        injected.ctor_scalar_u64(24),
        lam.data().0,
        "injected lam carries Expr.Data after the children"
    );
    assert_eq!(
        injected.ctor_scalar_u64(32) as u8,
        BinderInfo::Implicit.to_u64() as u8,
        "injected lam carries BinderInfo after Expr.Data"
    );
}

#[test]
fn a_lean_true_lam_projects_its_binder_info() {
    let mut heap = NativeHeap::new();
    let ty = Expr::sort(Level::zero());
    let body = Expr::bvar(0).expect("bvar 0 packs");
    let native = Expr::lam(
        Name::from_components(["x"]),
        ty,
        body,
        BinderInfo::StrictImplicit,
    );
    let handle = heap.alloc(native);
    let injected = inject_expr(&heap, handle).expect("lam injects");
    let back = Conversion::new()
        .project_expr(&mut heap, &injected)
        .expect("a Lean-true lam must project");
    let ExprNode::Lam { binder_info, .. } = heap.get(back).expect("handle").node() else {
        panic!("expected a lam");
    };
    assert_eq!(*binder_info, BinderInfo::StrictImplicit);
}

#[test]
fn a_stored_expr_data_word_that_disagrees_with_the_children_is_malformed() {
    let mut heap = NativeHeap::new();
    let sort = Obj::mk_ctor(3, vec![Obj::mk_nat(0)], &0xDEAD_BEEF_u64.to_le_bytes());
    match Conversion::new().project_expr(&mut heap, &sort) {
        Err(ConvertError::MalformedCompat { family, reason }) => {
            assert_eq!(family, "expr");
            assert!(
                reason.contains("Expr.Data"),
                "a hostile Data word must name Expr.Data, got {reason}"
            );
        }
        other => panic!("mismatched Expr.Data must be malformed, got {other:?}"),
    }
}

#[test]
fn a_stored_level_data_word_that_disagrees_with_the_children_is_malformed() {
    let mut heap = NativeHeap::new();
    let succ = Obj::mk_ctor(1, vec![Obj::mk_nat(0)], &0xDEAD_BEEF_u64.to_le_bytes());
    let sort = Obj::mk_ctor(3, vec![succ], &[]);
    match Conversion::new().project_expr(&mut heap, &sort) {
        Err(ConvertError::MalformedCompat { family, reason }) => {
            assert_eq!(family, "level");
            assert!(
                reason.contains("Level.Data"),
                "a hostile Data word must name Level.Data, got {reason}"
            );
        }
        other => panic!("mismatched Level.Data must be malformed, got {other:?}"),
    }
}

#[test]
fn a_lam_missing_its_binder_info_word_is_malformed_not_a_panic() {
    let mut heap = NativeHeap::new();
    let ty = Obj::mk_ctor(3, vec![Obj::mk_nat(0)], &[]);
    let body = Obj::mk_ctor(0, vec![Obj::mk_nat(0)], &[]);
    let lam = Obj::mk_ctor(6, vec![mk_name(&["x"]), ty, body], &[]);
    match Conversion::new().project_expr(&mut heap, &lam) {
        Err(ConvertError::MalformedCompat { family, reason }) => {
            assert_eq!(family, "expr");
            assert!(
                reason.contains("scalar"),
                "a lam without BinderInfo must name the missing scalar, got {reason}"
            );
        }
        other => panic!("a lam without BinderInfo must be malformed, got {other:?}"),
    }
}

#[test]
fn inject_and_project_round_trip_a_level_metavariable() {
    let mut heap = NativeHeap::new();
    let sort = Expr::sort(Level::mvar(LMVarId(Name::from_components(["u"]))));
    let handle = heap.alloc(sort.clone());
    let injected = inject_expr(&heap, handle).expect("level mvar injects");
    assert_eq!(
        injected.ctor_child(0).obj_tag(),
        5,
        "injected Level.mvar is ctor tag 5"
    );
    let back = Conversion::new()
        .project_expr(&mut heap, &injected)
        .expect("level mvar projects");
    assert_eq!(heap.get(back).expect("handle").hash(), sort.hash());
}

#[test]
fn inject_and_project_round_trip_mdata_int_entries() {
    let mut heap = NativeHeap::new();
    let body = Expr::bvar(0).expect("bvar 0 packs");
    let metadata = KVMap::from_entries(vec![
        (Name::from_components(["neg"]), DataValue::OfInt(-42)),
        (Name::from_components(["min"]), DataValue::OfInt(i64::MIN)),
        (Name::from_components(["max"]), DataValue::OfInt(i64::MAX)),
        (Name::from_components(["zero"]), DataValue::OfInt(0)),
    ]);
    let native = Expr::mdata(metadata, body);
    let handle = heap.alloc(native.clone());
    let injected = inject_expr(&heap, handle).expect("ofInt injects");
    let back = Conversion::new()
        .project_expr(&mut heap, &injected)
        .expect("ofInt projects");
    let ExprNode::MData { data: restored, .. } = heap.get(back).expect("handle").node() else {
        panic!("expected mdata");
    };
    let ExprNode::MData { data: original, .. } = native.node() else {
        panic!("the fixture is mdata");
    };
    assert_eq!(
        restored.entries(),
        original.entries(),
        "Lean Int scalars and i64-min mpz must survive the membrane"
    );
}

#[test]
fn an_int_payload_that_is_not_mpz_is_malformed_not_a_panic() {
    let mut heap = NativeHeap::new();
    let value = Obj::mk_ctor(4, vec![Obj::mk_string("not-an-int")], &[]);
    let pair = Obj::mk_ctor(0, vec![mk_name(&["k"]), value], &[]);
    let list = Obj::mk_ctor(1, vec![pair, Obj::mk_nat(0)], &[]);
    let body = Obj::mk_ctor(0, vec![Obj::mk_nat(0)], &[]);
    let mdata = Obj::mk_ctor(10, vec![list, body], &[]);
    match Conversion::new().project_expr(&mut heap, &mdata) {
        Err(ConvertError::MalformedCompat { family, reason }) => {
            assert_eq!(family, "data-value");
            assert!(
                reason.contains("Int"),
                "a string posing as an Int payload must name Int, got {reason}"
            );
        }
        other => panic!("a string posing as an Int must be malformed, got {other:?}"),
    }
}

#[test]
fn inject_and_project_round_trip_mdata_syntax_handles() {
    let mut heap = NativeHeap::new();
    let body = Expr::bvar(0).expect("bvar 0 packs");
    let metadata = KVMap::from_entries(vec![
        (
            Name::from_components(["small"]),
            DataValue::OfSyntax(SyntaxHandle(42)),
        ),
        (
            Name::from_components(["wide"]),
            DataValue::OfSyntax(SyntaxHandle(u64::MAX)),
        ),
    ]);
    let native = Expr::mdata(metadata, body);
    let handle = heap.alloc(native.clone());
    let injected = inject_expr(&heap, handle).expect("ofSyntax handle injects");
    let back = Conversion::new()
        .project_expr(&mut heap, &injected)
        .expect("ofSyntax handle projects");
    let ExprNode::MData { data: restored, .. } = heap.get(back).expect("handle").node() else {
        panic!("expected mdata");
    };
    let ExprNode::MData { data: original, .. } = native.node() else {
        panic!("the fixture is mdata");
    };
    assert_eq!(
        restored.entries(),
        original.entries(),
        "a scalar or mpz SyntaxHandle must survive the membrane"
    );
}

#[test]
fn a_syntax_tree_payload_stays_an_unsupported_constructor() {
    let mut heap = NativeHeap::new();
    let syntax = Obj::mk_ctor(0, vec![Obj::mk_string("ident")], &[]);
    let value = Obj::mk_ctor(5, vec![syntax], &[]);
    let pair = Obj::mk_ctor(0, vec![mk_name(&["k"]), value], &[]);
    let list = Obj::mk_ctor(1, vec![pair, Obj::mk_nat(0)], &[]);
    let body = Obj::mk_ctor(0, vec![Obj::mk_nat(0)], &[]);
    let mdata = Obj::mk_ctor(10, vec![list, body], &[]);
    match Conversion::new().project_expr(&mut heap, &mdata) {
        Err(ConvertError::UnsupportedConstructor { family, tag }) => {
            assert_eq!(family, "data-value");
            assert_eq!(tag, 5, "ofSyntax is DataValue ctor tag 5");
        }
        other => panic!("a Syntax tree payload must stay unsupported, got {other:?}"),
    }
}

#[test]
fn project_walks_a_hand_built_long_name_chain() {
    // Older convert-subset packing: children only, no hash word. Must still
    // walk iteratively — a 400-component Name is legal.
    let mut chain = Obj::mk_nat(0);
    for _ in 0..400 {
        chain = Obj::mk_ctor(1, vec![chain, Obj::mk_string("a")], &[]);
    }
    let expr = Obj::mk_ctor(4, vec![chain, Obj::mk_nat(0)], &[]);
    let mut heap = NativeHeap::new();
    let back = Conversion::new()
        .project_expr(&mut heap, &expr)
        .expect("a 400-component Compat Name is legal");
    let ExprNode::Const { name, .. } = heap.get(back).expect("handle").node() else {
        panic!("expected a const");
    };
    assert_eq!(name_component_count(name), 400);
}

#[test]
fn inject_walks_a_long_name_chain_without_a_stack_fault() {
    let mut name = Name::anonymous();
    for _ in 0..400 {
        name = Name::str(name, "a");
    }
    let mut heap = NativeHeap::new();
    let handle = heap.alloc(Expr::const_(name, Vec::new()));
    inject_expr(&heap, handle).expect("inject_name is iterative on the parent chain");
}

#[test]
fn project_walks_a_long_name_chain_without_a_stack_fault() {
    let mut name = Name::anonymous();
    for _ in 0..400 {
        name = Name::str(name, "a");
    }
    let mut heap = NativeHeap::new();
    let handle = heap.alloc(Expr::const_(name.clone(), Vec::new()));
    let injected = inject_expr(&heap, handle).expect("inject_name is iterative");
    let back = Conversion::new()
        .project_expr(&mut heap, &injected)
        .expect("project_name is iterative on the parent chain");
    let ExprNode::Const { name: restored, .. } = heap.get(back).expect("handle").node() else {
        panic!("expected a const");
    };
    assert_eq!(restored.hash(), name.hash());
    assert_eq!(name_component_count(restored), 400);
}

#[test]
fn inject_walks_a_long_succ_tower_without_a_stack_fault() {
    let mut level = Level::zero();
    for _ in 0..400 {
        level = level.succ().expect("400 < 2^24");
    }
    let mut heap = NativeHeap::new();
    let handle = heap.alloc(Expr::sort(level));
    inject_expr(&heap, handle).expect("inject_level is iterative on succ");
}

#[test]
fn project_walks_a_long_succ_tower_without_a_stack_fault() {
    let mut level = Level::zero();
    for _ in 0..400 {
        level = level.succ().expect("400 < 2^24");
    }
    let mut heap = NativeHeap::new();
    let handle = heap.alloc(Expr::sort(level.clone()));
    let injected = inject_expr(&heap, handle).expect("inject_level is iterative on succ");
    let back = Conversion::new()
        .project_expr(&mut heap, &injected)
        .expect("project_level is iterative on succ");
    let ExprNode::Sort { level: restored } = heap.get(back).expect("handle").node() else {
        panic!("expected a sort");
    };
    assert_eq!(restored.depth(), 400, "a legal 400-deep succ must project");
    assert_eq!(restored.hash(), level.hash());
}

#[test]
fn project_walks_a_hand_built_long_succ_tower() {
    // Older convert-subset packing: no Data word. Must still walk iteratively.
    let mut heap = NativeHeap::new();
    let sort = Obj::mk_ctor(3, vec![mk_level_succ(400)], &[]);
    let back = Conversion::new()
        .project_expr(&mut heap, &sort)
        .expect("a 400-deep Compat succ tower is a legal Level");
    let ExprNode::Sort { level } = heap.get(back).expect("handle").node() else {
        panic!("expected a sort");
    };
    assert_eq!(level.depth(), 400);
}

#[test]
fn project_reuses_a_shared_level_child() {
    let succ = Level::zero().succ().expect("packs");
    let diamond = Level::max(succ.clone(), succ).expect("packs");
    let mut heap = NativeHeap::new();
    let handle = heap.alloc(Expr::sort(diamond.clone()));
    let injected = inject_expr(&heap, handle).expect("a shared succ injects once");
    let back = Conversion::new()
        .project_expr(&mut heap, &injected)
        .expect("a max of a shared succ must not look like a cycle");
    let ExprNode::Sort { level: restored } = heap.get(back).expect("handle").node() else {
        panic!("expected a sort");
    };
    assert_eq!(restored.hash(), diamond.hash());
}

#[test]
fn inject_refuses_an_expr_deeper_than_the_walk_ceiling() {
    let mut expr = Expr::bvar(0).expect("packs");
    for _ in 0..400 {
        expr = Expr::app(expr, Expr::bvar(0).expect("packs"));
    }
    let mut heap = NativeHeap::new();
    let handle = heap.alloc(expr);
    match inject_expr(&heap, handle) {
        Err(ConvertError::NativeOverflow { family }) => assert_eq!(family, "expr"),
        Err(other) => panic!("a 400-deep app nest must overflow typed, got {other}"),
        Ok(_) => panic!("a 400-deep app nest must overflow typed, not inject"),
    }
}

// ---------------------------------------------------------------------------
// The declarations and the membrane tripwire
// ---------------------------------------------------------------------------

#[test]
fn the_five_declarations_are_present_and_non_blank() {
    for decl in [PROJECT_DECL, INJECT_DECL] {
        for field in [
            decl.ownership,
            decl.allocation,
            decl.failure,
            decl.capability,
            decl.no_claim,
        ] {
            assert!(!field.trim().is_empty(), "every declared field is written");
        }
    }
}

#[test]
fn the_converter_is_the_only_module_naming_both_heaps() {
    // The membrane law at the source level: convert.rs is the one module that
    // may name the Compat side's types and the NativeHeap's types together.
    // Any other module doing so is a second membrane, which the acceptance
    // forbids.
    let convert = include_str!("../src/convert.rs");
    assert!(convert.contains("fln_unsafe_abi::handle::Obj"));
    assert!(convert.contains("NativeHeap"));
    let native_heap = include_str!("../src/native_heap.rs");
    let code: String = native_heap
        .lines()
        .filter(|line| !line.trim_start().starts_with("//"))
        .collect::<Vec<_>>()
        .join("\n");
    assert!(
        !code.contains("fln_unsafe_abi"),
        "native_heap.rs must not name the Compat side in code (the converters are \
         the only membrane — this is the same tripwire as the native_heap suite's)"
    );
}
