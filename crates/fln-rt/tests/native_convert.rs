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

use fln_core::expr::{BinderInfo, Expr, ExprNode, Literal, NatLit};
use fln_core::level::Level;
use fln_core::name::Name;
use fln_rt::convert::{Conversion, ConvertError, INJECT_DECL, PROJECT_DECL, inject_expr};
use fln_rt::native_heap::NativeHeap;
use fln_unsafe_abi::handle::Obj;

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
    let (_, _, len, bytes) = back_leaf.string_view();
    assert_eq!(&bytes[..len], b"bar", "the leaf name is byte-exact");
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
    // lam (tag 6) is outside the converted subset.
    let lam = Obj::mk_ctor(
        6,
        vec![
            mk_name(&["x"]),
            Obj::mk_ctor(3, vec![Obj::mk_ctor(0, Vec::new(), &[])], &[]),
            Obj::mk_ctor(0, Vec::new(), &[]),
        ],
        &[],
    );
    let mut conversion = Conversion::new();
    match conversion.project_expr(&mut heap, &lam) {
        Err(ConvertError::UnsupportedConstructor { family, tag }) => {
            assert_eq!(family, "expr");
            assert_eq!(tag, 6);
        }
        other => panic!("a lam must be refused typed, got {other:?}"),
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
fn injecting_an_out_of_subset_constructor_is_refused_not_a_panic() {
    let mut heap = NativeHeap::new();
    let ty = Expr::sort(Level::zero());
    let body = Expr::bvar(0).expect("bvar 0 packs");
    let lam = Expr::lam(Name::from_components(["x"]), ty, body, BinderInfo::Default);
    let handle = heap.alloc(lam);
    match inject_expr(&heap, handle) {
        Err(ConvertError::UnsupportedConstructor { family, tag }) => {
            assert_eq!(family, "expr");
            assert_eq!(tag, 6, "lam is Expr ctor tag 6");
        }
        other => panic!(
            "injecting a lam must be a typed refusal, got {}",
            match other {
                Ok(_) => "Ok(obj)".to_string(),
                Err(error) => format!("Err({error})"),
            }
        ),
    }
}

#[test]
fn injecting_a_level_metavariable_is_refused_not_a_panic() {
    let mut heap = NativeHeap::new();
    let sort = Expr::sort(Level::mvar(fln_core::level::LMVarId(
        Name::from_components(["u"]),
    )));
    let handle = heap.alloc(sort);
    match inject_expr(&heap, handle) {
        Err(ConvertError::UnsupportedConstructor { family, tag }) => {
            assert_eq!(family, "level");
            assert_eq!(tag, 5, "Level.mvar is ctor tag 5");
        }
        other => panic!(
            "injecting a level mvar must be a typed refusal, got {}",
            match other {
                Ok(_) => "Ok(obj)".to_string(),
                Err(error) => format!("Err({error})"),
            }
        ),
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
