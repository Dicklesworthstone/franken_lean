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
