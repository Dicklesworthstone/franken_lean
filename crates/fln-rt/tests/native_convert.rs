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
use fln_rt::convert::{
    Conversion, ConvertError, ExprConstructor, INJECT_DECL, PROJECT_DECL, inject_expr, inject_level,
};
use fln_rt::native_heap::{HeapError, NativeHeap};
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

#[test]
fn projection_into_a_closed_heap_returns_a_typed_error_and_remains_reusable() {
    let input = Obj::mk_ctor(0, vec![Obj::mk_nat(0)], &[]);
    let mut closed = NativeHeap::new();
    closed.close();
    let mut conversion = Conversion::new();
    let error = conversion
        .project_expr(&mut closed, &input)
        .expect_err("a closed destination must refuse projection");
    assert_eq!(
        std::error::Error::source(&error).and_then(|source| source.downcast_ref::<HeapError>()),
        Some(&HeapError::Closed)
    );
    assert!(closed.is_closed());
    assert_eq!(closed.live(), 0);
    let mut fresh = NativeHeap::new();
    let recovered = conversion.project_expr(&mut fresh, &input).unwrap();
    assert_eq!(fresh.get(recovered).unwrap(), &Expr::bvar(0).unwrap());
    assert_eq!(fresh.live(), 1);
}

#[test]
fn standalone_levels_round_trip_without_normalizing_and_share_the_scope_budget() {
    let mut source = NativeHeap::new();
    let level = Level::max(Level::zero(), Level::one()).unwrap();
    let handle = source.alloc(level.clone());
    let object = inject_level(&source, handle).unwrap();
    let mut target = NativeHeap::new();
    let mut conversion = Conversion::with_node_budget(6);
    let first = conversion.project_level(&mut target, &object).unwrap();
    let second = conversion.project_level(&mut target, &object).unwrap();
    assert_eq!(first, second);
    assert_eq!(target.get(first).unwrap(), &level);
    assert_ne!(target.get(first).unwrap(), &Level::one());
    assert_eq!((conversion.projected(), conversion.dedup_hits()), (2, 1));
    assert!(matches!(
        conversion.project_level(&mut target, &Obj::mk_nat(0)),
        Err(ConvertError::NodeBudgetExhausted {
            family: "level",
            visited: 7,
            budget: 6,
        })
    ));
    assert_eq!(target.live(), 1, "a resource stop publishes no new handle");

    let mut closed = NativeHeap::new();
    closed.close();
    assert!(matches!(
        Conversion::new().project_level(&mut closed, &object),
        Err(ConvertError::NativeHeap(HeapError::Closed))
    ));
    assert!(matches!(
        inject_level(&closed, first),
        Err(ConvertError::NativeHeap(_))
    ));
}

#[test]
fn node_limits_stop_descent_before_unvisited_malformed_descendants() {
    // A postorder-only budget reaches the unknown leaf before charging any
    // ancestor. Charging first entry must instead stop at the ninth node.
    let mut expression = Obj::mk_ctor(99, Vec::new(), &[]);
    let mut level = Obj::mk_ctor(99, Vec::new(), &[]);
    for _ in 0..400 {
        expression = Obj::mk_ctor(
            5,
            vec![Obj::mk_ctor(0, vec![Obj::mk_nat(0)], &[]), expression],
            &[],
        );
        level = Obj::mk_ctor(1, vec![level], &[]);
    }
    let mut heap = NativeHeap::new();
    assert!(matches!(
        Conversion::with_node_budget(8).project_expr(&mut heap, &expression),
        Err(ConvertError::NodeBudgetExhausted {
            family: "expr",
            visited: 9,
            budget: 8,
        })
    ));
    assert!(matches!(
        Conversion::with_node_budget(8).project_level(&mut heap, &level),
        Err(ConvertError::NodeBudgetExhausted {
            family: "level",
            visited: 9,
            budget: 8,
        })
    ));
    assert!(matches!(
        Conversion::new().project_expr(&mut heap, &expression),
        Err(ConvertError::UnsupportedConstructor {
            family: "expr",
            tag: 99
        })
    ));
    assert!(matches!(
        Conversion::new().project_level(&mut heap, &level),
        Err(ConvertError::UnsupportedConstructor {
            family: "level",
            tag: 99
        })
    ));
    assert_eq!(
        heap.live(),
        0,
        "neither resource nor malformed stops publish handles"
    );
}

#[test]
fn first_entry_accounting_counts_shared_expr_nodes_once() {
    let child = Obj::mk_ctor(0, vec![Obj::mk_nat(0)], &[]);
    let root = Obj::mk_ctor(5, vec![child.clone_ref(), child.clone_ref()], &[]);
    let mut heap = NativeHeap::new();
    let mut conversion = Conversion::with_node_budget(2);
    let handle = conversion.project_expr(&mut heap, &root).unwrap();
    assert_eq!(
        heap.get(handle).unwrap(),
        &Expr::app(Expr::bvar(0).unwrap(), Expr::bvar(0).unwrap())
    );
    assert!(matches!(
        conversion.project_expr(&mut heap, &child),
        Err(ConvertError::NodeBudgetExhausted {
            family: "expr",
            visited: 3,
            budget: 2
        })
    ));
    assert_eq!(heap.live(), 1);
}

#[test]
fn string_payload_budget_is_aggregate_and_publishes_no_partial_handle() {
    let text = "λ\0🙂";
    let literal = Obj::mk_ctor(1, vec![Obj::mk_string(text)], &[]);
    let expression = Obj::mk_ctor(9, vec![literal.clone_ref()], &[]);
    let level = Obj::mk_ctor(4, vec![mk_name(&[text])], &[]);
    let mut heap = NativeHeap::new();
    let mut too_small = Conversion::with_budgets(100, text.len() - 1);
    assert!(matches!(
        too_small.project_expr(&mut heap, &expression),
        Err(ConvertError::ByteBudgetExhausted {
            family: "string",
            visited: 7,
            budget: 6
        })
    ));
    assert_eq!(heap.live(), 0);
    assert!(matches!(
        Conversion::with_budgets(100, text.len() - 1).project_level(&mut heap, &level),
        Err(ConvertError::ByteBudgetExhausted {
            family: "string",
            visited: 7,
            budget: 6
        })
    ));
    assert_eq!(heap.live(), 0);

    let mut shared = Conversion::with_budgets(100, text.len());
    let first = shared.project_expr(&mut heap, &expression).unwrap();
    assert!(matches!(
        shared.project_level(&mut heap, &level),
        Err(ConvertError::ByteBudgetExhausted {
            family: "string",
            visited: 14,
            budget: 7
        })
    ));
    assert_eq!(
        heap.live(),
        1,
        "a later exhausted projection preserves earlier handles"
    );
    assert_eq!(
        heap.get(first).unwrap(),
        &Expr::lit(Literal::Str(text.to_owned()))
    );
    let repaired = Conversion::with_budgets(100, text.len())
        .project_level(&mut heap, &level)
        .unwrap();
    assert_eq!(
        heap.get(repaired).unwrap(),
        &Level::param(Name::str(Name::anonymous(), text))
    );
}

#[test]
fn natural_literal_limb_copies_share_the_string_byte_allowance() {
    let literal = Obj::mk_ctor(0, vec![Obj::mk_mpz(&[7, 1], false)], &[]);
    let expression = Obj::mk_ctor(9, vec![literal.clone_ref()], &[]);
    let mut heap = NativeHeap::new();
    assert!(matches!(
        Conversion::with_budgets(100, 15).project_expr(&mut heap, &expression),
        Err(ConvertError::ByteBudgetExhausted {
            family: "literal",
            visited: 16,
            budget: 15
        })
    ));
    assert_eq!(heap.live(), 0);
    let string = Obj::mk_ctor(1, vec![Obj::mk_string("x")], &[]);
    let mut shared = Conversion::with_budgets(100, 16);
    assert_eq!(
        shared.project_literal(&string).unwrap(),
        Literal::Str("x".to_owned())
    );
    assert!(matches!(
        shared.project_literal(&literal),
        Err(ConvertError::ByteBudgetExhausted {
            family: "literal",
            visited: 17,
            budget: 16
        })
    ));
    let handle = Conversion::with_budgets(100, 16)
        .project_expr(&mut heap, &expression)
        .unwrap();
    assert_eq!(
        heap.get(handle).unwrap(),
        &Expr::lit(Literal::Nat(NatLit::from_limbs_le(vec![7, 1])))
    );
}

#[test]
fn injection_preserves_foreign_stale_and_closed_native_handle_causes() {
    let mut heap = NativeHeap::new();
    let handle = heap.alloc(Expr::bvar(0).unwrap());
    let other = NativeHeap::new();
    let foreign = inject_expr(&other, handle)
        .err()
        .expect("a foreign handle must refuse");
    assert_eq!(
        std::error::Error::source(&foreign).and_then(|source| source.downcast_ref::<HeapError>()),
        Some(&HeapError::WrongHeap)
    );
    assert_eq!(heap.live(), 1);
    heap.free(handle).unwrap();
    let stale = inject_expr(&heap, handle)
        .err()
        .expect("a stale handle must refuse");
    assert_eq!(
        std::error::Error::source(&stale).and_then(|source| source.downcast_ref::<HeapError>()),
        Some(&HeapError::StaleHandle)
    );
    let current = heap.alloc(Expr::bvar(1).unwrap());
    heap.close();
    let closed = inject_expr(&heap, current)
        .err()
        .expect("a closed heap must refuse");
    assert_eq!(
        std::error::Error::source(&closed).and_then(|source| source.downcast_ref::<HeapError>()),
        Some(&HeapError::Closed)
    );
    assert_eq!(heap.live(), 0);
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

#[test]
fn colliding_expression_hashes_preserve_full_identity_across_the_membrane() {
    let mut original = NativeHeap::new();
    let mut projected = NativeHeap::new();
    let name = |label| Name::from_components([label]);
    let lambda = |label, info| {
        Expr::lam(
            name(label),
            Expr::sort(Level::one()),
            Expr::bvar(0).unwrap(),
            info,
        )
    };
    let families = [
        vec![
            lambda("x", BinderInfo::Default),
            lambda("y", BinderInfo::Default),
            lambda("x", BinderInfo::Implicit),
            Expr::forall_e(
                name("x"),
                Expr::sort(Level::one()),
                Expr::bvar(0).unwrap(),
                BinderInfo::Default,
            ),
        ],
        vec![
            Expr::lit(Literal::Nat(NatLit::from_limbs_le(vec![7, 1]))),
            Expr::lit(Literal::Nat(NatLit::from_limbs_le(vec![7, 2]))),
        ],
        vec![
            Expr::let_e(
                name("x"),
                Expr::sort(Level::one()),
                Expr::sort(Level::zero()),
                Expr::bvar(0).unwrap(),
                false,
            ),
            Expr::let_e(
                name("y"),
                Expr::sort(Level::one()),
                Expr::sort(Level::zero()),
                Expr::bvar(0).unwrap(),
                false,
            ),
            Expr::let_e(
                name("x"),
                Expr::sort(Level::one()),
                Expr::sort(Level::zero()),
                Expr::bvar(0).unwrap(),
                true,
            ),
        ],
        vec![
            Expr::mdata(
                KVMap::from_entries(vec![(name("k"), DataValue::OfNat(1))]),
                lambda("x", BinderInfo::Default),
            ),
            Expr::mdata(
                KVMap::from_entries(vec![(name("k"), DataValue::OfNat(2))]),
                lambda("x", BinderInfo::Default),
            ),
        ],
    ];
    for family in families {
        let mut handles = Vec::new();
        for expr in &family {
            assert_eq!(
                expr.hash(),
                family[0].hash(),
                "real, not mocked, hash collision"
            );
            let handle = original.alloc(expr.clone());
            let object = inject_expr(&original, handle).unwrap();
            let native = Conversion::new()
                .project_expr(&mut projected, &object)
                .unwrap();
            assert_eq!(projected.get(native).unwrap(), expr);
            assert!(
                !handles.contains(&native),
                "distinct colliding expressions fused"
            );
            handles.push(native);
        }
        // Revisit every value after all collisions, in reverse order and with
        // newly allocated foreign graphs. Identity must not depend on the last
        // colliding value that happened to cross the membrane.
        let live = projected.live();
        for (expr, expected) in family.iter().zip(&handles).rev() {
            let handle = original.alloc(expr.clone());
            let object = inject_expr(&original, handle).unwrap();
            let actual = Conversion::new()
                .project_expr(&mut projected, &object)
                .unwrap();
            assert_eq!(actual, *expected);
        }
        assert_eq!(projected.live(), live);
    }
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

fn with_extra_constructor_field(object: &Obj) -> Obj {
    let header = object.header();
    let mut fields: Vec<_> = (0..usize::from(header.other))
        .map(|index| object.ctor_child(index))
        .collect();
    fields.push(Obj::mk_nat(0));
    let mut scalars = Vec::new();
    for offset in (usize::from(header.other) * 8..usize::from(header.cs_sz) - 8).step_by(8) {
        scalars.extend_from_slice(&object.ctor_scalar_u64(offset).to_le_bytes());
    }
    Obj::mk_ctor(header.tag, fields, &scalars)
}

fn assert_surplus_fields_refused(input: &Obj, family: &str) {
    let mut heap = NativeHeap::new();
    let result = Conversion::new().project_expr(&mut heap, input);
    assert!(
        matches!(result, Err(ConvertError::MalformedCompat { family: actual, .. }) if actual == family),
        "surplus {family} fields must be refused, got {result:?}"
    );
    assert_eq!(
        heap.live(),
        0,
        "a malformed graph must publish no native term"
    );
}

#[test]
fn expression_constructors_with_extra_fields_are_malformed() {
    let zero = Expr::bvar(0).unwrap();
    let sort = Expr::sort(Level::zero());
    for expression in [
        zero.clone(),
        Expr::fvar(fln_core::expr::FVarId(Name::from_components(["x"]))),
        Expr::mvar(MVarId(Name::from_components(["m"]))),
        sort.clone(),
        Expr::const_(Name::from_components(["f"]), Vec::new()),
        Expr::app(zero.clone(), zero.clone()),
        Expr::lam(
            Name::anonymous(),
            sort.clone(),
            zero.clone(),
            BinderInfo::Default,
        ),
        Expr::forall_e(
            Name::anonymous(),
            sort.clone(),
            zero.clone(),
            BinderInfo::Default,
        ),
        Expr::let_e(Name::anonymous(), sort, zero.clone(), zero.clone(), false),
        Expr::lit(Literal::Nat(NatLit::from_u64(7))),
        Expr::mdata(KVMap::new(), zero.clone()),
        Expr::proj(Name::from_components(["S"]), 0, zero),
    ] {
        let mut heap = NativeHeap::new();
        let handle = heap.alloc(expression.clone());
        let object = inject_expr(&heap, handle).unwrap();
        let projected = Conversion::new().project_expr(&mut heap, &object).unwrap();
        assert_eq!(heap.get(projected).unwrap(), &expression);
        assert_surplus_fields_refused(&with_extra_constructor_field(&object), "expr");
    }
}

#[test]
fn name_constructors_with_extra_fields_are_malformed() {
    for object in [
        Obj::mk_ctor(0, Vec::new(), &[]),
        fln_rt::convert::inject_name(&Name::from_components(["x"])),
        fln_rt::convert::inject_name(&Name::num(Name::anonymous(), 7)),
    ] {
        Conversion::new().project_name(&object).unwrap();
        let malformed = with_extra_constructor_field(&object);
        let input = Obj::mk_ctor(4, vec![malformed, Obj::mk_nat(0)], &[]);
        assert_surplus_fields_refused(&input, "name");
    }
}

#[test]
fn level_constructors_with_extra_fields_are_malformed() {
    let parameter = Level::param(Name::from_components(["u"]));
    for level in [
        Level::zero(),
        Level::zero().succ().unwrap(),
        Level::max(parameter.clone(), Level::one()).unwrap(),
        Level::imax(parameter, Level::one()).unwrap(),
        Level::param(Name::from_components(["v"])),
        Level::mvar(LMVarId(Name::from_components(["m"]))),
    ] {
        let expression = Expr::sort(level.clone());
        let mut heap = NativeHeap::new();
        let handle = heap.alloc(expression.clone());
        let object = inject_expr(&heap, handle).unwrap();
        let projected = Conversion::new().project_expr(&mut heap, &object).unwrap();
        assert_eq!(heap.get(projected).unwrap(), &expression);
        let encoded = if level.is_zero() {
            Obj::mk_ctor(0, Vec::new(), &[])
        } else {
            object.ctor_child(0)
        };
        let input = Obj::mk_ctor(3, vec![with_extra_constructor_field(&encoded)], &[]);
        assert_surplus_fields_refused(&input, "level");
    }
}

#[test]
fn literal_constructors_with_extra_fields_are_malformed() {
    for literal in [Literal::Nat(NatLit::from_u64(7)), Literal::Str("λ".into())] {
        let mut heap = NativeHeap::new();
        let expression = Expr::lit(literal);
        let handle = heap.alloc(expression.clone());
        let object = inject_expr(&heap, handle).unwrap();
        let projected = Conversion::new().project_expr(&mut heap, &object).unwrap();
        assert_eq!(heap.get(projected).unwrap(), &expression);
        let literal = with_extra_constructor_field(&object.ctor_child(0));
        assert!(matches!(
            Conversion::new().project_literal(&literal),
            Err(ConvertError::MalformedCompat {
                family: "literal",
                ..
            })
        ));
        assert_surplus_fields_refused(
            &Obj::mk_ctor(object.header().tag, vec![literal], &[]),
            "literal",
        );
    }
}

#[test]
fn data_value_constructors_with_extra_fields_are_malformed() {
    let key = Name::from_components(["key"]);
    for value in [
        DataValue::OfString("λ".into()),
        DataValue::OfBool(true),
        DataValue::OfName(Name::from_components(["value"])),
        DataValue::OfNat(7),
        DataValue::OfInt(-3),
        DataValue::OfSyntax(SyntaxHandle(9)),
    ] {
        let expression = Expr::mdata(
            KVMap::from_entries(vec![(key.clone(), value)]),
            Expr::bvar(0).unwrap(),
        );
        let mut heap = NativeHeap::new();
        let handle = heap.alloc(expression.clone());
        let object = inject_expr(&heap, handle).unwrap();
        let projected = Conversion::new().project_expr(&mut heap, &object).unwrap();
        assert_eq!(heap.get(projected).unwrap(), &expression);
        let entries = object.ctor_child(0);
        let pair = entries.ctor_child(0);
        let value = with_extra_constructor_field(&pair.ctor_child(1));
        let pair = Obj::mk_ctor(0, vec![pair.ctor_child(0), value], &[]);
        let entries = Obj::mk_ctor(1, vec![pair, entries.ctor_child(1)], &[]);
        let input = Obj::mk_ctor(
            object.header().tag,
            vec![entries, object.ctor_child(1)],
            &[],
        );
        assert_surplus_fields_refused(&input, "data-value");
    }
}

#[test]
fn list_constructors_with_extra_fields_are_malformed() {
    let pair = Obj::mk_ctor(
        0,
        vec![
            mk_name(&["key"]),
            Obj::mk_ctor(3, vec![Obj::mk_nat(7)], &[]),
        ],
        &[],
    );
    for (family, head) in [("level-list", Obj::mk_nat(0)), ("kvmap", pair)] {
        for list in [
            Obj::mk_ctor(0, Vec::new(), &[]),
            Obj::mk_ctor(1, vec![head.clone_ref(), Obj::mk_nat(0)], &[]),
        ] {
            let wrap = |list| {
                if family == "level-list" {
                    Obj::mk_ctor(4, vec![mk_name(&["f"]), list], &[])
                } else {
                    Obj::mk_ctor(
                        10,
                        vec![list, Obj::mk_ctor(0, vec![Obj::mk_nat(0)], &[])],
                        &[],
                    )
                }
            };
            Conversion::new()
                .project_expr(&mut NativeHeap::new(), &wrap(list.clone_ref()))
                .unwrap();
            assert_surplus_fields_refused(&wrap(with_extra_constructor_field(&list)), family);
        }
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
fn project_walks_a_hand_built_long_app_nest() {
    let mk_bvar = || Obj::mk_ctor(0, vec![Obj::mk_nat(0)], &[]);
    let mut nest = mk_bvar();
    for _ in 0..400 {
        nest = Obj::mk_ctor(5, vec![nest, mk_bvar()], &[]);
    }
    let mut heap = NativeHeap::new();
    Conversion::new()
        .project_expr(&mut heap, &nest)
        .expect("a 400-deep app nest is a legal Expr");
}

#[test]
fn project_reuses_a_shared_expr_child() {
    let bvar = Obj::mk_ctor(0, vec![Obj::mk_nat(0)], &[]);
    let diamond = Obj::mk_ctor(5, vec![bvar.clone_ref(), bvar], &[]);
    let mut heap = NativeHeap::new();
    let back = Conversion::new()
        .project_expr(&mut heap, &diamond)
        .expect("an app of a shared bvar must not look like a cycle");
    let ExprNode::App { f, a } = heap.get(back).expect("handle").node() else {
        panic!("expected an app");
    };
    assert_eq!(f.hash(), a.hash());
}

#[test]
fn project_does_not_mistake_a_queued_sibling_for_an_expr_ancestor() {
    for nested_on_right in [false, true] {
        let shared = Expr::bvar(0).unwrap();
        let nested = Expr::app(shared.clone(), Expr::bvar(1).unwrap());
        let expected = if nested_on_right {
            Expr::app(shared, nested)
        } else {
            Expr::app(nested, shared)
        };
        let mut heap = NativeHeap::new();
        let original = heap.alloc(expected.clone());
        let input = inject_expr(&heap, original).unwrap();
        let (shared, nested) = if nested_on_right {
            (input.ctor_child(0), input.ctor_child(1))
        } else {
            (input.ctor_child(1), input.ctor_child(0))
        };
        assert_eq!(
            shared.identity_token(),
            nested.ctor_child(0).identity_token()
        );
        let restored = Conversion::new()
            .project_expr(&mut heap, &input)
            .expect("a shared sibling reached through a descendant is not a cycle");
        assert_eq!(heap.get(restored).unwrap(), &expected);
    }
}

#[test]
fn project_does_not_mistake_a_queued_sibling_for_a_level_ancestor() {
    for imax in [false, true] {
        for nested_on_right in [false, true] {
            let shared = Level::zero().succ().unwrap();
            let nested = shared.clone().succ().unwrap();
            let (left, right) = if nested_on_right {
                (shared, nested)
            } else {
                (nested, shared)
            };
            let level = if imax {
                Level::imax(left, right).unwrap()
            } else {
                Level::max(left, right).unwrap()
            };
            let expected = Expr::sort(level);
            let mut heap = NativeHeap::new();
            let original = heap.alloc(expected.clone());
            let input = inject_expr(&heap, original).unwrap();
            let level = input.ctor_child(0);
            let (shared, nested) = if nested_on_right {
                (level.ctor_child(0), level.ctor_child(1))
            } else {
                (level.ctor_child(1), level.ctor_child(0))
            };
            assert_eq!(
                shared.identity_token(),
                nested.ctor_child(0).identity_token()
            );
            let restored = Conversion::new()
                .project_expr(&mut heap, &input)
                .expect("a shared sibling reached through a successor is not a cycle");
            assert_eq!(heap.get(restored).unwrap(), &expected);
        }
    }
}

#[test]
fn inject_walks_a_long_app_nest_without_a_stack_fault() {
    let mut expr = Expr::bvar(0).expect("packs");
    for _ in 0..400 {
        expr = Expr::app(expr, Expr::bvar(0).expect("packs"));
    }
    let mut heap = NativeHeap::new();
    let handle = heap.alloc(expr.clone());
    let injected = inject_expr(&heap, handle).expect("inject_expr is iterative on app");
    let back = Conversion::new()
        .project_expr(&mut heap, &injected)
        .expect("project_expr is iterative on app");
    assert_eq!(heap.get(back).expect("handle").hash(), expr.hash());
}

// ---------------------------------------------------------------------------
// The declarations and the membrane tripwire
// ---------------------------------------------------------------------------

#[test]
fn checked_expression_rebuild_preserves_identity_fields_and_recomputes_data() {
    let name = Name::num(Name::from_components(["binder"]), 19);
    let leaf = Expr::bvar(0).unwrap();
    let other = Expr::bvar(3).unwrap();
    let replacement = Expr::bvar(8).unwrap();
    let metadata = KVMap::from_entries(vec![
        (name.clone(), DataValue::OfString("first".into())),
        (name.clone(), DataValue::OfNat(7)),
    ]);
    let cases = vec![
        (
            Expr::app(leaf.clone(), other.clone()),
            Expr::app(replacement.clone(), other.clone()),
            vec![0, 1],
        ),
        (
            Expr::lam(
                name.clone(),
                leaf.clone(),
                other.clone(),
                BinderInfo::InstImplicit,
            ),
            Expr::lam(
                name.clone(),
                replacement.clone(),
                other.clone(),
                BinderInfo::InstImplicit,
            ),
            vec![1, 2],
        ),
        (
            Expr::forall_e(
                name.clone(),
                leaf.clone(),
                other.clone(),
                BinderInfo::StrictImplicit,
            ),
            Expr::forall_e(
                name.clone(),
                replacement.clone(),
                other.clone(),
                BinderInfo::StrictImplicit,
            ),
            vec![1, 2],
        ),
        (
            Expr::let_e(
                name.clone(),
                leaf.clone(),
                other.clone(),
                leaf.clone(),
                true,
            ),
            Expr::let_e(
                name.clone(),
                replacement.clone(),
                other.clone(),
                leaf.clone(),
                true,
            ),
            vec![1, 2, 3],
        ),
        (
            Expr::mdata(metadata.clone(), leaf.clone()),
            Expr::mdata(metadata, replacement.clone()),
            vec![1],
        ),
        (
            Expr::proj(name, 987, leaf),
            Expr::proj(
                Name::num(Name::from_components(["binder"]), 19),
                987,
                replacement.clone(),
            ),
            vec![2],
        ),
    ];
    let mut heap = NativeHeap::new();
    let replacement_handle = heap.alloc(replacement);
    let replacement_object = inject_expr(&heap, replacement_handle).unwrap();
    for (original, expected, slots) in cases {
        let handle = heap.alloc(original);
        let original_object = inject_expr(&heap, handle).unwrap();
        let mut scope = Conversion::new();
        let checked = scope.check_expr(&original_object).unwrap();
        let mut children = checked.children().unwrap();
        assert_eq!(children.len(), slots.len());
        for (child, &slot) in children.iter().zip(&slots) {
            assert_eq!(
                child.object().identity_token(),
                original_object
                    .try_ctor_child(slot)
                    .unwrap()
                    .identity_token()
            );
        }
        let unchanged = scope.rebuild_expr(&checked, &children).unwrap();
        assert_eq!(
            unchanged.object().identity_token(),
            original_object.identity_token()
        );
        children[0] = scope.check_expr(&replacement_object).unwrap();
        let changed = scope.rebuild_expr(&checked, &children).unwrap();
        assert_ne!(
            changed.object().identity_token(),
            original_object.identity_token()
        );
        assert_eq!(changed.expression(), &expected);
        assert_eq!(
            changed
                .object()
                .try_ctor_child(slots[0])
                .unwrap()
                .identity_token(),
            replacement_object.identity_token()
        );
        for slot in 0..usize::from(original_object.header().other) {
            if slot != slots[0] {
                assert_eq!(
                    changed
                        .object()
                        .try_ctor_child(slot)
                        .unwrap()
                        .identity_token(),
                    original_object
                        .try_ctor_child(slot)
                        .unwrap()
                        .identity_token(),
                    "all untouched fields retain the original carrier"
                );
            }
        }
        let mut verification = NativeHeap::new();
        let projected = Conversion::new()
            .project_expr(&mut verification, changed.object())
            .unwrap();
        assert_eq!(verification.get(projected).unwrap(), &expected);
        assert!(matches!(
            scope.rebuild_expr(&checked, &[]),
            Err(ConvertError::MalformedCompat { family: "expr", .. })
        ));
    }
}

#[test]
fn checked_expression_rebuild_and_callback_projections_share_aggregate_limits() {
    let leaf = Obj::mk_ctor(0, vec![Obj::mk_nat(0)], &[]);
    let original = Obj::mk_ctor(5, vec![leaf.clone_ref(), leaf.clone_ref()], &[]);
    let replacement = Obj::mk_ctor(0, vec![Obj::mk_nat(1)], &[]);
    let mut scope = Conversion::with_node_budget(3);
    let checked = scope.check_expr(&original).unwrap();
    let replacement = scope.check_expr(&replacement).unwrap();
    assert!(matches!(
        scope.rebuild_expr(&checked, &[replacement.clone(), replacement]),
        Err(ConvertError::NodeBudgetExhausted {
            visited: 4,
            budget: 3,
            ..
        })
    ));
    let original_children = checked.children().unwrap();
    assert_eq!(
        scope
            .rebuild_expr(&checked, &original_children)
            .unwrap()
            .object()
            .identity_token(),
        original.identity_token(),
        "a no-op does not allocate or consume another reconstruction node"
    );

    let mut heap = NativeHeap::new();
    let expr = Expr::mdata(
        KVMap::from_entries(vec![(
            Name::anonymous(),
            DataValue::OfString("data".into()),
        )]),
        Expr::bvar(0).unwrap(),
    );
    let handle = heap.alloc(expr);
    let object = inject_expr(&heap, handle).unwrap();
    let mut scope = Conversion::with_budgets(100, 7);
    let checked = scope.check_expr(&object).unwrap();
    let replacement = scope
        .check_expr(&Obj::mk_ctor(0, vec![Obj::mk_nat(1)], &[]))
        .unwrap();
    assert!(matches!(
        scope.rebuild_expr(&checked, &[replacement]),
        Err(ConvertError::ByteBudgetExhausted {
            visited: 8,
            budget: 7,
            ..
        })
    ));
    let forged = Obj::mk_ctor(0, vec![Obj::mk_nat(0)], &u64::MAX.to_le_bytes());
    assert!(matches!(
        Conversion::new().check_expr(&forged),
        Err(ConvertError::MalformedCompat { family: "expr", .. })
    ));
}

#[test]
fn checked_constructor_computes_only_fresh_root_data_and_checks_every_descendant() {
    let leaf = Obj::mk_ctor(0, vec![Obj::mk_nat(0)], &[]);
    let forged = Obj::mk_ctor(0, vec![Obj::mk_nat(0)], &u64::MAX.to_le_bytes());
    for constructor in [
        ExprConstructor::Lam(BinderInfo::Implicit),
        ExprConstructor::Forall(BinderInfo::StrictImplicit),
    ] {
        assert!(matches!(
            Conversion::new().construct_expr(
                constructor,
                vec![Obj::mk_nat(0), forged.clone_ref(), leaf.clone_ref()]
            ),
            Err(ConvertError::MalformedCompat { family: "expr", .. })
        ));
    }
    assert!(matches!(
        Conversion::new().construct_expr(
            ExprConstructor::Let(true),
            vec![Obj::mk_nat(0), leaf.clone_ref(), leaf.clone_ref(), forged]
        ),
        Err(ConvertError::MalformedCompat { family: "expr", .. })
    ));
    let mut scope = Conversion::with_node_budget(3);
    let constructed = scope
        .construct_expr(
            ExprConstructor::App,
            vec![leaf.clone_ref(), leaf.clone_ref()],
        )
        .unwrap();
    for slot in 0..2 {
        assert_eq!(
            constructed
                .object()
                .try_ctor_child(slot)
                .unwrap()
                .identity_token(),
            leaf.identity_token()
        );
    }
    assert!(matches!(
        scope.construct_expr(ExprConstructor::BVar, vec![Obj::mk_nat(0)]),
        Err(ConvertError::NodeBudgetExhausted {
            visited: 4,
            budget: 3,
            ..
        })
    ));
    assert!(matches!(
        Conversion::new().construct_expr(ExprConstructor::App, vec![leaf]),
        Err(ConvertError::MalformedCompat { family: "expr", .. })
    ));
}

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
