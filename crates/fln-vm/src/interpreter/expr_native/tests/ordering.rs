use super::*;
use fln_core::level::LMVarId;
use fln_core::options::{DataValue, KVMap, SyntaxHandle};

const ROWS: [&str; 2] = ["extern:Lean.Expr.lt", "extern:Lean.Expr.quickLt"];

fn ordered(row: &str, left: &Expr, right: &Expr) -> bool {
    let result = call(row, &[object(left.clone()), object(right.clone())]);
    assert!(result.is_scalar() && result.unbox() <= 1);
    result.unbox() == 1
}

fn budget(allowed: usize) -> WorkBudget {
    WorkBudget {
        allowed,
        visited: 0,
    }
}

#[test]
fn native_expr_order_uses_constructor_before_hash_for_every_kind() {
    let name = Name::from_components(["kind"]);
    let terms = [
        bvar(0),
        Expr::fvar(FVarId(name.clone())),
        Expr::mvar(MVarId(name.clone())),
        Expr::sort(Level::zero()),
        Expr::const_(name.clone(), vec![]),
        Expr::app(bvar(0), bvar(1)),
        Expr::lam(name.clone(), bvar(0), bvar(0), BinderInfo::Default),
        Expr::forall_e(name.clone(), bvar(0), bvar(0), BinderInfo::Default),
        Expr::let_e(name.clone(), bvar(0), bvar(0), bvar(0), false),
        literal(0),
        Expr::mdata(KVMap::new(), bvar(0)),
        Expr::proj(name, 0, bvar(0)),
    ];
    let mut reverses_hash = false;
    for (i, left) in terms.iter().enumerate() {
        for (j, right) in terms.iter().enumerate() {
            reverses_hash |= i < j && left.hash() > right.hash();
            for row in ROWS {
                assert_eq!(ordered(row, left, right), i < j, "{row}: {i} versus {j}");
            }
        }
    }
    assert!(
        reverses_hash,
        "the corpus must separate kind order from hash order"
    );
}

#[test]
fn native_expr_order_preserves_structural_field_precedence() {
    let a = Name::from_components(["a"]);
    let z = Name::from_components(["z"]);
    let pairs = [
        (bvar(0), bvar(1)),
        (Expr::fvar(FVarId(a.clone())), Expr::fvar(FVarId(z.clone()))),
        (Expr::mvar(MVarId(a.clone())), Expr::mvar(MVarId(z.clone()))),
        (
            Expr::const_(a.clone(), vec![Level::one()]),
            Expr::const_(z.clone(), vec![]),
        ),
        (
            Expr::app(bvar(0), literal(99)),
            Expr::app(bvar(1), literal(0)),
        ),
        (
            Expr::app(bvar(0), literal(0)),
            Expr::app(bvar(0), literal(1)),
        ),
        (
            Expr::lam(z.clone(), bvar(0), bvar(9), BinderInfo::Default),
            Expr::lam(a.clone(), bvar(1), bvar(0), BinderInfo::InstImplicit),
        ),
        (
            Expr::forall_e(z.clone(), bvar(0), bvar(0), BinderInfo::Default),
            Expr::forall_e(a.clone(), bvar(0), bvar(1), BinderInfo::InstImplicit),
        ),
        (
            Expr::let_e(z.clone(), bvar(9), literal(9), bvar(9), false),
            Expr::let_e(a.clone(), bvar(0), literal(0), bvar(0), true),
        ),
        (
            Expr::let_e(z.clone(), bvar(0), literal(0), bvar(9), false),
            Expr::let_e(a.clone(), bvar(0), literal(1), bvar(0), false),
        ),
        (
            Expr::let_e(z.clone(), bvar(0), literal(0), bvar(0), false),
            Expr::let_e(a.clone(), bvar(0), literal(0), bvar(1), false),
        ),
        (literal(u64::MAX - 1), literal(u64::MAX)),
        (literal(u64::MAX), Expr::lit(Literal::Str(String::new()))),
        (
            Expr::lit(Literal::Str("a\0λ".into())),
            Expr::lit(Literal::Str("a\0🙂".into())),
        ),
        (
            Expr::mdata(
                KVMap::from_entries(vec![(z.clone(), DataValue::OfNat(9))]),
                bvar(0),
            ),
            Expr::mdata(
                KVMap::from_entries(vec![(a.clone(), DataValue::OfNat(0))]),
                bvar(1),
            ),
        ),
        (
            Expr::proj(z.clone(), u64::MAX, bvar(0)),
            Expr::proj(a.clone(), 0, bvar(1)),
        ),
        (
            Expr::proj(a.clone(), u64::MAX, bvar(0)),
            Expr::proj(z.clone(), 0, bvar(0)),
        ),
        (
            Expr::proj(a.clone(), 1 << 40, bvar(0)),
            Expr::proj(a, (1 << 40) + 1, bvar(0)),
        ),
    ];
    for (left, right) in pairs {
        assert!(ordered(ROWS[0], &left, &right), "{left:?} < {right:?}");
        assert!(!ordered(ROWS[0], &right, &left));
        assert!(!ordered(ROWS[0], &left, &left));
    }
}

#[test]
fn native_expr_order_uses_alpha_equality_to_select_later_fields() {
    let left = Expr::lam(
        Name::from_components(["x"]),
        Expr::sort(Level::zero()),
        bvar(0),
        BinderInfo::Default,
    );
    let right = Expr::lam(
        Name::from_components(["y"]),
        Expr::sort(Level::zero()),
        bvar(0),
        BinderInfo::InstImplicit,
    );
    assert_ne!(left, right);
    assert!(left.is_alpha_equiv(&right));
    for row in ROWS {
        assert!(!ordered(row, &left, &right));
        assert!(!ordered(row, &right, &left));
    }
    // Strict Expr.equal would select the functions and miss the unequal args.
    assert!(ordered(
        ROWS[0],
        &Expr::app(left.clone(), literal(0)),
        &Expr::app(right.clone(), literal(1)),
    ));
    assert!(ordered(
        ROWS[0],
        &Expr::forall_e(Name::anonymous(), left, bvar(0), BinderInfo::Default),
        &Expr::forall_e(Name::anonymous(), right, bvar(1), BinderInfo::Default),
    ));
}

#[test]
fn native_expr_order_uses_cpp_prefix_first_name_order() {
    let left = Name::str(Name::from_components(["a"]), "tail");
    let right = Name::num(Name::from_components(["b"]), 0);
    assert!(left > right, "Lean Name.cmp orders leaf constructors first");
    for (left, right) in [
        (
            Expr::fvar(FVarId(left.clone())),
            Expr::fvar(FVarId(right.clone())),
        ),
        (
            Expr::mvar(MVarId(left.clone())),
            Expr::mvar(MVarId(right.clone())),
        ),
        (
            Expr::const_(left.clone(), vec![]),
            Expr::const_(right.clone(), vec![]),
        ),
        (
            Expr::sort(Level::param(left.clone())),
            Expr::sort(Level::param(right.clone())),
        ),
        (
            Expr::proj(left.clone(), 0, bvar(0)),
            Expr::proj(right.clone(), 0, bvar(0)),
        ),
        (
            Expr::mdata(
                KVMap::from_entries(vec![(left.clone(), DataValue::OfNat(0))]),
                bvar(0),
            ),
            Expr::mdata(
                KVMap::from_entries(vec![(right.clone(), DataValue::OfNat(0))]),
                bvar(0),
            ),
        ),
        (
            Expr::mdata(
                KVMap::from_entries(vec![(Name::anonymous(), DataValue::OfName(left))]),
                bvar(0),
            ),
            Expr::mdata(
                KVMap::from_entries(vec![(Name::anonymous(), DataValue::OfName(right))]),
                bvar(0),
            ),
        ),
    ] {
        assert!(ordered(ROWS[0], &left, &right));
        assert!(!ordered(ROWS[0], &right, &left));
    }
}

#[test]
fn native_expr_order_preserves_universe_depth_kind_and_list_order() {
    let name = Name::from_components(["u"]);
    let zero = Level::zero();
    let one = Level::one();
    let two = one.clone().succ().unwrap();
    for (left, right) in [
        (Level::param(name.clone()), two),
        (one, Level::max(zero.clone(), zero.clone()).unwrap()),
        (
            Level::max(zero.clone(), zero.clone()).unwrap(),
            Level::imax(zero.clone(), zero.clone()).unwrap(),
        ),
        (
            Level::param(name.clone()),
            Level::mvar(LMVarId(name.clone())),
        ),
    ] {
        for use_hash in [false, true] {
            assert!(
                super::super::order::level_less_than(&left, &right, use_hash, &mut budget(100))
                    .unwrap()
            );
            assert!(
                !super::super::order::level_less_than(&right, &left, use_hash, &mut budget(100))
                    .unwrap()
            );
        }
        assert!(ordered(ROWS[0], &Expr::sort(left), &Expr::sort(right)));
    }
    let constant = |levels| Expr::const_(name.clone(), levels);
    assert!(ordered(
        ROWS[0],
        &constant(vec![zero.clone()]),
        &constant(vec![zero.clone(), zero.clone()])
    ));
    assert!(!ordered(
        ROWS[0],
        &constant(vec![Level::one()]),
        &constant(vec![zero])
    ));
}

#[test]
fn native_expr_quick_order_uses_hash_then_structural_collision_fallback() {
    let mut opposite = false;
    for value in 0..32 {
        let left = bvar(value);
        let right = bvar(value + 1);
        assert_ne!(left.hash(), right.hash());
        let hash_order = left.hash() < right.hash();
        opposite |= !hash_order;
        assert!(ordered(ROWS[0], &left, &right));
        assert_eq!(ordered(ROWS[1], &left, &right), hash_order);
    }
    assert!(
        opposite,
        "the corpus must distinguish hash and structural order"
    );
    let key = Name::from_components(["same"]);
    let metadata = |value| {
        Expr::mdata(
            KVMap::from_entries(vec![(key.clone(), DataValue::OfNat(value))]),
            bvar(0),
        )
    };
    let left = metadata(1);
    let right = metadata(2);
    assert_eq!(
        left.hash(),
        right.hash(),
        "MData's hash excludes its metadata"
    );
    assert!(ordered(ROWS[1], &left, &right));
    assert!(!ordered(ROWS[1], &right, &left));
    let mut universe_opposite = false;
    for value in 0..32 {
        let left = Level::param(Name::num(Name::anonymous(), value));
        let right = Level::param(Name::num(Name::anonymous(), value + 1));
        assert_ne!(left.hash(), right.hash());
        let hash_order = left.hash() < right.hash();
        universe_opposite |= !hash_order;
        assert!(
            super::super::order::level_less_than(&left, &right, false, &mut budget(100)).unwrap()
        );
        assert_eq!(
            super::super::order::level_less_than(&left, &right, true, &mut budget(100)).unwrap(),
            hash_order
        );
    }
    assert!(universe_opposite);
}

#[test]
fn native_expr_order_keeps_metadata_entry_order_and_pin_partial_value_order() {
    let a = Name::from_components(["a"]);
    let z = Name::from_components(["z"]);
    let meta = |entries| Expr::mdata(KVMap::from_entries(entries), bvar(0));
    let left = meta(vec![
        (a.clone(), DataValue::OfNat(0)),
        (z.clone(), DataValue::OfNat(9)),
    ]);
    let right = meta(vec![
        (z.clone(), DataValue::OfNat(0)),
        (a.clone(), DataValue::OfNat(0)),
    ]);
    for row in ROWS {
        assert!(ordered(row, &left, &right));
    }
    // Same-tag Int and Syntax compare false in both directions at the pin.
    // Their values still differ structurally, so list ordering must explicitly
    // continue to the next entry (including a duplicated key).
    for (first, second) in [
        (DataValue::OfInt(100), DataValue::OfInt(-100)),
        (
            DataValue::OfSyntax(SyntaxHandle(100)),
            DataValue::OfSyntax(SyntaxHandle(1)),
        ),
    ] {
        let left = meta(vec![(a.clone(), first.clone())]);
        let right = meta(vec![(a.clone(), second.clone())]);
        assert_ne!(left, right);
        for row in ROWS {
            assert!(!ordered(row, &left, &right));
            assert!(!ordered(row, &right, &left));
            let earlier = meta(vec![(a.clone(), DataValue::OfNat(0))]);
            let later = meta(vec![(a.clone(), DataValue::OfNat(1))]);
            assert!(ordered(row, &earlier, &later));
            let applied_left = Expr::app(left.clone(), earlier);
            let applied_right = Expr::app(right.clone(), later);
            assert_eq!(applied_left.hash(), applied_right.hash());
            // App selects its first alpha-unequal child even when that child
            // is incomparable; it must not continue to the ordered args.
            assert!(!ordered(row, &applied_left, &applied_right));
            assert!(!ordered(row, &applied_right, &applied_left));
            let left = meta(vec![
                (a.clone(), first.clone()),
                (a.clone(), DataValue::OfNat(0)),
            ]);
            let right = meta(vec![
                (a.clone(), second.clone()),
                (a.clone(), DataValue::OfNat(1)),
            ]);
            assert!(ordered(row, &left, &right));
            assert!(!ordered(row, &right, &left));
        }
    }
    let values = [
        DataValue::OfString("λ\0🙂".into()),
        DataValue::OfBool(false),
        DataValue::OfName(z),
        DataValue::OfNat(u64::MAX),
        DataValue::OfInt(i64::MIN),
        DataValue::OfSyntax(SyntaxHandle(0)),
    ];
    for pair in values.windows(2) {
        for row in ROWS {
            assert!(ordered(
                row,
                &meta(vec![(a.clone(), pair[0].clone())]),
                &meta(vec![(a.clone(), pair[1].clone())])
            ));
        }
    }
}

#[test]
fn native_expr_order_validates_both_operands_before_fast_paths() {
    for row in ROWS {
        let malformed = Obj::mk_ctor(0, vec![Obj::mk_nat(0)], &[0; 8]);
        let valid = object(literal(0));
        for arguments in [
            vec![malformed.clone_ref(), valid.clone_ref()],
            vec![valid.clone_ref(), malformed.clone_ref()],
            vec![malformed.clone_ref(), malformed],
            vec![valid, Obj::mk_string("not an expression")],
        ] {
            assert!(matches!(
                execute(row, &arguments),
                Outcome::Complete(VmExit::Refused {
                    refusal: VmRefusal::InvalidCtorObject,
                    ..
                })
            ));
        }
        assert!(matches!(
            Intrinsic::for_row(row).unwrap().invoke_bounded(
                row,
                &[object(bvar(0)), object(bvar(1))],
                1
            ),
            Err(IntrinsicFailure::MirrorResource { .. })
        ));
    }
}

#[test]
fn native_expr_order_is_iterative_and_bounds_comparison_work() {
    let mut left = literal(0);
    let mut right = literal(1);
    for _ in 0..2048 {
        left = Expr::app(bvar(0), left);
        right = Expr::app(bvar(0), right);
    }
    assert!(super::super::order::less_than(&left, &right, false, &mut budget(10_000)).unwrap());
    assert!(matches!(
        super::super::order::less_than(&left, &right, false, &mut budget(100)),
        Err(IntrinsicFailure::MirrorResource { .. })
    ));
    assert!(ordered(ROWS[0], &left, &right));
    // Equal, differently allocated shared subgraphs must charge comparison
    // pairs, rather than doing an unbounded equality before the tail step.
    let shared = || {
        let mut value = bvar(0);
        for _ in 0..20 {
            value = Expr::app(value.clone(), value);
        }
        value
    };
    let left = Expr::app(shared(), literal(0));
    let right = Expr::app(shared(), literal(1));
    assert!(matches!(
        super::super::order::less_than(&left, &right, false, &mut budget(10)),
        Err(IntrinsicFailure::MirrorResource { .. })
    ));
    assert!(super::super::order::less_than(&left, &right, false, &mut budget(100)).unwrap());
}
