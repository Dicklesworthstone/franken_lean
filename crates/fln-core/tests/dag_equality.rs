//! Regressions for the term-store prerequisite in franken_lean-z8j.1.13.
//! These exercise the actual core equality implementations, not a model or timer.
use fln_core::expr::{BinderInfo, Expr, Literal, NatLit};
use fln_core::level::Level;
use fln_core::name::Name;
use fln_core::options::{DataValue, KVMap};

fn name(s: &str) -> Name {
    Name::str(Name::anonymous(), s)
}
fn diamond(mut leaf: Expr, depth: usize) -> Expr {
    for _ in 0..depth {
        leaf = Expr::app(leaf.clone(), leaf);
    }
    leaf
}
fn level_diamond(depth: usize, imax: bool) -> Level {
    let mut level = Level::param(name("u"));
    for _ in 0..depth {
        level = if imax {
            Level::imax(level.clone(), level)
        } else {
            Level::max(level.clone(), level)
        }
        .expect("test depth fits");
    }
    level
}
fn lam(n: &str, info: BinderInfo) -> Expr {
    Expr::lam(
        name(n),
        Expr::sort(Level::one()),
        Expr::bvar(0).unwrap(),
        info,
    )
}
#[test]
fn independently_allocated_expression_diamonds_compare_without_tree_expansion() {
    let left = diamond(Expr::const_(name("f"), vec![]), 96);
    let right = diamond(Expr::const_(name("f"), vec![]), 96);
    assert_ne!(left.allocation_identity(), right.allocation_identity());
    // Only 97 nodes per input; the old tree walk visited 2^97 - 1 pairs.
    assert!(left == right);
    assert!(right == left);
    assert!(left == left.clone());
}
#[test]
fn independently_allocated_max_and_imax_diamonds_compare_without_tree_expansion() {
    for imax in [false, true] {
        let left = level_diamond(96, imax);
        let right = level_diamond(96, imax);
        assert!(left == right);
        assert!(right == left);
        assert!(left == left.clone());
    }
}
#[test]
fn expression_payload_level_equality_is_also_dag_safe() {
    let left = Expr::const_(name("c"), vec![level_diamond(96, false)]);
    let right = Expr::const_(name("c"), vec![level_diamond(96, false)]);
    assert!(left == right);
    assert!(Expr::sort(level_diamond(96, true)) == Expr::sort(level_diamond(96, true)));
}
#[test]
fn visited_keys_include_both_allocations_not_just_the_left_node() {
    let shared = lam("x", BinderInfo::Default);
    let equal = lam("x", BinderInfo::Default);
    let different = lam("y", BinderInfo::Default);
    assert_eq!(
        shared.data(),
        different.data(),
        "names are not in Expr.Data"
    );
    let left = Expr::app(shared.clone(), shared);
    let right = Expr::app(equal, different);
    assert_eq!(left.data(), right.data());
    assert!(
        left != right,
        "the second partner must be checked independently"
    );
    assert!(right != left);
}
#[test]
fn hash_collisions_never_erase_binder_names_information_or_constructor_tags() {
    let plain = lam("x", BinderInfo::Default);
    let renamed = lam("y", BinderInfo::Default);
    let implicit = lam("x", BinderInfo::Implicit);
    let forall = Expr::forall_e(
        name("x"),
        Expr::sort(Level::one()),
        Expr::bvar(0).unwrap(),
        BinderInfo::Default,
    );
    for other in [renamed, implicit, forall] {
        assert_eq!(plain.data(), other.data());
        assert!(plain != other);
    }
}
#[test]
fn hash_collisions_never_erase_literal_high_limbs_or_let_annotations() {
    let a = Expr::lit(Literal::Nat(NatLit::from_limbs_le(vec![7, 1])));
    let b = Expr::lit(Literal::Nat(NatLit::from_limbs_le(vec![7, 2])));
    assert_eq!(a.data(), b.data());
    assert!(a != b);
    let make = |n: &str, non_dep: bool| {
        Expr::let_e(
            name(n),
            Expr::sort(Level::one()),
            Expr::sort(Level::zero()),
            Expr::bvar(0).unwrap(),
            non_dep,
        )
    };
    let original = make("x", false);
    for other in [make("y", false), make("x", true)] {
        assert_eq!(original.data(), other.data());
        assert!(original != other);
    }
}
#[test]
fn metadata_order_duplicates_and_shadowed_values_remain_observable() {
    let k = name("k");
    let wrap = |entries| Expr::mdata(KVMap::from_entries(entries), lam("x", BinderInfo::Default));
    let a = wrap(vec![
        (k.clone(), DataValue::OfNat(1)),
        (k.clone(), DataValue::OfNat(2)),
    ]);
    let b = wrap(vec![
        (k.clone(), DataValue::OfNat(1)),
        (k.clone(), DataValue::OfNat(3)),
    ]);
    let c = wrap(vec![(k.clone(), DataValue::OfNat(1))]);
    let d = wrap(vec![
        (k.clone(), DataValue::OfNat(2)),
        (k, DataValue::OfNat(1)),
    ]);
    for other in [b, c, d] {
        assert_eq!(a.data(), other.data());
        assert!(a != other);
    }
}
#[test]
fn unequal_diamond_does_not_poison_a_later_equal_comparison() {
    let a = diamond(lam("x", BinderInfo::Default), 96);
    let bad = diamond(lam("y", BinderInfo::Default), 96);
    let good = diamond(lam("x", BinderInfo::Default), 96);
    assert_eq!(a.data(), bad.data());
    assert!(a != bad);
    assert!(a == good);
}
#[test]
fn equality_does_not_depend_on_sharing_topology() {
    fn tree(depth: usize) -> Expr {
        if depth == 0 {
            lam("x", BinderInfo::Default)
        } else {
            Expr::app(tree(depth - 1), tree(depth - 1))
        }
    }
    for depth in 0..9 {
        let shared = diamond(lam("x", BinderInfo::Default), depth);
        let unshared = tree(depth);
        assert!(shared == unshared);
        assert!(unshared == shared);
    }
}
#[test]
fn equality_remains_thread_independent() {
    for workers in [1, 8, 32] {
        std::thread::scope(|scope| {
            let jobs: Vec<_> = (0..workers)
                .map(|_| {
                    scope.spawn(|| {
                        diamond(lam("x", BinderInfo::Default), 96)
                            == diamond(lam("x", BinderInfo::Default), 96)
                            && level_diamond(96, true) == level_diamond(96, true)
                    })
                })
                .collect();
            for job in jobs {
                assert!(job.join().expect("comparison worker"));
            }
        });
    }
}
