//! Graph-sized core operations for franken_lean-z8j.1.13.
//! Large shared inputs intentionally have astronomical tree expansions; these
//! exercise the real methods without timing assertions or ignored regressions.
#![forbid(unsafe_code)]

use fln_core::expr::{BinderInfo, Expr, ExprNode};
use fln_core::level::{LMVarId, Level, LevelView};
use fln_core::name::Name;
use fln_core::options::KVMap;
fn name(s: &str) -> Name {
    Name::str(Name::anonymous(), s)
}
fn expr_diamond(mut leaf: Expr, depth: usize) -> Expr {
    for _ in 0..depth {
        leaf = Expr::app(leaf.clone(), leaf);
    }
    leaf
}
fn level_diamond(mut leaf: Level, depth: usize, imax: bool) -> Level {
    for _ in 0..depth {
        leaf = if imax {
            Level::imax(leaf.clone(), leaf)
        } else {
            Level::max(leaf.clone(), leaf)
        }
        .unwrap();
    }
    leaf
}
#[test]
fn absent_bound_variable_query_does_not_expand_a_diamond() {
    let expression = expr_diamond(Expr::bvar(1).unwrap(), 96);
    assert!(!expression.has_loose_bvar(0));
    assert!(expression.has_loose_bvar(1));
    assert!(!expression.has_loose_bvar(2));
    assert!(!expression.has_loose_bvar(u32::MAX));
    let wrapped = Expr::mdata(KVMap::default(), Expr::proj(name("S"), 0, expression));
    assert!(!wrapped.has_loose_bvar(0));
    assert!(wrapped.has_loose_bvar(1));
}
#[test]
fn bound_variable_seen_keys_include_the_effective_binder_index() {
    let shared = Expr::bvar(1).unwrap();
    let closed = Expr::sort(Level::zero());
    // The first visit misses at index 0; the second must test index 1.
    for binder in [
        Expr::lam(
            name("x"),
            closed.clone(),
            shared.clone(),
            BinderInfo::Default,
        ),
        Expr::forall_e(
            name("x"),
            closed.clone(),
            shared.clone(),
            BinderInfo::Default,
        ),
        Expr::let_e(
            name("x"),
            closed.clone(),
            closed.clone(),
            shared.clone(),
            false,
        ),
    ] {
        assert!(Expr::app(shared.clone(), binder).has_loose_bvar(0));
    }
    // Reverse depth order: visit the shared application inside a binder first.
    let shared = Expr::app(Expr::bvar(0).unwrap(), Expr::bvar(2).unwrap());
    let bound = Expr::lam(name("x"), closed, shared.clone(), BinderInfo::Default);
    assert!(Expr::app(bound, shared).has_loose_bvar(0));
}
#[test]
fn universe_predicates_and_occurrence_queries_walk_shared_nodes_once() {
    let u = Level::param(name("u"));
    let graph = level_diamond(u.clone(), 96, false);
    assert!(!graph.is_never_zero());
    assert!(!graph.is_always_zero());
    assert!(u.occurs_in(&graph));
    assert!(!Level::param(name("absent")).occurs_in(&graph));
    assert!(!Level::one().occurs_in(&graph));
    let zeros = level_diamond(Level::zero(), 96, false);
    assert!(zeros.is_always_zero());
    assert!(!zeros.is_never_zero());
    assert!(!u.occurs_in(&zeros));
}
#[test]
fn imax_zero_predicates_ignore_only_the_left_argument_not_occurrence_queries() {
    let one = Level::one();
    let level = Level::imax(one.clone(), level_diamond(Level::zero(), 96, false)).unwrap();
    assert!(level.is_always_zero());
    assert!(!level.is_never_zero());
    assert!(one.occurs_in(&level));
    let level = Level::imax(Level::zero(), one).unwrap();
    assert!(!level.is_always_zero());
    assert!(level.is_never_zero());
}
#[test]
fn universe_normalization_does_not_flatten_an_exponential_max_tree() {
    let u = Level::param(name("u"));
    for imax in [false, true] {
        let graph = level_diamond(u.clone(), 96, imax);
        assert!(graph.normalize() == u);
        assert!(graph.normalize_fixpoint() == u);
    }
    let shifted = level_diamond(u.clone(), 96, false).add_offset(7).unwrap();
    assert!(shifted.normalize() == u.add_offset(7).unwrap());
}
#[test]
fn normalization_preserves_distinct_offsets_and_imax_leaves() {
    let u = Level::param(name("u"));
    let v = Level::param(name("v"));
    let inner = Level::imax(u.clone(), v.clone()).unwrap();
    let leaf = Level::max(inner.clone(), u.clone().add_offset(3).unwrap()).unwrap();
    let shared = level_diamond(leaf.clone(), 96, false);
    assert!(shared.normalize() == leaf.normalize());
    let mixed = Level::max(shared, Level::max(v, inner).unwrap()).unwrap();
    let unshared_small = Level::max(
        leaf,
        Level::max(
            Level::param(name("v")),
            Level::imax(u, Level::param(name("v"))).unwrap(),
        )
        .unwrap(),
    )
    .unwrap();
    assert!(mixed.normalize() == unshared_small.normalize());
}
#[test]
fn decrement_preserves_sharing_and_the_pins_imax_to_max_rule() {
    let u = Level::param(name("u"));
    for imax in [false, true] {
        let graph = level_diamond(u.clone().succ().unwrap(), 96, imax);
        let result = graph.dec().expect("all leaves are successors");
        assert!(result == level_diamond(u.clone(), 96, false));
        // Equality alone does not ensure the output retained the diamond.
        let mut current = &result;
        for _ in 0..96 {
            let LevelView::Max(left, right) = current.view() else {
                panic!("decrement must retain the raw Max structure");
            };
            let (LevelView::Max(ll, _), LevelView::Max(rl, _)) = (left.view(), right.view()) else {
                assert!(left == &u && right == &u);
                break;
            };
            assert!(std::ptr::eq(ll, rl), "a shared child was copied");
            current = left;
        }
    }
    assert!(level_diamond(u, 96, false).dec().is_none());
    assert!(
        Level::max(Level::one(), Level::param(name("v")))
            .unwrap()
            .dec()
            .is_none()
    );
}
#[test]
fn deeply_nested_universe_decrement_and_ordering_are_stack_safe() {
    std::thread::Builder::new()
        .stack_size(128 * 1024)
        .spawn(|| {
            let mut left = Level::param(name("a"));
            let mut right = Level::param(name("b"));
            let common = Level::param(name("common"));
            let mut decrementable = Level::one();
            for _ in 0..12_000 {
                left = Level::imax(common.clone(), left).unwrap();
                right = Level::imax(common.clone(), right).unwrap();
                decrementable = Level::imax(Level::one(), decrementable).unwrap();
            }
            assert!(left.norm_lt(&right));
            assert!(!right.norm_lt(&left));
            assert!(!left.norm_lt(&left));
            let decremented = decrementable.dec().expect("successor frontier");
            assert_eq!(decremented.depth(), 12_000);
            assert!(decremented.is_always_zero());
            assert!(!decremented.is_never_zero());
        })
        .expect("small-stack worker")
        .join()
        .expect("graph operations and destruction are stack safe");
}
// Small independent recursive models are confined to bounded test inputs.
fn model_dec(level: &Level) -> Option<Level> {
    match level.view() {
        LevelView::Zero | LevelView::Param(_) | LevelView::MVar(_) => None,
        LevelView::Succ(child) => Some(child.clone()),
        LevelView::Max(left, right) | LevelView::IMax(left, right) => {
            Some(Level::max(model_dec(left)?, model_dec(right)?).unwrap())
        }
    }
}
fn model_never(level: &Level) -> bool {
    match level.view() {
        LevelView::Succ(_) => true,
        LevelView::Max(left, right) => model_never(left) || model_never(right),
        LevelView::IMax(_, right) => model_never(right),
        _ => false,
    }
}
fn model_always(level: &Level) -> bool {
    match level.view() {
        LevelView::Zero => true,
        LevelView::Max(left, right) => model_always(left) && model_always(right),
        LevelView::IMax(_, right) => model_always(right),
        _ => false,
    }
}
fn unshare(level: &Level) -> Level {
    match level.view() {
        LevelView::Zero => Level::zero(),
        LevelView::Param(name) => Level::param(name.clone()),
        LevelView::MVar(id) => Level::mvar(id.clone()),
        LevelView::Succ(child) => unshare(child).succ().unwrap(),
        LevelView::Max(left, right) => Level::max(unshare(left), unshare(right)).unwrap(),
        LevelView::IMax(left, right) => Level::imax(unshare(left), unshare(right)).unwrap(),
    }
}
#[test]
fn generated_small_universes_match_recursive_models_and_ignore_sharing_topology() {
    let mut levels = vec![
        Level::zero(),
        Level::one(),
        Level::param(name("u")),
        Level::param(name("v")),
        Level::mvar(LMVarId(name("m"))),
    ];
    for _ in 0..3 {
        let previous = levels.clone();
        for (i, left) in previous.iter().enumerate().take(64) {
            let right = &previous[(i * 17 + 3) % previous.len()];
            levels.push(left.clone().succ().unwrap());
            levels.push(Level::max(left.clone(), right.clone()).unwrap());
            levels.push(Level::imax(left.clone(), right.clone()).unwrap());
            levels.push(Level::max(left.clone(), left.clone()).unwrap());
        }
    }
    for level in levels {
        assert_eq!(level.is_never_zero(), model_never(&level));
        assert_eq!(level.is_always_zero(), model_always(&level));
        assert!(level.dec() == model_dec(&level));
        assert!(level.normalize() == unshare(&level).normalize());
    }
}
fn model_occurs(expr: &Expr, index: u32) -> bool {
    match expr.node() {
        ExprNode::BVar { idx } => *idx == index,
        ExprNode::App { f, a } => model_occurs(f, index) || model_occurs(a, index),
        ExprNode::Lam {
            binder_type, body, ..
        }
        | ExprNode::ForallE {
            binder_type, body, ..
        } => model_occurs(binder_type, index) || model_occurs(body, index.saturating_add(1)),
        ExprNode::LetE {
            type_, value, body, ..
        } => {
            model_occurs(type_, index)
                || model_occurs(value, index)
                || model_occurs(body, index.saturating_add(1))
        }
        ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => model_occurs(expr, index),
        _ => false,
    }
}
#[test]
fn generated_bound_variable_queries_match_a_binder_sensitive_model() {
    let mut expressions = vec![Expr::sort(Level::zero())];
    expressions.extend((0..5).map(|i| Expr::bvar(i).unwrap()));
    for _ in 0..3 {
        let previous = expressions.clone();
        for (i, left) in previous.iter().enumerate().take(64) {
            let right = previous[(i * 13 + 1) % previous.len()].clone();
            expressions.push(Expr::app(left.clone(), right.clone()));
            expressions.push(Expr::lam(
                name("x"),
                left.clone(),
                right.clone(),
                BinderInfo::Default,
            ));
            expressions.push(Expr::forall_e(
                name("x"),
                left.clone(),
                right.clone(),
                BinderInfo::Implicit,
            ));
            expressions.push(Expr::let_e(
                name("x"),
                left.clone(),
                left.clone(),
                right,
                false,
            ));
        }
    }
    for expression in expressions {
        for index in 0..8 {
            assert_eq!(
                expression.has_loose_bvar(index),
                model_occurs(&expression, index)
            );
        }
    }
}
