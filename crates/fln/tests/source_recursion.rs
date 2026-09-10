//! Recursive definitions become recursors, never unchecked self declarations.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, Name, SourceCheckLimits};
use fln_core::expr::{Expr, ExprNode};
use fln_env::constants::ConstantInfo;
use std::collections::HashSet;
fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}
fn engine() -> Engine {
    Engine::with_source_seed(limits())
        .unwrap()
        .into_complete()
        .unwrap()
}
fn check(text: &str) -> fln::SourceFileCheck {
    engine()
        .check_source_files(
            &[text.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        )
        .unwrap_or_else(|error| panic!("{text}\n{error:?}"))
        .into_complete()
        .unwrap()
}
fn constants(expr: &Expr) -> HashSet<Name> {
    let mut seen = HashSet::new();
    let mut found = HashSet::new();
    let mut pending = vec![expr];
    while let Some(expr) = pending.pop() {
        if !seen.insert(expr.allocation_identity()) {
            continue;
        }
        match expr.node() {
            ExprNode::Const { name, .. } => {
                found.insert(name.clone());
            }
            ExprNode::App { f, a } => {
                pending.push(f);
                pending.push(a);
            }
            ExprNode::Lam {
                binder_type, body, ..
            }
            | ExprNode::ForallE {
                binder_type, body, ..
            } => {
                pending.push(binder_type);
                pending.push(body);
            }
            ExprNode::LetE {
                type_, value, body, ..
            } => {
                pending.push(type_);
                pending.push(value);
                pending.push(body);
            }
            ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => pending.push(expr),
            _ => {}
        }
    }
    found
}
#[test]
fn primitive_nat_recursion_computes_through_both_checkers() {
    let checked = check(
        "def count (n : Nat) : Nat := match n with | .zero => 0 | .succ k => count k + 1\ntheorem ok : count 7 = 7 := by rfl",
    );
    let Some(ConstantInfo::Defn(definition)) = checked
        .engine
        .environment()
        .find(&Name::from_components(["count"]))
    else {
        panic!("definition");
    };
    let dependencies = constants(&definition.value);
    assert!(dependencies.contains(&Name::from_components(["Nat", "rec"])));
    assert!(!dependencies.contains(&Name::from_components(["count"])));
    assert!(!definition.value.has_fvar());
    assert!(!definition.value.has_expr_mvar());
}
#[test]
fn root_major_references_are_rebound_at_every_recursive_step() {
    check(
        "def sumTo (n : Nat) : Nat := match n with | .zero => n | .succ k => sumTo k + n\ntheorem ok : sumTo 4 = 10 := by rfl",
    );
    check(
        "def count (n : Nat) : Nat := match n with | .zero => 0 | .succ n => count n + 1\ntheorem ok : count 4 = 4 := by rfl",
    );
}
#[test]
fn tree_recursion_uses_the_hypothesis_for_each_distinct_child() {
    check(
        "inductive Tree where | leaf (value : Nat) | fork (left right : Tree)\ndef sum (tree : Tree) : Nat := match tree with | .leaf value => value | .fork left right => sum left + sum right\ntheorem ok : sum (Tree.fork (Tree.leaf 3) (Tree.fork (Tree.leaf 7) (Tree.leaf 11))) = 21 := by rfl",
    );
}
#[test]
fn implicit_type_arguments_and_fixed_functions_are_preserved() {
    check(
        "def iterate {A : Type} (step : A -> A) (zero : A) (n : Nat) : A := match n with | .zero => zero | .succ k => step (iterate step zero k)\ntheorem ok : iterate (fun x => x + 2) 1 3 = 7 := by rfl",
    );
}
#[test]
fn direct_child_calls_survive_nested_nonrecursive_matches_and_lets() {
    check(
        "def count (flag : Bool) (n : Nat) : Nat := match n with | .zero => 0 | .succ k => let previous := count flag k; match flag with | true => previous + 1 | false => previous + 2\ntheorem yes : count true 3 = 3 := by rfl\ntheorem no : count false 3 = 6 := by rfl",
    );
}
#[test]
fn nondecreasing_and_escaping_calls_are_failure_atomic_even_when_unused() {
    let base = engine();
    let snapshot = base.environment().clone();
    let invalid = [
        "def loop (n : Nat) : Nat := loop n",
        "def loop (n : Nat) : Nat := match n with | .zero => 0 | .succ k => loop n",
        "def loop (n : Nat) : Nat := match n with | .zero => 0 | .succ k => loop (Nat.succ k)",
        "def loop (n : Nat) : Nat := match n with | .zero => loop n | .succ k => 1",
        "def loop (n : Nat) : Nat := match n with | .zero => 0 | .succ k => let unused := loop n; 0",
        "def loop (n : Nat) : Nat := match n with | .zero => 0 | .succ k => let escaped := loop; escaped k",
        "def loop (n : Nat) : Nat := (match n with | .zero => 0 | .succ k => loop k) + 1",
        "def loop (fixed n : Nat) : Nat := match n with | .zero => fixed | .succ k => loop 1 k",
    ];
    for text in invalid {
        assert!(
            base.check_source_files(
                &[text.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits())
            )
            .is_err(),
            "{text}"
        );
        assert_eq!(base.environment(), &snapshot);
    }
    assert!(
        base.check_source_files(
            &[b"def good (n : Nat) : Nat := match n with | .zero => 0 | .succ k => good k + 1"],
            &KVMap::new(),
            SourceCheckLimits::new(limits())
        )
        .is_ok()
    );
}
#[test]
fn lexical_self_name_shadowing_stays_nonrecursive() {
    check(
        "def same (same : Nat) : Nat := same\ndef local : Nat := let local := 3; local\ntheorem ok : same local = 3 := by rfl",
    );
}
#[test]
fn a_bad_unreachable_recursive_branch_still_reaches_kernel_checking() {
    assert!(engine().check_source_files(&[b"def count (n : Nat) : Nat := match n with | .zero => 0 | .succ k => let bad : String := count k; 1\ndef zero : Nat := count 0"], &KVMap::new(), SourceCheckLimits::new(limits())).is_err());
}
