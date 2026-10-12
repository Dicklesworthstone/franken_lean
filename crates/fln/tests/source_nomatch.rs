//! Empty matches construct ordinary recursors, admitted by both checking engines.
#![forbid(unsafe_code)]

use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, Name, Outcome, SourceCheckLimits};
use fln_core::expr::{Expr, ExprNode};
use fln_env::constants::ConstantInfo;
use std::collections::HashSet;

fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}

fn engine() -> Engine {
    Engine::with_source_seed(limits())
        .expect("source seed admission")
        .into_complete()
        .expect("both checking engines complete")
}

fn check(source: &str) -> fln::SourceFileCheck {
    engine()
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        )
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .expect("both checking engines complete")
}

fn constants(expr: &Expr) -> HashSet<Name> {
    let mut found = HashSet::new();
    let mut seen = HashSet::new();
    let mut pending = vec![expr];
    while let Some(expr) = pending.pop() {
        if !seen.insert(expr.allocation_identity()) {
            continue;
        }
        match expr.node() {
            ExprNode::Const { name, .. } => {
                found.insert(name.clone());
            }
            ExprNode::App { f, a } => pending.extend([f, a]),
            ExprNode::Lam {
                binder_type, body, ..
            }
            | ExprNode::ForallE {
                binder_type, body, ..
            } => {
                pending.extend([binder_type, body]);
            }
            ExprNode::LetE {
                type_, value, body, ..
            } => {
                pending.extend([type_, value, body]);
            }
            ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => pending.push(expr),
            _ => {}
        }
    }
    found
}

#[test]
fn false_elimination_keeps_the_admitted_recursor() {
    let result = check("def absurdNat (h : False) : Nat := nomatch h");
    let Some(ConstantInfo::Defn(definition)) = result
        .engine
        .environment()
        .find(&Name::from_components(["absurdNat"]))
    else {
        panic!("checked definition");
    };
    let used = constants(&definition.value);
    assert!(used.contains(&Name::from_components(["False", "rec"])));
    assert!(!used.contains(&Name::from_components(["sorryAx"])));
}

#[test]
fn empty_elimination_supports_dependent_and_function_valued_results() {
    for source in [
        "def absurdProp (h : False) : False := nomatch h",
        "def absurdFunction (h : False) : Nat -> Nat := nomatch h",
        "def dependent (P : False -> Type) (h : False) : P h := nomatch h",
        "def absurdType (h : False) : Type := nomatch h",
    ] {
        check(source);
    }
}

#[test]
fn computed_discriminants_and_aliases_remain_checked() {
    for source in [
        "def alias (h : False) : Nat := let k : False := h; nomatch k",
        "def computed (f : Nat -> False) : Nat := nomatch (f 0)",
        "def annotated (h : False) : Nat := nomatch (h : False)",
    ] {
        check(source);
    }
}

#[test]
fn impossible_equality_indices_use_the_existing_contradiction_backend() {
    for source in [
        "def impossibleSucc (n : Nat) (h : Nat.succ n = 0) : Nat := nomatch h",
        "def impossibleZero (n : Nat) (h : 0 = Nat.succ n) : Nat := nomatch h",
        "def impossibleBool (h : true = false) : Nat := nomatch h",
    ] {
        check(source);
    }
}

#[test]
fn live_branches_and_invalid_discriminants_are_refused_atomically() {
    let engine = engine();
    let options = KVMap::new();
    let root = engine.logical_root(&options);
    for source in [
        "def bad (n : Nat) : Nat := nomatch n",
        "def bad (b : Bool) : Nat := nomatch b",
        "def bad : Nat := nomatch true",
        "def bad (n : Nat) (h : n = n) : Nat := nomatch h",
        "def bad (n : Nat) (h : n = 0) : Nat := nomatch h",
        "def bad (h : False) : Nat := nomatch (h : Nat)",
        "def bad (h : False) : Nat := nomatch missing",
        "def bad (h : False) : Nat := nomatch h, missing",
        "def bad (n : Nat) (b : Bool) : Nat := nomatch n, b",
    ] {
        let error = engine
            .check_source_files(
                &[source.as_bytes()],
                &options,
                SourceCheckLimits::new(limits()),
            )
            .expect_err("a live branch or invalid input must not publish");
        assert_eq!(error.disposition().0, "elaboration", "{source}: {error:?}");
        assert_eq!(engine.logical_root(&options), root, "{source}");
        assert!(
            engine
                .environment()
                .find(&Name::from_components(["bad"]))
                .is_none()
        );
    }
    assert!(matches!(
        engine.check_source_files(
            &[b"def answer : Nat := 42"],
            &options,
            SourceCheckLimits::new(limits()),
        ),
        Ok(Outcome::Complete(_))
    ));
}

#[test]
fn an_impossible_branch_can_coexist_with_a_computing_branch() {
    let result = check(
        "inductive Abortable where | done | impossible (h : False)\n\
         def choose (x : Abortable) : Nat := match x with \
         | .done => 42 | .impossible h => nomatch h\n\
         theorem chosen : choose Abortable.done = 42 := by rfl",
    );
    assert_eq!(result.theorems, 1);
}

#[test]
fn ordinary_match_coverage_is_not_weakened() {
    for source in [
        "def bad (b : Bool) : Nat := match b with | true => 42",
        "def bad (n : Nat) : Nat := match n with | Nat.zero => 42",
    ] {
        engine()
            .check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits()),
            )
            .expect_err("ordinary matches still require every live constructor");
    }
}
