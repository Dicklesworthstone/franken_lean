//! Function extensionality must produce ordinary checked evidence.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, SourceCheckLimits};
use fln_core::{expr::ExprNode, name::Name};
use fln_env::constants::ConstantInfo;

fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}
fn engine() -> Engine {
    Engine::with_source_seed(limits())
        .unwrap()
        .into_complete()
        .unwrap()
}
fn check(base: &Engine, source: &str) -> Engine {
    base.check_source_files(
        &[source.as_bytes()],
        &KVMap::new(),
        SourceCheckLimits::new(limits()),
    )
    .unwrap_or_else(|e| panic!("{source}\n{e:?}"))
    .into_complete()
    .unwrap()
    .engine
}

#[test]
fn named_funext_proves_pointwise_equal_functions_with_real_quotient_evidence() {
    let base = engine();
    let result = check(
        &base,
        "theorem extensional (A B : Type) (f g : A -> B) (h : (x : A) -> f x = g x) : f = g := by\n  funext x\n  exact h x",
    );
    let Some(ConstantInfo::Thm(value)) = result
        .environment()
        .find(&Name::from_components(["extensional"]))
    else {
        panic!("not a theorem")
    };
    assert!(!value.value.has_expr_mvar());
    assert!(!value.value.has_level_mvar());
    assert!(!value.value.has_fvar());
    assert!(!value.value.has_loose_bvars());
    let mut nodes = vec![&value.value];
    let mut constants = Vec::new();
    while let Some(node) = nodes.pop() {
        match node.node() {
            ExprNode::Const { name, .. } => constants.push(name.to_display_string()),
            ExprNode::App { f, a } => nodes.extend([f, a]),
            ExprNode::Lam {
                binder_type, body, ..
            }
            | ExprNode::ForallE {
                binder_type, body, ..
            } => nodes.extend([binder_type, body]),
            ExprNode::LetE {
                type_, value, body, ..
            } => nodes.extend([type_, value, body]),
            _ => {}
        }
    }
    assert!(constants.iter().any(|n| n == "Quot.sound"));
    assert!(constants.iter().any(|n| n == "Quot.lift"));
    assert!(!constants.iter().any(|n| n == "sorryAx"));
    assert_eq!(result.environment().len(), base.environment().len() + 1);
}

#[test]
fn funext_handles_dependent_universes_and_multiple_arguments() {
    let base = engine();
    for source in [
        "universe u v\ntheorem t (A : Sort u) (B : A -> Sort v) (f g : (a : A) -> B a) (h : (a : A) -> f a = g a) : f = g := by\n  funext a\n  exact h a",
        "theorem t (F : Nat -> Type) (f g : (n : Nat) -> F n -> Nat) (h : (n : Nat) -> (x : F n) -> f n x = g n x) : f = g := by\n  funext n x\n  exact h n x",
        "theorem t (P : Nat -> Prop) (f g : (n : Nat) -> P n) : f = g := by\n  funext n\n  rfl",
        "theorem t (f : Nat -> Nat) : (fun x => f x) = f := by\n  funext x\n  rfl",
    ] {
        check(&base, source);
    }
}

#[test]
fn bare_funext_repeats_and_is_a_noop_when_the_goal_is_not_a_function_equality() {
    let base = engine();
    for source in [
        "theorem t (A B : Type) (f g : A -> B) (h : (x : A) -> f x = g x) : f = g := by\n  funext\n  apply h",
        "theorem t (f g : Nat -> Nat -> Nat) (h : (x y : Nat) -> f x y = g x y) : f = g := by\n  funext\n  apply h",
        "theorem t (P : Prop) (h : P) : P := by\n  funext\n  exact h",
        "theorem t : True := by\n  constructor\n  funext",
        "theorem t (f : Nat -> Nat) : f = f := by\n  funext _\n  rfl",
    ] {
        check(&base, source);
    }
}

#[test]
fn funext_preserves_sibling_goals_introductions_and_backtracking() {
    let base = engine();
    for source in [
        "theorem t (f g : Nat -> Nat) (h : (x : Nat) -> f x = g x) : (f = g) ∧ True := by\n  constructor\n  · funext x\n    exact h x\n  · constructor",
        "theorem t (f g : Nat -> Nat) : ((x : Nat) -> f x = g x) -> f = g := by\n  intro h\n  funext x\n  exact h x",
        "theorem t (f g : Nat -> Nat) (h : (x : Nat) -> f x = g x) : f = g := by\n  first | (funext x; fail) | skip\n  guard_target = f = g\n  funext y\n  exact h y",
        "theorem t (f : Nat -> Nat -> Nat) : f = f := by\n  funext x\n  guard_target = f x = f x\n  rfl",
    ] {
        check(&base, source);
    }
}

#[test]
fn function_equality_requires_all_pointwise_evidence_and_rejects_unsafe_proofs() {
    let base = engine();
    let root = base.logical_root(&KVMap::new());
    for source in [
        "theorem bad (f g : Nat -> Nat) : f = g := by funext x",
        "theorem bad : (fun (_ : Nat) => 0) = (fun (_ : Nat) => 1) := by funext x; rfl",
        "theorem bad (P : Prop) (h : P) : P := by funext x; exact h",
        "theorem bad (f : Nat -> Nat) : f = f := by funext x y; rfl",
        "theorem bad (f g : Nat -> Nat) (h : (x : Nat) -> f x = g x) : (f = g) ∧ False := by constructor; focus (funext x; exact h x)",
    ] {
        let result = base.check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        );
        assert!(!matches!(result, Ok(fln::Outcome::Complete(_))), "{source}");
        assert_eq!(base.logical_root(&KVMap::new()), root);
    }
    let source = "unsafe def forged (a b : Nat) : a = b := forged a b\ntheorem bad (f g : Nat -> Nat) : f = g := by\n  funext x\n  exact forged (f x) (g x)";
    let problem = base
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        )
        .unwrap_err();
    assert!(
        format!("{problem:?}").contains("SafetyViolation"),
        "{problem:?}"
    );
    assert_eq!(base.logical_root(&KVMap::new()), root);
    check(
        &base,
        "theorem recovered (f : Nat -> Nat) : f = f := by funext x; rfl",
    );
}
