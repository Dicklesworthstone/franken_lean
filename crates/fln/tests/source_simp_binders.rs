//! Selected simp rewrites beneath binders retain checked transport evidence.
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
fn lambda_rewriting_retains_quotient_derived_extensionality() {
    let base = engine();
    let after = check(
        &base,
        "theorem lifted (A B : Type) (f g : A -> B) (h : (x : A) -> f x = g x) : (fun x => f x) = (fun x => g x) := by simp only [h]",
    );
    let Some(ConstantInfo::Thm(theorem)) =
        after.environment().find(&Name::from_components(["lifted"]))
    else {
        panic!("missing checked theorem")
    };
    assert!(!theorem.value.has_expr_mvar());
    assert!(!theorem.value.has_level_mvar());
    assert!(!theorem.value.has_fvar());
    assert!(!theorem.value.has_loose_bvars());
    let mut pending = vec![&theorem.value];
    let mut names = std::collections::HashSet::new();
    while let Some(term) = pending.pop() {
        match term.node() {
            ExprNode::Const { name, .. } => {
                names.insert(name.to_display_string());
            }
            ExprNode::App { f, a } => pending.extend([f, a]),
            ExprNode::Lam {
                binder_type, body, ..
            }
            | ExprNode::ForallE {
                binder_type, body, ..
            } => pending.extend([binder_type, body]),
            ExprNode::LetE {
                type_, value, body, ..
            } => pending.extend([type_, value, body]),
            ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => pending.push(expr),
            _ => {}
        }
    }
    assert!(names.contains("Quot.sound"));
    assert!(names.contains("Eq.rec"));
    assert!(!names.contains("sorryAx"));
    assert_eq!(after.environment().len(), base.environment().len() + 1);
}

#[test]
fn lambda_rewriting_handles_nested_dependent_binders_and_polymorphic_rules() {
    let base = engine();
    for source in [
        "universe u v\ntheorem t (A : Sort u) (B : A -> Sort v) (f g : (x : A) -> B x) (h : (x : A) -> f x = g x) : (fun x => f x) = (fun x => g x) := by simp only [h]",
        "theorem t (F : Nat -> Type) (f g : (n : Nat) -> F n -> Nat) (h : (n : Nat) -> (x : F n) -> f n x = g n x) : (fun n x => f n x) = (fun n x => g n x) := by simp only [h]",
        "theorem t (f g : Nat -> Nat) (wrap : (Nat -> Nat) -> Nat) (h : (n : Nat) -> f n = g n) : wrap (fun n => f n) = wrap (fun n => g n) := by simp only [h]",
        "theorem t (f g : Nat -> Nat) (h : (n : Nat) -> f n = g n) : (fun h => f h) = (fun h => g h) := by simp only [h]",
        "theorem t (f g : Nat -> Nat) (h : (n : Nat) -> f n = g n) : (fun x => f x) = (fun x => g x) := by simp only [<- h]",
    ] {
        check(&base, source);
    }
}

#[test]
fn binder_rewrites_preserve_goals_and_backtracking() {
    let base = engine();
    for source in [
        "theorem t (f g k : Nat -> Nat) (h : (n : Nat) -> f n = g n) (hk : g = k) : (fun n => f n) = k := by\n  simp only [h]\n  guard_target = (fun n => g n) = k\n  exact hk",
        "theorem t (f g : Nat -> Nat) (h : (n : Nat) -> f n = g n) : ((fun n => f n) = (fun n => g n)) ∧ True := by\n  constructor\n  · first | (simp only [h]; fail) | skip\n    simp only [h]\n  · constructor",
    ] {
        check(&base, source);
    }
}

#[test]
fn lambda_simplification_cannot_use_unselected_or_unsafe_evidence() {
    let base = engine();
    let root = base.logical_root(&KVMap::new());
    for source in [
        "theorem bad (f g : Nat -> Nat) (h : (n : Nat) -> f n = g n) : (fun x => f x) = (fun x => g x) := by simp only []",
        "theorem bad (f g : Nat -> Nat) (h : f 0 = g 0) : (fun x => f x) = (fun x => g x) := by simp only [h]",
        "theorem bad (f g : Nat -> Nat) (h : (n : Nat) -> f n = g n) : ((fun x => f x) = (fun x => g x)) ∧ False := by constructor; focus (simp only [h])",
        "theorem bad (f g : Nat -> Nat) (h : (n : Nat) -> f n = g n) : (fun x => f x) = (fun x => g x) := by rw [h]",
    ] {
        assert!(
            base.check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits())
            )
            .is_err(),
            "{source}"
        );
        assert_eq!(base.logical_root(&KVMap::new()), root);
    }
    let source = "unsafe def forged (f g : Nat -> Nat) (n : Nat) : f n = g n := forged f g n\ntheorem bad (f g : Nat -> Nat) : (fun n => f n) = (fun n => g n) := by simp only [forged f g]";
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
    check(&base, "theorem recovered : True := by constructor");
}
