//! Default congruence builds checked equality eliminations, not guessed evidence.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, Name, SourceCheckLimits};
use fln_core::expr::ExprNode;
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
fn reject(base: &Engine, source: &str) {
    let root = base.logical_root(&KVMap::new());
    assert!(
        base.check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        )
        .is_err(),
        "{source}"
    );
    assert_eq!(base.logical_root(&KVMap::new()), root);
    assert!(!base.environment().contains(&Name::from_components(["bad"])));
}

#[test]
fn argument_congruence_proves_nested_applications_at_distinct_universes() {
    let base = engine();
    for source in [
        "theorem result (A B : Type) (f : A -> B) (x y : A) (h : x = y) : f x = f y := by solve_by_elim",
        "theorem result (A B C : Type) (f : A -> B) (g : B -> C) (x y : A) (h : x = y) : g (f x) = g (f y) := by solve_by_elim",
        "theorem result (A : Type 1) (B : Type) (f : A -> B) (x y : A) (h : x = y) : f x = f y := by solve_by_elim",
        "theorem result (A : Type) (f : A -> Prop) (x y : A) (h : x = y) : f x = f y := by solve_by_elim",
    ] {
        check(&base, source);
    }
}

#[test]
fn function_congruence_keeps_the_dependent_result_family() {
    let base = engine();
    for source in [
        "theorem result (A B : Type) (f g : A -> B) (h : f = g) (a : A) : f a = g a := by solve_by_elim",
        "theorem result (A : Type) (B : A -> Type) (f g : (x : A) -> B x) (h : f = g) (a : A) : f a = g a := by solve_by_elim",
        "theorem result (A : Type 1) (B : A -> Type) (f g : (x : A) -> B x) (h : f = g) (a : A) : f a = g a := by solve_by_elim",
        "theorem result (A B C : Type) (f g : A -> B -> C) (h : f = g) (a : A) (b : B) : f a b = g a b := by solve_by_elim",
    ] {
        check(&base, source);
    }
}

#[test]
fn argument_congruence_cannot_treat_equal_endpoints_as_a_constant_family() {
    let base = check(
        &engine(),
        "def Family (n : Nat) : Type := if n = 0 then Nat else Bool",
    );
    // Family 1 and Family 2 both reduce to Bool, but the whole function is
    // dependent. Applying congrArg as though it were Nat -> Bool would build
    // an ill-typed motive even in the presence of the equality hypothesis.
    reject(
        &base,
        "theorem bad (f : (n : Nat) -> Family n) (h : 1 = 2) : f 1 = f 2 := by apply_assumption -exfalso",
    );
    // A reducible family that really is constant is a nondependent function.
    let base = check(&base, "def Constant (_ : Nat) : Type := Nat");
    check(
        &base,
        "theorem result (f : (n : Nat) -> Constant n) (x y : Nat) (h : x = y) : f x = f y := by solve_by_elim",
    );
}

#[test]
fn greedy_rules_expose_congruence_premises_and_preserve_only() {
    let base = engine();
    for source in [
        "theorem result (f : Nat -> Nat) (x y : Nat) (h : x = y) : f x = f y := by\n  apply_assumption\n  exact h",
        "theorem result (f g : Nat -> Nat) (x : Nat) (h : f = g) : f x = g x := by\n  apply_assumption\n  exact h",
        "theorem result (f g : Nat -> Nat) (x y : Nat) (h : x = y) : g (f x) = g (f y) := by apply_rules",
    ] {
        check(&base, source);
    }
    reject(
        &base,
        "theorem bad (f : Nat -> Nat) (x y : Nat) (h : x = y) : f x = f y := by solve_by_elim -constructor only [h]",
    );
    reject(
        &base,
        "theorem bad (f : Nat -> Nat) (x y : Nat) (h : x = y) : f x = f y := by apply_rules only [h]",
    );
    // Applying a rule is not solving its missing premise.
    reject(
        &base,
        "theorem bad (f : Nat -> Nat) (x y : Nat) : f x = f y := by apply_assumption",
    );
}

#[test]
fn congruence_steps_consume_depth_and_respect_symmetry_selection() {
    let base = engine();
    let source = "theorem result (f : Nat -> Nat) (x y : Nat) (h : x = y) : f x = f y := by solve_by_elim -intro -constructor -exfalso (maxDepth := 3)";
    check(&base, source);
    reject(
        &base,
        &source.replace("result", "bad").replace(":= 3", ":= 2"),
    );
    check(
        &base,
        "theorem result (f : Nat -> Nat) (x y : Nat) (h : y = x) : f x = f y := by solve_by_elim +symm",
    );
    reject(
        &base,
        "theorem bad (f : Nat -> Nat) (x y : Nat) (h : y = x) : f x = f y := by solve_by_elim -symm -exfalso -constructor",
    );
}

#[test]
fn congruence_proof_terms_retain_real_elimination_and_global_evidence() {
    let base = check(
        &engine(),
        "axiom a : Nat\naxiom b : Nat\naxiom evidence : a = b",
    );
    let result = check(
        &base,
        "theorem result (f : Nat -> Nat) : f a = f b := by solve_by_elim [evidence]",
    );
    let ConstantInfo::Thm(theorem) = result
        .environment()
        .find(&Name::from_components(["result"]))
        .unwrap()
    else {
        panic!("congruence must produce a theorem, not an axiom");
    };
    assert!(!theorem.value.has_fvar());
    assert!(!theorem.value.has_expr_mvar());
    assert!(!theorem.value.has_level_mvar());
    assert!(!theorem.value.has_loose_bvars());
    let mut pending = vec![&theorem.value];
    let mut recursor = false;
    let mut evidence = false;
    while let Some(expr) = pending.pop() {
        match expr.node() {
            ExprNode::Const { name, .. } => {
                recursor |= name == &Name::from_components(["Eq", "rec"]);
                evidence |= name == &Name::from_components(["evidence"]);
            }
            ExprNode::App { f, a } => pending.extend([f, a]),
            ExprNode::Lam {
                binder_type, body, ..
            }
            | ExprNode::ForallE {
                binder_type, body, ..
            } => pending.extend([binder_type, body]),
            ExprNode::MData { expr, .. } => pending.push(expr),
            _ => {}
        }
    }
    assert!(
        recursor && evidence,
        "the original equality must remain in the checked recursor"
    );
}

#[test]
fn missing_or_unsafe_equality_cannot_become_congruence_evidence() {
    let base = check(
        &engine(),
        "unsafe def forged (f g : Nat -> Nat) : f = g := forged f g",
    );
    for source in [
        "theorem bad (f : Nat -> Nat) (x y : Nat) : f x = f y := by solve_by_elim -exfalso",
        "theorem bad (f g : Nat -> Nat) (x : Nat) : f x = g x := by solve_by_elim -exfalso",
        "theorem bad (f g : Nat -> Nat) (x : Nat) : f x = g x := by solve_by_elim [forged f g]",
    ] {
        reject(&base, source);
    }
    check(
        &base,
        "theorem result (f : Nat -> Nat) (x y : Nat) (h : x = y) : f x = f y := by solve_by_elim",
    );
}

#[test]
fn congruence_composes_with_introductions_joint_goals_and_backtracking() {
    let base = engine();
    for source in [
        "theorem result (f : Nat -> Nat) (x y : Nat) : x = y -> f x = f y := by solve_by_elim",
        "theorem result (f g : Nat -> Nat) (x y : Nat) (h : x = y) : (f x = f y) ∧ (g x = g y) := by\n  constructor\n  solve_by_elim* (maxDepth := 3)",
        "theorem result (f : Nat -> Nat) (x y : Nat) (h : x = y) : f x = f y := by\n  first | solve_by_elim (maxDepth := 2) | solve_by_elim (maxDepth := 3)",
        "theorem result (f : Nat -> Nat) (x y : Nat) (h : x = y) : (f x = f y) ∧ True := by\n  constructor\n  focus solve_by_elim*\n  constructor",
    ] {
        check(&base, source);
    }
}
