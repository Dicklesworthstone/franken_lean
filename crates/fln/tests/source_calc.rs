//! Native calculations must survive the ordinary K1 plus independent council.
#![forbid(unsafe_code)]
use fln::{Engine, EngineAdmissionLimits};
use fln_core::options::KVMap;
use fln_kernel::verdict::Budget;
fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}
fn engine() -> Engine {
    Engine::with_source_seed(limits())
        .unwrap()
        .into_complete()
        .unwrap()
}
fn prove(source: &str) {
    engine()
        .admit_source_declaration(source.as_bytes(), &KVMap::new(), limits())
        .unwrap_or_else(|e| panic!("{source}\n{e:?}"))
        .into_complete()
        .expect("completed council");
}
#[test]
fn direct_calculation_composes_local_equalities() {
    prove(
        "theorem chain (a b c : Nat) (h : a = b) (k : b = c) : a = c := calc\n  a = b := h\n  _ = c := k",
    );
    prove(
        "theorem chain (a b c : Nat) (h : a = b) (k : b = c) : a = c := calc\n  a = b := h\n  b = c := k",
    );
}
#[test]
fn tactic_and_exact_calculations_use_native_proof_scripts() {
    prove(
        "theorem chain (a b c : Nat) (h : a = b) (k : b = c) : a = c := by\n  calc\n    a = b := by exact h\n    _ = c := by assumption",
    );
    prove("theorem chain (a : Nat) : a = a := by\n  exact calc\n    a = a := by rfl");
}
/// A first step on the `calc` line leaves the remaining steps a position of their own
/// (`calcSteps := withPosition(calcFirstStep) withPosition((calcStep ppLine)*)`), here left of it.
#[test]
fn a_first_step_on_the_calc_line_leaves_the_rest_their_own_column() {
    prove(
        "theorem chain (a b c : Nat) (h : a = b) (k : b = c) : a = c :=\n  calc a = b := h\n    _ = c := k",
    );
    prove(
        "theorem chain (a b c : Nat) (h : a = b) (k : b = c) : a = c := by\n  calc a = b := h\n    _ = c := k",
    );
}
#[test]
fn polymorphic_and_propositional_carriers_are_checked() {
    prove(
        "theorem chain {α : Type} (a b c : α) (h : a = b) (k : b = c) : a = c := calc\n  a = b := h\n  _ = c := k",
    );
    prove(
        "theorem chain (P Q R : Prop) (h : P = Q) (k : Q = R) : P = R := calc\n  P = Q := h\n  _ = R := k",
    );
}
#[test]
fn nested_calculations_and_introduced_locals_keep_their_scopes() {
    // The inner calculation is parenthesized: unclosed, it takes the outer `_ = c := k` as its own
    // step at the pin, whose steps' position is that line's (`withPosition((ppLine linebreak
    // calcStep)*)`), and the proof is rejected ("unsolved goals"); it is refused here.
    prove(
        "theorem chain (a b c : Nat) : a = b -> b = c -> a = c := by\n  intro h k\n  calc\n    a = b := by\n      exact (calc\n        a = b := h)\n    _ = c := k",
    );
    let base = engine();
    assert!(
        base.admit_source_declaration(
            b"theorem chain (a b c : Nat) : a = b -> b = c -> a = c := by\n  intro h k\n  calc\n    a = b := by\n      calc\n        a = b := h\n    _ = c := k",
            &KVMap::new(),
            limits(),
        )
        .is_err()
    );
    prove("theorem chain (a : Nat) : a = a := calc\n  a = a := calc\n    a = a := by rfl");
}
#[test]
fn wrong_steps_disconnected_chains_and_wrong_conclusions_are_refused() {
    for source in [
        "theorem bad : 0 = 1 := calc\n  0 = 1 := by rfl",
        "theorem bad : 0 = 1 := calc\n  0 = 0 := by rfl\n  1 = 1 := by rfl",
        "theorem bad : 0 = 1 := calc\n  0 = 0 := by rfl",
        "theorem bad : 0 = 0 := calc\n  0 = 1 := by rfl\n  _ = 0 := by rfl",
        "theorem bad (a : Nat) : a = a := calc\n  a = a := _",
        "theorem bad (a b : Nat) (h : a = a) : a = b := calc\n  a = b := h",
    ] {
        let base = engine();
        let count = base.environment().len();
        assert!(
            base.admit_source_declaration(source.as_bytes(), &KVMap::new(), limits())
                .is_err(),
            "{source}"
        );
        assert_eq!(count, base.environment().len());
    }
}
#[test]
fn reflexive_arithmetic_steps_compose_without_extra_axioms() {
    prove("theorem chain : 2 + 3 = 5 := calc\n  2 + 3 = 5 := by rfl\n  _ = 5 := by rfl");
}
