//! Equality tactics must retain ordinary checked proofs and dependent contexts.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, SourceCheckLimits};
fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}
fn engine() -> Engine {
    Engine::with_source_seed(limits())
        .unwrap()
        .into_complete()
        .unwrap()
}
fn check(source: &str) {
    engine()
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        )
        .unwrap_or_else(|e| panic!("{source}\n{e:?}"))
        .into_complete()
        .unwrap();
}
#[test]
fn subst_orients_equalities_and_finds_named_variables() {
    for tactic in ["subst h", "subst x", "subst y"] {
        check(&format!(
            "theorem transport (x y : Nat) (h : x = y) : y = x := by\n  {tactic}\n  rfl"
        ));
    }
    check("theorem transport (x : Nat) (h : x = 7) : x = 7 := by\n  subst h\n  rfl");
    check("theorem transport (x : Nat) (h : 7 = x) : x = 7 := by\n  subst h\n  rfl");
}
#[test]
fn subst_rebuilds_dependent_data_and_proof_telescopes() {
    check(
        "theorem transport (A : Type) (P : A -> Prop) (x y : A) (h : x = y) (hx : P x) : P y := by\n  subst h\n  exact hx",
    );
    check("def cast (A B : Type) (h : A = B) (a : A) : B := by\n  subst h\n  exact a");
    check(
        "theorem dependentProof (x y : Nat) (h : x = y) (P : (x = y) -> Prop) (hp : P h) : P h := by\n  subst h\n  exact hp",
    );
}
#[test]
fn substitution_preserves_introduced_scopes_and_nested_branches() {
    check("theorem introduced (x y : Nat) : x = y -> y = x := by\n  intro h\n  subst h\n  rfl");
    check(
        "theorem scoped (b : Bool) (x y : Nat) (h : x = y) : x = y := by\n  cases b with\n  | false =>\n    subst h\n    rfl\n  | true => exact h",
    );
}
#[test]
fn false_substitution_proofs_and_cycles_never_publish_a_successor() {
    let base = engine();
    let root = base.logical_root(&KVMap::new());
    for s in [
        "theorem bad (x y : Nat) (h : x = y) : 0 = 1 := by\n  subst h\n  rfl",
        "theorem bad (x : Nat) (h : x = Nat.succ x) : x = x := by\n  subst h\n  rfl",
        "theorem bad (x : Nat) : x = x := by\n  subst x\n  rfl",
        "theorem bad (x y : Nat) (h : x = y) : y = x := by\n  subst h\n  exact h",
    ] {
        assert!(
            base.check_source_files(
                &[s.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits())
            )
            .is_err(),
            "{s}"
        );
        assert_eq!(root, base.logical_root(&KVMap::new()));
    }
}

#[test]
fn substitution_reintroduces_local_let_values_and_their_dependents() {
    check(
        "theorem lets (x y : Nat) (h : x = y) : x = y := let saved := x; by\n  subst h\n  exact rfl",
    );
    check(
        "def localValue (x y : Nat) (h : x = y) : Nat := let saved := x; by\n  subst h\n  exact saved",
    );
}
#[test]
fn proof_dependent_substitution_does_not_need_symmetry_involution_conversion() {
    check(
        "theorem fixed (x : Nat) (h : x = 7) (P : (x = 7) -> Prop) (p : P h) : P h := by\n  subst h\n  exact p",
    );
    check(
        "theorem reversed (x : Nat) (h : 7 = x) (P : (7 = x) -> Prop) (p : P h) : P h := by\n  subst h\n  exact p",
    );
}
#[test]
fn substitution_follows_alias_dependencies_and_refuses_unused_ill_typed_terms() {
    let base = engine();
    for source in [
        "theorem cyclic (x : Nat) : x = x := let alias := x; by\n  intro h\n  subst x\n  rfl",
        "theorem bad (x y : Nat) (h : x = y) : y = x := by\n  subst h\n  exact (fun ignored => rfl) (1 : String)",
    ] {
        assert!(
            base.check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits())
            )
            .is_err()
        );
    }
}
