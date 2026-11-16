//! Hypothesis rewriting through the actual K1/independent-checker council.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, Name, SourceCheckLimits};
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
fn named_hypotheses_transport_in_both_directions() {
    check(
        "theorem forward (P : Nat -> Prop) (x y : Nat) (h : x = y) (hx : P x) : P y := by rw [h] at hx; exact hx",
    );
    check(
        "theorem backward (P : Nat -> Prop) (x y : Nat) (h : x = y) (hy : P y) : P x := by rw [← h] at hy; exact hy",
    );
    check("def castValue {A B : Type} (h : A = B) (x : A) : B := by rw [h] at x; exact x");
}
#[test]
fn introduced_locals_and_rule_lists_have_correct_closure_scopes() {
    check(
        "theorem introed (P : Nat -> Prop) (x y z : Nat) : x = y -> y = z -> P x -> P z := by intro h k hx; rewrite [h, k] at hx; exact hx",
    );
    check(
        "theorem both (P : Nat -> Nat -> Prop) (x y z : Nat) (h : x = y) (k : y = z) (hx : P x x) (hy : P x x) : P z z := by rewrite [h, k] at hx hy; exact hy",
    );
    check(
        "theorem loc (P : Nat -> Prop) (x y : Nat) (h : x = y) (hx : P x) : P y := by have p := hx; rw [h] at p; exact p",
    );
}
#[test]
fn dependent_hypotheses_and_goals_keep_their_original_identity() {
    check(
        "theorem dependent (P : Nat -> Prop) (x y : Nat) (h : x = y) (hx : P x) (Q : P x -> Prop) (q : Q hx) : Q hx := by rewrite [h] at hx; exact q",
    );
    check(
        "def dependentType (A B : Type) (h : A = B) (x : A) (Q : A -> Type) (q : Q x) : Q x := by rewrite [h] at x; exact q",
    );
    check(
        "theorem localDependent (P : Nat -> Prop) (x y : Nat) (h : x = y) : P x -> P y := by intro hx; have saved := hx; rewrite [h] at hx; exact hx",
    );
}
#[test]
fn conditional_rules_retain_their_real_side_goals() {
    check(
        "theorem conditional (P : Prop) (x y : Nat) (h : P -> x = y) (Q : Nat -> Prop) (hx : Q x) (p : P) : Q y := by rewrite [h] at hx; exact hx; exact p",
    );
    check(
        "theorem conditional (P : Prop) (Q : Nat -> Prop) (x y : Nat) : (P -> x = y) -> Q x -> P -> Q y := by intro h hx p; rewrite [h] at hx; exact hx; exact p",
    );
}
#[test]
fn quantified_rules_instantiate_separately_at_each_hypothesis() {
    check(
        "theorem many (f : Nat -> Nat) (h : forall n : Nat, f n = n) (P : Nat -> Prop) (p : P (f 1)) (q : P (f 2)) : P 2 := by rewrite [h] at p q; exact q",
    );
}
#[test]
fn failures_and_speculative_prefixes_do_not_leak_context_changes() {
    check(
        "theorem recover (P : Nat -> Prop) (x y z : Nat) (h : x = y) (k : z = y) (hx : P x) : P x := by\n try (rewrite [h, k] at hx)\n exact hx",
    );
    let base = engine();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    for source in [
        "theorem bad (P : Nat -> Prop) (x y : Nat) (h : x = y) (hx : P x) : P x := by rewrite [h] at hx; assumption",
        "theorem bad (P : Nat -> Prop) (x y : Nat) (h : x = y) (hx : P x) : P y := by rewrite [h] at missing; exact hx",
        "theorem bad (P : Prop) (x y : Nat) (h : P -> x = y) (Q : Nat -> Prop) (hx : Q x) : Q y := by rewrite [h] at hx; exact hx",
        "theorem bad (x y : Nat) (h : x = y) : 0 = 1 := by rw [h] at h; rfl",
    ] {
        assert!(
            base.check_source_files(
                &[source.as_bytes()],
                &options,
                SourceCheckLimits::new(limits())
            )
            .is_err(),
            "{source}"
        );
        assert_eq!(base.logical_root(&options), root);
        assert!(!base.environment().contains(&Name::from_components(["bad"])));
    }
    check("theorem again (x y : Nat) (h : x = y) : x = y := by exact h");
}

#[test]
fn symmetry_replaces_named_equalities_and_selected_targets() {
    for source in [
        "theorem backward {A : Type} (x y : A) (h : x = y) : y = x := by symm at h; exact h",
        "theorem both (x y : Nat) (h : x = y) : x = y := by symm at h ⊢; exact h",
        "theorem asciiGoal (x y : Nat) (h : x = y) : x = y := by symm at h |-; exact h",
        "theorem several (x y : Nat) (h k : x = y) : y = x := by symm at h k; exact k",
        "theorem introduced (x y : Nat) : x = y → y = x := by intro h; symm at h; exact h",
        "theorem quoted (x y : Nat) («h.x» : x = y) : y = x := by symm /- orientation -/ at «h.x»; exact «h.x»",
        "theorem twice (x y : Nat) (h : x = y) : x = y := by symm at h h; exact h",
    ] {
        check(source);
    }
}

#[test]
fn symmetry_keeps_proof_dependent_hypotheses_and_targets_valid() {
    check(
        "theorem dependent (x y : Nat) (h : x = y) (Q : x = y → Prop) (q : Q h) : Q h := by symm at h; have backward : y = x := h; exact q",
    );
    check(
        "theorem saved (x y : Nat) (h : x = y) : y = x := by have saved := h; symm at h; exact h",
    );
}

#[test]
fn wildcard_symmetry_skips_nonrelations_but_requires_progress() {
    check("theorem allLocations (x y : Nat) (h : x = y) : y = x := by symm at *; symm; exact h");
    check(
        "theorem nonrelationalGoal (P : Prop) (p : P) (x y : Nat) (h : x = y) : P := by symm at *; have backward : y = x := h; exact p",
    );
    check("theorem noProgress (P : Prop) (p : P) : P := by fail_if_success symm at *; exact p");
    check("theorem targetOnly (x : Nat) : x = x := by symm at *; rfl");
    check(
        "theorem shadowed (x y : Nat) (h : x = y) (h : True) : y = x := by symm at *; symm; rename_i backward; exact backward",
    );
    check(
        "theorem inaccessible (x y : Nat) : x = y → y = x := by intro _; symm at *; symm; rename_i backward; exact backward",
    );
}

#[test]
fn failed_symmetry_locations_roll_back_and_cannot_admit_false_proofs() {
    check("theorem restore (x y : Nat) (h : x = y) : x = y := by try (symm at h x); exact h");
    check(
        "theorem restoreGoal (x y : Nat) (h : x = y) : x = y := by first | (symm at h; exact h) | exact h",
    );
    let base = engine();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    for source in [
        "theorem bad (x y : Nat) (h : x = y) : x = y := by symm at h; exact h",
        "theorem bad (x y : Nat) (h : x = y) : y = x := by symm at missing; exact h",
        "theorem bad (P : Prop) (p : P) : P := by symm at p; exact p",
        "theorem bad (P : Prop) (p : P) : P := by symm at *; exact p",
        "theorem bad (x y : Nat) (h : x = y) : 0 = 1 := by symm at *; rfl",
    ] {
        assert!(
            base.check_source_files(
                &[source.as_bytes()],
                &options,
                SourceCheckLimits::new(limits())
            )
            .is_err(),
            "{source}"
        );
        assert_eq!(base.logical_root(&options), root);
        assert!(!base.environment().contains(&Name::from_components(["bad"])));
    }
}
