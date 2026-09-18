//! Source-level context transformations, admitted by both checker seats.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, SourceCheckLimits};

fn check(source: &str) {
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let engine = Engine::with_source_seed(limits)
        .unwrap()
        .into_complete()
        .unwrap();
    engine
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits),
        )
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"));
}

#[test]
fn revert_reintroduces_assumptions_and_dependent_telescopes() {
    check("theorem t (P : Prop) (p : P) : P := by\n  revert p\n  intro q\n  exact q");
    check(
        "theorem t (A : Type) (x : A) (P : A -> Prop) (p : P x) : P x := by\n  revert A\n  intro B y Q q\n  exact q",
    );
    check(
        "theorem t (P Q : Prop) (p : P) (q : Q) : P := by\n  revert q p\n  intro hp hq\n  exact hp",
    );
}

#[test]
fn revert_preserves_introduced_binders_and_type_valued_goals() {
    check(
        "theorem t : forall (A : Type) (x : A), x = x := by\n  intro A x\n  revert A\n  intro B y\n  rfl",
    );
    check("def t (A : Type) (x : A) : A := by\n  revert x\n  intro y\n  exact y");
}

#[test]
fn revert_preserves_let_values_and_their_forward_dependencies() {
    check(
        "theorem t (x : Nat) : x = x := by\n  let y : Nat := x\n  have h : y = x := by rfl\n  revert x\n  intro n z hz\n  exact hz",
    );
    check("theorem t (x : Nat) : x = x := by\n  let y : Nat := x\n  revert y\n  intro z\n  rfl");
}

#[test]
fn revert_instance_binders_remain_available_to_instance_search() {
    check(
        "class Witness (A : Type) where\n value : A\ndef t (A : Type) [w : Witness A] : A := by\n  revert w\n  intro inst\n  exact Witness.value",
    );
}

#[test]
fn generalize_replaces_all_occurrences_and_composes_with_revert() {
    check("theorem t : 3 = 3 := by\n  generalize 3 = x\n  revert x\n  intro y\n  rfl");
    check("theorem t (f : Nat -> Nat) (n : Nat) : f n = f n := by\n  generalize f n = x\n  rfl");
    check(
        "theorem t (x : Nat) : forall (y : Nat), x = x := by\n  generalize x = y\n  intro z\n  rfl",
    );
    check("theorem t : 0 = 0 := by\n  generalize 7 = n\n  rfl");
}

#[test]
fn generalize_retains_real_equality_evidence_for_rewriting() {
    check("theorem t : 3 = 1 + 2 := by\n  generalize h : 3 = x\n  rewrite [<- h]\n  rfl");
    check(
        "theorem t (P : Nat -> Prop) (n : Nat) (p : P n) : P n := by\n  generalize h : n = m\n  rw [<- h]\n  exact p",
    );
    check(
        "theorem t (P : Nat -> Prop) (n : Nat) (p : P n) : P n := by\n  generalize h : n = n\n  rw [<- h]\n  exact p",
    );
    check(
        "theorem t : True := by\n  generalize h : 7 = n\n  have eq : 7 = n := by exact h\n  constructor",
    );
}

#[test]
fn generalize_supports_types_lets_and_universe_parameters() {
    check("def t (A : Type) (x : A) : A := by\n  generalize h : A = B\n  rw [<- h]\n  exact x");
    check("theorem t (x : Nat) : x = x := by\n  let y : Nat := x\n  generalize h : y = z\n  rfl");
    check(
        "universe u\ntheorem t (A : Sort u) (x : A) : x = x := by\n  generalize h : x = y\n  rfl",
    );
}

#[test]
fn generalize_is_branch_local_and_rolls_back_ill_typed_dependent_targets() {
    check("theorem t : 0 = 0 := by\n  first | (generalize 0 = x; fail) | rfl");
    check(
        "theorem t : And (0 = 0) (0 = 0) := by\n  constructor\n  · generalize 0 = x\n    rfl\n  · rfl",
    );
    // Replacing the index in the explicit Eq domain does not change x's type.
    // Reject this branch immediately, so `first` can select the well-typed one.
    check(
        "theorem t (F : Nat -> Type) (n : Nat) (x : F n) : x = x := by\n  first | generalize n = m | skip\n  rfl",
    );
}

#[test]
fn generalize_refuses_unproved_or_invalid_generalizations() {
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let engine = Engine::with_source_seed(limits)
        .unwrap()
        .into_complete()
        .unwrap();
    let options = KVMap::new();
    let root = engine.logical_root(&options);
    for bad in [
        "theorem bad : 0 = 1 := by generalize 0 = x; rfl",
        "theorem bad : 0 = 1 := by generalize h : 0 = x; exact h",
        "theorem bad (P : Nat -> Prop) (n : Nat) (p : P n) : P n := by generalize n = m; exact p",
        "theorem bad : 0 = 0 := by generalize 0 = x",
        "theorem bad : 0 = 0 := by generalize missing = x; rfl",
        "theorem bad : 0 = 0 := by generalize _ = x; rfl",
        "theorem bad : 0 = 0 := by generalize (1 : String) = x; rfl",
        "theorem bad : 0 = 0 := by generalize h : 0 = h; rfl",
        "theorem bad (F : Nat -> Type) (n : Nat) (x : F n) : x = x := by generalize n = m; rfl",
    ] {
        let result =
            engine.check_source_files(&[bad.as_bytes()], &options, SourceCheckLimits::new(limits));
        assert!(
            !matches!(result, Ok(fln::Outcome::Complete(_))),
            "accepted {bad}"
        );
        assert_eq!(engine.logical_root(&options), root);
    }
    check("theorem t : 3 = 3 := by generalize 3 = x; rfl");
}

#[test]
fn generalization_resource_stops_are_not_successful_tactic_alternatives() {
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let engine = Engine::with_source_seed(limits)
        .unwrap()
        .into_complete()
        .unwrap();
    let options = KVMap::new();
    let root = engine.logical_root(&options);
    let source = b"theorem t : 0 = 0 := by first | (generalize 0 = x; rfl) | rfl";
    let mut constrained = SourceCheckLimits::new(limits);
    constrained.admission.kernel = constrained.admission.kernel.narrowed(0, 32);
    match engine.check_source_files(&[source], &options, constrained) {
        Ok(fln::Outcome::Inconclusive(_)) => {}
        Err(error) => assert!(
            matches!(error.disposition(), ("resource" | "inconclusive", false, 3)),
            "{error:?}"
        ),
        other => panic!("expected a resource stop, got {other:?}"),
    }
    assert_eq!(engine.logical_root(&options), root);
    engine
        .check_source_files(&[source], &options, SourceCheckLimits::new(limits))
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(engine.logical_root(&options), root);
}

#[test]
fn revert_is_branch_local_and_failed_alternatives_restore_scope() {
    check("theorem t (P : Prop) (p : P) : P := by\n  first | (revert p; fail) | exact p");
    check("theorem t (P : Prop) (p : P) : P := by\n  try revert p missing\n  exact p");
    check(
        "theorem t (P : Prop) (p : P) : And P P := by\n  constructor\n  · revert p\n    intro q\n    exact q\n  · exact p",
    );
}

#[test]
fn revert_refusals_are_atomic_and_do_not_poison_later_checks() {
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let engine = Engine::with_source_seed(limits)
        .unwrap()
        .into_complete()
        .unwrap();
    let options = KVMap::new();
    let root = engine.logical_root(&options);
    for bad in [
        "theorem bad (P : Prop) (p : P) : P := by revert p; exact p",
        "theorem bad (P : Prop) (p : P) : P := by revert missing; exact p",
        "theorem bad (n : Nat) : 0 = 1 := by revert n; intro x; rfl",
        "theorem bad (P : Prop) (p : P) : P := by revert p",
    ] {
        let result = engine.check_source_files(
            &[b"theorem prior : 0 = 0 := by rfl", bad.as_bytes()],
            &options,
            SourceCheckLimits::new(limits),
        );
        assert!(
            !matches!(result, Ok(fln::Outcome::Complete(_))),
            "accepted {bad}"
        );
        assert_eq!(engine.logical_root(&options), root);
    }
    engine
        .check_source_files(
            &[b"theorem recovered (x : Nat) : x = x := by revert x; intro y; rfl"],
            &options,
            SourceCheckLimits::new(limits),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(engine.logical_root(&options), root);
}
