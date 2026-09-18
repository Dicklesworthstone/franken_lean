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
