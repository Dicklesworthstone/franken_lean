//! Indexed declarations retain their constructor result indices through both checkers.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, Name, Outcome, SourceCheckLimits};

fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}
fn engine() -> Engine {
    Engine::with_source_seed(limits())
        .unwrap()
        .into_complete()
        .unwrap()
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
        .unwrap()
}
const VECTOR: &str = "inductive Vec (A : Type) : Nat -> Type where\n  | nil : Vec A 0\n  | cons (n : Nat) (head : A) (tail : Vec A n) : Vec A (Nat.succ n)\n";

#[test]
fn length_indexed_vector_constructors_retain_their_result_types() {
    let result = check(&format!(
        "{VECTOR}\
        def empty : Vec Nat 0 := Vec.nil\n\
        def two : Vec Nat 2 := Vec.cons 1 7 (Vec.cons 0 9 Vec.nil)\n\
        theorem same : two = Vec.cons 1 7 (Vec.cons 0 9 Vec.nil) := by rfl"
    ));
    assert_eq!(result.commands, 4);
    assert_eq!(result.theorems, 1);
    assert!(
        result
            .engine
            .environment()
            .contains(&Name::from_components(["Vec", "rec"]))
    );
}

#[test]
fn multiple_indices_can_depend_on_prior_indices() {
    check(
        "inductive Witness (A : Type) (P : A -> Type) : forall a : A, P a -> Type where\n\
        | intro (a : A) (value : P a) : Witness A P a value\n\
        def witness : Witness Nat (fun n => Bool) 7 true := Witness.intro 7 true\n\
        theorem same : witness = Witness.intro 7 true := by rfl",
    );
}

#[test]
fn recursive_families_can_change_several_indices() {
    check(
        "inductive Path (A : Type) : A -> A -> Type where\n\
        | refl (a : A) : Path A a a\n\
        | step (a b c : A) (first : Path A a b) (second : Path A b c) : Path A a c\n\
        def path : Path Nat 3 3 := Path.step 3 3 3 (Path.refl 3) (Path.refl 3)",
    );
}

#[test]
fn wrong_length_values_and_nonuniform_parameters_never_publish_a_prefix() {
    let base = engine();
    let root = base.logical_root(&KVMap::new());
    for bad in [
        "def bad : Vec Nat 1 := Vec.nil",
        "def bad : Vec Nat 1 := Vec.cons 0 7 (Vec.cons 0 9 Vec.nil)",
        "def bad : Vec Nat 1 := Vec.cons 0 true Vec.nil",
        "theorem bad : (Vec.cons 0 7 Vec.nil : Vec Nat 1) = Vec.cons 0 9 Vec.nil := by rfl",
    ] {
        assert!(
            !matches!(
                base.check_source_files(
                    &[VECTOR.as_bytes(), bad.as_bytes()],
                    &KVMap::new(),
                    SourceCheckLimits::new(limits())
                ),
                Ok(Outcome::Complete(_))
            ),
            "{bad}"
        );
        assert_eq!(base.logical_root(&KVMap::new()), root);
        assert!(!base.environment().contains(&Name::from_components(["Vec"])));
    }
    for bad in [
        "inductive Bad (A : Type) : Nat -> Type where | mk (tail : Bad Nat 0) : Bad A 1",
        "inductive Bad (A : Type) : Nat -> Type where | mk : Bad Bool 0",
        "inductive Bad (A : Type) : Nat -> Type where | mk",
        "inductive Bad : Nat -> Type where | mk : Bad true",
        "inductive Bad : Nat -> Type where | mk : Bad",
        "inductive Bad : Nat -> Type where | mk (f : Bad 0 -> Nat) : Bad 1",
    ] {
        assert!(
            !matches!(
                base.check_source_files(
                    &[bad.as_bytes()],
                    &KVMap::new(),
                    SourceCheckLimits::new(limits())
                ),
                Ok(Outcome::Complete(_))
            ),
            "{bad}"
        );
        assert_eq!(base.logical_root(&KVMap::new()), root);
    }
}

#[test]
fn dependent_quantifiers_are_real_pi_types_and_preserve_shadowing() {
    check(
        "theorem all : forall x : Nat, x = x := by intro x; rfl\n\
        theorem two : ∀ x y : Nat, x = x := by intro x y; rfl\n\
        def keep (x : Bool) : forall x : Nat, Nat := fun x => x\n\
        theorem same : keep true 7 = 7 := by rfl",
    );
    let base = engine();
    for source in [
        "def bad : forall x : Nat, x := fun x => x",
        "def bad : forall x : (1 : Type), Nat := fun x => x",
        "theorem bad : forall x : Nat, 1 = 2 := by intro x; rfl",
        "inductive Bad : (let unused : String := 1; Nat -> Type) where | intro : Bad 0",
        "inductive Bad : Nat -> Type where | intro : (let unused : String := 1; Bad 0)",
    ] {
        assert!(
            !matches!(
                base.check_source_files(
                    &[source.as_bytes()],
                    &KVMap::new(),
                    SourceCheckLimits::new(limits())
                ),
                Ok(Outcome::Complete(_))
            ),
            "{source}"
        );
    }
}

#[test]
fn indexed_fields_and_indices_have_independent_telescope_scopes() {
    check(
        "inductive Box (A : Type) : forall x : A, Type where\n\
        | put (x : A) : Box A x\n\
        def good : Box Nat 7 := Box.put 7",
    );
    for bad in [
        "inductive Bad : forall n : Nat, Type where | intro : Bad n",
        "inductive Bad : Nat -> Type where | intro (n : Nat) : Bad missing",
        "inductive Bad : Nat -> Type where | intro (n : Nat) (n : Bool) : Bad n",
    ] {
        assert!(
            !matches!(
                engine().check_source_files(
                    &[bad.as_bytes()],
                    &KVMap::new(),
                    SourceCheckLimits::new(limits())
                ),
                Ok(Outcome::Complete(_))
            ),
            "{bad}"
        );
    }
}
