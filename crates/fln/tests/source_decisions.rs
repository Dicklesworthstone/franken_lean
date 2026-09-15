//! Constructive decisions are ordinary admitted data with checked proof fields.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, SourceCheckLimits};

fn engine() -> (Engine, EngineAdmissionLimits) {
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    (
        Engine::with_source_seed(limits)
            .unwrap()
            .into_complete()
            .unwrap(),
        limits,
    )
}
fn check(source: &str) {
    let (engine, limits) = engine();
    engine
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits),
        )
        .unwrap_or_else(|e| panic!("{source}\n{e:?}"))
        .into_complete()
        .unwrap();
}
fn reject(source: &str) {
    let (engine, limits) = engine();
    let before = engine.logical_root(&KVMap::new());
    let result = engine.check_source_files(
        &[source.as_bytes()],
        &KVMap::new(),
        SourceCheckLimits::new(limits),
    );
    assert!(result.is_err(), "{source}");
    assert_eq!(engine.logical_root(&KVMap::new()), before);
}
#[test]
fn checked_decisions_and_negation_compute_through_admitted_recursors() {
    check(
        r#"
        theorem yes : ite True 7 9 = 7 := by rfl
        theorem no : ite False 7 9 = 9 := by rfl
        theorem true_bit : decide True = true := by rfl
        theorem false_bit : decide False = false := by rfl
        theorem negative_bit : decide (Not False) = true := by rfl
        theorem positive_bit : decide (Not True) = false := by rfl
        theorem twice : decide (Not (Not True)) = true := by rfl
    "#,
    );
}
#[test]
fn local_and_global_decision_dictionaries_retain_their_proofs() {
    check(
        r#"
        inductive Holds : Prop where | yes
        instance decideHolds : Decidable Holds := Decidable.isTrue Holds.yes
        theorem global_decision : decide Holds = true := by rfl
        def choose (p : Prop) [d : Decidable p] : Nat := ite p 11 13
        theorem local_decision : choose Holds = 11 := by rfl
        def explicit (p : Prop) (d : Decidable p) : Bool := decide p
        theorem explicit_decision : explicit True (Decidable.isTrue True.intro) = true := by rfl
        def proved (p : Prop) [Decidable p] (value : Nat) (good : p -> Nat) : Nat := dite p good (fun unused => value)
        theorem applied : proved True 3 (fun unused => 17) = 17 := by rfl
    "#,
    );
}
#[test]
fn decision_elimination_can_return_proofs_functions_and_types() {
    check(
        r#"
        theorem preserved (p : Prop) [Decidable p] (h : p) : p := dite p (fun yes => yes) (fun unused => h)
        def function : Nat -> Nat := ite True (fun n => n + 1) (fun n => n + 2)
        theorem applied : function 7 = 8 := by rfl
        def Carrier : Type := ite True Nat Bool
        def inhabitant : Carrier := 23
        theorem checked : inhabitant = 23 := by rfl
    "#,
    );
}
#[test]
fn no_decision_or_false_constructor_proof_is_not_invented() {
    for source in [
        "def missing (p : Prop) : Bool := decide p",
        "def invalid : Decidable False := Decidable.isTrue True.intro",
        "def invalid : Decidable True := Decidable.isFalse (fun h => h)",
        "theorem invalid : False := ite True True.intro True.intro",
        "def invalid : Nat := ite True 7 (1 : String)",
        "def invalid : Bool := decide (1 : Prop)",
    ] {
        reject(source);
    }
}
#[test]
fn logical_seed_additions_are_not_axioms() {
    use fln::Name;
    use fln_env::constants::ConstantInfo;
    let (engine, _) = engine();
    for name in [
        "False",
        "True",
        "Not",
        "Decidable",
        "Decidable.isTrue",
        "Decidable.isFalse",
        "Decidable.rec",
        "ite",
        "dite",
        "decide",
        "instDecidableTrue",
        "instDecidableFalse",
        "instDecidableNot",
        "of_decide_eq_true",
    ] {
        assert!(
            !matches!(
                engine
                    .environment()
                    .find(&Name::from_components(name.split('.'))),
                None | Some(ConstantInfo::Axiom(_))
            ),
            "{name}"
        );
    }
}
