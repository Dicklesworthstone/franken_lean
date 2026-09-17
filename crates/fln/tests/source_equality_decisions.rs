//! Native equality decisions carry kernel-checked positive and negative proofs.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, Name, SourceCheckLimits};
use fln_env::constants::ConstantInfo;

fn engine() -> (Engine, EngineAdmissionLimits) {
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let engine = Engine::with_source_seed(limits)
        .expect("source seed admission")
        .into_complete()
        .expect("source seed council");
    (engine, limits)
}
fn check(source: &str) {
    let (engine, limits) = engine();
    engine
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits),
        )
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .expect("source check must complete");
}
#[test]
fn bool_equality_decides_the_entire_truth_table() {
    check(
        r#"
        theorem ff : false = false := by decide
        theorem tt : true = true := by decide
        theorem ft : Not (false = true) := by decide
        theorem tf : Not (true = false) := by decide
        theorem ff_bit : decide (false = false) = true := by rfl
        theorem tt_bit : decide (true = true) = true := by rfl
        theorem ft_bit : decide (false = true) = false := by rfl
        theorem tf_bit : decide (true = false) = false := by rfl
    "#,
    );
}
#[test]
fn nat_equality_decides_zero_successors_and_both_inequality_directions() {
    let mut source = String::new();
    for left in 0..5 {
        for right in 0..5 {
            let proposition = if left == right {
                format!("{left} = {right}")
            } else {
                format!("Not ({left} = {right})")
            };
            source.push_str(&format!(
                "theorem cell_{left}_{right} : {proposition} := by decide\n"
            ));
        }
    }
    check(&source);
}
#[test]
fn computed_equalities_drive_conditionals_and_proof_automation() {
    check(
        r#"
        theorem sum : 2 + 3 = 5 := by decide
        theorem product : 3 * 4 = 12 := by decide
        theorem unequal : Not (2 + 3 = 6) := by decide
        theorem nested : Not (Not (3 = 3)) := by decide
        theorem positive_branch : ite (2 + 3 = 5) 17 19 = 17 := by rfl
        theorem negative_branch : ite (2 = 3) 17 19 = 19 := by rfl
        theorem bool_branch : ite (true = false) 17 19 = 19 := by rfl
        theorem proof_field : 3 = 3 := dite (3 = 3) (fun h => h) (fun unused => rfl)
        theorem no_field (fallback : Not (3 = 4)) : Not (3 = 4) := dite (3 = 4) (fun unused => fallback) (fun h => h)
    "#,
    );
}
#[test]
fn symbolic_equalities_have_dictionaries_without_being_guessed_true() {
    check(
        r#"
        def nat_dictionary (a b : Nat) : Decidable (a = b) := inferInstance
        def bool_dictionary (a b : Bool) : Decidable (a = b) := inferInstance
        def choose (a b : Nat) : Nat := ite (a = b) 11 13
        theorem chosen : choose 2 2 = 11 := by rfl
        theorem not_chosen : choose 2 3 = 13 := by rfl
        def classify (a b : Bool) : Bool := decide (a = b)
        theorem classified : classify true false = false := by rfl
    "#,
    );
}
#[test]
fn false_equalities_and_forged_proof_fields_are_rejected_transactionally() {
    let (engine, limits) = engine();
    let before = engine.logical_root(&KVMap::new());
    for source in [
        "theorem invalid : 2 = 3 := by decide",
        "theorem invalid : true = false := by decide",
        "theorem invalid : Not (2 = 2) := by decide",
        "theorem invalid : Not (true = true) := by decide",
        "theorem invalid (a b : Nat) : a = b := by decide",
        "def invalid : Decidable (2 = 3) := Decidable.isTrue (Eq.refl 2)",
        "def invalid : Decidable (2 = 2) := Decidable.isFalse (fun h => h)",
        "def invalid : Bool := decide (1 : Prop)",
    ] {
        let result = engine.check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits),
        );
        assert!(result.is_err(), "accepted invalid source: {source}");
        assert_eq!(engine.logical_root(&KVMap::new()), before, "{source}");
    }
}
#[test]
fn equality_deciders_are_safe_definitions_not_axioms_or_opaque_oracles() {
    let (engine, _) = engine();
    for name in [
        "Bool.decEq",
        "Nat.decEq",
        "instDecidableEqBool",
        "instDecidableEqNat",
    ] {
        assert!(
            matches!(
                engine
                    .environment()
                    .find(&Name::from_components(name.split('.'))),
                Some(ConstantInfo::Defn(_))
            ),
            "{name} must have an admitted implementation"
        );
    }
}
