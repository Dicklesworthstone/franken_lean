//! Partial self headers constrain inferred results before tactic alternatives run.
//! These tests do not require an installed Reference or imported .olean files.
#![forbid(unsafe_code)]
use fln::{
    Budget, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap, Name, SourceCheckLimits,
};
use fln_env::constants::{ConstantInfo, DefinitionSafety};
use std::sync::OnceLock;

fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}

fn engine() -> Engine {
    static SEED: OnceLock<Engine> = OnceLock::new();
    SEED.get_or_init(|| {
        Engine::with_source_seed(limits())
            .unwrap()
            .into_complete()
            .unwrap()
    })
    .clone()
}

fn check(base: &Engine, source: &str) -> Engine {
    base.check_source_files(
        &[source.as_bytes()],
        &KVMap::new(),
        SourceCheckLimits::new(limits()),
    )
    .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
    .into_complete()
    .expect("both checkers answered")
    .engine
}

fn values(base: &Engine, source: &str) -> Vec<String> {
    let batch = base
        .execute_source_definitions(
            &[source.as_bytes()],
            &KVMap::new(),
            EngineExecutionLimits::new(limits().kernel),
        )
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .expect("native execution completed");
    batch
        .source_evaluation_indices
        .iter()
        .map(|index| {
            let execution = &batch.executions[*index];
            let fln::VmExit::Returned(value) = &execution.exit else {
                panic!("unexpected exit: {:?}", execution.exit);
            };
            fln_vm::interpreter::nat_decimal(&value.value).expect("Nat result")
        })
        .collect()
}

fn refuses(base: &Engine, source: &str, label: &str) {
    let root = base.logical_root(&KVMap::new());
    assert!(
        base.check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        )
        .is_err(),
        "accepted {source}"
    );
    assert_eq!(base.logical_root(&KVMap::new()), root);
    assert!(
        !base
            .environment()
            .contains(&Name::from_components(label.split('.')))
    );
}

#[test]
fn leading_lambdas_and_function_valued_results_keep_their_telescope() {
    assert_eq!(
        values(
            &engine(),
            r#"
partial def lambda : Nat -> Nat := fun n => if n == 0 then 7 else lambda (n - 1) + 1
partial def higher (n : Nat) : Nat -> Nat := fun k => if n == 0 then k else higher (n - 1) (k + 1)
partial def pick : (A : Type) -> A -> Nat -> A := fun A x n => if n == 0 then x else pick A x (n - 1)
#eval lambda 3
#eval higher 4 20
#eval pick Nat 42 3
"#
        ),
        ["10", "24", "42"]
    );
}

#[test]
fn recursive_names_are_available_before_tactic_alternative_selection() {
    assert_eq!(
        values(
            &engine(),
            "partial def chosen (n : Nat) : Nat := by first | exact (if n == 0 then 7 else chosen (n - 1) + 1) | exact 99\n#eval chosen 4\n",
        ),
        ["11"]
    );
    let base = check(
        &engine(),
        "partial def discarded (n : Nat) : Nat := by first | exact (let unused := discarded n; true) | exact 42\n",
    );
    assert!(
        matches!(base.environment().find(&Name::from_components(["discarded"])), Some(ConstantInfo::Defn(value)) if value.safety == DefinitionSafety::Safe)
    );
    assert!(
        !base
            .environment()
            .contains(&Name::from_components(["discarded", "_unsafe_rec"]))
    );
    assert_eq!(values(&base, "#eval discarded 3\n"), ["42"]);
}

#[test]
fn local_structural_recursion_and_where_helpers_capture_partial_self() {
    assert_eq!(
        values(
            &engine(),
            r#"
partial def nested (n : Nat) : Nat :=
  let rec inner (k : Nat) : Nat := match k with
    | .zero => if n == 0 then 2 else nested (n - 1)
    | .succ j => inner j + 1
  inner 3
partial def helper (n : Nat) : Nat := if n == 0 then 5 else go (n - 1)
where go (k : Nat) : Nat := helper k + 1
#eval nested 2
#eval helper 3
"#
        ),
        ["11", "8"]
    );
}

#[test]
fn inferred_results_are_constrained_by_the_selected_body_not_a_fallback() {
    assert_eq!(
        values(
            &engine(),
            r#"
partial def inferred (n : Nat) := if n == 0 then 6 else inferred (n - 1) + 1
partial def generic {A : Type} (x : A) (n : Nat) := if n == 0 then x else generic x (n - 1)
partial def function := fun (n : Nat) => if n == 0 then 9 else function (n - 1) + 1
partial def literal := 41
#eval inferred 3
#eval generic 37 4
#eval function 2
#eval literal
"#
        ),
        ["9", "37", "11", "41"]
    );
    for source in [
        "partial def bad (n : Nat) := bad n",
        "partial def bad : False := by assumption",
    ] {
        refuses(&engine(), source, "bad");
    }
}

#[test]
fn higher_order_self_references_keep_the_actual_recursive_function() {
    assert_eq!(
        values(
            &engine(),
            r#"
def call (f : Nat -> Nat) (n : Nat) : Nat := f n
partial def callback (n : Nat) : Nat := if n == 0 then 3 else call callback (n - 1) + 1
section
variable (step : Nat)
partial def captured (n : Nat) : Nat := if n == 0 then step else call captured (n - 1) + step
end
#eval callback 4
#eval captured 2 3
"#
        ),
        ["7", "8"]
    );
}

#[test]
fn explicit_lambda_domains_see_the_registered_partial_self() {
    assert_eq!(
        values(
            &engine(),
            r#"
partial def typed (n : Nat) : Nat -> Nat :=
  fun (x : (let unused := typed n; Nat)) => if n == 0 then x else typed (n - 1) (x + 1)
#eval typed 3 8
"#
        ),
        ["11"]
    );
}

#[test]
fn infinite_partial_execution_stops_with_a_resource_nonanswer() {
    let base = engine();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    let source = "partial def loop (n : Nat) : Nat := loop (n + 1)\n#eval loop 0\n";
    let mut bounded = EngineExecutionLimits::new(limits().kernel);
    bounded.vm.max_steps = 100;
    assert!(matches!(
        base.execute_source_definitions(&[source.as_bytes()], &options, bounded)
            .unwrap(),
        fln::Outcome::Inconclusive(_)
    ));
    assert_eq!(base.logical_root(&options), root);
    assert!(
        !base
            .environment()
            .contains(&Name::from_components(["loop"]))
    );
}

#[test]
fn universe_polymorphism_and_default_shadowing_do_not_capture_the_witness() {
    let base = check(
        &engine(),
        r#"
universe u
partial def retainSort {A : Sort u} (x : A) (n : Nat) : A := if n == 0 then x else retainSort x (n - 1)
partial def shadow (default : Bool) (n : Nat) : Nat := if n == 0 then 8 else shadow default (n - 1)
"#,
    );
    let Some(ConstantInfo::Opaque(logical)) = base
        .environment()
        .find(&Name::from_components(["retainSort"]))
    else {
        panic!("missing polymorphic partial interface");
    };
    let Some(ConstantInfo::Defn(executable)) = base
        .environment()
        .find(&Name::from_components(["retainSort", "_unsafe_rec"]))
    else {
        panic!("missing polymorphic executable");
    };
    assert_eq!(logical.base.level_params, [Name::from_components(["u"])]);
    assert_eq!(logical.base.level_params, executable.base.level_params);
    assert_eq!(logical.base.type_, executable.base.type_);
    assert_eq!(
        values(&base, "#eval retainSort 23 4\n#eval shadow true 4\n"),
        ["23", "8"]
    );
}
