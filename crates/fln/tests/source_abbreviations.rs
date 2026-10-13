//! Real source abbreviations retain their kernel hints and scoped signatures.
#![forbid(unsafe_code)]

use fln::{
    Budget, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap,
    SourceCommandBatchExecution, VmExit,
};
use fln_core::name::Name;
use fln_env::constants::{ConstantInfo, DefinitionSafety, DefinitionVal, ReducibilityHints};

fn name(text: &str) -> Name {
    Name::from_components(text.split('.'))
}

fn budget() -> Budget {
    Budget::for_stack_bytes(2 * 1024 * 1024)
}

fn engine() -> Engine {
    Engine::with_source_seed(EngineAdmissionLimits::new(budget()))
        .unwrap()
        .into_complete()
        .unwrap()
}

fn execute(engine: &Engine, source: &str) -> SourceCommandBatchExecution {
    engine
        .execute_source_commands_with_checks(
            source.as_bytes(),
            &KVMap::new(),
            EngineExecutionLimits::new(budget()),
        )
        .unwrap_or_else(|error| panic!("{source}: {error:?}"))
        .into_complete()
        .expect("source declarations must pass both checkers and execute")
}

fn abbreviation(engine: &Engine, text: &str) -> DefinitionVal {
    let declaration = engine.environment().find(&name(text)).unwrap();
    let ConstantInfo::Defn(definition) = declaration else {
        panic!("{text} must be an admitted definition");
    };
    assert_eq!(definition.hints, ReducibilityHints::Abbrev);
    assert_eq!(definition.safety, DefinitionSafety::Safe);
    assert!(!definition.base.type_.has_fvar());
    assert!(!definition.base.type_.has_loose_bvars());
    assert!(!definition.value.has_fvar());
    assert!(!definition.value.has_loose_bvars());
    definition.clone()
}

fn natural_results(result: &SourceCommandBatchExecution) -> Vec<String> {
    result
        .batch
        .source_evaluation_indices
        .iter()
        .map(|&index| {
            let VmExit::Returned(value) = &result.batch.executions[index].exit else {
                panic!("evaluation must return");
            };
            fln_vm::interpreter::nat_decimal(&value.value).expect("a Nat result")
        })
        .collect()
}

#[test]
fn namespaced_type_abbreviations_feed_inductive_headers_and_native_functions() {
    // This exact header is used by the pin's Lean.Grind.AC.Expr source.
    let result = execute(
        &engine(),
        "namespace Lean.Grind.AC
abbrev Var := Nat
inductive Expr where
  | var (x : Var)
  | op (lhs rhs : Expr)
abbrev next (x : Var) : Var := x + 1
theorem stored : Expr.var 7 = Expr.var 7 := by rfl
end Lean.Grind.AC
#eval Lean.Grind.AC.next 41",
    );
    abbreviation(&result.batch.engine, "Lean.Grind.AC.Var");
    abbreviation(&result.batch.engine, "Lean.Grind.AC.next");
    assert!(
        result
            .batch
            .engine
            .environment()
            .contains(&name("Lean.Grind.AC.Expr"))
    );
    assert!(!result.batch.engine.environment().contains(&name("Var")));
    assert_eq!(natural_results(&result), ["42"]);
}

#[test]
fn abbreviation_signatures_preserve_explicit_universes_and_used_section_variables() {
    let result = execute(
        &engine(),
        "universe u
abbrev Identity.{v} {A : Sort v} (value : A) : A := value
section
variable {A : Type u} (initial : A)
abbrev captured := initial
end
#eval Identity (captured 42)",
    );
    let identity = abbreviation(&result.batch.engine, "Identity");
    let captured = abbreviation(&result.batch.engine, "captured");
    assert_eq!(identity.base.level_params, [name("v")]);
    assert_eq!(captured.base.level_params, [name("u")]);
    assert!(!result.batch.engine.environment().contains(&name("initial")));
    assert_eq!(natural_results(&result), ["42"]);
}

#[test]
fn class_abbreviations_unfold_for_instance_search_and_failed_bodies_do_not_publish() {
    let base = engine();
    let before = base.logical_root(&KVMap::new());
    assert!(
        base.execute_source_commands_with_checks(
            b"abbrev leaked := Nat\nabbrev wrong : Nat := false",
            &KVMap::new(),
            EngineExecutionLimits::new(budget()),
        )
        .is_err()
    );
    assert_eq!(base.logical_root(&KVMap::new()), before);
    assert!(!base.environment().contains(&name("leaked")));
    let result = execute(
        &base,
        "class Selection where
  value : Nat
instance chosen : Selection := Selection.mk 42
abbrev SelectionAlias := Selection
def selected [SelectionAlias] : Nat := Selection.value
#eval selected",
    );
    abbreviation(&result.batch.engine, "SelectionAlias");
    assert_eq!(natural_results(&result), ["42"]);
}
