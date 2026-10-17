//! Named patterns retain their checked receiver in lambda and ordinary let binders.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, SourceCheckLimits};

const PAIR: &str = "structure Pair where\n  first : Nat\n  second : Nat\n";
fn check(source: &str) {
    let admission = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    Engine::with_source_seed(admission)
        .unwrap()
        .into_complete()
        .unwrap()
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(admission),
        )
        .unwrap_or_else(|e| panic!("{source}\n{e:?}"))
        .into_complete()
        .unwrap();
}

#[test]
fn named_lambda_binders_keep_whole_receivers() {
    check(&format!(
        "{PAIR}def total : Pair -> Nat := fun whole@⟨x, y⟩ => whole.first + y\ntheorem result : total ⟨7, 8⟩ = 15 := by rfl"
    ));
}
#[test]
fn grouped_named_lambda_binders_keep_whole_receivers() {
    check(&format!(
        "{PAIR}def keep : Pair -> Pair := fun (whole@⟨x, y⟩) => whole\ntheorem result : (keep ⟨7, 8⟩).second = 8 := by rfl"
    ));
}
#[test]
fn named_ordinary_let_binders_keep_whole_receivers() {
    check(&format!(
        "{PAIR}def total (p : Pair) : Nat := let whole@⟨x, y⟩ := p; whole.first + y\ntheorem result : total ⟨7, 8⟩ = 15 := by rfl"
    ));
}
#[test]
fn named_ordinary_let_inside_match_keeps_whole_receiver() {
    check(&format!(
        "{PAIR}def total (n : Nat) (p : Pair) : Nat := match n with | .zero => let whole@⟨x, y⟩ := p; whole.first + y | .succ _ => 0\ntheorem result : total 0 ⟨7, 8⟩ = 15 := by rfl"
    ));
}

#[test]
fn named_lets_work_inside_lambdas_and_term_arguments() {
    check(&format!(
        "{PAIR}def total : Pair -> Nat := fun p => let whole@⟨x, y⟩ := p; whole.first + y\ntheorem result : total ⟨7, 8⟩ = 15 := by rfl"
    ));
    check(&format!(
        "{PAIR}def idNat (n : Nat) := n\ndef total (p : Pair) : Nat := idNat (let whole@⟨x, y⟩ := p; whole.first + y)\ntheorem result : total ⟨7, 8⟩ = 15 := by rfl"
    ));
}
#[test]
fn named_lambdas_preserve_the_complete_parameter_telescope() {
    check(
        "def first : {A : Type} -> A -> A -> A := fun {A} whole@_ (other : A) => whole\ntheorem result : first 7 8 = 7 := by rfl",
    );
    check(
        "def second (whole : Type) : whole -> whole -> whole := fun whole@_ (other : whole) => other\ntheorem result : second Nat 7 8 = 8 := by rfl",
    );
}
#[test]
fn named_let_type_annotations_and_simultaneous_aliases_are_preserved() {
    check(&format!(
        "{PAIR}def keep (p : Pair) : Pair := let all@(Pair.mk x y) : Pair := p; all\ntheorem result : (keep ⟨7, 8⟩).second = 8 := by rfl"
    ));
    check(&format!(
        "{PAIR}def total (p : Pair) : Nat := let x@(Pair.mk y z) := p; let y := x.first; y + z\ntheorem result : total ⟨7, 8⟩ = 15 := by rfl"
    ));
}

fn reject(source: &str) {
    let admission = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let base = Engine::with_source_seed(admission)
        .unwrap()
        .into_complete()
        .unwrap();
    let options = KVMap::new();
    let before = base.logical_root(&options);
    let error = base
        .check_source_files(
            &[source.as_bytes()],
            &options,
            SourceCheckLimits::new(admission),
        )
        .unwrap_err();
    assert!(
        !format!("{error:?}").contains("Frontend(Parse("),
        "negative did not parse: {source}\n{error:?}"
    );
    assert_eq!(error.disposition().2, 1, "{error:?}");
    assert_eq!(base.logical_root(&options), before);
    base.check_source_files(
        &[b"theorem recovery (n : Nat) : n = n := by rfl"],
        &options,
        SourceCheckLimits::new(admission),
    )
    .unwrap()
    .into_complete()
    .unwrap();
}

#[test]
fn named_binder_payloads_and_annotations_remain_checked() {
    for source in [
        "def bad : Nat -> Nat := fun whole@0 => whole".to_owned(),
        "def bad : Nat := let whole@0 := 0; whole".to_owned(),
        format!("{PAIR}def bad : Pair -> Nat := fun whole@(Pair.mk whole y) => 0"),
        format!("{PAIR}def bad (p : Pair) : Nat := let whole@(Pair.mk x y) : Bool := p; 0"),
        format!("{PAIR}def bad (p : Pair) : Nat := let result := (let whole@⟨x,y⟩ := p; x); whole"),
        format!("{PAIR}def bad : Pair -> Nat -> Nat := fun whole@⟨x,y⟩ (other : whole) => 0"),
        format!("{PAIR}def bad : Pair -> Nat := fun whole@⟨x,y⟩ => (whole : Nat)"),
    ] {
        reject(&source);
    }
}

#[test]
fn named_lambda_scope_and_expected_function_types_are_preserved() {
    check(&format!(
        "{PAIR}def apply (f : Pair -> Nat) (p : Pair) : Nat := f p\ntheorem result : apply (fun whole@⟨x,y⟩ => whole.first + y) ⟨7,8⟩ = 15 := by rfl"
    ));
    check(&format!(
        "{PAIR}def pick : Pair -> Pair -> Nat := fun whole@⟨a,b⟩ whole@⟨c,d⟩ => whole.first + b\ntheorem result : pick ⟨1,2⟩ ⟨7,8⟩ = 9 := by rfl"
    ));
    check(
        "def identity (A : Type) : A -> A := fun whole@part => part\ntheorem result : identity Nat 7 = 7 := by rfl",
    );
}

#[test]
fn named_binding_results_execute_after_both_checkers_admit() {
    use fln::{EngineExecutionLimits, SourceCommandOutput, VmExit};
    let limits = EngineExecutionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let base = Engine::with_source_seed(limits.admission())
        .unwrap()
        .into_complete()
        .unwrap();
    let source = format!(
        "{}\n#eval namedTotal ⟨7,8⟩\n#eval namedTotal ⟨40,2⟩",
        include_str!("../../fln-parse/tests/fixtures/named_binder_forms.lean")
    );
    let result = base
        .execute_source_commands_with_checks(source.as_bytes(), &KVMap::new(), limits)
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(result.outputs.len(), 2);
    for (event, expected) in result.outputs.iter().zip(["15", "42"]) {
        let SourceCommandOutput::Evaluation {
            execution_index, ..
        } = event
        else {
            panic!("expected evaluation")
        };
        let VmExit::Returned(value) = &result.batch.executions[*execution_index].exit else {
            panic!("expected value")
        };
        assert_eq!(
            fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
            Some(expected)
        );
    }
}
