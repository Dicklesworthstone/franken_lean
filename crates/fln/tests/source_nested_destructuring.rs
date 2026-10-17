//! Ordinary destructuring lets must compose with lambdas and term arguments.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, SourceCheckLimits};

const PROD: &str = "structure Prod (A B : Type) where\n  fst : A\n  snd : B\n";
const PAIR: &str = "structure Pair where\n  first : Nat\n  second : Nat\n";
fn limits() -> SourceCheckLimits {
    SourceCheckLimits::new(EngineAdmissionLimits::new(Budget::for_stack_bytes(
        2 * 1024 * 1024,
    )))
}
fn check(source: &str) {
    let source = format!("{PROD}{source}");
    let base = Engine::with_source_seed(limits().admission)
        .unwrap()
        .into_complete()
        .unwrap();
    base.check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .unwrap();
}
#[test]
fn ordinary_record_lets_compose_with_lambda_bodies() {
    check(&format!(
        "{PAIR}def total : Pair -> Nat := fun p => let ⟨x, y⟩ := p; x + y\ntheorem result : total ⟨7, 8⟩ = 15 := by rfl"
    ));
}
#[test]
fn tuple_lets_compose_with_ordinary_application_arguments() {
    check(
        "def idNat (n : Nat) := n\ndef total (p : Nat × Nat) : Nat := idNat (let (x, y) := p; x + y)\ntheorem result : total (7, 8) = 15 := by rfl",
    );
}
#[test]
fn nested_patterns_annotations_and_inner_aliases_keep_their_scopes() {
    check(
        "def sum : Nat × (Nat × Nat) -> Nat := fun p => let (a, (b, c)) : Nat × (Nat × Nat) := p; a + b + c\ntheorem result : sum (1, (2, 3)) = 6 := by rfl",
    );
    check(&format!(
        "{PAIR}def sum : Pair -> Nat := fun p => let ⟨x, whole@y⟩ := p; x + whole\ntheorem result : sum ⟨7, 8⟩ = 15 := by rfl"
    ));
    check(&format!(
        "{PAIR}def sum : Pair -> Nat := fun p => let (Pair.mk x y) := p; x + y\ntheorem result : sum ⟨7, 8⟩ = 15 := by rfl"
    ));
}
#[test]
fn source_order_and_shadowing_are_preserved_across_nested_destructuring() {
    check(
        "def swap (p : Nat × Nat) : Nat × Nat := (fun (x y : Nat) => let (y, x) := p; (x, y)) 80 90\ntheorem result : swap (7, 8) = (8, 7) := by rfl",
    );
    check(
        "def use : Nat × Nat -> Nat := fun p => let (x, y) := p; let (x, z) := (y, x); x + z\ntheorem result : use (7, 8) = 15 := by rfl",
    );
}
#[test]
fn refutable_ill_typed_and_escaping_nested_lets_are_rejected_atomically() {
    let base = Engine::with_source_seed(limits().admission)
        .unwrap()
        .into_complete()
        .unwrap();
    let options = KVMap::new();
    let before = base.logical_root(&options);
    for source in [
        "def bad : Nat × Nat -> Nat := fun p => let (0, x) := p; x".to_owned(),
        "def bad : Nat := (fun (p : Nat × Nat) => let (0, x) := p; x) (0, 7)".to_owned(),
        "def bad : Nat × Nat -> Nat := fun p => let (x, x) := p; x".to_owned(),
        format!("{PAIR}def bad : Pair -> Nat := fun p => let ⟨x, y⟩ : Bool := p; x"),
        "def bad (p : Nat × Nat) : Nat := let n := (fun (q : Nat × Nat) => let (x, y) := q; x) p; x".to_owned(),
    ] {
        let source = format!("{PROD}{source}");
        let error = base.check_source_files(&[source.as_bytes()], &options, limits()).unwrap_err();
        assert!(!format!("{error:?}").contains("Frontend(Parse("), "negative did not parse: {source}\n{error:?}");
        assert_eq!(error.disposition().2, 1, "{error:?}");
        assert_eq!(base.logical_root(&options), before);
    }
    base.check_source_files(
        &[b"theorem recovery (n : Nat) : n = n := by rfl"],
        &options,
        limits(),
    )
    .unwrap()
    .into_complete()
    .unwrap();
}

#[test]
fn nested_destructuring_executes_the_checked_term() {
    use fln::{EngineExecutionLimits, SourceCommandOutput, VmExit};
    let limits = EngineExecutionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let base = Engine::with_source_seed(limits.admission())
        .unwrap()
        .into_complete()
        .unwrap();
    let source = format!(
        "{PROD}def total : Nat × Nat -> Nat := fun p => let (x, y) := p; x + y\n#eval total (7, 8)\n#eval total (40, 2)"
    );
    let out = base
        .execute_source_commands_with_checks(source.as_bytes(), &KVMap::new(), limits)
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(out.outputs.len(), 2);
    for (event, expected) in out.outputs.iter().zip(["15", "42"]) {
        let SourceCommandOutput::Evaluation {
            execution_index, ..
        } = event
        else {
            panic!("expected evaluation")
        };
        let VmExit::Returned(value) = &out.batch.executions[*execution_index].exit else {
            panic!("expected value")
        };
        assert_eq!(
            fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
            Some(expected)
        );
    }
}
