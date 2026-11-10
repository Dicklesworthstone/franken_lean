//! Explicit records with generic fields specialize at known checked constructors.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap, Outcome, VmExit};

fn limits() -> EngineExecutionLimits {
    EngineExecutionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}

fn engine() -> Engine {
    Engine::with_source_seed(EngineAdmissionLimits::new(limits().kernel))
        .unwrap()
        .into_complete()
        .unwrap()
}

fn run(source: &str, expected: &str) -> u64 {
    let report = engine()
        .execute_source_definitions(&[source.as_bytes()], &KVMap::new(), limits())
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .unwrap();
    let VmExit::Returned(result) = &report.executions.last().unwrap().exit else {
        panic!("generic record evaluation did not return");
    };
    assert_eq!(
        fln::nat_decimal(&result.value).as_deref(),
        Some(expected),
        "{source}"
    );
    result.usage.steps
}

const IDENTITY: &str = r#"
structure GenericFunctions where
  convert : (A : Type) -> A -> A
def useGeneric (functions : GenericFunctions) : Nat :=
  functions.convert Nat 36 + String.length (functions.convert String "answer")
def useGenericBool (functions : GenericFunctions) : Nat :=
  if functions.convert Bool true then 42 else 0
def useGenericCallback (functions : GenericFunctions) : Nat :=
  let next : Nat -> Nat := functions.convert (Nat -> Nat) (fun n => n + 1)
  next 41
"#;

#[test]
fn explicit_generic_record_consumers_execute_at_distinct_runtime_types() {
    // The source command stream must admit these consumers as templates;
    // eager compilation used to fail before it reached the concrete #eval.
    for consumer in ["useGeneric", "useGenericBool", "useGenericCallback"] {
        run(
            &format!("{IDENTITY}#eval {consumer} {{ convert := fun A x => x }}"),
            "42",
        );
    }
}

const AMOUNT: &str = r#"
structure GenericAmount where
  amount : (A : Type) -> A -> Nat
def recordWork (n : Nat) : Nat :=
  match n with | 0 => 0 | k + 1 => recordWork k + 1
def makeAmount (n : Nat) : GenericAmount :=
  let paid := recordWork n
  { amount := fun A x => paid }
def amountOnce (record : GenericAmount) : Nat := record.amount Nat 0
def amountTwice (record : GenericAmount) : Nat :=
  record.amount Nat 0 + record.amount String "λ"
def localAmountOnce (n : Nat) : Nat :=
  let record := makeAmount n
  record.amount Nat 0
def localAmountTwice (n : Nat) : Nat :=
  let record := makeAmount n
  record.amount Nat 0 + record.amount String "λ"
"#;

#[test]
fn computed_record_captures_execute_once_across_consumers_and_local_aliases() {
    let mut deltas = Vec::new();
    for (body, expected) in [
        ("amountOnce (makeAmount 30)", "30"),
        ("amountTwice (makeAmount 30)", "60"),
        ("localAmountOnce 30", "30"),
        ("localAmountTwice 30", "60"),
    ] {
        let busy = run(&format!("{AMOUNT}#eval {body}"), expected);
        let idle = run(&format!("{AMOUNT}#eval {}", body.replace("30", "0")), "0");
        deltas.push(busy - idle);
    }
    assert!(deltas[0] > 30, "a live record capture did not execute: {deltas:?}");
    assert!(
        deltas.iter().all(|delta| *delta == deltas[0]),
        "record construction was duplicated at a second method use: {deltas:?}"
    );
}

const PICKER: &str = r#"
structure GenericPicker where
  pick : (A : Type) -> A -> A -> A
def pickerWork (n : Nat) : Nat :=
  match n with | 0 => 0 | k + 1 => pickerWork k + 1
def makePicker (n : Nat) : GenericPicker :=
  let choice := pickerWork n
  { pick := fun A x y => match choice with | 0 => x | _ + 1 => y }
def scopedPick (before : String) (cost : Nat) (after : String) : Nat :=
  let record := makePicker cost
  let chosen := record.pick String (before ++ "λ") (after ++ "🙂")
  String.length chosen + record.pick Nat 39 40
"#;

#[test]
fn explicit_record_prefixes_keep_outer_captures_and_owned_unicode_values() {
    run(&format!("{PICKER}#eval scopedPick \"abc\" 0 \"ω\""), "43");
    run(&format!("{PICKER}#eval scopedPick \"abc\" 3 \"ω\""), "42");
    run(
        &format!(
            "{PICKER}#eval String.length ((makePicker 3).pick String \"wrong\" (\"a\" ++ \"λ🙂\"))"
        ),
        "3",
    );
}

#[test]
fn generic_record_artifacts_replay_and_budget_stops_leave_clean_retries() {
    let base = engine();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    let source = format!("{AMOUNT}#eval localAmountTwice 30");
    let execute = || {
        base.execute_source_definitions(&[source.as_bytes()], &options, limits())
            .unwrap()
            .into_complete()
            .unwrap()
    };
    let first = execute();
    let execution = first.executions.last().unwrap();
    let VmExit::Returned(returned) = &execution.exit else {
        panic!("generic record evaluation did not return");
    };
    assert_eq!(fln::nat_decimal(&returned.value).as_deref(), Some("60"));
    let replay = fln::execute_flbc_artifact(
        &execution.flbc_artifact,
        &options,
        Default::default(),
    )
    .unwrap()
    .into_complete()
    .unwrap();
    let VmExit::Returned(returned) = replay else {
        panic!("generic record artifact did not return");
    };
    assert_eq!(fln::nat_decimal(&returned.value).as_deref(), Some("60"));
    let mut bounded = limits();
    bounded.vm.max_steps = 1;
    assert!(matches!(
        base.execute_source_definitions(&[source.as_bytes()], &options, bounded)
            .unwrap(),
        Outcome::Inconclusive(_)
    ));
    bounded = limits();
    bounded.ingress.max_nodes = 1;
    assert!(
        base.execute_source_definitions(&[source.as_bytes()], &options, bounded)
            .is_err()
    );
    assert_eq!(base.logical_root(&options), root);
    let retried = execute();
    assert_eq!(
        execution.flbc_artifact,
        retried.executions.last().unwrap().flbc_artifact
    );
    assert_eq!(first.result_logical_root, retried.result_logical_root);
    assert_eq!(base.logical_root(&options), root);
}

#[test]
fn explicit_record_specialization_preserves_factory_consumer_and_projection_authority() {
    let options = KVMap::new();
    let clean = engine()
        .check_source_files(
            &[AMOUNT.as_bytes()],
            &options,
            fln::SourceCheckLimits::new(limits().admission()),
        )
        .unwrap()
        .into_complete()
        .unwrap()
        .engine;
    for declaration in ["makeAmount", "amountOnce", "GenericAmount.amount"] {
        let decorated = Engine::from_environment(
            fln_elab::externs::register(
                clean.environment(),
                &fln::Name::from_components(declaration.split('.')),
                vec![fln_elab::externs::ExternEntry::Standard {
                    backend: fln::Name::from_components(["all"]),
                    symbol: "foreign_generic_record_execution".to_owned(),
                }],
            )
            .unwrap(),
        );
        let root = decorated.logical_root(&options);
        let mut error = decorated
            .execute_source_definitions(
                &[b"#eval amountOnce (makeAmount 30)"],
                &options,
                limits(),
            )
            .expect_err("a selected foreign record cannot use its logical body");
        while let fln::EngineExecutionError::BatchCommand { error: inner, .. } = error {
            error = *inner;
        }
        assert!(
            matches!(error, fln::EngineExecutionError::Ingress(_)),
            "{declaration}: {error:?}"
        );
        assert_eq!(decorated.logical_root(&options), root);
    }
}

#[test]
fn a_dynamic_generic_record_method_retains_a_typed_refusal() {
    let source = r#"
structure DynamicRecord where
  amount : (A : Type) -> A -> Nat
def chooseRecordMethod (flag : Bool) : (A : Type) -> A -> Nat :=
  if flag then (fun A x => 41) else (fun A x => 42)
def makeDynamicRecord (flag : Bool) : DynamicRecord :=
  { amount := chooseRecordMethod flag }
def consumeDynamicRecord (record : DynamicRecord) : Nat := record.amount Nat 0
"#;
    let options = KVMap::new();
    let base = engine()
        .check_source_files(
            &[source.as_bytes()],
            &options,
            fln::SourceCheckLimits::new(limits().admission()),
        )
        .unwrap()
        .into_complete()
        .unwrap()
        .engine;
    let root = base.logical_root(&options);
    let mut error = base
        .execute_source_definitions(
            &[b"#eval consumeDynamicRecord (makeDynamicRecord true)"],
            &options,
            limits(),
        )
        .expect_err("an unknown generic method must not acquire a guessed runtime ABI");
    while let fln::EngineExecutionError::BatchCommand { error: inner, .. } = error {
        error = *inner;
    }
    assert!(
        matches!(
            error,
            fln::EngineExecutionError::Ingress(
                fln_comp::ingress::IngressError::UnsupportedCallableSignature { .. }
            )
        ),
        "{error:?}"
    );
    assert_eq!(base.logical_root(&options), root);
}
