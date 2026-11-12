//! Actual source admission, static dictionaries, native compilation and Golem.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap, VmExit};

fn limits() -> EngineExecutionLimits {
    EngineExecutionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}
fn engine() -> Engine {
    Engine::with_source_seed(EngineAdmissionLimits::new(limits().kernel))
        .unwrap()
        .into_complete()
        .unwrap()
}
fn execute(source: &str, expected: &str) -> u64 {
    let run = engine()
        .execute_source_definitions(&[source.as_bytes()], &KVMap::new(), limits())
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .unwrap();
    let VmExit::Returned(value) = &run.executions.last().unwrap().exit else {
        panic!("execution did not return");
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
        Some(expected),
        "{source}"
    );
    value.usage.steps
}

fn strict_dictionary(source: &str, caller: &str) {
    let base = engine();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    let source = |cost| format!("{source}\n#eval {caller} {cost} {{ value := 42 }}");
    let run = |cost| {
        base.execute_source_definitions(&[source(cost).as_bytes()], &options, limits())
            .unwrap_or_else(|error| panic!("{}\n{error:?}", source(cost)))
            .into_complete()
            .expect("the complete dictionary has a uniform executable layout")
    };
    let idle = run(0);
    let busy = run(30);
    let mut steps = Vec::new();
    for report in [&idle, &busy] {
        let execution = report.executions.last().unwrap();
        let VmExit::Returned(value) = &execution.exit else {
            panic!("dictionary method did not return");
        };
        assert_eq!(fln::nat_decimal(&value.value).as_deref(), Some("42"));
        steps.push(value.usage.steps);
        let replay =
            fln::execute_flbc_artifact(&execution.flbc_artifact, &options, Default::default())
                .unwrap()
                .into_complete()
                .unwrap();
        let VmExit::Returned(value) = replay else {
            panic!("dictionary artifact did not return");
        };
        assert_eq!(fln::nat_decimal(&value.value).as_deref(), Some("42"));
    }
    assert!(
        steps[1] > steps[0] + 30,
        "the unused dictionary field must still execute: {steps:?}"
    );
    let mut bounded = limits();
    bounded.vm.max_steps = steps[0];
    assert!(matches!(
        base.execute_source_definitions(&[source(30).as_bytes()], &options, bounded)
            .unwrap(),
        fln::Outcome::Inconclusive(_)
    ));
    assert_eq!(base.logical_root(&options), root);
    let retry = run(30);
    assert_eq!(
        busy.executions.last().unwrap().flbc_artifact,
        retry.executions.last().unwrap().flbc_artifact
    );
    assert_eq!(busy.result_logical_root, retry.result_logical_root);
    assert_eq!(base.logical_root(&options), root);
}

const ECHO: &str = r#"
class Echo (K : Type) where
  echo : {A : Type} -> A -> A
instance echoFor (K : Type) : Echo K := { echo := fun a => a }
"#;

const INDEXED: &str = r#"
structure IndexedBox (A : Type) (n : Nat) where
  value : A
class GetAt (C A : Type) (valid : C -> Nat -> Prop) where
  get : (xs : C) -> (i : Nat) -> valid xs i -> A
instance makeGetAt (n : Nat) {A : Type} :
    GetAt (IndexedBox A n) A (fun _ _ => n = n) :=
  { get := fun xs _ _ => xs.value }
"#;

#[test]
fn inferred_parameterized_dictionaries_can_contain_polymorphic_methods() {
    execute(&format!("{ECHO}#eval Echo.echo (K := Nat) 42"), "42");
    execute(
        &format!("{ECHO}#eval if Echo.echo (K := Bool) true then 42 else 0"),
        "42",
    );
    execute(
        &format!("{ECHO}#eval String.length (Echo.echo (K := Nat) \"abcdef\")"),
        "6",
    );
}

#[test]
fn scoped_polymorphic_dictionaries_cross_global_consumers_without_losing_captures() {
    let source = r#"
class PickAt (n : Nat) where
  pick : {A : Type} -> A -> A -> A
instance pickAt (n : Nat) : PickAt n :=
  { pick := fun x y => match n with | 0 => x | _ + 1 => y }
def consume {n : Nat} {A : Type} [PickAt n] (x y : A) : A :=
  PickAt.pick (n := n) x y
def forwardNat (n : Nat) : Nat := consume (n := n) 41 42
def forwardBool (n : Nat) : Bool := consume (n := n) false true
def forwardString (n : Nat) : String := consume (n := n) "a" "xyz"
"#;
    for (body, expected) in [
        ("forwardNat 0", "41"),
        ("forwardNat 1", "42"),
        ("if forwardBool 0 then 9 else 42", "42"),
        ("if forwardBool 1 then 42 else 9", "42"),
        ("String.length (forwardString 1)", "3"),
    ] {
        execute(&format!("{source}#eval {body}"), expected);
    }
}

#[test]
fn scoped_polymorphic_dictionaries_can_capture_fields_of_bound_records() {
    let source = r#"
structure ProjectionSettings where
  choice : Nat
structure ProjectionWrapper where
  settings : ProjectionSettings
class ProjectedPick (n : Nat) where
  pick : {A : Type} -> A -> A -> A
instance projectedPick (n : Nat) : ProjectedPick n :=
  { pick := fun x y => match n with | 0 => x | _ + 1 => y }
def consumeProjected {n : Nat} {A : Type} [ProjectedPick n] (x y : A) : A :=
  ProjectedPick.pick (n := n) x y
def forwardProjected (settings : ProjectionSettings) : Nat :=
  consumeProjected (n := settings.choice) 41 42
def forwardNestedProjection (wrapper : ProjectionWrapper) : Nat :=
  consumeProjected (n := wrapper.settings.choice) 41 42
"#;
    for (body, expected) in [
        ("forwardProjected (ProjectionSettings.mk 0)", "41"),
        ("forwardProjected (ProjectionSettings.mk 1)", "42"),
        (
            "forwardNestedProjection (ProjectionWrapper.mk (ProjectionSettings.mk 0))",
            "41",
        ),
        (
            "forwardNestedProjection (ProjectionWrapper.mk (ProjectionSettings.mk 1))",
            "42",
        ),
    ] {
        execute(&format!("{source}#eval {body}"), expected);
    }
}

#[test]
fn scoped_projection_inputs_preserve_strict_record_initializers() {
    let source = r#"
structure StrictProjectionSettings where
  choice : Nat
  unused : Nat
class StrictProjectedPick (n : Nat) where
  pick : {A : Type} -> A -> A -> A
instance strictProjectedPick (n : Nat) : StrictProjectedPick n :=
  { pick := fun x y => match n with | 0 => x | _ + 1 => y }
def consumeStrictProjected {n : Nat} [StrictProjectedPick n] : Nat :=
  StrictProjectedPick.pick (n := n) 41 42
def projectionWork (n : Nat) : Nat :=
  match n with | 0 => 0 | k + 1 => projectionWork k + 1
def strictProjection (cost : Nat) : Nat :=
  let settings := StrictProjectionSettings.mk 1 (projectionWork cost)
  consumeStrictProjected (n := settings.choice)
"#;
    let short = execute(&format!("{source}#eval strictProjection 1"), "42");
    let long = execute(&format!("{source}#eval strictProjection 40"), "42");
    assert!(long > short, "the unused record field must still execute");
}

#[test]
fn scoped_dictionary_factories_retain_erased_theorem_applications() {
    let source = r#"
def proofArgumentWork (n : Nat) : Nat :=
  match n with | 0 => 0 | k + 1 => proofArgumentWork k + 1
theorem factoryWitness (unused : Nat) : True := True.intro
class ProofSelected (n : Nat) where
  pick : {A : Type} -> A -> A -> A
  witness : True
instance proofSelected (n : Nat) : ProofSelected n :=
  { pick := fun x y => match n with | 0 => x | _ + 1 => y,
    witness := factoryWitness (proofArgumentWork n) }
def consumeProofSelected {n : Nat} [ProofSelected n] : Nat :=
  ProofSelected.pick (n := n) 41 42
def forwardProofSelected (n : Nat) : Nat := consumeProofSelected (n := n)
"#;
    execute(&format!("{source}#eval forwardProofSelected 0"), "41");
    execute(&format!("{source}#eval forwardProofSelected 1"), "42");
    execute(&format!("{source}#eval forwardProofSelected 40"), "42");
}

#[test]
fn scoped_polymorphic_dictionaries_can_retain_computed_constructor_fields() {
    let source = r#"
class PickAt (n : Nat) where
  pick : {A : Type} -> A -> A -> A
  unused : Nat
def count (n : Nat) : Nat := match n with | 0 => 0 | k + 1 => count k + 1
instance pickAt (n : Nat) : PickAt n :=
  { pick := fun x _ => x, unused := count n }
def consume {n : Nat} {A : Type} [PickAt n] (x y : A) : A :=
  PickAt.pick (n := n) x y
def forward (n : Nat) : Nat := consume (n := n) 42 9
#eval forward 30
"#;
    execute(source, "42");
}

const COMPUTED_AMOUNT: &str = r#"
class RuntimeAmount (n : Nat) where
  amount : {A : Type} -> A -> Nat
  unused : Nat
def amountWork (n : Nat) : Nat := match n with | 0 => 0 | k + 1 => amountWork k + 1
instance runtimeAmount (n : Nat) : RuntimeAmount n :=
  let paid : Nat := amountWork n
  { amount := fun _ => paid, unused := amountWork n }
def amountOnce {n : Nat} [RuntimeAmount n] : Nat :=
  RuntimeAmount.amount (n := n) "λ"
def amountTwice {n : Nat} [RuntimeAmount n] : Nat :=
  RuntimeAmount.amount (n := n) 20 + RuntimeAmount.amount (n := n) "λ"
def forwardAmount (n : Nat) : Nat := amountOnce (n := n)
def forwardAmountTwice (n : Nat) : Nat := amountTwice (n := n)
"#;

#[test]
fn computed_polymorphic_dictionary_captures_run_once_across_method_uses() {
    let program = |caller, cost| format!("{COMPUTED_AMOUNT}\n#eval {caller} {cost}");
    let once =
        execute(&program("forwardAmount", 30), "30") - execute(&program("forwardAmount", 0), "0");
    let twice = execute(&program("forwardAmountTwice", 30), "60")
        - execute(&program("forwardAmountTwice", 0), "0");
    assert!(once > 30, "the live factory capture was not evaluated");
    assert_eq!(twice, once, "the shared factory capture was duplicated");
    execute(
        r#"
class RuntimeChoice (n : Nat) where
  choose : {A : Type} -> A -> A -> A
  unused : Nat
def choiceWork (n : Nat) : Nat := match n with | 0 => 0 | k + 1 => choiceWork k + 1
instance runtimeChoice (n : Nat) : RuntimeChoice n :=
  let selected := choiceWork n
  { choose := fun x y => match selected with | 0 => x | _ + 1 => y,
    unused := choiceWork n }
def chooseValue {n : Nat} {A : Type} [RuntimeChoice n] (x y : A) : A :=
  RuntimeChoice.choose (n := n) x y
def chooseLengths (n : Nat) : Nat :=
  String.length (chooseValue (n := n) "a" "λab") + chooseValue (n := n) 10 39
#eval chooseLengths 30
"#,
        "42",
    );
}

#[test]
fn residual_dictionary_captures_replay_and_recover_after_budget_exhaustion() {
    let base = engine();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    let program = |cost| format!("{COMPUTED_AMOUNT}\n#eval forwardAmount {cost}");
    let run = |cost| {
        base.execute_source_definitions(&[program(cost).as_bytes()], &options, limits())
            .unwrap()
            .into_complete()
            .unwrap()
    };
    let idle = run(0);
    let busy = run(30);
    let VmExit::Returned(idle_value) = &idle.executions.last().unwrap().exit else {
        panic!("idle dictionary did not return");
    };
    let execution = busy.executions.last().unwrap();
    let VmExit::Returned(value) = &execution.exit else {
        panic!("computed dictionary did not return");
    };
    assert_eq!(fln::nat_decimal(&value.value).as_deref(), Some("30"));
    assert!(value.usage.steps > idle_value.usage.steps + 30);
    let replay = fln::execute_flbc_artifact(&execution.flbc_artifact, &options, Default::default())
        .unwrap()
        .into_complete()
        .unwrap();
    let VmExit::Returned(replayed) = replay else {
        panic!("computed dictionary artifact did not return");
    };
    assert_eq!(fln::nat_decimal(&replayed.value).as_deref(), Some("30"));
    assert_eq!(replayed.usage.steps, value.usage.steps);
    let mut bounded = limits();
    bounded.vm.max_steps = idle_value.usage.steps;
    assert!(matches!(
        base.execute_source_definitions(&[program(30).as_bytes()], &options, bounded)
            .unwrap(),
        fln::Outcome::Inconclusive(_)
    ));
    assert_eq!(base.logical_root(&options), root);
    let retried = run(30);
    assert_eq!(
        retried.executions.last().unwrap().flbc_artifact,
        execution.flbc_artifact
    );
    assert_eq!(retried.result_logical_root, busy.result_logical_root);
    assert_eq!(base.logical_root(&options), root);
}

#[test]
fn residual_dictionary_exposure_preserves_foreign_factory_and_consumer_authority() {
    let options = KVMap::new();
    let clean = engine()
        .check_source_files(
            &[COMPUTED_AMOUNT.as_bytes()],
            &options,
            fln::SourceCheckLimits::new(limits().admission()),
        )
        .unwrap()
        .into_complete()
        .unwrap()
        .engine;
    for declaration in ["runtimeAmount", "amountOnce"] {
        let decorated = Engine::from_environment(
            fln_elab::externs::register(
                clean.environment(),
                &fln::Name::from_components([declaration]),
                vec![fln_elab::externs::ExternEntry::Standard {
                    backend: fln::Name::from_components(["all"]),
                    symbol: "foreign_dictionary_execution".to_owned(),
                }],
            )
            .unwrap(),
        );
        let root = decorated.logical_root(&options);
        let mut error = decorated
            .execute_source_definitions(&[b"#eval forwardAmount 30"], &options, limits())
            .expect_err("a selected foreign dictionary cannot use its logical body");
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
fn a_dynamic_generic_dictionary_method_retains_a_typed_refusal() {
    let source = r#"
class DynamicAmount where
  amount : (A : Type) -> A -> Nat
def chooseMethod (flag : Bool) : (A : Type) -> A -> Nat :=
  if flag then (fun A x => 41) else (fun A x => 42)
def makeDynamic (flag : Bool) : DynamicAmount := { amount := chooseMethod flag }
def consumeDynamic [chosen : DynamicAmount] : Nat := DynamicAmount.amount Nat 0
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
            &[b"#eval consumeDynamic (chosen := makeDynamic true)"],
            &options,
            limits(),
        )
        .expect_err("an unknown generic method cannot acquire a guessed runtime ABI");
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

#[test]
fn value_indexed_factories_expose_methods_before_runtime_catalog_selection() {
    execute(
        r#"
class EchoAt (n : Nat) where
  echo : Nat -> Nat
instance echoAt (n : Nat) : EchoAt n := { echo := fun x => x }
def useEchoAt (n x : Nat) : Nat := EchoAt.echo (n := n) x
#eval useEchoAt 7 42
"#,
        "42",
    );
    execute(
        &format!(
            r#"{INDEXED}
def fromIndexedBox (n : Nat) (xs : IndexedBox Nat n) : Nat :=
  @GetAt.get (IndexedBox Nat n) Nat (fun _ _ => n = n)
    (makeGetAt n (A := Nat)) xs 0 rfl
#eval fromIndexedBox 7 {{ value := 42 }}
"#,
        ),
        "42",
    );
    execute(
        &format!(
            r#"{INDEXED}
def fromStringBox (n : Nat) (suffix : String) : Nat :=
  String.length (@GetAt.get (IndexedBox String n) String (fun _ _ => n = n)
    (makeGetAt n (A := String)) {{ value := "λ" ++ suffix }} 0 rfl)
#eval fromStringBox 7 "ab"
"#,
        ),
        "3",
    );
    execute(
        &format!(
            r#"{INDEXED}
def fromFunctionBox (n delta : Nat) : Nat :=
  let f := @GetAt.get (IndexedBox (Nat -> Nat) n) (Nat -> Nat) (fun _ _ => n = n)
    (makeGetAt n (A := Nat -> Nat)) {{ value := fun x => x + delta }} 0 rfl
  f 40
#eval fromFunctionBox 7 2
"#,
        ),
        "42",
    );
}

#[test]
fn constant_methods_and_parent_instances_keep_bound_factory_arguments() {
    execute(
        r#"
structure IndexedBox (A : Type) (n : Nat) where
  value : A
class GetAt (C A : Type) (valid : C -> Nat -> Prop) where
  get : (xs : C) -> (i : Nat) -> valid xs i -> A
def boxGet {A : Type} {n : Nat} (xs : IndexedBox A n) (_ : Nat) (_ : n = n) : A := xs.value
instance makeGetAt (n : Nat) {A : Type} : GetAt (IndexedBox A n) A (fun _ _ => n = n) :=
  { get := boxGet (A := A) (n := n) }
def fromBox (n : Nat) (xs : IndexedBox Nat n) : Nat :=
  @GetAt.get (IndexedBox Nat n) Nat (fun _ _ => n = n) (makeGetAt n (A := Nat)) xs 0 rfl
#eval fromBox 7 { value := 42 }
"#,
        "42",
    );
    execute(
        r#"
structure IndexedBox (A : Type) (n : Nat) where
  value : A
class GetAt (C A : Type) (valid : C -> Nat -> Prop) where
  get : (xs : C) -> (i : Nat) -> valid xs i -> A
class BothAt (C A : Type) (valid : C -> Nat -> Prop) extends GetAt C A valid where
  other : Nat
instance makeBothAt (n : Nat) {A : Type} : BothAt (IndexedBox A n) A (fun _ _ => n = n) :=
  { get := fun xs _ _ => xs.value, other := 0 }
def fromBox (n : Nat) (xs : IndexedBox Nat n) : Nat :=
  @GetAt.get (IndexedBox Nat n) Nat (fun _ _ => n = n)
    (@BothAt.toGetAt (IndexedBox Nat n) Nat (fun _ _ => n = n) (makeBothAt n (A := Nat))) xs 0 rfl
#eval fromBox 7 { value := 42 }
"#,
        "42",
    );
    execute(
        r#"
structure IndexedBox (A : Type) (n : Nat) where
  value : A
class GetAt (C A : Type) (valid : C -> Nat -> Prop) where
  get : (xs : C) -> (i : Nat) -> valid xs i -> A
def addBox (delta n : Nat) (xs : IndexedBox Nat n) (_ : Nat) (_ : n = n) : Nat := xs.value + delta
instance makeGetAt (n delta : Nat) : GetAt (IndexedBox Nat n) Nat (fun _ _ => n = n) :=
  { get := addBox delta n }
def fromBox (n delta x : Nat) : Nat :=
  @GetAt.get (IndexedBox Nat n) Nat (fun _ _ => n = n) (makeGetAt n delta) { value := x } 0 rfl
#eval fromBox 7 1 20 + fromBox 8 2 20
"#,
        "43",
    );
}

#[test]
fn inherited_methods_cannot_discard_a_computed_sibling() {
    let source = r#"
structure IndexedBox (A : Type) (n : Nat) where
  value : A
class GetAt (C A : Type) (valid : C -> Nat -> Prop) where
  get : (xs : C) -> (i : Nat) -> valid xs i -> A
class BothAt (C A : Type) (valid : C -> Nat -> Prop) extends GetAt C A valid where
  other : Nat
def count (n : Nat) : Nat := match n with | .zero => 0 | .succ k => count k + 1
instance makeBothAt (n : Nat) {A : Type} : BothAt (IndexedBox A n) A (fun _ _ => n = n) :=
  { get := fun xs _ _ => xs.value, other := count n }
def fromBox (n : Nat) (xs : IndexedBox Nat n) : Nat :=
  @GetAt.get (IndexedBox Nat n) Nat (fun _ _ => n = n)
    (@BothAt.toGetAt (IndexedBox Nat n) Nat (fun _ _ => n = n) (makeBothAt n (A := Nat))) xs 0 rfl
"#;
    strict_dictionary(source, "fromBox");
}

#[test]
fn dependent_computed_dictionary_fields_are_not_discarded_as_inert_metadata() {
    let source = r#"
structure IndexedBox (A : Type) (n : Nat) where
  value : A
class GetAt (C A : Type) (valid : C -> Nat -> Prop) where
  get : (xs : C) -> (i : Nat) -> valid xs i -> A
  unused : Nat
def count (n : Nat) : Nat := match n with | .zero => 0 | .succ k => count k + 1
instance makeGetAt (n : Nat) {A : Type} :
    GetAt (IndexedBox A n) A (fun _ _ => n = n) :=
  { get := fun xs _ _ => xs.value, unused := count n }
def fromIndexedBox (n : Nat) (xs : IndexedBox Nat n) : Nat :=
  @GetAt.get (IndexedBox Nat n) Nat (fun _ _ => n = n)
    (makeGetAt n (A := Nat)) xs 0 rfl
"#;
    strict_dictionary(source, "fromIndexedBox");
}

#[test]
fn class_method_projection_preserves_a_computed_datatype_parameter() {
    let definitions = r#"
class EchoAt (n : Nat) where
  echo : Nat -> Nat
instance echoAt (n : Nat) : EchoAt n := { echo := fun x => x }
def count (n : Nat) : Nat := match n with | .zero => 0 | .succ k => count k + 1
"#;
    let idle = execute(
        &format!("{definitions}#eval @EchoAt.echo 30 (echoAt 30) 42"),
        "42",
    );
    let program = format!("{definitions}#eval @EchoAt.echo (count 30) (echoAt 30) 42");
    let busy = execute(&program, "42");
    assert!(
        busy > idle + 30,
        "computed projection parameter vanished: {idle} vs {busy}"
    );
    let base = engine();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    let mut bounded = limits();
    bounded.vm.max_steps = idle;
    assert!(matches!(
        base.execute_source_definitions(&[program.as_bytes()], &options, bounded)
            .unwrap(),
        fln::Outcome::Inconclusive(_)
    ));
    assert_eq!(base.logical_root(&options), root);
}

#[test]
fn factory_methods_preserve_owned_values_and_callback_representations() {
    execute(
        &format!(
            "{ECHO}#eval let f : Nat -> Nat := Echo.echo (K := Nat) (fun (n : Nat) => n + 1); f 41"
        ),
        "42",
    );
    execute(
        &format!(
            "{ECHO}def run (suffix : String) : Nat := String.length (Echo.echo (K := String) (\"a\" ++ suffix))\n#eval run \"xyz\""
        ),
        "4",
    );
}

#[test]
fn recursively_inferred_factories_retain_their_actual_dictionary_dependencies() {
    execute(
        r#"
structure Box (A : Type) where
  value : A
class Echo (K : Type) where
  echo : {A : Type} -> A -> A
instance baseEcho : Echo Nat := { echo := fun a => a }
instance boxedEcho {K : Type} [Echo K] : Echo (Box K) :=
  { echo := fun a => Echo.echo (K := K) a }
#eval Echo.echo (K := Box (Box Nat)) 42
"#,
        "42",
    );
}

#[test]
fn distinct_factory_arguments_do_not_alias_in_the_specialization_cache() {
    execute(
        r#"
class Bump (A : Type) where
  bump : A -> A
def makeBump (K : Type) (delta : Nat) : Bump Nat :=
  { bump := fun x => x + delta }
def useBump [chosen : Bump Nat] (n : Nat) : Nat := Bump.bump n
#eval useBump (chosen := makeBump Nat 1) 20 + useBump (chosen := makeBump Bool 2) 19
"#,
        "42",
    );
}

const MONAD: &str = r#"
class Pure (f : Type -> Type) where
  pure : {A : Type} -> A -> f A
class Bind (m : Type -> Type) where
  bind : {A B : Type} -> m A -> (A -> m B) -> m B
def Id (A : Type) : Type := A
def makePure (K : Type) : Pure Id := { pure := fun a => a }
def makeBind (K : Type) : Bind Id := { bind := fun a k => k a }
instance idPure : Pure Id := makePure Nat
instance idBind : Bind Id := makeBind Bool
"#;

#[test]
fn monad_operations_use_applied_factories_without_a_trusted_monad_evaluator() {
    execute(
        &format!(
            "{MONAD}def work (n : Nat) : Id Nat := do\n  let x ← (n : Id Nat)\n  return (x + 1)\n#eval work 41"
        ),
        "42",
    );
    execute(
        &format!(
            "{MONAD}def mapping {{M : Type -> Type}} [Pure M] [Bind M] {{A B : Type}} (f : A -> B) (action : M A) : M B := do let x ← action; return (f x)\n#eval (mapping (M := Id) (fun (n : Nat) => n + 1) (41 : Nat) : Id Nat)"
        ),
        "42",
    );
}

#[test]
fn ordinary_computed_factory_fields_still_consume_vm_work() {
    let program = |cost| {
        format!(
            r#"
class Probe (A : Type) where
  call : A -> A
  unused : Nat
def count (n : Nat) : Nat := match n with | .zero => 0 | .succ k => count k + 1
def makeProbe (K : Type) (n : Nat) : Probe Nat :=
  {{ call := fun x => x, unused := count n }}
instance computed : Probe Nat := makeProbe Nat {cost}
def useProbe [chosen : Probe Nat] (n : Nat) : Nat := Probe.call n
#eval useProbe 42
"#
        )
    };
    let idle = execute(&program(0), "42");
    let busy = execute(&program(30), "42");
    assert!(
        busy > idle + 30,
        "factory initializer vanished: {idle} vs {busy}"
    );
    let base = engine();
    let root = base.logical_root(&KVMap::new());
    let mut bounded = limits();
    bounded.vm.max_steps = idle;
    assert!(matches!(
        base.execute_source_definitions(&[program(30).as_bytes()], &KVMap::new(), bounded)
            .unwrap(),
        fln::Outcome::Inconclusive(_)
    ));
    assert_eq!(base.logical_root(&KVMap::new()), root);
}

#[test]
fn invalid_calls_and_resource_stops_leave_a_deterministic_clean_retry() {
    let base = engine();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    let valid = format!("{ECHO}#eval Echo.echo (K := Nat) 42");
    let invalid = format!("{ECHO}#eval Echo.echo (K := Nat) (A := Bool) 42");
    assert!(
        base.execute_source_definitions(&[invalid.as_bytes()], &options, limits())
            .is_err()
    );
    let mut bounded = limits();
    bounded.ingress.max_nodes = 1;
    assert!(
        base.execute_source_definitions(&[valid.as_bytes()], &options, bounded)
            .is_err()
    );
    assert_eq!(base.logical_root(&options), root);
    let run = || {
        base.execute_source_definitions(&[valid.as_bytes()], &options, limits())
            .unwrap()
            .into_complete()
            .unwrap()
    };
    let first = run();
    let second = run();
    assert_eq!(
        first.executions.last().unwrap().flbc_artifact,
        second.executions.last().unwrap().flbc_artifact
    );
    assert_eq!(first.result_logical_root, second.result_logical_root);
    assert_eq!(base.logical_root(&options), root);
    assert!(!first.engine.environment().contains(&fln::Name::num(
        fln::Name::from_components(["_fln_runtime_specialization"]),
        0,
    )));
}
