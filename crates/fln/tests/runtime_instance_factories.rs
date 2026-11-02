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
    let base = engine();
    let options = KVMap::new();
    let root = base.logical_root(&options);
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
#eval fromBox 30 { value := 42 }
"#;
    let error = base
        .execute_source_definitions(&[source.as_bytes()], &options, limits())
        .expect_err("an inherited method cannot erase its outer dictionary's strict work");
    let mut cause = &error;
    while let fln::EngineExecutionError::BatchCommand { error, .. } = cause {
        cause = error;
    }
    assert!(
        matches!(
            cause,
            fln::EngineExecutionError::Ingress(
                fln_comp::ingress::IngressError::UnsupportedCallableSignature { name }
            ) if name.to_display_string().starts_with("_fln_runtime_specialization.")
        ),
        "{error:?}"
    );
    assert_eq!(base.logical_root(&options), root);
}

#[test]
fn dependent_computed_dictionary_fields_are_not_discarded_as_inert_metadata() {
    let base = engine();
    let options = KVMap::new();
    let root = base.logical_root(&options);
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
#eval fromIndexedBox 30 { value := 42 }
"#;
    let error = base
        .execute_source_definitions(&[source.as_bytes()], &options, limits())
        .expect_err("an unsupported strict dictionary must not become a fabricated inert method");
    let mut cause = &error;
    while let fln::EngineExecutionError::BatchCommand { error, .. } = cause {
        cause = error;
    }
    assert!(
        matches!(
            cause,
            fln::EngineExecutionError::Ingress(
                fln_comp::ingress::IngressError::UnsupportedCallableSignature { name }
            ) if name.to_display_string().starts_with("_fln_runtime_specialization.")
        ),
        "{error:?}"
    );
    assert!(
        error
            .to_string()
            .contains("supported ground runtime signature")
    );
    assert_eq!(base.logical_root(&options), root);
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
