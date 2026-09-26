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
fn factory_methods_preserve_owned_values_and_callback_representations() {
    execute(
        &format!("{ECHO}#eval let f : Nat -> Nat := Echo.echo (K := Nat) (fun (n : Nat) => n + 1); f 41"),
        "42",
    );
    execute(
        &format!("{ECHO}def run (suffix : String) : Nat := String.length (Echo.echo (K := String) (\"a\" ++ suffix))\n#eval run \"xyz\""),
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
        &format!("{MONAD}def work (n : Nat) : Id Nat := do\n  let x ← (n : Id Nat)\n  return (x + 1)\n#eval work 41"),
        "42",
    );
    execute(
        &format!("{MONAD}def mapping {{M : Type -> Type}} [Pure M] [Bind M] {{A B : Type}} (f : A -> B) (action : M A) : M B := do let x ← action; return (f x)\n#eval (mapping (M := Id) (fun (n : Nat) => n + 1) 41 : Id Nat)"),
        "42",
    );
}

#[test]
fn ordinary_computed_factory_fields_still_consume_vm_work() {
    let program = |cost| format!(r#"
class Probe (A : Type) where
  call : A -> A
  unused : Nat
def count (n : Nat) : Nat := match n with | .zero => 0 | .succ k => count k + 1
def makeProbe (K : Type) (n : Nat) : Probe Nat :=
  {{ call := fun x => x, unused := count n }}
instance computed : Probe Nat := makeProbe Nat {cost}
def useProbe [chosen : Probe Nat] (n : Nat) : Nat := Probe.call n
#eval useProbe 42
"#);
    let idle = execute(&program(0), "42");
    let busy = execute(&program(30), "42");
    assert!(busy > idle + 30, "factory initializer vanished: {idle} vs {busy}");
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
