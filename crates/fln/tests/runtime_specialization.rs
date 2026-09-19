//! Post-admission specialization retains the checked environment and runs Golem.
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
        panic!("not returned")
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
        Some(expected),
        "{source}"
    );
    value.usage.steps
}

#[test]
fn polymorphic_identity_specializes_distinct_scalar_representations() {
    execute(
        "def identity.{u} {A : Type u} (a : A) : A := a\n#eval identity 42",
        "42",
    );
    execute(
        "def identity.{u} {A : Type u} (a : A) : A := a\n#eval if identity true then identity 42 else 0",
        "42",
    );
    execute(
        "def identity.{u} {A : Type u} (a : A) : A := a\n#eval String.length (identity \"abcdef\")",
        "6",
    );
}

#[test]
fn distinct_universes_and_literal_callbacks_get_checked_closure_interfaces() {
    execute(
        "def applyPoly.{u,v} {A : Type u} {B : Type v} (f : A -> B) (x : A) : B := f x\n#eval applyPoly (fun (s : String) => String.length s + 40) \"ab\"",
        "42",
    );
    execute(
        "def twice.{u} {A : Type u} (f : A -> A) (x : A) : A := f (f x)\n#eval twice (fun (x : Nat) => x + 1) 40",
        "42",
    );
}

#[test]
fn callbacks_capture_runtime_locals_after_specialization() {
    execute(
        "def twice.{u} {A : Type u} (f : A -> A) (x : A) : A := f (f x)\ndef run (delta : Nat) : Nat := twice (fun x => x + delta) 30\n#eval run 6",
        "42",
    );
    execute(
        "def twice.{u} {A : Type u} (f : A -> A) (x : A) : A := f (f x)\ndef run (suffix : String) : Nat := String.length (twice (fun s => s ++ suffix) \"a\")\n#eval run \"abc\"",
        "7",
    );
}

#[test]
fn partial_applications_preserve_their_instantiated_interfaces() {
    execute(
        "def applyPoly.{u,v} {A : Type u} {B : Type v} (f : A -> B) (x : A) : B := f x\n#eval let inc : Nat -> Nat := applyPoly (fun x => x + 1); inc 41",
        "42",
    );
}

#[test]
fn strict_runtime_beta_uses_scoped_lets_not_capture_or_duplication() {
    execute(
        "def run (a b : Nat) : Nat := (fun (x y : Nat) => x + y + a) b 2\n#eval run 10 30",
        "42",
    );
    execute(
        "def run (suffix : String) : Nat := String.length ((fun (f : String -> String) => f \"a\") (fun s => s ++ suffix))\n#eval run \"abc\"",
        "4",
    );
}

#[test]
fn erased_type_arguments_do_not_erase_strict_runtime_work() {
    let definitions = "def count (n : Nat) : Nat := match n with | .zero => 0 | .succ k => count k + 1\ndef ignore.{u} {A : Type u} (x : A) : Nat := 42\n";
    let idle = execute(&format!("{definitions}#eval ignore 0"), "42");
    let busy = execute(&format!("{definitions}#eval ignore (count 30)"), "42");
    assert!(
        busy > idle + 30,
        "strict argument disappeared: {idle} vs {busy}"
    );
    let single = execute(
        &format!("{definitions}#eval (fun (x : Nat) => x + x) (count 30)"),
        "60",
    );
    let duplicate = execute(&format!("{definitions}#eval count 30 + count 30"), "60");
    assert!(
        single < duplicate,
        "argument was duplicated: {single} vs {duplicate}"
    );
}

const ID: &str = r#"
class Pure (f : Type -> Type) where
  pure : {A : Type} -> A -> f A
class Bind (m : Type -> Type) where
  bind : {A B : Type} -> m A -> (A -> m B) -> m B
def Id (A : Type) : Type := A
instance idPure : Pure Id := { pure := fun a => a }
instance idBind : Bind Id := { bind := fun a k => k a }
"#;

#[test]
fn complete_source_files_register_dictionaries_and_execute_do() {
    execute(
        &format!(
            "{ID}\ndef nested (seed : Nat) : Id Nat := do\n  let n ← do\n    let n ← (seed : Id Nat)\n    return (n + 1)\n  (10 : Id Nat)\n  let n ← (n + 1 : Id Nat)\n  return n\n#eval nested 40"
        ),
        "42",
    );
    execute(
        &format!(
            "{ID}\ndef mapping {{M : Type -> Type}} [Pure M] [Bind M] {{A B : Type}} (f : A -> B) (action : M A) : M B := do let x ← action; return (f x)\n#eval (mapping (M := Id) (fun (x : Nat) => x + 1) 41 : Id Nat)"
        ),
        "42",
    );
    execute(
        &format!(
            "{ID}\ndef append (suffix : String) : Id Nat := do let s ← (\"a\" : Id String); return (String.length (s ++ suffix))\n#eval append \"xyz\""
        ),
        "4",
    );
}

#[test]
fn concrete_instance_identity_is_part_of_the_specialization_key() {
    execute(
        r#"
class Bump (A : Type) where
  bump : A -> A
instance one : Bump Nat := { bump := fun x => x + 1 }
instance two : Bump Nat := { bump := fun x => x + 2 }
def useBump [chosen : Bump Nat] (n : Nat) : Nat := Bump.bump n
#eval useBump (chosen := one) 20 + useBump (chosen := two) 19
"#,
        "42",
    );
}

#[test]
fn nested_closure_returning_monads_remain_explicit_refusals() {
    let base = engine();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    let source = r#"
class Pure (f : Type -> Type) where
  pure : {A : Type} -> A -> f A
class Bind (m : Type -> Type) where
  bind : {A B : Type} -> m A -> (A -> m B) -> m B
def Reader (A : Type) : Type := Nat -> A
instance readerPure : Pure Reader := { pure := fun a r => a }
instance readerBind : Bind Reader := { bind := fun action k r => k (action r) r }
def ask : Reader Nat := fun r => r
def work : Reader Nat := do
  let n ← ask
  return (n + 2)
#eval work 40
"#;
    // This requires a closure-returning callback ABI, not merely erasure of
    // the Reader alias. Do not relabel an unsupported lambda as a value.
    assert!(
        base.execute_source_definitions(&[source.as_bytes()], &options, limits())
            .is_err()
    );
    assert_eq!(base.logical_root(&options), root);
}

#[test]
fn specialization_budgets_and_vm_nonanswers_are_failure_atomic() {
    use fln::Outcome;
    let base = engine();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    let source = b"def identity.{u} {A : Type u} (a : A) : A := a\n#eval identity 42";
    for bounded in [
        {
            let mut l = limits();
            l.ingress.max_nodes = 5;
            l
        },
        {
            let mut l = limits();
            l.ingress.fir.max_functions = 0;
            l
        },
    ] {
        assert!(
            base.execute_source_definitions(&[source], &options, bounded)
                .is_err()
        );
        assert_eq!(base.logical_root(&options), root);
    }
    let mut tiny = limits();
    tiny.vm.max_steps = 1;
    assert!(matches!(
        base.execute_source_definitions(&[source], &options, tiny)
            .unwrap(),
        Outcome::Inconclusive(_)
    ));
    assert_eq!(base.logical_root(&options), root);
    let run = || {
        base.execute_source_definitions(&[source], &options, limits())
            .unwrap()
            .into_complete()
            .unwrap()
    };
    let a = run();
    let b = run();
    assert_eq!(
        a.executions.last().unwrap().flbc_artifact,
        b.executions.last().unwrap().flbc_artifact
    );
    assert_eq!(a.result_logical_root, b.result_logical_root);
    assert_eq!(base.logical_root(&options), root);
    assert!(
        !base
            .environment()
            .contains(&fln::Name::from_components(["identity"]))
    );
    let name = fln::Name::num(
        fln::Name::from_components(["_fln_runtime_specialization"]),
        0,
    );
    assert!(
        !a.engine.environment().contains(&name),
        "runtime clone leaked into checked declarations"
    );
}

#[test]
fn ill_typed_templates_and_evaluated_type_values_cannot_be_admitted_as_executions() {
    let base = engine();
    let root = base.logical_root(&KVMap::new());
    for source in [
        "def bad.{u} {A : Type u} (a : A) : A := 7\n#eval 42",
        "def identity.{u} {A : Type u} (a : A) : A := a\n#eval identity (A := Bool) 7",
        "#eval Nat",
    ] {
        assert!(
            base.execute_source_definitions(&[source.as_bytes()], &KVMap::new(), limits())
                .is_err(),
            "{source}"
        );
        assert_eq!(base.logical_root(&KVMap::new()), root);
    }
}

#[test]
fn computed_dictionary_fields_are_not_executed_or_discarded_during_specialization() {
    let source = r#"
class Probe (A : Type) where
  call : A -> A
  unused : Nat
def count (n : Nat) : Nat := match n with | .zero => 0 | .succ k => count k + 1
instance computed : Probe Nat := { call := fun x => x, unused := count 30 }
def useProbe [chosen : Probe Nat] (n : Nat) : Nat := Probe.call n
#eval useProbe 42
"#;
    let base = engine();
    let root = base.logical_root(&KVMap::new());
    // Inspect all fields, not just `call`: compiling a selected projection is
    // not permission to evaluate or erase an arbitrary dictionary initializer.
    assert!(
        base.execute_source_definitions(&[source.as_bytes()], &KVMap::new(), limits())
            .is_err()
    );
    assert_eq!(base.logical_root(&KVMap::new()), root);
}

#[test]
fn templates_are_checked_admissions_not_phantom_vm_results() {
    let source = b"def identity.{u} {A : Type u} (a : A) : A := a\n#eval identity 42";
    let base = engine();
    let run = base
        .execute_source_definitions(&[source], &KVMap::new(), limits())
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(run.source_admissions.len(), 1);
    assert_eq!(run.executions.len(), 1);
    assert_eq!(run.source_evaluation_indices, vec![0]);
    assert_eq!(run.source_execution_command_indices, vec![1]);
    let name = fln::Name::from_components(["identity"]);
    let logical = base
        .admit_source_declaration(
            b"def identity.{u} {A : Type u} (a : A) : A := a",
            &KVMap::new(),
            EngineAdmissionLimits::new(limits().kernel),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(
        run.engine.environment().find(&name),
        logical.engine.environment().find(&name)
    );
}
