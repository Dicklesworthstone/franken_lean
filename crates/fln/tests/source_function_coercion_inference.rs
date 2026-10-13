//! Generic consumers infer their function types through registered CoeFun
//! dictionaries, before ordinary council admission and native execution.
#![forbid(unsafe_code)]
use fln::{
    Budget, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap, SourceCheckLimits, VmExit,
};

fn limits() -> SourceCheckLimits {
    SourceCheckLimits::new(EngineAdmissionLimits::new(Budget::for_stack_bytes(
        2 * 1024 * 1024,
    )))
}
fn seed() -> Engine {
    Engine::with_coercion_seed(limits().admission)
        .unwrap()
        .into_complete()
        .unwrap()
}
fn checked(base: &Engine, source: &str) -> Engine {
    base.check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .unwrap()
        .engine
}
const BUNDLE: &str = r#"
structure Callable where
  run : Nat -> Nat
instance callable : CoeFun Callable (fun _ => Nat -> Nat) := CoeFun.mk (fun c => c.run)
"#;

#[test]
fn generic_higher_order_source_preserves_the_chosen_callable() {
    let base = checked(&seed(), BUNDLE);
    checked(
        &base,
        r#"
def use {A : Type} (f : A -> A) (x : A) : A := f x
def pass (c : Callable) (x : Nat) : Nat := use c x
def anonymous : Callable := Callable.mk (fun n => n + 3)
def application : Nat := use anonymous 39
"#,
    );
}

#[test]
fn inferred_function_coercions_run_through_golem() {
    let source = format!(
        "{BUNDLE}{}",
        r#"
def twice {A : Type} (f : A -> A) (x : A) : A := f (f x)
def plusThree (n : Nat) : Nat := n + 3
def boxed : Callable := Callable.mk plusThree
#eval twice boxed 36
"#
    );
    let run = seed()
        .execute_source_definitions(
            &[source.as_bytes()],
            &KVMap::new(),
            EngineExecutionLimits::new(limits().admission.kernel),
        )
        .unwrap_or_else(|error| panic!("{error:?}"))
        .into_complete()
        .unwrap();
    let VmExit::Returned(value) = &run.executions.last().unwrap().exit else {
        panic!("Golem did not return");
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
        Some("42")
    );
}

#[test]
fn incompatible_function_coercions_refuse_atomically_and_recover() {
    let base = checked(&seed(), BUNDLE);
    let root = base.logical_root(&KVMap::new());
    let invalid =
        "def bad (c : Callable) (use : {A : Type} -> ((Nat -> Nat) -> A) -> Nat) : Nat := use c";
    assert!(
        base.check_source_files(&[invalid.as_bytes()], &KVMap::new(), limits())
            .is_err()
    );
    assert_eq!(base.logical_root(&KVMap::new()), root);
    checked(
        &base,
        "def recovered (c : Callable) (use : {A : Type} -> (A -> A) -> Nat) : Nat := use c",
    );
}
