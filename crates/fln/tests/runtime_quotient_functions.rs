//! Quotient primitives participate in higher-order source programs.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap, VmExit};

fn limits() -> EngineExecutionLimits {
    EngineExecutionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}
fn execute(source: &str, expected: &str) -> u64 {
    let engine = Engine::with_source_seed(EngineAdmissionLimits::new(limits().kernel))
        .unwrap()
        .into_complete()
        .unwrap();
    let run = engine
        .execute_source_definitions(&[source.as_bytes()], &KVMap::new(), limits())
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .unwrap();
    let VmExit::Returned(value) = &run.executions.last().unwrap().exit else {
        panic!("quotient function did not return");
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
        Some(expected),
        "{source}"
    );
    value.usage.steps
}

#[test]
fn constructors_and_lifters_are_reusable_first_class_functions() {
    execute(include_str!("../../../examples/native_quotient_runtime.lean"), "42");
    execute(
        r#"
def Q : Type := Quot (fun (a b : Nat) => a = b)
#eval let lift := @Quot.lift Nat (fun (a b : Nat) => a = b) Nat; lift (fun n => n) (fun a b h => h) (Quot.mk (fun a b => a = b) 42)
"#,
        "42",
    );
    execute(
        r#"
def Q : Type := Quot (fun (a b : Nat) => a = b)
#eval let lift := @Quot.lift Nat (fun (a b : Nat) => a = b) Nat (fun n => n); lift (fun a b h => h) (Quot.mk (fun a b => a = b) 42)
"#,
        "42",
    );
}

#[test]
fn polymorphic_lifting_and_nested_quotients_keep_concrete_representations() {
    execute(
        r#"
def read {A : Type} {r : A -> A -> Prop} (f : A -> Nat) (h : (a b : A) -> r a b -> f a = f b) (q : Quot r) : Nat := Quot.lift f h q
#eval read (fun (s : String) => String.length s) (fun (a b : String) (h : String.length a = String.length b) => h) (Quot.mk (fun (a b : String) => String.length a = String.length b) "abcd")
"#,
        "4",
    );
    execute(
        r#"
def Q : Type := Quot (fun (a b : Nat) => a = b)
def read (q : Q) : Nat := Quot.lift (fun (n : Nat) => n) (fun (a b : Nat) (h : a = b) => h) q
def QQ : Type := Quot (fun (a b : Q) => read a = read b)
def readTwice (q : QQ) : Nat := Quot.lift read (fun (a b : Q) (h : read a = read b) => h) q
#eval readTwice (Quot.mk (fun (a b : Q) => read a = read b) (Quot.mk (fun (a b : Nat) => a = b) 42))
"#,
        "42",
    );
}

#[test]
fn closures_can_be_quotient_representatives_with_owned_captures() {
    execute(
        r#"
def run (q : Quot (fun (f g : String -> String) => f "a" = g "a")) : String :=
  Quot.lift (fun (f : String -> String) => f "a") (fun (f g : String -> String) (h : f "a" = g "a") => h) q
#eval let suffix : String := "xyz"; String.length (run (Quot.mk (fun (f g : String -> String) => f "a" = g "a") (fun s => s ++ suffix)))
"#,
        "4",
    );
}

#[test]
fn function_valued_lifts_execute_successive_return_stages() {
    execute(
        r#"
def build (n : Nat) : Nat -> Nat := let base : Nat := n + 1; fun (x : Nat) => base + x
#eval Quot.lift build (fun (a b : Nat) (h : build a = build b) => h) (Quot.mk (fun (a b : Nat) => build a = build b) 20) 21
"#,
        "42",
    );
    execute(
        r#"
def build (n : Nat) : Nat -> Nat -> Nat := let base : Nat := n + 1; fun (x : Nat) => let middle : Nat := base + x; fun (y : Nat) => middle + y
#eval Quot.lift build (fun (a b : Nat) (h : build a = build b) => h) (Quot.mk (fun (a b : Nat) => build a = build b) 20) 10 11
"#,
        "42",
    );
}

#[test]
fn unused_partial_lifts_do_not_defer_the_supplied_function_initializer() {
    let source = r#"
def count (n : Nat) : Nat := match n with | .zero => 0 | .succ k => count k + 1
def factory (n : Nat) : Nat -> Nat := let forced : Nat := count n; fun (x : Nat) => 42
def Q : Type := Quot (fun (a b : Nat) => True)
#eval let saved : Q -> Nat := Quot.lift (factory 30) (fun (a b : Nat) (h : True) => rfl); 42
"#;
    let idle = execute(&source.replace("factory 30", "factory 0"), "42");
    let busy = execute(source, "42");
    assert!(busy > idle + 30, "partial lift delayed f: {idle} vs {busy}");
}

#[test]
fn relations_may_capture_runtime_values_without_changing_the_carrier_layout() {
    execute(
        r#"
def readShift (offset : Nat) (q : Quot (fun (a b : Nat) => a + offset = b + offset)) : Nat :=
  Quot.lift (fun (n : Nat) => n + offset) (fun (a b : Nat) (h : a + offset = b + offset) => h) q
#eval readShift 2 (Quot.mk (fun (a b : Nat) => a + 2 = b + 2) 40)
"#,
        "42",
    );
}
