//! Closures are owned runtime fields, not compile-time dictionary substitutions.
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
    let result = engine()
        .execute_source_definitions(&[source.as_bytes()], &KVMap::new(), limits())
        .unwrap_or_else(|e| panic!("{source}\n{e:?}"))
        .into_complete()
        .unwrap();
    let VmExit::Returned(value) = &result.executions.last().unwrap().exit else {
        panic!("return")
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
        Some(expected),
        "{source}"
    );
    value.usage.steps
}
#[test]
fn literal_and_named_functions_are_callable_object_fields() {
    run(
        "structure Handler where\n  run : Nat -> Nat\ndef use (h : Handler) (n : Nat) : Nat := h.run n\n#eval use { run := fun (n : Nat) => n + 2 } 40",
        "42",
    );
    run(
        "structure Handler (A B : Type) where\n  run : A -> B\ndef use (h : Handler String Nat) (s : String) : Nat := h.run s\n#eval use { run := String.length } \"hello\" + 37",
        "42",
    );
}
#[test]
fn closures_survive_collection_storage_and_recursive_elimination() {
    run(
        "def operations : List (Nat -> Nat) := [Nat.add 10, Nat.sub 50]\n#eval List.foldl (fun (n : Nat) (f : Nat -> Nat) => f n) 0 operations",
        "40",
    );
    run(
        "def operations : List (Nat -> Nat) := [fun n => n + 1, fun n => n + 3]\n#eval List.foldl Nat.add 0 (List.map (fun (f : Nat -> Nat) => f 19) operations)",
        "42",
    );
}
#[test]
fn variants_and_partial_constructors_retain_function_payloads() {
    run(
        "inductive Operation where | plus (f : Nat -> Nat) | none\ndef use (o : Operation) : Nat := match o with | .plus f => f 40 | .none => 0\n#eval use (Operation.plus (Nat.add 2))",
        "42",
    );
    run(
        "structure Pair where\n  run : Nat -> Nat\n  offset : Nat\ndef use (p : Pair) : Nat := p.run p.offset\n#eval List.foldl Nat.add 0 (List.map use (List.map (Pair.mk (Nat.add 1)) [19, 21]))",
        "42",
    );
}
#[test]
fn field_interfaces_remain_distinct_after_canonicalization() {
    run(
        "structure Operations where\n  text : String -> String\n  number : Nat -> Nat\n  measure : String -> Nat\ndef use (o : Operations) : Nat := o.number 30 + o.measure (o.text \"abc\")\n#eval use { text := String.append \"hello\", number := Nat.add 4, measure := String.length }",
        "42",
    );
    run(
        "structure Operations where\n  number : Nat -> Nat\n  text : String -> String\n  measure : String -> Nat\ndef use (o : Operations) : Nat := o.number 30 + o.measure (o.text \"abc\")\n#eval use { number := Nat.add 4, text := String.append \"hello\", measure := String.length }",
        "42",
    );
}
#[test]
fn field_closures_capture_owned_strings_callbacks_and_nested_data() {
    run(
        "structure Handler where\n  run : String -> Nat\ndef capture (prefix : String) (f : Nat -> Nat) : Handler := { run := fun s => f (String.length (prefix ++ s)) }\n#eval (capture \"hello\" (Nat.add 34)).run \"abc\"",
        "42",
    );
    run(
        "structure Box (A : Type) where\n  value : A\nstructure Factory where\n  make : Nat -> Box Nat\ndef use (f : Factory) : Nat := (f.make 42).value\n#eval use { make := Box.mk }",
        "42",
    );
}
#[test]
fn constructor_captures_are_strict_and_shared_but_unselected_records_are_lazy() {
    let prefix = "structure Handler where\n  run : Nat -> Nat\n  ignored : Nat\ndef work (n : Nat) : Nat := match n with | .zero => 0 | .succ k => work k + 1\ndef make (n : Nat) : Handler := { run := Nat.add (work n), ignored := work n }\ndef use (h : Handler) : Nat := h.run 1 + h.run 1\n";
    let idle = run(&format!("{prefix}#eval use (make 0)"), "2");
    let busy = run(&format!("{prefix}#eval use (make 30)"), "62");
    assert!(busy > idle + 30);
    let duplicated = run(
        &format!("{prefix}#eval (make 30).run 1 + (make 30).run 1"),
        "62",
    );
    assert!(busy < duplicated, "field capture was duplicated");
    let lazy = run(
        &format!("{prefix}#eval use (if true then make 0 else make 30)"),
        "2",
    );
    assert!(lazy < busy, "unselected record branch was evaluated");
}
#[test]
fn stopped_closure_layouts_do_not_publish_and_retries_are_deterministic() {
    let base = engine();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    let source = b"structure Handler where\n  run : Nat -> Nat\ndef use (h : Handler) : Nat := h.run 40\n#eval use { run := Nat.add 2 }";
    let mut small = limits();
    small.ingress.fir.max_closure_types = 0;
    assert!(
        base.execute_source_definitions(&[source], &options, small)
            .is_err()
    );
    small = limits();
    small.vm.max_steps = 1;
    assert!(matches!(
        base.execute_source_definitions(&[source], &options, small)
            .unwrap(),
        Outcome::Inconclusive(_)
    ));
    assert_eq!(base.logical_root(&options), root);
    let one = base
        .execute_source_definitions(&[source], &options, limits())
        .unwrap()
        .into_complete()
        .unwrap();
    let two = base
        .execute_source_definitions(&[source], &options, limits())
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(
        one.executions.last().unwrap().flbc_artifact,
        two.executions.last().unwrap().flbc_artifact
    );
    assert_eq!(
        one.engine.logical_root(&options),
        two.engine.logical_root(&options)
    );
}

#[test]
fn higher_order_methods_and_closure_bearing_results_keep_their_interfaces() {
    run(
        "structure Runner where\n  run : (Nat -> Nat) -> Nat\ndef use (r : Runner) : Nat := r.run (Nat.add 2)\n#eval use { run := fun (f : Nat -> Nat) => f 40 }",
        "42",
    );
    run(
        "structure Box (A : Type) where\n  value : A\nstructure Factory where\n  make : Nat -> Box (Nat -> Nat)\ndef make (n : Nat) : Box (Nat -> Nat) := Box.mk (Nat.add n)\ndef use (f : Factory) : Nat := (f.make 2).value 40\n#eval use { make := make }",
        "42",
    );
}

#[test]
fn selected_closures_can_be_called_after_variant_and_boolean_elimination() {
    run(
        "#eval (Option.getD (Option.some (Nat.add 2)) Nat.succ) 40",
        "42",
    );
    run(
        "def choose (b : Bool) (n : Nat) : Nat := (if b then Nat.add 2 else Nat.sub 2) n\n#eval choose true 40",
        "42",
    );
    run(
        "def choose (b : Bool) : Nat -> Nat := if b then (fun n => n + 2) else (fun n => n + 3)\n#eval choose false 39",
        "42",
    );
}

#[test]
fn nullary_and_singleton_matches_return_captured_functions() {
    run(
        "#eval (Option.getD (Option.none : Option (Nat -> Nat)) (Nat.add 2)) 40",
        "42",
    );
    run(
        "inductive Choice where | first | second\ndef select (x : Choice) : Nat -> Nat := match x with | .first => fun n => n + 2 | .second => fun n => n + 3\n#eval select Choice.second 39",
        "42",
    );
    run(
        "structure Handler where\n  run : Nat -> Nat\ndef extract (h : Handler) : Nat -> Nat := match h with | .mk f => f\n#eval extract { run := Nat.add 2 } 40",
        "42",
    );
}
