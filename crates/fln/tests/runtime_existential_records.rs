//! Hidden record carriers retain their boxed values across real callback and
//! container boundaries. Every program goes through source checking, FIR/FLBC
//! validation and the native VM; no Reference result supplies execution.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap, Outcome, VmExit};

fn admission() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}
fn engine() -> Engine {
    Engine::with_source_seed(admission())
        .unwrap()
        .into_complete()
        .unwrap()
}
fn execute(base: &Engine, source: &str) -> fln::DefinitionBatchExecution {
    base.execute_source_definitions(
        &[source.as_bytes()],
        &KVMap::new(),
        EngineExecutionLimits::new(admission().kernel),
    )
    .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
    .into_complete()
    .unwrap()
}
fn run(source: &str, expected: &str) {
    let result = execute(&engine(), source);
    let VmExit::Returned(value) = &result.executions.last().unwrap().exit else {
        panic!("not returned: {source}")
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
        Some(expected),
        "{source}"
    );
}

const SHOWN: &str =
    "structure Shown where\n  carrier : Type\n  value : carrier\n  measure : carrier -> Nat\n";

#[test]
fn a_generic_receiver_calls_hidden_nat_and_string_callbacks() {
    run(
        &format!(
            "{SHOWN}\
        def n : Shown := {{ carrier := Nat, value := 40, measure := fun x => x + 1 }}\n\
        def s : Shown := {{ carrier := String, value := \"a\", measure := String.length }}\n\
        def read (p : Shown) : Nat := p.measure p.value\n\
        #eval read n + read s"
        ),
        "42",
    );
}

#[test]
fn constructor_minors_keep_hidden_carriers_as_type_metadata() {
    run(
        "inductive HiddenChoice : Type 1 where\n  | empty\n  | pack (A : Type) (value : A) (measure : A -> Nat)\n\
        def read (p : HiddenChoice) : Nat := match p with\n  | .empty => 0\n  | .pack A value measure => measure value\n\
        #eval read (HiddenChoice.pack String \"boxed\" String.length) + read HiddenChoice.empty",
        "5",
    );
    run(
        &format!(
            "{SHOWN}\
        def read (p : Shown) : Nat := match p with | .mk A value measure => measure value\n\
        #eval read (Shown.mk Nat 40 (fun n => n + 2))"
        ),
        "42",
    );
}

#[test]
fn dependent_record_elimination_returns_the_hidden_carrier() {
    run(
        "structure Package where\n  carrier : Type\n  value : carrier\n\
        def unpack (p : Package) : p.carrier := by cases p with | mk A value => exact value\n\
        def n : Package := { carrier := Nat, value := 40 }\n\
        def s : Package := { carrier := String, value := \"ab\" }\n\
        #eval Nat.add (unpack n) (String.length (unpack s))",
        "42",
    );
}

#[test]
fn dependent_record_elimination_preserves_callable_and_container_results() {
    run(
        "structure Package where\n  carrier : Type\n  value : carrier\n  change : carrier -> carrier\n\
        def getChange (p : Package) : p.carrier -> p.carrier := by cases p with | mk A value change => exact change\n\
        def read (p : Package) : p.carrier := getChange p p.value\n\
        def make (suffix : String) : Package := { carrier := String, value := \"a\", change := fun s => s ++ suffix }\n\
        #eval String.length (read (make \"bc\") : String)",
        "3",
    );
    run(
        "structure Package where\n  carrier : Type\n  values : List carrier\n\
        def unpack (p : Package) : List p.carrier := by cases p with | mk A values => exact values\n\
        def n : Package := { carrier := Nat, values := [17, 25] }\n\
        #eval (unpack n : List Nat).foldl Nat.add 0",
        "42",
    );
}

#[test]
fn dependent_record_elimination_keeps_source_type_checks_and_failure_isolation() {
    let base = engine();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    let prefix = "structure Package where\n  carrier : Type\n  value : carrier\n\
        def unpack (p : Package) : p.carrier := by cases p with | mk A value => exact value\n\
        def n : Package := { carrier := Nat, value := 42 }\n";
    let invalid = format!("{prefix}#eval String.length (unpack n)");
    assert!(
        base.execute_source_definitions(
            &[invalid.as_bytes()],
            &options,
            EngineExecutionLimits::new(admission().kernel),
        )
        .is_err()
    );
    assert_eq!(base.logical_root(&options), root);
    let valid = format!("{prefix}#eval (unpack n : Nat)");
    let first = execute(&base, &valid);
    let second = execute(&base, &valid);
    let VmExit::Returned(value) = &first.executions.last().unwrap().exit else {
        panic!("clean retry did not return")
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
        Some("42")
    );
    assert_eq!(
        first.executions.last().unwrap().flbc_artifact,
        second.executions.last().unwrap().flbc_artifact
    );
    assert_eq!(base.logical_root(&options), root);
}

#[test]
fn hidden_callbacks_box_results_and_preserve_owned_captures() {
    run(
        "structure Pipeline where\n  carrier : Type\n  value : carrier\n  change : carrier -> carrier\n  render : carrier -> String\n\
        def make (suffix : String) : Pipeline := { carrier := String, value := \"a\", change := fun s => s ++ suffix, render := fun s => s ++ s }\n\
        def read (p : Pipeline) : Nat := String.length (p.render (p.change p.value))\n\
        #eval read (make \"bc\")",
        "6",
    );
}

#[test]
fn hidden_callbacks_are_passed_returned_and_partially_applied() {
    run(
        "structure Combine where\n  carrier : Type\n  left : carrier\n  right : carrier\n  combine : carrier -> carrier -> Nat\n\
        def get (p : Combine) : p.carrier -> Nat := p.combine p.left\n\
        def read (p : Combine) : Nat := get p p.right\n\
        def p : Combine := { carrier := Nat, left := 17, right := 25, combine := Nat.add }\n\
        #eval read p",
        "42",
    );
}

#[test]
fn hidden_lists_are_consumed_through_generic_receivers() {
    run(
        "structure Listed where\n  carrier : Type\n  values : List carrier\n\
        def count (p : Listed) : Nat := p.values.length\n\
        def n : Listed := { carrier := Nat, values := [17, 25] }\n\
        def s : Listed := { carrier := String, values := [\"a\", \"b\", \"c\"] }\n\
        #eval count n + count s",
        "5",
    );
}

#[test]
fn hidden_lists_and_callbacks_compose_in_a_generic_fold() {
    run(
        "structure Collection where\n  carrier : Type\n  values : List carrier\n  measure : carrier -> Nat\n\
        def total (p : Collection) : Nat := p.values.foldl (fun n x => n + p.measure x) 0\n\
        def numbers : Collection := { carrier := Nat, values := [17, 20], measure := fun n => n }\n\
        def words : Collection := { carrier := String, values := [\"ab\", \"cde\"], measure := String.length }\n\
        #eval total numbers + total words",
        "42",
    );
}

#[test]
fn nested_containers_share_the_verified_recursive_layout() {
    run(
        "structure Nested where\n  carrier : Type\n  values : List (List carrier)\n\
        def count (p : Nested) : Nat := p.values.foldl (fun n (xs : List p.carrier) => n + List.length xs) 0\n\
        def p : Nested := { carrier := String, values := [[\"a\", \"b\"], [\"c\"]] }\n\
        #eval count p",
        "3",
    );
}

#[test]
fn parameterized_shells_resolve_hidden_carriers_in_the_original_context() {
    run(
        "structure Shell (Label : Type) where\n  label : Label\n  carrier : Type\n  values : List carrier\n  measure : carrier -> Nat\n\
         def total (p : Shell String) : Nat := p.values.foldl (fun n x => n + p.measure x) (String.length p.label)\n\
         def p : Shell String := { label := \"hello\", carrier := Nat, values := [17, 20], measure := fun n => n }\n\
         #eval total p",
        "42",
    );
}

#[test]
fn repacking_and_record_updates_preserve_existing_erased_callbacks() {
    run(
        &format!(
            "{SHOWN}\
        def repack (p : Shown) : Shown := {{ carrier := p.carrier, value := p.value, measure := p.measure }}\n\
        def read (p : Shown) : Nat := p.measure p.value\n\
        def p : Shown := {{ carrier := Nat, value := 41, measure := fun x => x + 1 }}\n\
        #eval read (repack p)"
        ),
        "42",
    );
}

#[test]
fn callbacks_return_hidden_immediate_and_heap_naturals_and_booleans() {
    for (carrier, value, step, measure, expected) in [
        ("Nat", "41", "fun n => n + 1", "fun n => n", "42"),
        (
            "Nat",
            "18446744073709551616",
            "fun n => n + 1",
            "fun n => n",
            "18446744073709551617",
        ),
        (
            "Bool",
            "true",
            "fun b => b",
            "fun b => if b then 42 else 0",
            "42",
        ),
    ] {
        run(
            &format!(
                "structure Step where\n  carrier : Type\n  value : carrier\n  step : carrier -> carrier\n  measure : carrier -> Nat\n\
             def p : Step := {{ carrier := {carrier}, value := {value}, step := {step}, measure := {measure} }}\n\
             def read (p : Step) : Nat := p.measure (p.step p.value)\n#eval read p"
            ),
            expected,
        );
    }
}

#[test]
fn an_unused_adapter_initializer_runs_once_and_exhaustion_is_not_success() {
    let base = engine();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    let program = |cost| {
        format!(
            "{SHOWN}\
         def spend (n : Nat) : Nat := match n with | .zero => 0 | .succ k => spend k + 1\n\
         def make (cost : Nat) : Shown := {{ carrier := Nat, value := 42, measure := let paid : Nat := spend cost; fun n => n }}\n\
         def read (p : Shown) : Nat := p.measure p.value\n#eval read (make {cost})"
        )
    };
    let mut limits = EngineExecutionLimits::new(admission().kernel);
    limits.vm.max_steps = 2000;
    limits.vm.max_stack_depth = 256;
    assert!(matches!(
        base.execute_source_definitions(&[program(100000).as_bytes()], &options, limits,)
            .unwrap(),
        Outcome::Inconclusive(_)
    ));
    assert_eq!(base.logical_root(&options), root);
    let cheap = program(0);
    let retry = || {
        base.execute_source_definitions(&[cheap.as_bytes()], &options, limits)
            .unwrap()
            .into_complete()
            .unwrap()
    };
    let first = retry();
    let second = retry();
    let VmExit::Returned(value) = &first.executions.last().unwrap().exit else {
        panic!("clean retry did not return")
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
        Some("42")
    );
    assert_eq!(
        first.executions.last().unwrap().flbc_artifact,
        second.executions.last().unwrap().flbc_artifact
    );
    assert_eq!(base.logical_root(&options), root);
}

#[test]
fn lists_of_hidden_callbacks_are_rebuilt_with_real_adapters() {
    run(
        r#"structure Handlers where
  carrier : Type
  value : carrier
  values : List (carrier -> Nat)
def total (p : Handlers) : Nat :=
  p.values.foldl (fun (n : Nat) (f : p.carrier -> Nat) => n + f p.value) 0
def make (offset : Nat) : Handlers :=
  { carrier := Nat, value := 20, values := [fun n => n + offset, fun n => n] }
#eval total (make 2)"#,
        "42",
    );
}

#[test]
fn nested_callback_containers_retain_owned_values_and_captures() {
    run(
        r#"structure NestedHandlers where
  carrier : Type
  value : carrier
  values : List (List (carrier -> String))
def total (p : NestedHandlers) : Nat :=
  p.values.foldl (fun (n : Nat) (fs : List (p.carrier -> String)) =>
    fs.foldl (fun (k : Nat) (f : p.carrier -> String) => k + String.length (f p.value)) n) 0
def make (suffix : String) : NestedHandlers :=
  { carrier := String, value := "x", values := [[fun s => s ++ suffix], [fun s => suffix ++ s]] }
#eval total (make "abc")"#,
        "8",
    );
}

#[test]
fn user_records_and_options_use_their_admitted_constructor_shapes() {
    run(
        r#"structure Slot (A : Type) where
  value : Option A
structure Packet where
  carrier : Type
  value : carrier
  handler : Slot (carrier -> Nat)
def read (p : Packet) : Nat := match p.handler.value with
  | .none => 0
  | .some f => f p.value
def p : Packet :=
  { carrier := Nat, value := 17, handler := Slot.mk (Option.some (fun n => n + 25)) }
#eval read p"#,
        "42",
    );
}

#[test]
fn recursive_user_containers_convert_every_child_and_callback() {
    run(
        r#"inductive Branch (A : Type) where
  | leaf (value : A)
  | node (left : Branch A) (right : Branch A)
def total {A : Type} (measure : A -> Nat) (tree : Branch A) : Nat := match tree with
  | .leaf value => measure value
  | .node left right => total measure left + total measure right
structure ForestHandlers where
  carrier : Type
  value : carrier
  handlers : Branch (carrier -> Nat)
def read (p : ForestHandlers) : Nat := total (fun (f : p.carrier -> Nat) => f p.value) p.handlers
def p : ForestHandlers :=
  { carrier := Nat, value := 20,
    handlers := Branch.node (Branch.leaf (fun n => n + 2)) (Branch.leaf (fun n => n)) }
#eval read p"#,
        "42",
    );
}

#[test]
fn recursive_container_callbacks_select_children_only_when_called() {
    run(
        r#"inductive Route (A : Type) where
  | leaf (value : A)
  | node (next : Nat -> Route A)
def read {A : Type} (measure : A -> Nat) (tree : Route A) : Nat := match tree with
  | .leaf value => measure value
  | .node next => read measure (next 20)
structure RouteHandlers where
  carrier : Type
  value : carrier
  handlers : Route (carrier -> Nat)
def total (p : RouteHandlers) : Nat := read (fun (f : p.carrier -> Nat) => f p.value) p.handlers
def p : RouteHandlers :=
  { carrier := Nat, value := 20, handlers := Route.node (fun offset => Route.leaf (fun n => n + offset + 2)) }
#eval total p"#,
        "42",
    );
}

#[test]
fn higher_order_hidden_callbacks_convert_arguments_and_results() {
    run(
        r#"structure Runner where
  carrier : Type
  value : carrier
  change : carrier -> carrier
  run : (carrier -> carrier) -> carrier
  measure : carrier -> Nat
def read (p : Runner) : Nat := p.measure (p.run p.change)
def p : Runner :=
  { carrier := Nat, value := 40, change := fun n => n + 2,
    run := fun f => f 40, measure := fun n => n }
#eval read p"#,
        "42",
    );
    run(
        r#"structure Runner where
  carrier : Type
  value : carrier
  make : Nat -> List (carrier -> Nat)
  consume : List (carrier -> Nat) -> Nat
def read (p : Runner) : Nat := p.consume (p.make 2)
def p : Runner :=
  { carrier := Nat, value := 20,
    make := fun offset => [fun n => n + offset, fun n => n],
    consume := fun (fs : List (Nat -> Nat)) =>
      fs.foldl (fun (n : Nat) (f : Nat -> Nat) => n + f 20) 0 }
#eval read p"#,
        "42",
    );
}

#[test]
fn partial_constructors_adapt_later_callback_and_container_arguments() {
    run(
        "structure Package where\n  carrier : Type\n  value : carrier\n\
         def make : Nat -> Package := Package.mk Nat\n\
         #eval (List.map make [17, 25]).length",
        "2",
    );
    run(
        "structure Listed where\n  carrier : Type\n  values : List carrier\n\
         def make : List String -> Listed := Listed.mk String\n\
         def read (p : Listed) : Nat := p.values.length\n\
         #eval read (make [\"a\", \"b\"])",
        "2",
    );
    run(
        r#"structure Handlers where
  carrier : Type
  value : carrier
  values : List (carrier -> Nat)
def make : List (Nat -> Nat) -> Handlers := Handlers.mk Nat 40
def read (p : Handlers) : Nat :=
  p.values.foldl (fun (n : Nat) (f : p.carrier -> Nat) => n + f p.value) 0
#eval read (make [fun n => n + 2])"#,
        "42",
    );
    run(
        &format!(
            "{SHOWN}def make : (Nat -> Nat) -> Shown := Shown.mk Nat 40\n\
             def read (p : Shown) : Nat := p.measure p.value\n#eval read (make (fun n => n + 2))"
        ),
        "42",
    );
}

#[test]
fn container_adapters_preserve_strict_initializers_and_resource_recovery() {
    let base = engine();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    let declarations = r#"def spend (n : Nat) : Nat := match n with | .zero => 0 | .succ k => spend k + 1
structure Handlers where
  carrier : Type
  values : List (carrier -> Nat)
def make (cost : Nat) : Handlers :=
  { carrier := Nat, values := let paid : Nat := spend cost; [fun n => n + 2] }
"#;
    let usage = |source: String| {
        let batch = execute(&base, &source);
        let VmExit::Returned(value) = &batch.executions.last().unwrap().exit else {
            panic!("strict initializer did not return")
        };
        value.usage.steps
    };
    let mapped = |cost| format!("{declarations}#eval (make {cost}).values.length");
    let direct = |cost| format!("{declarations}#eval let paid : Nat := spend {cost}; 1");
    assert_eq!(
        usage(mapped(60)) - usage(mapped(0)),
        usage(direct(60)) - usage(direct(0))
    );
    let mut limits = EngineExecutionLimits::new(admission().kernel);
    limits.vm.max_steps = 2000;
    assert!(matches!(
        base.execute_source_definitions(&[mapped(100000).as_bytes()], &options, limits)
            .unwrap(),
        Outcome::Inconclusive(_)
    ));
    let retry = || {
        base.execute_source_definitions(&[mapped(0).as_bytes()], &options, limits)
            .unwrap()
            .into_complete()
            .unwrap()
    };
    let one = retry();
    let two = retry();
    assert_eq!(
        one.executions.last().unwrap().flbc_artifact,
        two.executions.last().unwrap().flbc_artifact
    );
    assert_eq!(base.logical_root(&options), root);
}

#[test]
fn unsupported_container_profiles_do_not_publish_unconverted_closures() {
    let base = engine();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    let source = r#"mutual
inductive Tree (A : Type) where
  | leaf (value : A)
  | node (children : Forest A)
inductive Forest (A : Type) where
  | nil
  | cons (tree : Tree A) (rest : Forest A)
end
structure Handlers where
  carrier : Type
  values : Tree (carrier -> Nat)
def p : Handlers := { carrier := Nat, values := Tree.leaf (fun n => n + 2) }
"#;
    let error = base
        .execute_source_definitions(
            &[source.as_bytes()],
            &options,
            EngineExecutionLimits::new(admission().kernel),
        )
        .expect_err("mutual container adapters require their own recursive group");
    assert!(
        format!("{error:?}").contains("hidden container recursive profile"),
        "{error:?}"
    );
    assert_eq!(base.logical_root(&options), root);
    run("#eval 42", "42");
}

#[test]
fn callback_adapter_resource_refusals_preserve_the_snapshot() {
    let base = engine();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    let source = format!(
        "{SHOWN}def p : Shown := {{ carrier := Nat, value := 41, measure := fun n => n + 1 }}\n#eval p.measure p.value"
    );
    let mut limits = EngineExecutionLimits::new(admission().kernel);
    limits.ingress.fir.max_closure_types = 0;
    let error = base
        .execute_source_definitions(&[source.as_bytes()], &options, limits)
        .expect_err("closure type budget");
    assert!(format!("{error:?}").contains("ResourceLimit"), "{error:?}");
    assert_eq!(base.logical_root(&options), root);
    execute(&base, &source);
}

#[test]
fn erased_record_compilation_is_deterministic() {
    let base = engine();
    let source = format!(
        "{SHOWN}def p : Shown := {{ carrier := String, value := \"hello\", measure := String.length }}\n#eval p.measure p.value"
    );
    let one = execute(&base, &source);
    let two = execute(&base, &source);
    assert_eq!(one.executions.len(), two.executions.len());
    for (one, two) in one.executions.iter().zip(&two.executions) {
        assert_eq!(one.flbc_artifact, two.flbc_artifact);
        assert_eq!(one.declaration, two.declaration);
    }
}
