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
fn nonuniform_nested_callbacks_are_refused_without_retagging() {
    let base = engine();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    // Sharing this list would leave Nat -> Nat closures in slots requiring
    // boxed -> Nat. Container-wide callback mapping is not this feature.
    let source = b"structure Handlers where\n  carrier : Type\n  values : List (carrier -> Nat)\ndef p : Handlers := { carrier := Nat, values := [fun n => n + 1] }";
    let error = base
        .execute_source_definitions(
            &[source],
            &options,
            EngineExecutionLimits::new(admission().kernel),
        )
        .expect_err("nested callback adapters are required");
    assert!(format!("{error:?}").contains("Ingress("), "{error:?}");
    assert_eq!(base.logical_root(&options), root);
    execute(&base, "#eval 42");
}

#[test]
fn partial_constructors_preserve_uniform_slots_and_refuse_unsupplied_adapters() {
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
    let base = engine();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    let source = b"structure Handlers where\n  carrier : Type\n  values : List (carrier -> carrier)\ndef make : List (Nat -> Nat) -> Handlers := Handlers.mk Nat\n#eval (make []).values.length";
    let error = base
        .execute_source_definitions(
            &[source],
            &options,
            EngineExecutionLimits::new(admission().kernel),
        )
        .expect_err("an unsupplied nested callback still requires an adapter");
    assert!(
        format!("{error:?}").contains("partial hidden constructor requires an adapter"),
        "{error:?}"
    );
    assert_eq!(base.logical_root(&options), root);
    execute(&base, "#eval 42");
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
