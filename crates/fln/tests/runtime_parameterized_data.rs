//! Ground data instantiations run through admission, FIR, FLBC and the real VM.
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
    let batch = engine()
        .execute_source_definitions(&[source.as_bytes()], &KVMap::new(), limits())
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .unwrap();
    let VmExit::Returned(value) = &batch.executions.last().unwrap().exit else {
        panic!("expected VM return")
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
        Some(expected),
        "{source}"
    );
    value.usage.steps
}

#[test]
fn builtin_collections_execute_their_real_recursors() {
    for (source, value) in [
        ("#eval List.length [1, 2, 3]", "3"),
        ("#eval List.foldl (fun (a b : Nat) => a - b) 10 [5, 2]", "3"),
        ("#eval List.foldr (fun (a b : Nat) => a - b) 10 [5, 2]", "5"),
        ("#eval Option.getD (Option.some 42) 7", "42"),
        ("#eval Option.getD (Option.none : Option Nat) 42", "42"),
        (
            "#eval Option.getD (List.head? (List.reverse [1, 2, 42])) 0",
            "42",
        ),
    ] {
        run(source, value);
    }
}

#[test]
fn named_intrinsics_and_scalar_constructors_are_first_class_callbacks() {
    for (source, value) in [
        ("#eval List.foldl Nat.sub 10 [5, 2]", "3"),
        ("#eval List.foldr Nat.sub 10 [5, 2]", "5"),
        (
            "#eval List.foldl Nat.add 37 (List.map String.length [\"ab\", \"cde\"])",
            "42",
        ),
        (
            "#eval Option.getD (Option.map Nat.succ (Option.some 41)) 0",
            "42",
        ),
        (
            "#eval List.foldl Nat.add 0 (List.map (Nat.sub 10) [3, 5])",
            "12",
        ),
    ] {
        run(source, value);
    }
}

#[test]
fn constructor_callbacks_keep_ground_result_types_and_supplied_fields() {
    run(
        "#eval Option.getD (Option.bind (Option.some 42) Option.some) 0",
        "42",
    );
    run(
        "#eval List.foldl Nat.add 0 (List.map List.length (List.map (List.cons 37) [[1, 2], []]))",
        "4",
    );
    run(
        "inductive Box where | make (n : Nat)\ndef apply (f : Nat -> Box) (n : Nat) : Nat := match f n with | .make a => a\n#eval apply Box.make 42",
        "42",
    );
    run(
        "inductive Pair (A B : Type) where | make (first : A) (second : B)\ndef read (p : Pair String Nat) : Nat := match p with | .make a b => String.length a + b\n#eval List.foldl Nat.add 0 (List.map read (List.map (Pair.make \"abc\") [7, 29]))",
        "42",
    );
}

#[test]
fn partial_callbacks_keep_runtime_captures_strict_and_shared() {
    let prefix = "def work (n : Nat) : Nat := match n with | .zero => 0 | .succ k => work k + 1\ndef ignore (f : Nat -> Nat) : Nat := 42\n";
    let idle = run(&format!("{prefix}#eval ignore (Nat.add 0)"), "42");
    let busy = run(&format!("{prefix}#eval ignore (Nat.add (work 30))"), "42");
    assert!(
        busy > idle + 30,
        "captured argument was not evaluated: {idle} vs {busy}"
    );
    let shared = run(
        &format!("{prefix}#eval let f : Nat -> Nat := Nat.add (work 30); f 1 + f 1"),
        "62",
    );
    let duplicated = run(
        &format!("{prefix}#eval Nat.add (work 30) 1 + Nat.add (work 30) 1"),
        "62",
    );
    assert!(
        shared < duplicated,
        "partial closure duplicated its capture: {shared} vs {duplicated}"
    );
    run(
        "def capture (prefix : String) : Nat := let f : String -> String := String.append prefix; String.length (f \"a\") + String.length (f \"b\")\n#eval capture \"abc\"",
        "8",
    );
}

#[test]
fn stopped_callback_conversion_leaves_no_partial_result_and_can_be_retried() {
    let base = engine();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    let source = b"#eval List.foldl Nat.add 0 (List.map Nat.succ [19, 21])";
    let mut limited = limits();
    limited.ingress.max_lambda_bindings = 0;
    assert!(
        base.execute_source_definitions(&[source], &options, limited)
            .is_err()
    );
    limited = limits();
    limited.vm.max_steps = 1;
    assert!(matches!(
        base.execute_source_definitions(&[source], &options, limited)
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
    assert_eq!(base.logical_root(&options), root);
    let VmExit::Returned(value) = &one.executions.last().unwrap().exit else {
        panic!("native return")
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
        Some("42")
    );
}

#[test]
fn nested_data_and_distinct_instantiations_have_distinct_layouts() {
    run("#eval List.length [[1, 2], [3], []]", "3");
    run(
        "#eval List.length [Option.some 1, Option.none, Option.some 42]",
        "3",
    );
    run(
        "#eval List.length [true, false] + List.length [1, 2, 3] + List.length [\"a\", \"b\", \"c\"]",
        "8",
    );
    run(
        "#eval List.foldl (fun (acc : Nat) (xs : List Nat) => acc + List.length xs) 37 [[1, 2], [3, 4, 5]]",
        "42",
    );
}

#[test]
fn polymorphic_callbacks_change_the_output_collection_representation() {
    run(
        "def measure.{u} {A : Type u} (f : A -> Nat) (xs : List A) : Nat := match xs with | .nil => 0 | .cons a tail => f a + measure f tail\n#eval measure (fun (s : String) => String.length s) [\"hello\", \"world\"]",
        "10",
    );
    run(
        "#eval List.foldl (fun (a b : Nat) => a + b) 37 (List.map (fun (s : String) => String.length s) [\"ab\", \"cde\"])",
        "42",
    );
    run(
        "#eval Option.getD (Option.map (fun (s : String) => String.length s) (Option.some \"abcdef\")) 0",
        "6",
    );
}

#[test]
fn user_families_and_record_matches_are_not_name_special_cases() {
    run(
        "inductive Choice (A B : Type) where | left (a : A) | right (b : B)\ndef read (x : Choice Nat String) : Nat := match x with | .left a => a | .right b => String.length b\n#eval read (Choice.left 37) + read (Choice.right \"hello\")",
        "42",
    );
    run(
        "structure Box (A : Type) where\n  value : A\ndef read (b : Box Nat) : Nat := match b with | .mk a => a\n#eval read { value := 42 }",
        "42",
    );
    run(
        "inductive Sequence (A : Type) where | nil | cons (x : A) (xs : Sequence A)\ndef size {A : Type} (xs : Sequence A) : Nat := match xs with | .nil => 0 | .cons x tail => size tail + 1\n#eval size (Sequence.cons \"hello\" (Sequence.cons \"world\" Sequence.nil))",
        "2",
    );
}

#[test]
fn runtime_fields_stay_strict_even_when_the_match_ignores_them() {
    let prefix = "def work (n : Nat) : Nat := match n with | .zero => 0 | .succ k => work k + 1\ndef ignore (x : Option Nat) : Nat := match x with | .none => 42 | .some n => 42\n";
    let idle = run(&format!("{prefix}#eval ignore (Option.some 0)"), "42");
    let busy = run(
        &format!("{prefix}#eval ignore (Option.some (work 30))"),
        "42",
    );
    assert!(
        busy > idle + 30,
        "runtime field was erased: {idle} vs {busy}"
    );
}

#[test]
fn reused_recursive_results_remain_shared_after_type_specialization() {
    let source = "def make (n : Nat) : List Nat := match n with | .zero => [] | .succ k => n :: make k\ndef double (xs : List Nat) : Nat := match xs with | .nil => 1 | .cons n tail => double tail + double tail\n#eval double (make 25)";
    let steps = run(source, "33554432");
    assert!(steps < 30000, "recursive hypothesis recomputed: {steps}");
}

#[test]
fn specialization_stops_and_late_errors_do_not_publish_an_engine() {
    let base = engine();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    let source = b"#eval List.length [1, 2, 3, 4, 5]";
    let mut small = limits();
    small.vm.max_steps = 20;
    assert!(matches!(
        base.execute_source_definitions(&[source], &options, small)
            .unwrap(),
        Outcome::Inconclusive(_)
    ));
    let mut small = limits();
    small.ingress.fir.max_constructors = 0;
    assert!(
        base.execute_source_definitions(&[source], &options, small)
            .is_err()
    );
    assert!(
        base.execute_source_definitions(
            &[b"#eval List.length [1, 2]\ntheorem bad : 0 = 1 := by rfl"],
            &options,
            limits(),
        )
        .is_err()
    );
    assert_eq!(base.logical_root(&options), root);
    base.execute_source_definitions(&[source], &options, limits())
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(base.logical_root(&options), root);
}

#[test]
fn repeated_compilation_keeps_bytecode_and_logical_declarations_identical() {
    let base = engine();
    let options = KVMap::new();
    let source = b"#eval List.length [\"hello\"] + List.length [[1, 2], [3]]";
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
    for (a, b) in one.executions.iter().zip(&two.executions) {
        assert_eq!(a.flbc_artifact, b.flbc_artifact);
        assert_eq!(a.declaration, b.declaration);
    }
    assert_eq!(
        one.engine.logical_root(&options),
        two.engine.logical_root(&options)
    );
}
