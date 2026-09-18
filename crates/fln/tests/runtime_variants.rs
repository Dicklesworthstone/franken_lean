//! Native source variants, payload ownership, lazy matches and replay.
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
fn run(source: &str, expected: &str) {
    let batch = engine()
        .execute_source_definitions(&[source.as_bytes()], &KVMap::new(), limits())
        .unwrap_or_else(|e| panic!("{source}\n{e:?}"))
        .into_complete()
        .unwrap();
    let VmExit::Returned(value) = &batch.executions.last().unwrap().exit else {
        panic!("VM return");
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
        Some(expected),
        "{source}"
    );
}
const RESULT: &str =
    "inductive Result where\n | missing\n | text (s : String)\n | number (n : Nat)\n";
const SCORE: &str = "def score (r : Result) : Nat := match r with | .missing => 0 | .text s => String.length s | .number n => n\n";
#[test]
fn constructors_with_different_payload_shapes_dispatch_in_semantic_order() {
    for (term, expected) in [
        ("Result.missing", "0"),
        ("Result.text \"hello\"", "5"),
        ("Result.number 42", "42"),
    ] {
        run(&format!("{RESULT}{SCORE}#eval score ({term})"), expected);
    }
}
#[test]
fn nullary_enumerations_are_native_tagged_values() {
    run(
        "inductive Colour where\n | blue\n | red\n | green\ndef code (c : Colour) : Nat := match c with | .blue => 17 | .red => 25 | .green => 42\n#eval code Colour.green + code Colour.blue",
        "59",
    );
}
#[test]
fn variants_and_nested_records_share_checked_object_fields() {
    run(
        &format!(
            "{RESULT}{SCORE}structure Box where\n  result : Result\n  label : String\ndef scoreBox (b : Box) : Nat := score b.result + String.length b.label\n#eval scoreBox {{ result := Result.number 37, label := \"hello\" }}"
        ),
        "42",
    );
    run(
        "structure Point where\n  x : Nat\n  y : Nat\ninductive Choice where\n | empty\n | point (p : Point)\ndef score (c : Choice) : Nat := match c with | .empty => 0 | .point p => p.x + p.y\n#eval score (Choice.point { x := 17, y := 25 })",
        "42",
    );
}
#[test]
fn matches_return_owned_variants_and_capture_local_helpers() {
    run(
        &format!(
            "{RESULT}{SCORE}def modify (delta : Nat) (r : Result) : Result := let bump (n : Nat) : Nat := n + delta; match r with | .missing => Result.missing | .text s => Result.text (s ++ s) | .number n => Result.number (bump n)\n#eval score (modify 5 (Result.number 37)) + score (modify 0 (Result.text \"\"))"
        ),
        "42",
    );
}
#[test]
fn nested_matches_and_shared_payloads_preserve_owned_strings() {
    run(
        &format!(
            "{RESULT}def count (r : Result) : Nat := match r with | .missing => 0 | .text s => let again : Result := Result.text (s ++ s); (match again with | .missing => 1 | .text t => String.length s + String.length t | .number n => n) | .number n => n\n#eval count (Result.text \"abcdefghijklmn\")"
        ),
        "42",
    );
}
#[test]
fn nat_recursion_can_return_variants_and_carry_them_as_accumulators() {
    run(
        &format!(
            "{RESULT}{SCORE}def walk (n : Nat) (r : Result) : Result := match n with | .zero => r | .succ k => walk k (Result.number (score r + 1))\n#eval score (walk 7 (Result.number 35))"
        ),
        "42",
    );
}
#[test]
fn unused_constructor_branches_are_not_executed() {
    run(
        &format!(
            "{RESULT}def score (r : Result) : Nat := match r with | .missing => 42 | .text s => 2 ^ 1000000000000000000000000 | .number n => n\n#eval score Result.missing"
        ),
        "42",
    );
}
#[test]
fn invalid_branch_payload_types_do_not_publish_partial_success() {
    let base = engine();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    for bad in [
        "def bad (r : Result) : Nat := match r with | .missing => 0 | .text s => s | .number n => n",
        "def bad (r : Result) : Nat := match r with | .missing => 0 | .text s => 1",
        "def bad : Result := Result.number true",
    ] {
        let source = format!("{RESULT}#eval 42\n{bad}");
        assert!(
            base.execute_source_definitions(&[source.as_bytes()], &options, limits())
                .is_err(),
            "{bad}"
        );
        assert_eq!(base.logical_root(&options), root);
    }
}

#[test]
fn different_families_with_identical_tags_keep_payload_layouts_distinct() {
    run(
        "inductive A where\n | z (x : Nat)\n | a\ninductive B where\n | z (s : String)\n | a\ndef left (x : A) : Nat := match x with | .z n => n | .a => 0\ndef right (x : B) : Nat := match x with | .z s => String.length s | .a => 0\n#eval left (A.z 37) + right (B.z \"hello\")",
        "42",
    );
}
#[test]
fn distinct_preparations_produce_identical_replayable_variant_bytecode() {
    let base = engine();
    let options = KVMap::new();
    let source = format!("{RESULT}{SCORE}#eval score (Result.number 42)");
    let root = base.logical_root(&options);
    let compile = || {
        base.execute_source_definitions(&[source.as_bytes()], &options, limits())
            .unwrap()
            .into_complete()
            .unwrap()
    };
    let one = compile();
    let two = compile();
    assert_eq!(one.result_logical_root, two.result_logical_root);
    let bytes = &one.executions.last().unwrap().flbc_artifact;
    assert_eq!(bytes, &two.executions.last().unwrap().flbc_artifact);
    let program =
        fln_comp::flbc::decode_canonical(bytes, fln_comp::flbc::CodecLimits::default()).unwrap();
    let fln::Outcome::Complete(VmExit::Returned(value)) = fln_vm::interpreter::execute(
        &program,
        fln_vm::interpreter::ExecutionLimits::default(),
        None,
    ) else {
        panic!("replay");
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
        Some("42")
    );
    assert_eq!(base.logical_root(&options), root);
}
#[test]
fn layout_and_branch_limits_preserve_the_original_snapshot() {
    let base = engine();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    let source = format!("{RESULT}{SCORE}#eval score (Result.number 42)");
    for small in [
        {
            let mut x = limits();
            x.ingress.max_lambda_bindings = 0;
            x
        },
        {
            let mut x = limits();
            x.ingress.fir.max_constructors = 1;
            x
        },
        {
            let mut x = limits();
            x.ingress.fir.max_blocks = 2;
            x
        },
    ] {
        assert!(
            base.execute_source_definitions(&[source.as_bytes()], &options, small)
                .is_err()
        );
        assert_eq!(base.logical_root(&options), root);
    }
    run(&source, "42");
}
