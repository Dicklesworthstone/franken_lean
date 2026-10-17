//! Native source variants, payload ownership, lazy matches and replay.
#![forbid(unsafe_code)]
use fln::{
    Budget, Engine, EngineAdmissionLimits, EngineExecutionError, EngineExecutionLimits, KVMap,
    Mode, SourceCheckLimits, VmExit,
};
use fln_comp::ingress::IngressError;
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
    run_with(&engine(), source, expected);
}
fn run_with(base: &Engine, source: &str, expected: &str) -> u64 {
    let batch = base
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
    value.usage.steps
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
fn variant_functions_erase_proof_domains_without_erasing_data_arguments() {
    // Direct source recursors use the frontier lane. Ordinary source deriving
    // exercises these generated recursors in the default lane separately.
    let base = Engine::builder()
        .mode(Mode::Frontier)
        .build_with_source_seed(EngineAdmissionLimits::new(limits().kernel))
        .unwrap()
        .into_complete()
        .unwrap();
    let literal = "fun (choice : Choice) => (n : Nat) -> choice = choice -> n = n -> Nat";
    for motive in [
        format!("({literal})"),
        format!("((fun (m : Choice -> Type) => m) ({literal}))"),
        format!("(let m : Choice -> Type := {literal}; m)"),
    ] {
        let source = format!(
            "inductive Choice where\n | empty\n | offset (value : Nat)\ndef select (choice : Choice) : (n : Nat) -> choice = choice -> n = n -> Nat := @Choice.rec {motive} (fun n choiceProof numberProof => n + 2) (fun value n choiceProof numberProof => value + n) choice\n"
        );
        for (choice, input, expected) in [("Choice.empty", 37, "39"), ("Choice.offset 5", 37, "42")]
        {
            run_with(
                &base,
                &format!("{source}#eval select ({choice}) {input} (by rfl) (by rfl)"),
                expected,
            );
        }
    }
}

#[test]
fn variant_motives_that_select_runtime_representations_are_refused() {
    let base = Engine::builder()
        .mode(Mode::Frontier)
        .build_with_source_seed(EngineAdmissionLimits::new(limits().kernel))
        .unwrap()
        .into_complete()
        .unwrap();
    let options = KVMap::new();
    let before = base.logical_root(&options);
    let source = b"inductive Choice where\n | number\n | text\ndef Selected (choice : Choice) : Type := match choice with | .number => Nat | .text => String\n#eval @Choice.rec Selected (7 : Nat) \"seven\" Choice.number";
    let mut error = base
        .execute_source_definitions(&[source], &options, limits())
        .expect_err("a static motive must not choose a representation from a runtime major");
    while let EngineExecutionError::BatchCommand { error: inner, .. } = error {
        error = *inner;
    }
    assert!(
        matches!(
            error,
            EngineExecutionError::Ingress(IngressError::UnsupportedNode {
                kind: "dependent variant recursor result"
            })
        ),
        "the logical declarations must first be admitted: {error:?}"
    );
    assert_eq!(base.logical_root(&options), before);
}

#[test]
fn fully_applied_variant_functions_keep_stage_work_and_argument_order() {
    let base = engine();
    let definitions = r#"
inductive Choice where
  | empty
  | offset (value : Nat)
def expensive (n : Nat) : Nat := match n with
  | .zero => 0
  | .succ k => expensive k
def use (choice : Choice) (stage before after : Nat) : Nat :=
  ((match choice with
    | .empty => fun (x y : Nat) => x * 10 + y
    | .offset value => fun (x : Nat) => by
      let spent := expensive stage
      exact fun (y : Nat) => x * 10 + y + value + spent) : Nat -> Nat -> Nat)
    (by let spent := expensive before; exact 4)
    (by let spent := expensive after; exact 2)
"#;
    let steps = |expression: &str, expected| {
        run_with(
            &base,
            &format!("{definitions}\n#eval {expression}"),
            expected,
        )
    };
    // The two branches have the same logical telescope but different actual
    // stages. Swapping the arguments changes both observable answers.
    let flat = steps("use Choice.empty 0 0 0", "42");
    let staged = steps("use (Choice.offset 5) 0 0 0", "47");
    let work = steps("expensive 20", "0") - steps("expensive 0", "0");
    assert!(work > 20);
    for arguments in ["20 0 0", "0 20 0", "0 0 20"] {
        assert_eq!(
            steps(&format!("use (Choice.offset 5) {arguments}"), "47") - staged,
            work,
            "the selected stage and each actual operand must run exactly once"
        );
    }
    assert_eq!(
        steps("use (Choice.offset 5) 20 20 20", "47") - staged,
        3 * work
    );
    assert_eq!(
        steps("use Choice.empty 100000 0 0", "42"),
        flat,
        "the unselected function's stage must remain lazy"
    );
}

#[test]
fn nested_variant_ascriptions_preserve_strict_prefixes_and_replay() {
    let definitions = r#"
inductive Choice where
  | empty
  | offset (value : Nat)
def expensive (n : Nat) : Nat := match n with
  | .zero => 0
  | .succ k => expensive k
def prefixed (choice : Choice) (setupFuel stage before after : Nat) : Nat :=
  (((by
      let setup := expensive setupFuel
      exact match choice with
        | .empty => fun (x y : Nat) => x * 10 + y + setup
        | .offset value => fun (x : Nat) => by
          let spent := expensive stage
          exact fun (y : Nat) => x * 10 + y + value + setup + spent
    ) : Nat -> Nat -> Nat) : Nat -> Nat -> Nat)
    (by let spent := expensive before; exact 4)
    (by let spent := expensive after; exact 2)
"#;
    let options = KVMap::new();
    let base = engine()
        .check_source_files(
            &[definitions.as_bytes()],
            &options,
            SourceCheckLimits::new(limits().admission()),
        )
        .unwrap()
        .into_complete()
        .unwrap()
        .engine;
    let root = base.logical_root(&options);
    let steps = |expression: &str, expected| {
        let source = format!("#eval {expression}");
        let batch = base
            .execute_source_definitions(&[source.as_bytes()], &options, limits())
            .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
            .into_complete()
            .unwrap();
        let execution = batch.executions.last().unwrap();
        let VmExit::Returned(value) = &execution.exit else {
            panic!("ascribed variant evaluation did not return");
        };
        assert_eq!(fln::nat_decimal(&value.value).as_deref(), Some(expected));
        let VmExit::Returned(replayed) =
            fln::execute_flbc_artifact(&execution.flbc_artifact, &options, Default::default())
                .unwrap()
                .into_complete()
                .unwrap()
        else {
            panic!("ascribed variant bytecode did not return");
        };
        assert_eq!(fln::nat_decimal(&replayed.value).as_deref(), Some(expected));
        assert_eq!(value.usage.steps, replayed.usage.steps);
        value.usage.steps
    };
    let work = steps("expensive 20", "0") - steps("expensive 0", "0");
    assert!(work > 20);
    let staged = steps("prefixed (Choice.offset 5) 0 0 0 0", "47");
    assert_eq!(
        steps("prefixed (Choice.offset 5) 20 0 0 0", "47") - staged,
        work,
        "the strict prefix executes exactly once before constructing the callback"
    );
    assert_eq!(
        steps("prefixed (Choice.offset 5) 20 20 20 20", "47") - staged,
        4 * work
    );
    let flat = steps("prefixed Choice.empty 0 0 0 0", "42");
    assert_eq!(
        steps("prefixed Choice.empty 20 100000 0 0", "42") - flat,
        work,
        "prefix work stays strict while the unselected branch's stage stays lazy"
    );
    assert_eq!(base.logical_root(&options), root);
}

#[test]
fn escaping_and_underapplied_variant_ascriptions_keep_exact_interfaces() {
    let definitions = r#"
inductive Choice where
  | empty
  | offset (value : Nat)
def expensive (n : Nat) : Nat := match n with
  | .zero => 0
  | .succ k => expensive k
def take (f : Nat -> Nat -> Nat) : Nat := f 4 2
"#;
    let branches = r#"
match choice with
  | .empty => fun (x y : Nat) => x * 10 + y
  | .offset value => fun (x : Nat) => by
    let spent := expensive stage
    exact fun (y : Nat) => x * 10 + y + value + spent
"#;
    let base = engine();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    for operation in [
        format!(
            "def escaped (choice : Choice) (stage : Nat) : Nat := take (({branches}) : Nat -> Nat -> Nat)\n#eval escaped (Choice.offset 5) 0"
        ),
        format!(
            "def partiallySelected (choice : Choice) (stage : Nat) : Nat -> Nat := (({branches}) : Nat -> Nat -> Nat) 4\n#eval partiallySelected (Choice.offset 5) 0 2"
        ),
    ] {
        let source = format!("{definitions}\n{operation}");
        let mut error = base
            .execute_source_definitions(&[source.as_bytes()], &options, limits())
            .expect_err("escaping mixed-stage branches still require one exact callable interface");
        while let EngineExecutionError::BatchCommand { error: inner, .. } = error {
            error = *inner;
        }
        assert!(
            matches!(
                error,
                EngineExecutionError::Ingress(IngressError::LambdaResultType { .. })
            ),
            "logical admission must succeed before the representation refusal: {error:?}"
        );
        assert_eq!(base.logical_root(&options), root);
    }
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
