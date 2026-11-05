//! All expected values are shared verbatim with the actual pinned Lean oracle.
#![forbid(unsafe_code)]
use super::*;
use fln::{
    CheckerAdmissionGround, ClosedVmValue, EngineExecutionLimits, FlbcExecutionLimits, VmExit,
};
use fln_comp::flbc::{CodecLimits, Instruction, decode_canonical, encode_canonical};
use fln_rt::obj::Obj;
use fln_vm::interpreter::{ExecutionLimits, execute_function};

#[derive(Debug)]
enum Expected<'a> {
    Nat(&'a str),
    String(&'a str),
}

fn expected_values(source: &str) -> Vec<Expected<'_>> {
    let mut values = Vec::new();
    let mut pending = None;
    for line in source.lines().map(str::trim) {
        if let Some(value) = line.strip_prefix("-- FLN_EXPECT_NAT ") {
            assert!(pending.is_none(), "exactly one expectation per evaluation");
            assert!(!value.is_empty() && value.bytes().all(|byte| byte.is_ascii_digit()));
            pending = Some(Expected::Nat(value));
        } else if let Some(value) = line.strip_prefix("-- FLN_EXPECT_STRING ") {
            assert!(pending.is_none(), "exactly one expectation per evaluation");
            pending = Some(Expected::String(value));
        } else if line.starts_with("#eval ") {
            values.push(
                pending
                    .take()
                    .expect("every actual evaluation has an expected value"),
            );
        }
    }
    assert!(pending.is_none(), "no expectation may omit its evaluation");
    values
}

fn assert_value(exit: &VmExit, expected: &Expected<'_>, label: &str, index: usize) {
    match expected {
        Expected::Nat(expected) => {
            let VmExit::Returned(result) = exit else {
                panic!("{label} evaluation {index} must return a Nat: {exit:?}");
            };
            assert_eq!(
                fln_vm::interpreter::nat_decimal(&result.value).as_deref(),
                Some(*expected),
                "{label} evaluation {index}",
            );
        }
        Expected::String(expected) => {
            assert_eq!(
                fln::closed_vm_value(exit).expect("closed native result"),
                Some(ClosedVmValue::String((*expected).to_owned())),
                "{label} evaluation {index}",
            );
        }
    }
}

// The live oracle includes String.Defs for its String fixtures. Native tests
// supply checked imports and check every used declaration; Nat-only fixtures
// also run against the smaller Array/List closure.
const ADMITTED_IMPORT_HEADER: &str = "prelude\nimport Init.Data.Array.Basic\nimport Init.Data.List.Control\nimport Init.Data.String.Defs\n\n";

fn commands_after_admitted_imports(source: &str) -> &str {
    if let Some(commands) = source.strip_prefix(ADMITTED_IMPORT_HEADER) {
        return commands;
    }
    assert!(
        !source
            .lines()
            .any(|line| { matches!(line.split_whitespace().next(), Some("prelude" | "import")) }),
        "shared source imports must match the exact already-admitted fixture header",
    );
    source
}

pub(super) fn program(engine: &Engine, label: &str, source: &str, count: usize) {
    let expected = expected_values(source);
    assert_eq!(
        expected.len(),
        count,
        "{label}: preserve every shared oracle probe"
    );
    let options = KVMap::new();
    let before = engine.logical_root(&options);
    let completed = engine
        .execute_source_commands_with_checks(
            commands_after_admitted_imports(source).as_bytes(),
            &options,
            EngineExecutionLimits::new(Budget::for_stack_bytes(STACK)),
        )
        .unwrap_or_else(|error| panic!("{label}: actual admitted source execution: {error:?}"))
        .into_complete()
        .unwrap_or_else(|error| panic!("{label}: explicit execution budget: {error:?}"));
    let evaluations = &completed.batch.source_evaluation_indices;
    assert_eq!(evaluations.len(), expected.len(), "{label}");
    for (index, (&evaluation, expected)) in evaluations.iter().zip(&expected).enumerate() {
        let execution = &completed.batch.executions[evaluation];
        assert_eq!(execution.checker.schema, "fln.checker-admission/1");
        // Every counted evaluation is an `#eval` (see `expected_values`), and
        // #eval's auxiliary is unsafe at the pin (BuiltinEvalCommand.lean:92).
        assert_eq!(
            execution.checker.ground,
            CheckerAdmissionGround::UnsafeQuarantine,
            "{label} evaluation {index}",
        );
        assert_value(&execution.exit, expected, label, index);
        let decoded = decode_canonical(&execution.flbc_artifact, CodecLimits::default())
            .expect("Array program produces independently validated FLBC");
        assert_eq!(
            encode_canonical(&decoded, CodecLimits::default()).expect("canonical FLBC encoding"),
            execution.flbc_artifact,
            "{label} evaluation {index}: exact canonical artifact",
        );
        let replay = fln::execute_flbc_artifact(
            &execution.flbc_artifact,
            &options,
            FlbcExecutionLimits::default(),
        )
        .unwrap_or_else(|error| panic!("{label} evaluation {index}: replay: {error:?}"))
        .into_complete()
        .unwrap_or_else(|error| panic!("{label} evaluation {index}: replay budget: {error:?}"));
        assert_value(&replay, expected, label, index);
    }
    assert_eq!(engine.logical_root(&options), before);
    eprintln!(
        "{label}: {} checked native evaluations and independent FLBC replays",
        expected.len()
    );
}

pub(super) fn native_fold_window(engine: &Engine) {
    indexed_traversal(
        engine,
        "native Array bounded fold",
        br#"
def nativeFinalElement (xs : Array Nat) (start stop : Nat) : Nat :=
  Array.foldl (fun total x => total + x) 0 xs start stop
"#,
        |array, size| (vec![array, Obj::mk_nat(size - 1), Obj::mk_nat(size)], size),
    );
}

pub(super) fn native_early_iteration(engine: &Engine) {
    indexed_traversal(
        engine,
        "native Array early termination",
        br#"
def nativeFirstElement (xs : Array Nat) : Nat :=
  Id.run (Array.forIn' (m := Id) xs 0
    (fun x _h _total => pure (ForInStep.done x)))
"#,
        |array, _size| (vec![array], 1),
    );
}

/// Reuse the exact live-oracle definitions and expectations while admitting
/// only their Array/List imports. The full fixtures still exercise these same
/// cases together with their String and higher-order programs.
pub(super) fn native_aliasing(engine: &Engine, label: &str, source: &str) {
    fn region<'a>(source: &'a str, kind: &str) -> &'a str {
        let begin = format!("-- FLN_NATIVE_ALIAS_{kind}_BEGIN\n");
        let end = format!("-- FLN_NATIVE_ALIAS_{kind}_END\n");
        assert_eq!(source.matches(&begin).count(), 1, "unique {kind} start");
        assert_eq!(source.matches(&end).count(), 1, "unique {kind} end");
        let after = source.split_once(&begin).expect("the start exists").1;
        let contents = after.split_once(&end).expect("the end follows the start").0;
        assert!(!contents.trim().is_empty(), "the {kind} region is nonempty");
        contents
    }

    let definitions = region(source, "DEFINITIONS");
    assert!(expected_values(definitions).is_empty());
    let evaluations = region(source, "EVALUATIONS");
    assert_eq!(expected_values(evaluations).len(), 2);
    program(engine, label, &format!("{definitions}\n{evaluations}"), 2);
}

/// Invoke a source-compiled traversal on existing native arrays. Construction
/// is outside the measured VM call, so a one-element window must fit the same
/// instruction budget even when its starting index is far into the array.
fn indexed_traversal(
    engine: &Engine,
    label: &str,
    source: &[u8],
    arguments: impl Fn(Obj, usize) -> (Vec<Obj>, usize),
) {
    let options = KVMap::new();
    let before = engine.logical_root(&options);
    let compiled = engine
        .execute_source_definition(
            source,
            &options,
            EngineExecutionLimits::new(Budget::for_stack_bytes(STACK)),
        )
        .unwrap_or_else(|error| panic!("{label}: source callable: {error:?}"))
        .into_complete()
        .unwrap_or_else(|error| panic!("{label}: callable construction: {error:?}"));
    let program = decode_canonical(&compiled.flbc_artifact, CodecLimits::default())
        .expect("the source traversal has independently validated bytecode");
    let rows: BTreeSet<_> = program
        .functions()
        .iter()
        .flat_map(|function| &function.code)
        .filter_map(|instruction| match instruction {
            Instruction::Intrinsic { row, .. } => Some(row.as_str()),
            _ => None,
        })
        .collect();
    assert!(
        rows.contains("extern:Array.getInternal"),
        "{label}: the traversal must read native Array elements",
    );
    assert!(
        !rows.contains("extern:Array.toList"),
        "{label}: unvisited elements must not be copied into a List",
    );
    let targets: Vec<_> = program
        .function(program.entry())
        .expect("the callable entry exists")
        .code
        .iter()
        .filter_map(|instruction| match instruction {
            Instruction::Closure {
                function, captures, ..
            } if captures.is_empty() => Some(*function),
            _ => None,
        })
        .collect();
    let [target] = targets.as_slice() else {
        panic!("{label}: the closed source function has one uncaptured callable");
    };
    let mut limits = ExecutionLimits::default();
    let mut first_steps = None;
    for size in [2, 1024, 16_384] {
        let array = Obj::mk_array((1..=size).map(Obj::mk_nat).collect());
        let (inputs, expected) = arguments(array.clone_ref(), size);
        let exit = execute_function(&program, *target, inputs, limits, None)
            .into_complete()
            .unwrap_or_else(|error| panic!("{label}, size {size}: fixed window budget: {error:?}"));
        let VmExit::Returned(result) = exit else {
            panic!("{label}, size {size}: the bounded traversal must return: {exit:?}");
        };
        let expected = expected.to_string();
        assert_eq!(
            fln_vm::interpreter::nat_decimal(&result.value).as_deref(),
            Some(expected.as_str()),
            "{label}, size {size}: exactly the selected element contributes",
        );
        if let Some(steps) = first_steps {
            assert_eq!(result.usage.steps, steps, "{label}, size {size}");
        } else {
            first_steps = Some(result.usage.steps);
            limits.max_steps = result.usage.steps;
        }
        assert_eq!(array.array_view().0, size, "the shared input survives");
        assert_eq!(array.array_child(0).unbox(), 1);
        assert_eq!(array.array_child(size - 1).unbox(), size);
        eprintln!("{label}: size {size}, {} VM steps", result.usage.steps);
    }
    assert_eq!(engine.logical_root(&options), before);
}
