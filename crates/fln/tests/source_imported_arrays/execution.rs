//! All expected values are shared verbatim with the actual pinned Lean oracle.
#![forbid(unsafe_code)]
use super::*;
use fln::{
    CheckerAdmissionGround, ClosedVmValue, EngineExecutionLimits, FlbcExecutionLimits, VmExit,
};
use fln_comp::flbc::{CodecLimits, decode_canonical, encode_canonical};

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

// The live oracle uses these imports; this Engine already admitted the same closure.
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
        assert_eq!(
            execution.checker.ground,
            CheckerAdmissionGround::BodyCheckedAgainstDeclaredType,
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
