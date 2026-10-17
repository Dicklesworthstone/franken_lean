//! Deferred record arguments use the ordinary source checker and runtime.
#![forbid(unsafe_code)]

use fln::{
    Budget, CheckerAdmissionGround, Engine, EngineAdmissionLimits, EngineExecutionLimits,
    FlbcExecutionLimits, KVMap, Name, SourceCheckLimits, VmExit,
};
use fln_comp::flbc::{CodecLimits, decode_canonical, encode_canonical};

const SOURCE: &str = include_str!("source_postponed_records.lean");
const HEADER: &str = "prelude\nimport Init.Prelude\nimport Init.Tactics\n\n";
const CASES: &str = "-- FLN_RECORD_CASES\n";
const PROBES: [(&str, &str, &str); 10] = [
    ("recordLaterValue", "(recordFromLater 41).value", "42"),
    ("recordResultValue", "(recordFromResult 40).value", "42"),
    ("recordCallbackValue", "(recordFromCallback 39).value", "42"),
    ("recordNestedSum", "(recordNestedCallback 35).sum", "42"),
    ("recordNestedCount", "(recordNestedCallback 35).count", "1"),
    (
        "recordNestedValue",
        "(recordNestedApplication 38).value",
        "42",
    ),
    (
        "recordUpdateSum",
        "(recordFromUpdate (DeferredTotals.mk 37 9)).sum",
        "42",
    ),
    (
        "recordUpdateCount",
        "(recordFromUpdate (DeferredTotals.mk 37 9)).count",
        "9",
    ),
    ("recordDependentValue", "(recordDependent 36).value", "42"),
    ("recordRetryValue", "recordRetry.value", "42"),
];

fn limits() -> SourceCheckLimits {
    SourceCheckLimits::new(EngineAdmissionLimits::new(Budget::for_stack_bytes(
        2 * 1024 * 1024,
    )))
}

fn seed() -> Engine {
    Engine::with_source_seed(limits().admission)
        .unwrap()
        .into_complete()
        .unwrap()
}

fn body() -> &'static str {
    SOURCE
        .strip_prefix(HEADER)
        .expect("the exact explicit pin fixture header")
}

fn check(engine: &Engine, source: &str) -> fln::SourceFileCheck {
    engine
        .check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .unwrap()
}

fn common() -> Engine {
    let (library, _) = body()
        .split_once(CASES)
        .expect("the shared library precedes all cases");
    check(&seed(), library).engine
}

fn assert_nat(exit: &VmExit, expected: &str, query: &str) {
    let VmExit::Returned(result) = exit else {
        panic!("{query} did not return: {exit:?}");
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&result.value).as_deref(),
        Some(expected),
        "{query}",
    );
}

#[test]
fn later_constraints_resume_records_without_changing_checked_values() {
    let original = seed();
    let options = KVMap::new();
    let original_root = original.logical_root(&options);
    let checked = check(&original, body());
    assert_eq!(checked.theorems, PROBES.len());
    let engine = checked.engine;
    let root = engine.logical_root(&options);
    for (proof, expression, expected) in PROBES {
        // Each execution is paired with the exact shared proof checked by Lean
        // and by the native source admission path; no oracle output is guessed.
        let theorem = format!("theorem {proof} : {expression} = {expected} := by rfl");
        assert!(SOURCE.lines().any(|line| line == theorem), "{proof}");
        assert!(
            engine
                .environment()
                .contains(&Name::from_components([proof]))
        );
        let query = format!("#eval {expression}");
        let completed = engine
            .execute_source_commands_with_checks(
                query.as_bytes(),
                &options,
                EngineExecutionLimits::new(limits().admission.kernel),
            )
            .unwrap_or_else(|error| panic!("{proof}: {error:?}"))
            .into_complete()
            .unwrap();
        assert_eq!(completed.batch.source_evaluation_indices.len(), 1);
        let execution = &completed.batch.executions[completed.batch.source_evaluation_indices[0]];
        assert_eq!(execution.checker.schema, "fln.checker-admission/1");
        assert_eq!(
            execution.checker.ground,
            CheckerAdmissionGround::BodyCheckedAgainstDeclaredType,
        );
        assert_nat(&execution.exit, expected, expression);
        let decoded = decode_canonical(&execution.flbc_artifact, CodecLimits::default())
            .expect("independent FLBC validation");
        assert_eq!(
            encode_canonical(&decoded, CodecLimits::default()).expect("canonical FLBC encoding"),
            execution.flbc_artifact,
        );
        let replay = fln::execute_flbc_artifact(
            &execution.flbc_artifact,
            &options,
            FlbcExecutionLimits::default(),
        )
        .unwrap_or_else(|error| panic!("{proof}: replay: {error:?}"))
        .into_complete()
        .unwrap();
        assert_nat(&replay, expected, expression);
        assert_eq!(engine.logical_root(&options), root);
    }
    assert_eq!(original.logical_root(&options), original_root);
    assert!(
        !original
            .environment()
            .contains(&Name::from_components(["recordFromLater"]))
    );
}

#[test]
fn wrong_or_unresolved_record_types_still_refuse_and_recover_atomically() {
    let engine = common();
    let options = KVMap::new();
    let root = engine.logical_root(&options);
    for (source, diagnostic) in [
        (
            "def rejectedRecord : DeferredCell := recordChoose { value := true } (DeferredCell.mk 0)",
            None,
        ),
        (
            "def rejectedRecord : DeferredCell := recordChoose { missing := 7 } (DeferredCell.mk 0)",
            Some("UnknownField"),
        ),
        (
            "def rejectedRecord : DeferredCell := { missing := 7 }",
            Some("UnknownField"),
        ),
        (
            "def rejectedRecord : Nat := recordChoose { value := 7 } (0 : Nat)",
            Some("ExpectedRecordType"),
        ),
        ("def rejectedRecord := recordRelay { value := 7 }", None),
        (
            "def rejectedRecord : Nat := let unused := recordChoose { value := true } (DeferredCell.mk 0); 42",
            None,
        ),
    ] {
        fln_parse::parse_definition(source.as_bytes()).unwrap_or_else(|error| {
            panic!("negative case must reach elaboration: {source}\n{error:?}")
        });
        let staged = format!("def uncommittedRecordPrefix : Nat := 77\n{source}");
        let error = engine
            .check_source_files(&[staged.as_bytes()], &options, limits())
            .expect_err(source);
        assert_eq!(error.disposition().0, "elaboration", "{source}: {error:?}");
        let detail = format!("{error:?}");
        assert!(!detail.contains("Frontend(Parse("), "{source}: {detail}");
        if let Some(diagnostic) = diagnostic {
            assert!(detail.contains(diagnostic), "{source}: {detail}");
        }
        assert_eq!(engine.logical_root(&options), root);
        for label in ["uncommittedRecordPrefix", "rejectedRecord"] {
            assert!(
                !engine
                    .environment()
                    .contains(&Name::from_components([label]))
            );
        }
    }
    let recovered = check(
        &engine,
        "def recoveredRecord : DeferredCell := recordChoose { value := 42 } (DeferredCell.mk 0)\ntheorem recoveredRecordValue : recoveredRecord.value = 42 := by rfl",
    );
    assert_eq!(recovered.theorems, 1);
    assert_eq!(engine.logical_root(&options), root);
}
