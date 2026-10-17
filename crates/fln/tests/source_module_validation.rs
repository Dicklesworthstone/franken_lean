//! A module's retained validation must finish before its consumers execute.
#![forbid(unsafe_code)]

use fln::source_check::modules::SourceModuleCheckError;
use fln::source_check::modules::execution::{SourceProgramExecutionError, SourceProgramLimits};
use fln::source_check::modules::imported::SourceOleanImport;
use fln::{Budget, EngineExecutionLimits, EvaluationPresentation, KVMap, Name, SourceModuleInput};

#[test]
fn refusing_a_completed_dependency_stops_before_a_consumers_independent_error() {
    let options = KVMap::new();
    let receipt = SourceOleanImport::empty(&options);
    let before = receipt.engine.logical_root(&options);
    let entry = Name::from_components(["Main"]);
    let dependency = Name::from_components(["Dependency"]);
    let token = Name::from_components(["Token"]);
    let limits = SourceProgramLimits::new(EngineExecutionLimits::new(Budget::for_stack_bytes(
        2 * 1024 * 1024,
    )));
    let sources = [
        SourceModuleInput {
            name: &entry,
            source: b"prelude\nimport Dependency\ndef broken : Token := missing\n",
        },
        SourceModuleInput {
            name: &dependency,
            source: b"prelude\ninductive Token where\n  | mk\n",
        },
    ];

    let mut visited = Vec::new();
    let refused = receipt
        .execute_lean_source_modules_with_validation(
            &sources,
            &entry,
            &options,
            limits,
            None,
            EvaluationPresentation::Lean,
            &mut |module, completed| {
                visited.push(module.clone());
                assert!(completed.batch.engine.environment().contains(&token));
                Err("dependency validation failed")
            },
        )
        .expect_err("dependency validation must stop the program");
    assert!(matches!(
        refused,
        SourceProgramExecutionError::Validation { module, error }
            if module == dependency && error == "dependency validation failed"
    ));
    assert_eq!(visited.as_slice(), std::slice::from_ref(&dependency));
    assert_eq!(receipt.engine.logical_root(&options), before);

    // The same consumer has a real elaboration error. Allowing its dependency
    // through must expose that error, proving the first run stopped before it.
    visited.clear();
    let consumer_error = receipt
        .execute_lean_source_modules_with_validation(
            &sources,
            &entry,
            &options,
            limits,
            None,
            EvaluationPresentation::Lean,
            &mut |module, _| {
                visited.push(module.clone());
                Ok::<(), std::convert::Infallible>(())
            },
        )
        .expect_err("the unblocked consumer must still be checked");
    let SourceProgramExecutionError::Source(SourceModuleCheckError::Source { module, error }) =
        consumer_error
    else {
        panic!("expected the consumer's source error: {consumer_error:?}");
    };
    assert_eq!(module, entry);
    assert!(error.to_string().contains("missing"), "{error}");
    assert_eq!(visited.as_slice(), std::slice::from_ref(&dependency));
    assert_eq!(receipt.engine.logical_root(&options), before);

    // The existing API retains the source-error type without a validation
    // wrapper when its internal validator is infallible.
    let legacy = receipt
        .execute_lean_source_modules_with_presentation(
            &sources,
            &entry,
            &options,
            limits,
            None,
            EvaluationPresentation::Lean,
        )
        .expect_err("the existing API must preserve source failures");
    assert!(matches!(
        legacy,
        SourceModuleCheckError::Source { module, .. } if module == entry
    ));
}
