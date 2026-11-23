//! Source wrappers preserve the three distinct eliminator metadata nonanswers.
#![forbid(unsafe_code)]

use fln::{EngineExecutionError, Name, SourceCheckError};
use fln_elab::eliminator_tags::EliminatorTagError;
use fln_elab::source::SourceInferenceError;
use fln_elab::{DefinitionFrontendError, NatDefinitionElabError};

#[test]
fn eliminator_tag_nonanswers_keep_their_source_disposition_through_batches() {
    for (cause, expected) in [
        (
            EliminatorTagError::UnsupportedEliminator(Name::from_components([
                "Public",
                "aliasElim",
            ])),
            ("capability", false, 5),
        ),
        (EliminatorTagError::Limit, ("resource", false, 3)),
        (EliminatorTagError::Malformed, ("internal-fault", false, 4)),
    ] {
        for nested in [false, true] {
            let mut error = EngineExecutionError::Frontend(DefinitionFrontendError::Elaborate(
                NatDefinitionElabError::Inference(SourceInferenceError::EliminatorTags(
                    cause.clone(),
                )),
            ));
            if nested {
                error = EngineExecutionError::BatchCommand {
                    index: 2,
                    error: Box::new(error),
                    at: None,
                };
            }
            let error = SourceCheckError::Command {
                file: 0,
                command: 2,
                offset: 11,
                error: Box::new(error),
            };
            assert_eq!(error.disposition(), expected, "{cause:?}, nested={nested}");
        }
    }
}
