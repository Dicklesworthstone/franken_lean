//! Native source syntax over the same checked import overlay as editor queries.
use super::*;
use fln::source_check::inspect::SemanticTokenKind as NativeKind;
use fln_server::dispatch::semantic::{SemanticToken, SemanticTokenKind};

pub(super) fn collect(
    session: &mut SourceModuleSession,
    sources: &Sources,
    inputs: &[fln::SourceModuleInput<'_>],
) -> Result<Option<Answer>, String> {
    let entry = sources
        .names
        .first()
        .ok_or("semantic tokens have no entry module")?;
    let tokens = match session
        .semantic_tokens(inputs, entry)
        .map_err(|error| error.to_string())?
    {
        fln::Outcome::Complete(tokens) => tokens,
        fln::Outcome::Inconclusive(reason) => {
            return Err(format!(
                "native semantic tokens were inconclusive: {reason:?}"
            ));
        }
        fln::Outcome::InternalFault(reason) => {
            return Err(format!("native semantic tokens fault: {reason:?}"));
        }
    };
    Ok(Some(Answer::SemanticTokens {
        tokens: tokens
            .into_iter()
            .map(|token| SemanticToken {
                range: token.range,
                kind: match token.kind {
                    NativeKind::Keyword => SemanticTokenKind::Keyword,
                    NativeKind::Property => SemanticTokenKind::Property,
                    NativeKind::SorryLike => SemanticTokenKind::SorryLike,
                },
            })
            .collect(),
    }))
}
