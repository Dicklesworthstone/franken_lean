//! Completion shares the proof worker and the exact unsaved import overlay.
use super::*;
use fln_server::dispatch::semantic::CompletionItem;

pub(super) fn complete(
    session: &mut SourceModuleSession,
    sources: &Sources,
    inputs: &[fln::SourceModuleInput<'_>],
    offset: usize,
) -> Result<Option<Answer>, String> {
    let entry = sources.names.first().ok_or("completion has no entry module")?;
    let result = session.complete(inputs, entry, offset).map_err(|error| error.to_string())?;
    match result {
        fln::Outcome::Complete(None) => Ok(None),
        fln::Outcome::Complete(Some(completion)) => Ok(Some(Answer::Completion {
            items: completion.items.into_iter().map(|item| CompletionItem {
                label: item.label, replacement: item.replacement,
            }).collect(),
            range: completion.range,
            is_incomplete: completion.is_incomplete,
        })),
        fln::Outcome::Inconclusive(reason) => Err(format!("native completion was inconclusive: {reason:?}")),
        fln::Outcome::InternalFault(fault) => Err(format!("native completion fault: {fault:?}")),
    }
}
