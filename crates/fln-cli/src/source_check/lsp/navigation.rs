//! Native definition lookup shares the proof worker and its exact import overlay.
use super::*;

pub(super) fn definition(
    session: &mut SourceModuleSession,
    sources: &Sources,
    inputs: &[fln::SourceModuleInput<'_>],
    offset: usize,
) -> Result<Option<Answer>, String> {
    let entry = sources.names.first().ok_or("definition query has no entry module")?;
    let target = match session.definition(inputs, entry, offset).map_err(|e| e.to_string())? {
        fln::Outcome::Complete(target) => target,
        fln::Outcome::Inconclusive(reason) => {
            return Err(format!("native definition lookup was inconclusive: {reason:?}"));
        }
        fln::Outcome::InternalFault(reason) => {
            return Err(format!("native definition lookup fault: {reason:?}"));
        }
    };
    let Some(target) = target else { return Ok(None) };
    // Do not resolve a path or read disk again: these are precisely the bytes
    // that supplied the checked origin, including any unsaved imported document.
    let index = sources.names.iter().position(|name| name == &target.module)
        .ok_or("definition target escaped the checked source closure")?;
    let uri = sources.uris.get(index).ok_or("definition target has no source URI")?;
    let source = sources.sources.get(index).ok_or("definition target has no source bytes")?;
    let source = std::str::from_utf8(source).map_err(|_| "definition source is not UTF-8")?;
    if source.get(target.range.clone()).is_none() || target.range.is_empty() {
        return Err("definition range escaped its source snapshot".into());
    }
    Ok(Some(Answer::Definition {
        uri: uri.clone(),
        source: source.to_owned(),
        range: target.range,
    }))
}
