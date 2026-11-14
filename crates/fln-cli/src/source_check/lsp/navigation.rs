//! Native definition lookup shares the proof worker and its exact import overlay.
use super::*;

pub(super) fn locations(
    sources: &Sources,
    locations: Vec<fln::source_check::inspect::SourceDeclarationLocation>,
) -> Result<
    std::collections::HashMap<fln::Name, fln_server::dispatch::semantic::NavigationLocation>,
    String,
> {
    let mut result = std::collections::HashMap::new();
    let mut modules = std::collections::BTreeMap::<usize, Vec<_>>::new();
    let mut bytes = 0usize;
    for location in locations {
        let index = sources
            .names
            .iter()
            .position(|name| name == &location.module)
            .ok_or("navigation target escaped the checked source closure")?;
        modules.entry(index).or_default().push(location);
    }
    for (index, mut locations) in modules {
        let uri = sources
            .uris
            .get(index)
            .ok_or("navigation target has no source URI")?;
        let source = sources
            .sources
            .get(index)
            .ok_or("navigation target has no source bytes")?;
        let source = std::str::from_utf8(source).map_err(|_| "navigation source is not UTF-8")?;
        locations.sort_by_key(|location| location.range.start);
        let symbols: Vec<_> = locations
            .iter()
            .map(|location| fln_server::dispatch::semantic::DocumentSymbol {
                name: String::new(),
                range: location.range.clone(),
                selection_range: location.selection_range.clone(),
            })
            .collect();
        // Charge before cloning the URI into each compact destination.
        for _ in &locations {
            bytes = bytes
                .checked_add(64 + uri.len())
                .filter(|bytes| *bytes <= 1024 * 1024)
                .ok_or("navigation origin index exceeded its byte limit")?;
        }
        let targets =
            fln_server::dispatch::semantic::NavigationLocation::from_symbols(uri, source, &symbols)
                .map_err(str::to_owned)?;
        for (location, target) in locations.into_iter().zip(targets) {
            if result.insert(location.name, target).is_some() {
                return Err("navigation origin is ambiguous".into());
            }
        }
    }
    Ok(result)
}

pub(super) fn document_symbols(
    session: &mut SourceModuleSession,
    sources: &Sources,
    inputs: &[fln::SourceModuleInput<'_>],
) -> Result<Option<Answer>, String> {
    let entry = sources
        .names
        .first()
        .ok_or("document symbols have no entry module")?;
    let symbols = match session
        .document_symbols(inputs, entry)
        .map_err(|error| error.to_string())?
    {
        fln::Outcome::Complete(symbols) => symbols,
        fln::Outcome::Inconclusive(reason) => {
            return Err(format!(
                "native document symbols were inconclusive: {reason:?}"
            ));
        }
        fln::Outcome::InternalFault(reason) => {
            return Err(format!("native document symbols fault: {reason:?}"));
        }
    };
    Ok(Some(Answer::DocumentSymbols {
        symbols: symbols
            .into_iter()
            .map(|symbol| fln_server::dispatch::semantic::DocumentSymbol {
                name: symbol.name.to_display_string(),
                range: symbol.range,
                selection_range: symbol.selection_range,
            })
            .collect(),
    }))
}

pub(super) fn definition(
    session: &mut SourceModuleSession,
    sources: &Sources,
    inputs: &[fln::SourceModuleInput<'_>],
    offset: usize,
) -> Result<Option<Answer>, String> {
    let entry = sources
        .names
        .first()
        .ok_or("definition query has no entry module")?;
    let target = match session
        .definition(inputs, entry, offset)
        .map_err(|e| e.to_string())?
    {
        fln::Outcome::Complete(target) => target,
        fln::Outcome::Inconclusive(reason) => {
            return Err(format!(
                "native definition lookup was inconclusive: {reason:?}"
            ));
        }
        fln::Outcome::InternalFault(reason) => {
            return Err(format!("native definition lookup fault: {reason:?}"));
        }
    };
    let Some(target) = target else {
        return Ok(None);
    };
    // Do not resolve a path or read disk again: these are precisely the bytes
    // that supplied the checked origin, including any unsaved imported document.
    let index = sources
        .names
        .iter()
        .position(|name| name == &target.module)
        .ok_or("definition target escaped the checked source closure")?;
    let uri = sources
        .uris
        .get(index)
        .ok_or("definition target has no source URI")?;
    let source = sources
        .sources
        .get(index)
        .ok_or("definition target has no source bytes")?;
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
