//! Reuse ParserDescr's bounded structural text, with Names stored losslessly.
//! Its census printer flattens Name string components, so replace every name
//! position by an ordinal before printing and retain the actual Syntax.ident
//! values alongside it. The ordinal table is checked exactly on replay.
use super::*;
use fln_core::name::LeafView;

pub(super) fn encode(descr: &Descr) -> Result<Syntax, EngineExecutionError> {
    // The existing description reader/printer/clone have a depth contract.
    // Check that contract iteratively before calling any of them.
    let mut pending = vec![(descr, 0usize)];
    while let Some((descr, depth)) = pending.pop() {
        if depth > 64 {
            return Err(limit("native grammar description depth", 64));
        }
        match descr {
            Descr::Unary(_, body)
            | Descr::Node { body, .. }
            | Descr::TrailingNode { body, .. }
            | Descr::NodeWithAntiquot(_, _, body) => {
                pending.push((body, depth + 1));
            }
            Descr::Binary(_, left, right) => {
                pending.push((left, depth + 1));
                pending.push((right, depth + 1));
            }
            Descr::SepBy { item, parser, .. } => {
                pending.push((item, depth + 1));
                pending.push((parser, depth + 1));
            }
            _ => {}
        }
    }
    let mut structural = descr.clone();
    let mut names = Vec::new();
    map_names(&mut structural, |name| {
        names.push(ident(name));
        *name = Name::num(Name::anonymous(), (names.len() - 1) as u64);
        Ok(())
    })?;
    let text = structural.to_string();
    if Descr::parse(&text).ok().as_ref() != Some(&structural) {
        return Err(EngineExecutionError::NotImplemented {
            feature: "a native parser description without an exact journal representation",
        });
    }
    Ok(node("description", vec![atom(text), node("names", names)]))
}

pub(super) fn decode(syntax: &Syntax) -> Result<Descr, EngineExecutionError> {
    let [text, names] = children(syntax, "description")? else {
        return Err(malformed());
    };
    let names = children(names, "names")?;
    let mut descr = Descr::parse(as_text(text)?).map_err(|_| malformed())?;
    let mut next = 0usize;
    map_names(&mut descr, |name| {
        if !name.parent().is_anonymous()
            || !matches!(name.leaf_view(), LeafView::Num(index) if index == next as u64)
        {
            return Err(malformed());
        }
        *name = as_name(names.get(next).ok_or_else(malformed)?)?;
        next += 1;
        Ok(())
    })?;
    if next != names.len() {
        return Err(malformed());
    }
    Ok(descr)
}

fn map_names(
    root: &mut Descr,
    mut map: impl FnMut(&mut Name) -> Result<(), EngineExecutionError>,
) -> Result<(), EngineExecutionError> {
    let mut pending = vec![root];
    while let Some(descr) = pending.pop() {
        match descr {
            Descr::Const(name) | Descr::Parser(name) | Descr::Cat(name, _) => map(name)?,
            Descr::Unary(name, body) | Descr::NodeWithAntiquot(_, name, body) => {
                map(name)?;
                pending.push(body);
            }
            Descr::Binary(name, left, right) => {
                map(name)?;
                pending.push(right);
                pending.push(left);
            }
            Descr::Node { kind, body, .. } | Descr::TrailingNode { kind, body, .. } => {
                map(kind)?;
                pending.push(body);
            }
            Descr::SepBy { item, parser, .. } => {
                pending.push(parser);
                pending.push(item);
            }
            Descr::Symbol(_) | Descr::NonReservedSymbol(..) | Descr::UnicodeSymbol(..) => {}
        }
    }
    Ok(())
}
