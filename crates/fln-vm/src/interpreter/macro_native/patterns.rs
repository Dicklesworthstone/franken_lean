//! Native quotation-pattern and repetition services from the pinned Init.
//!
//! The predicates have deliberately different shape rules: `isNodeOf` accepts
//! zero-argument pseudo-kinds, `matchesLit` ignores arguments after the first,
//! and `getOptional?` requires a real null node with exactly one child.

use super::{
    IntrinsicFailure, MAX_SYNTAX_NODES, Name, Obj, SyntaxKind, VmRefusal, child, expansion_layout,
    limit, literals, name, nat_as_usize, syntax_kind,
};

/// `Init.Meta.Defs`: separators are arbitrary Syntax, inserted only between
/// elements. Retain their exact handles, including source info and hygiene.
pub(super) fn mk_sep_array(values: &Obj, separator: &Obj) -> Result<Obj, IntrinsicFailure> {
    let (size, _) = values
        .try_array_view()
        .ok_or(VmRefusal::InvalidArrayObject)?;
    let result_size = size.saturating_mul(2).saturating_sub(1);
    limit(
        "separated syntax argument count",
        MAX_SYNTAX_NODES,
        result_size as u64,
    )?;
    syntax_kind(separator)?;
    let mut result = Vec::with_capacity(result_size);
    for index in 0..size {
        let value = values.array_child(index);
        syntax_kind(&value)?;
        if index != 0 {
            result.push(separator.clone_ref());
        }
        result.push(value);
    }
    Ok(Obj::mk_array(result))
}

/// The pin's separated arrays use `Array.getEvenElems`. No separator spelling
/// or null-kind check is involved; a trailing separator is simply skipped.
/// The typed SepArray wrappers erase to this same array carrier.
pub(super) fn sep_elems(values: &Obj) -> Result<Obj, IntrinsicFailure> {
    let (size, _) = values
        .try_array_view()
        .ok_or(VmRefusal::InvalidArrayObject)?;
    limit(
        "separated syntax argument count",
        MAX_SYNTAX_NODES,
        size as u64,
    )?;
    let mut result = Vec::with_capacity(size.div_ceil(2));
    for index in (0..size).step_by(2) {
        let value = values.array_child(index);
        syntax_kind(&value)?;
        result.push(value);
    }
    Ok(Obj::mk_array(result))
}

pub(super) fn is_node_of(
    value: &Obj,
    expected: &Name,
    size: &Obj,
    operation: &'static str,
    argument: usize,
) -> Result<bool, IntrinsicFailure> {
    let size = nat_as_usize(size, operation, argument)?;
    let (kind, actual_size) = match syntax_kind(value)? {
        SyntaxKind::Missing => (Name::str(Name::anonymous(), "missing"), 0),
        SyntaxKind::Ident => (Name::str(Name::anonymous(), "ident"), 0),
        SyntaxKind::Atom => {
            let text = child(value, 1)?;
            (
                Name::str(Name::anonymous(), literals::literal_text(&text)?),
                0,
            )
        }
        SyntaxKind::Node => {
            let args = child(value, 2)?;
            let (size, _) = args.try_array_view().ok_or(VmRefusal::InvalidArrayObject)?;
            (name(&child(value, 1)?)?, size)
        }
    };
    Ok(kind == *expected && size == Some(actual_size))
}

pub(super) fn matches_ident(value: &Obj, id: &Obj) -> Result<bool, IntrinsicFailure> {
    let id = name(id)?;
    if !matches!(syntax_kind(value)?, SyntaxKind::Ident) {
        return Ok(false);
    }
    let actual = name(&child(value, 2)?)?;
    // Ignore spelling, SourceInfo and preresolution. Quotation matching is
    // structural Name equality after erasing each name's own macro scopes.
    Ok(actual.erase_macro_scopes() == id.erase_macro_scopes())
}

pub(super) fn matches_lit(value: &Obj, kind: &Obj, text: &Obj) -> Result<bool, IntrinsicFailure> {
    let kind = name(kind)?;
    let expected = literals::literal_text(text)?;
    if !matches!(syntax_kind(value)?, SyntaxKind::Node) || name(&child(value, 1)?)? != kind {
        return Ok(false);
    }
    let args = child(value, 2)?;
    let (size, _) = args.try_array_view().ok_or(VmRefusal::InvalidArrayObject)?;
    if size == 0 {
        return Ok(false);
    }
    let first = args.array_child(0);
    if !matches!(syntax_kind(&first)?, SyntaxKind::Atom) {
        return Ok(false);
    }
    Ok(literals::literal_text(&child(&first, 1)?)? == expected)
}

pub(super) fn get_optional(value: &Obj) -> Result<Obj, IntrinsicFailure> {
    let none = || Obj::mk_nat(expansion_layout::OPTION_NONE_TAG);
    if !matches!(syntax_kind(value)?, SyntaxKind::Node)
        || name(&child(value, 1)?)? != Name::str(Name::anonymous(), "null")
    {
        return Ok(none());
    }
    let args = child(value, 2)?;
    let (size, _) = args.try_array_view().ok_or(VmRefusal::InvalidArrayObject)?;
    if size != 1 {
        return Ok(none());
    }
    let value = args.array_child(0);
    syntax_kind(&value)?;
    Ok(Obj::mk_ctor(
        expansion_layout::OPTION_SOME.tag,
        vec![value],
        &[],
    ))
}
