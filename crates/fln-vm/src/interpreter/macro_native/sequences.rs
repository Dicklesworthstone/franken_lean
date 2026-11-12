//! Separated quotation captures from the pinned `Init.Meta.Defs`.
//!
//! Elements occupy even array positions; separator syntax is deliberately
//! unconstrained. The typed wrappers erase to the same array representation.
//! Every retained child is shared unchanged, including its source and hygiene.

use super::{
    IntrinsicFailure, MAX_SYNTAX_NODES, Name, Obj, VmRefusal, inject_name, layout, limit, literals,
    patterns, syntax_kind,
};

fn array_size(value: &Obj) -> Result<usize, IntrinsicFailure> {
    let (size, _) = value
        .try_array_view()
        .ok_or(VmRefusal::InvalidArrayObject)?;
    limit("syntax argument count", MAX_SYNTAX_NODES, size as u64)?;
    Ok(size)
}

pub(super) fn null_node(args: Obj) -> Obj {
    Obj::mk_ctor(
        layout::SYNTAX_NODE.tag,
        vec![
            Obj::mk_nat(layout::SOURCE_NONE_TAG),
            inject_name(&Name::str(Name::anonymous(), "null")),
            args,
        ],
        &[],
    )
}

pub(super) fn from_elements(separator: &Obj, value: &Obj) -> Result<Obj, IntrinsicFailure> {
    let text = literals::literal_text(separator)?;
    // `SepArray.ofElems` represents an empty delimiter with a null node.
    // `TSepArray.push` below intentionally does not share that convention.
    let separator = if text.is_empty() {
        null_node(Obj::mk_array(Vec::new()))
    } else {
        atom(separator)
    };
    patterns::mk_sep_array(value, &separator)
}

fn atom(text: &Obj) -> Obj {
    Obj::mk_ctor(
        layout::SYNTAX_ATOM.tag,
        vec![Obj::mk_nat(layout::SOURCE_NONE_TAG), text.clone_ref()],
        &[],
    )
}

pub(super) fn push(separator: Obj, value: Obj, element: Obj) -> Result<Obj, IntrinsicFailure> {
    let size = array_size(&value)?;
    let output_size = size.saturating_add(if size == 0 { 1 } else { 2 });
    limit(
        "syntax argument count",
        MAX_SYNTAX_NODES,
        output_size as u64,
    )?;
    literals::literal_text(&separator)?;
    syntax_kind(&element)?;
    let value = if size != 0 {
        // The pin appends an atom even for `sep = ""`, and does not repair a
        // trailing separator in a caller-constructed separated array.
        value
            .try_array_push(atom(&separator))
            .map_err(|_| VmRefusal::InvalidArrayObject)?
    } else {
        value
    };
    // Keep the validated owned handle: cloning here would turn a uniquely
    // owned quotation accumulator into a quadratic copy-on-write loop.
    value
        .try_array_push(element)
        .map_err(|_| VmRefusal::InvalidArrayObject.into())
}
