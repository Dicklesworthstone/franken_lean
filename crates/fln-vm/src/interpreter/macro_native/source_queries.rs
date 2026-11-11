//! Source inspection used by imported user macros. Walks use explicit sibling
//! cursors, preserve arbitrary Nat positions, and bound all native traversal
//! and reprint work independently of the VM instruction budget.

use super::{
    IntrinsicFailure, MAX_NAME_BYTES, MAX_SYNTAX_NODES, Name, NameBudget, Obj, SyntaxKind,
    VmRefusal, check_layout, child, expansion_layout, get_head_info_bounded,
    get_head_info_optional_bounded, get_tail_pos_bounded, layout, limit, name, source_info,
    source_position, string, syntax_kind,
};
use crate::interpreter::{extract_utf8, strings::Substring, with_nat_view};

fn option(value: Option<Obj>) -> Obj {
    value.map_or_else(
        || Obj::mk_nat(expansion_layout::OPTION_NONE_TAG),
        |value| Obj::mk_ctor(expansion_layout::OPTION_SOME.tag, vec![value], &[]),
    )
}

pub(super) fn info(value: &Obj) -> Result<Obj, IntrinsicFailure> {
    if matches!(syntax_kind(value)?, SyntaxKind::Missing) {
        return Ok(option(None));
    }
    let info = child(value, 0)?;
    source_info(&info)?;
    Ok(option(Some(info)))
}

pub(super) fn head_info(value: &Obj) -> Result<Obj, IntrinsicFailure> {
    Ok(option(get_head_info_optional_bounded(
        value,
        &mut 0,
        "syntax optional head-info nodes",
    )?))
}

pub(super) fn range(value: &Obj, canonical_only: bool) -> Result<Obj, IntrinsicFailure> {
    let mut visited = 0;
    let info = get_head_info_bounded(value, &mut visited, "syntax range nodes")?;
    let start = source_position(&info, canonical_only, false, "Lean.Syntax.getRange?")?;
    // The pin evaluates both endpoints, even when the head has no position.
    // The two walks share one allowance, rather than granting each a new one.
    let stop = get_tail_pos_bounded(value, canonical_only, &mut visited, "syntax range nodes")?;
    Ok(option(start.zip(stop).map(|(start, stop)| {
        let mut fields: Vec<_> = (0..layout::SYNTAX_RANGE.object_fields)
            .map(|_| Obj::mk_nat(0))
            .collect();
        fields[layout::SYNTAX_RANGE_START_FIELD] = start;
        fields[layout::SYNTAX_RANGE_STOP_FIELD] = stop;
        Obj::mk_ctor(layout::SYNTAX_RANGE.tag, fields, &[])
    })))
}

pub(super) fn has_missing(value: &Obj) -> Result<bool, IntrinsicFailure> {
    let mut current = value.clone_ref();
    let mut pending = Vec::new();
    let mut visited = 0;
    loop {
        visited += 1;
        limit("syntax has-missing nodes", MAX_SYNTAX_NODES, visited)?;
        match syntax_kind(&current)? {
            SyntaxKind::Missing => return Ok(true),
            SyntaxKind::Node => {
                let args = child(&current, 2)?;
                let (size, _) = args.try_array_view().ok_or(VmRefusal::InvalidArrayObject)?;
                if size != 0 {
                    current = args.array_child(0);
                    if size > 1 {
                        pending.push((args, 1, size));
                    }
                    continue;
                }
            }
            SyntaxKind::Atom | SyntaxKind::Ident => {}
        }
        let Some((args, index, size)) = pending.pop() else {
            return Ok(false);
        };
        current = args.array_child(index);
        if index + 1 < size {
            pending.push((args, index + 1, size));
        }
    }
}

enum ReprintFrame {
    Children {
        args: Obj,
        next: usize,
        size: usize,
    },
    Choice {
        args: Obj,
        next: usize,
        size: usize,
        first: Option<String>,
        prefix: String,
    },
}

pub(super) fn reprint(value: &Obj) -> Result<Obj, IntrinsicFailure> {
    let mut budget = NameBudget::new("syntax reprint nodes", "syntax reprint bytes");
    let mut output = String::new();
    let mut pending = Vec::new();
    let mut current = Some(value.clone_ref());
    let choice_kind = Name::str(Name::anonymous(), "choice");
    loop {
        if let Some(value) = current.take() {
            budget.nodes(1)?;
            match syntax_kind(&value)? {
                SyntaxKind::Missing => {}
                SyntaxKind::Atom | SyntaxKind::Ident => {
                    reprint_leaf(&value, &mut output, &mut budget)?;
                }
                SyntaxKind::Node => {
                    let kind = name(&child(&value, 1)?)?;
                    budget.name(&kind)?;
                    let args = child(&value, 2)?;
                    let (size, _) = args.try_array_view().ok_or(VmRefusal::InvalidArrayObject)?;
                    if kind == choice_kind {
                        if size == 0 {
                            // Both topDown(firstChoiceOnly) and reprint's
                            // ambiguity check use args[0]!. Each reports a
                            // recoverable panic and supplies Syntax.missing.
                            budget.nodes(2)?;
                            crate::interpreter::arrays::report_bounds_panic()?;
                            crate::interpreter::arrays::report_bounds_panic()?;
                        } else {
                            current = Some(args.array_child(0));
                            pending.push(ReprintFrame::Choice {
                                args,
                                next: 1,
                                size,
                                first: None,
                                prefix: std::mem::take(&mut output),
                            });
                            continue;
                        }
                    } else if size != 0 {
                        current = Some(args.array_child(0));
                        if size > 1 {
                            pending.push(ReprintFrame::Children {
                                args,
                                next: 1,
                                size,
                            });
                        }
                        continue;
                    }
                }
            }
        }
        match pending.pop() {
            None => return Ok(option(Some(Obj::mk_string(&output)))),
            Some(ReprintFrame::Children { args, next, size }) => {
                current = Some(args.array_child(next));
                if next + 1 < size {
                    pending.push(ReprintFrame::Children {
                        args,
                        next: next + 1,
                        size,
                    });
                }
            }
            Some(ReprintFrame::Choice {
                args,
                next,
                size,
                first,
                prefix,
            }) => {
                let printed = std::mem::take(&mut output);
                let first = match first {
                    Some(first) if first != printed => return Ok(option(None)),
                    Some(first) => first,
                    None => printed,
                };
                if next < size {
                    current = Some(args.array_child(next));
                    pending.push(ReprintFrame::Choice {
                        args,
                        next: next + 1,
                        size,
                        first: Some(first),
                        prefix,
                    });
                } else {
                    output = prefix;
                    // Reference checks every alternative, then traverses the
                    // first again to emit it. Preserve that second traversal:
                    // nested empty choices have observable panic diagnostics.
                    current = Some(args.array_child(0));
                }
            }
        }
    }
}

fn bounded_string<'a>(
    value: &'a Obj,
    budget: &mut NameBudget,
) -> Result<&'a str, IntrinsicFailure> {
    let (_, _, _, bytes) = value
        .try_borrow_string_view()
        .ok_or(VmRefusal::InvalidStringObject)?;
    // Account before UTF-8/character-count validation scans the carrier. This
    // also bounds repeated visits to shared strings and discarded choices.
    budget.bytes = budget
        .bytes
        .saturating_add(bytes.len().saturating_sub(1) as u64);
    limit("syntax reprint bytes", MAX_NAME_BYTES, budget.bytes)?;
    Ok(string(value)?)
}

fn substring(value: &Obj, budget: &mut NameBudget) -> Result<String, IntrinsicFailure> {
    check_layout(value, layout::SUBSTRING_RAW)?;
    let raw = Substring::read(value, "Lean.Syntax.reprint", 0)?;
    with_nat_view(&raw.start, "Lean.Syntax.reprint", 0, |_| ())?;
    with_nat_view(&raw.stop, "Lean.Syntax.reprint", 0, |_| ())?;
    let text = bounded_string(&raw.string, budget)?;
    // Substring.Raw deliberately accepts arbitrary Nat endpoints. Reuse the
    // runtime's exact extraction quirks, including mid-UTF-8 and mpz offsets.
    extract_utf8(
        text.as_bytes(),
        raw.start.is_scalar().then(|| raw.start.unbox()),
        raw.stop.is_scalar().then(|| raw.stop.unbox()),
    )
    .ok_or_else(|| VmRefusal::InvalidStringObject.into())
}

fn append(
    output: &mut String,
    text: &str,
    budget: &mut NameBudget,
) -> Result<(), IntrinsicFailure> {
    budget.text(text)?;
    output.push_str(text);
    Ok(())
}

fn reprint_leaf(
    value: &Obj,
    output: &mut String,
    budget: &mut NameBudget,
) -> Result<(), IntrinsicFailure> {
    let info = child(value, 0)?;
    source_info(&info)?;
    let raw = child(value, 1)?;
    let text = if matches!(syntax_kind(value)?, SyntaxKind::Ident) {
        substring(&raw, budget)?
    } else {
        bounded_string(&raw, budget)?.to_owned()
    };
    if !info.is_scalar() && info.obj_tag() == usize::from(layout::SOURCE_ORIGINAL.tag) {
        let leading = substring(
            &child(&info, layout::SOURCE_ORIGINAL_LEADING_FIELD)?,
            budget,
        )?;
        let trailing = substring(
            &child(&info, layout::SOURCE_ORIGINAL_TRAILING_FIELD)?,
            budget,
        )?;
        append(output, &leading, budget)?;
        append(output, &text, budget)?;
        append(output, &trailing, budget)?;
    } else {
        append(output, " ", budget)?;
        append(output, &text, budget)?;
        append(output, " ", budget)?;
    }
    Ok(())
}
