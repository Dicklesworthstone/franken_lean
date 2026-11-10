//! Preserve the quotation variables' sequence types after their values become
//! untyped null syntax nodes. The pin binds Option, TSyntaxArray and TSepArray
//! separately (`Quotation.getHeadInfo`, `MacroArgUtil.expandMacroArg`).
//!
//! This interpreter handles arrays with unchanged separator framing. Other
//! array conversions are refused before registration, even for empty inputs.
use super::*;

pub(in crate::extensions) const INCOMPATIBLE_CAPTURE: &str =
    "a quotation splice with incompatible capture families";

pub(in crate::extensions) fn registration_error(reason: &str) -> bool {
    matches!(
        reason,
        INCOMPATIBLE_CAPTURE
            | repetition::DUPLICATE_ITERATION_CAPTURE
            | "a quoted macro pattern past the node or depth budget"
            | "a macro template past the node budget"
            | "macro template work overflow"
            | "a macro syntax construction with incompatible value types"
    )
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(in crate::extensions) enum CaptureKind {
    Scalar,
    Optional,
    Many,
    Separated(String),
}

fn charge(visited: &mut usize, depth: usize) -> Result<(), &'static str> {
    if depth > MAX_DESCR_DEPTH {
        return Err("a quoted macro pattern past the node or depth budget");
    }
    templates::charge(visited)
}

fn splice_kind(syntax: &Syntax) -> Result<CaptureKind, &'static str> {
    let Syntax::Node { kind, args, .. } = syntax else {
        return Err(INCOMPATIBLE_CAPTURE);
    };
    let [_, Syntax::Atom { val: suffix, .. }] = args.as_slice() else {
        return Err(INCOMPATIBLE_CAPTURE);
    };
    let parent = kind.parent();
    if parent == Name::from_components(["optional"]) && suffix == "?" {
        Ok(CaptureKind::Optional)
    } else if parent == Name::from_components(["many"]) && suffix == "*" {
        Ok(CaptureKind::Many)
    } else if parent == Name::from_components(["sepBy"]) {
        suffix
            .strip_suffix('*')
            .filter(|separator| !separator.is_empty())
            .map(|separator| CaptureKind::Separated(separator.to_owned()))
            .ok_or(INCOMPATIBLE_CAPTURE)
    } else {
        Err(INCOMPATIBLE_CAPTURE)
    }
}

/// Check a compiled template. Sole bracketed captures compile to suffix nodes,
/// so both forms are checked here, including when a native journal is replayed.
fn validate(
    rhs: &Syntax,
    variables: &[(Vec<usize>, Name)],
    mut capture_kind: impl FnMut(&[usize], &mut usize) -> Result<CaptureKind, &'static str>,
) -> Result<(), &'static str> {
    let mut visited = 0;
    let mut paths = BTreeMap::new();
    for (path, name) in variables {
        charge(&mut visited, path.len())?;
        if paths.insert(name, path.as_slice()).is_some() {
            return Err(INCOMPATIBLE_CAPTURE);
        }
    }
    let mut pending = vec![(rhs, 0)];
    while let Some((syntax, depth)) = pending.pop() {
        charge(&mut visited, depth)?;
        let Syntax::Node { kind, args, .. } = syntax else {
            continue;
        };
        if kind.leaf_view() == LeafView::Str("antiquot_suffix_splice") {
            let sequence = repetition::suffix(syntax)?.ok_or(INCOMPATIBLE_CAPTURE)?;
            let name = sequence.name()?;
            let path = paths.get(&name).ok_or(INCOMPATIBLE_CAPTURE)?;
            if capture_kind(path, &mut visited)? != splice_kind(syntax)? {
                return Err(INCOMPATIBLE_CAPTURE);
            }
            continue;
        }
        if kind.leaf_view() == LeafView::Str("antiquot_scope") {
            let [body, _] = args.as_slice() else {
                return Err(INCOMPATIBLE_CAPTURE);
            };
            let expected = splice_kind(syntax)?;
            let mut captures = BTreeSet::new();
            let mut body_nodes = vec![(body, depth + 1)];
            while let Some((node, depth)) = body_nodes.pop() {
                charge(&mut visited, depth)?;
                if let Syntax::Ident { val, .. } = node
                    && let Some(path) = paths.get(val)
                {
                    if !captures.insert(val) {
                        return Err(repetition::DUPLICATE_ITERATION_CAPTURE);
                    }
                    if capture_kind(path, &mut visited)? != expected {
                        return Err(INCOMPATIBLE_CAPTURE);
                    }
                } else if let Syntax::Node { args, .. } = node {
                    if node.kind().is_some_and(|kind| {
                        matches!(
                            kind.leaf_view(),
                            LeafView::Str("antiquot_scope" | "antiquot_suffix_splice")
                        )
                    }) {
                        return Err(INCOMPATIBLE_CAPTURE);
                    }
                    if args.len() > MAX_TEMPLATE_NODES.saturating_sub(visited) {
                        return Err("a macro template past the node budget");
                    }
                    body_nodes.extend(args.iter().map(|child| (child, depth + 1)));
                }
            }
            if captures.is_empty() {
                return Err(INCOMPATIBLE_CAPTURE);
            }
            continue;
        }
        if args.len() > MAX_TEMPLATE_NODES.saturating_sub(visited) {
            return Err("a macro template past the node budget");
        }
        pending.extend(args.iter().map(|child| (child, depth + 1)));
    }
    Ok(())
}

pub(in crate::extensions) fn item_kind(
    item: &StxItem,
    visited: &mut usize,
    depth: usize,
) -> Result<CaptureKind, &'static str> {
    charge(visited, depth)?;
    Ok(match item {
        StxItem::Postfix(suffix, _) => match suffix.as_str() {
            "?" => CaptureKind::Optional,
            "*" | "+" => CaptureKind::Many,
            ",*" | ",+" | ",*,?" | ",+,?" => CaptureKind::Separated(",".to_owned()),
            _ => CaptureKind::Scalar,
        },
        StxItem::SepBy { separator, .. } => CaptureKind::Separated(separator.clone()),
        StxItem::Unary(name, items) => match simple(name).as_deref() {
            Some("optional") => CaptureKind::Optional,
            Some("many" | "many1") => CaptureKind::Many,
            Some("withPosition") if items.len() == 1 => {
                return item_kind(&items[0], visited, depth + 1);
            }
            _ => CaptureKind::Scalar,
        },
        _ => CaptureKind::Scalar,
    })
}

pub(in crate::extensions) fn direct(
    rhs: &Syntax,
    variables: &[(Vec<usize>, Name)],
    items: &[StxItem],
) -> Result<(), &'static str> {
    validate(rhs, variables, |path, visited| {
        let [index] = path else {
            return Err(INCOMPATIBLE_CAPTURE);
        };
        item_kind(items.get(*index).ok_or(INCOMPATIBLE_CAPTURE)?, visited, 0)
    })
}

pub(in crate::extensions) fn pattern_kind(
    children: &[Syntax],
    path: &[usize],
    visited: &mut usize,
) -> Result<CaptureKind, &'static str> {
    let (first, rest) = path.split_first().ok_or(INCOMPATIBLE_CAPTURE)?;
    let mut pattern = children.get(*first).ok_or(INCOMPATIBLE_CAPTURE)?;
    charge(visited, path.len())?;
    for index in rest {
        charge(visited, path.len())?;
        pattern = node_args(pattern)
            .and_then(|args| args.get(*index))
            .ok_or(INCOMPATIBLE_CAPTURE)?;
    }
    let Some(items) = null_args(pattern) else {
        return Ok(CaptureKind::Scalar);
    };
    for _ in items {
        templates::charge(visited)?;
    }
    if repetition::whole(pattern)?.is_some() || repetition::slice(pattern)?.is_some() {
        for item in items {
            if repetition::suffix(item)?.is_some() {
                return splice_kind(item);
            }
        }
    }
    Ok(CaptureKind::Scalar)
}

pub(in crate::extensions) fn pattern(
    rhs: &Syntax,
    variables: &[(Vec<usize>, Name)],
    children: &[Syntax],
) -> Result<(), &'static str> {
    validate(rhs, variables, |path, visited| {
        pattern_kind(children, path, visited)
    })
}

/// Recover the output slots of a direct macro's persisted parser description.
/// `withPosition` preserves the typed argument; other wrappers bind scalar
/// syntax under MacroArgUtil, even when that syntax happens to be a null node.
fn descriptor_slots(
    descr: &Descr,
    slots: &mut Vec<CaptureKind>,
    visited: &mut usize,
    depth: usize,
) -> Result<(), &'static str> {
    charge(visited, depth)?;
    match descr {
        Descr::Binary(name, left, right) if simple(name).as_deref() == Some("andthen") => {
            descriptor_slots(left, slots, visited, depth + 1)?;
            descriptor_slots(right, slots, visited, depth + 1)?;
        }
        Descr::Binary(name, left, right) if simple(name).as_deref() == Some("orelse") => {
            let mut left_slots = Vec::new();
            let mut right_slots = Vec::new();
            descriptor_slots(left, &mut left_slots, visited, depth + 1)?;
            descriptor_slots(right, &mut right_slots, visited, depth + 1)?;
            if left_slots.len() != right_slots.len() {
                return Err(INCOMPATIBLE_CAPTURE);
            }
            slots.extend(std::iter::repeat_n(CaptureKind::Scalar, left_slots.len()));
        }
        Descr::Unary(name, body) if simple(name).as_deref() == Some("withPosition") => {
            descriptor_slots(body, slots, visited, depth + 1)?;
        }
        Descr::Unary(name, _) if simple(name).as_deref() == Some("optional") => {
            slots.push(CaptureKind::Optional);
        }
        Descr::Unary(name, _) if matches!(simple(name).as_deref(), Some("many" | "many1")) => {
            slots.push(CaptureKind::Many);
        }
        Descr::SepBy { separator, .. } => slots.push(CaptureKind::Separated(separator.clone())),
        Descr::Const(name) | Descr::Unary(name, _) | Descr::Binary(name, _, _) => {
            let alias = simple(name)
                .and_then(|name| extension_census().aliases.get(&name))
                .ok_or(INCOMPATIBLE_CAPTURE)?;
            match alias.stack {
                Some(count) if count <= MAX_TEMPLATE_NODES.saturating_sub(*visited) => {
                    for _ in 0..count {
                        templates::charge(visited)?;
                        slots.push(CaptureKind::Scalar);
                    }
                }
                Some(_) => return Err("a macro template past the node budget"),
                None => {
                    let start = slots.len();
                    match descr {
                        Descr::Unary(_, body) => {
                            descriptor_slots(body, slots, visited, depth + 1)?;
                        }
                        _ => return Err(INCOMPATIBLE_CAPTURE),
                    }
                    slots[start..].fill(CaptureKind::Scalar);
                }
            }
        }
        _ => slots.push(CaptureKind::Scalar),
    }
    Ok(())
}

pub(in crate::extensions) fn imported(
    rule: &NotationRule,
    descr: Option<&Descr>,
) -> Result<(), &'static str> {
    if let Some(pattern) = &rule.pattern {
        return self::pattern(
            &rule.rhs,
            &rule.variables,
            node_args(pattern).ok_or(INCOMPATIBLE_CAPTURE)?,
        );
    }
    let mut slots = None;
    validate(&rule.rhs, &rule.variables, |path, visited| {
        if slots.is_none() {
            let mut output = Vec::new();
            match descr.ok_or(INCOMPATIBLE_CAPTURE)? {
                Descr::Node { body, .. } => descriptor_slots(body, &mut output, visited, 0)?,
                Descr::TrailingNode { body, .. } => {
                    templates::charge(visited)?;
                    output.push(CaptureKind::Scalar);
                    descriptor_slots(body, &mut output, visited, 0)?;
                }
                _ => return Err(INCOMPATIBLE_CAPTURE),
            }
            slots = Some(output);
        }
        let [index] = path else {
            return Err(INCOMPATIBLE_CAPTURE);
        };
        templates::charge(visited)?;
        slots
            .as_ref()
            .and_then(|slots| slots.get(*index))
            .cloned()
            .ok_or(INCOMPATIBLE_CAPTURE)
    })
}

#[cfg(test)]
mod tests;
