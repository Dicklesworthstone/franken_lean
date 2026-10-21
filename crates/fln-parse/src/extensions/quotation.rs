//! Native matching of quoted syntax, before expansion of its arguments.
//!
//! Anchors: Lean/Elab/Quotation.lean (`getHeadInfo`) and Init/Prelude.lean
//! (`Syntax.matchesIdent`, `matchesLit`) at SUITE.lock's Reference. Names compare
//! modulo macro scopes; atoms are significant only inside the built-in literals.
//! This is a bounded quotation interpreter, not execution of arbitrary MacroM.
use super::*;

pub(super) mod repetition;
pub(super) mod templates;

pub(super) fn at_path<'a>(args: &'a [Syntax], path: &[usize]) -> Option<&'a Syntax> {
    let (first, rest) = path.split_first()?;
    let mut current = args.get(*first)?;
    for index in rest {
        current = node_args(current)?.get(*index)?;
    }
    Some(current)
}

pub(super) fn variables(children: &[Syntax]) -> Result<Vec<(Vec<usize>, Name)>, &'static str> {
    let mut tasks: Vec<_> = children
        .iter()
        .enumerate()
        .rev()
        .map(|(index, child)| (child, vec![index]))
        .collect();
    let mut variables = Vec::new();
    let mut bound = BTreeSet::new();
    let mut visited = 0;
    while let Some((pattern, path)) = tasks.pop() {
        visited += 1;
        if visited > MAX_TEMPLATE_NODES || path.len() > MAX_DESCR_DEPTH {
            return Err("a quoted macro pattern past the node or depth budget");
        }
        if let Some(sequence) = repetition::whole(pattern)? {
            let name = sequence.name()?;
            if name != Name::from_components(["_"]) {
                let name = macro_variable(&name);
                if !bound.insert(name.clone()) {
                    return Err("a repeated quoted macro pattern variable");
                }
                variables.push((path, name));
            }
            continue;
        }
        if let Some(tail) = repetition::tail(pattern)? {
            let name = tail.sequence.name()?;
            if name != Name::from_components(["_"]) {
                let name = macro_variable(&name);
                if !bound.insert(name.clone()) {
                    return Err("a repeated quoted macro pattern variable");
                }
                variables.push((path.clone(), name));
            }
            for (index, child) in tail.prefix.iter().enumerate().rev() {
                let mut child_path = path.clone();
                child_path.push(index);
                tasks.push((child, child_path));
            }
            continue;
        }
        if let Some(name) = antiquotation_name(pattern) {
            if name == Name::from_components(["_"]) {
                continue;
            }
            let name = macro_variable(&name);
            if !bound.insert(name.clone()) {
                return Err("a repeated quoted macro pattern variable");
            }
            variables.push((path, name));
            continue;
        }
        if let Syntax::Node { kind, args, .. } = pattern {
            let leaf = components(kind).last().cloned().unwrap_or_default();
            if leaf.contains("antiquot") || matches!(leaf.as_str(), "quot" | "quotSeq") {
                return Err(
                    "a splice, expression antiquotation or nested quotation in a macro pattern",
                );
            }
            for (index, child) in args.iter().enumerate().rev() {
                let mut path = path.clone();
                path.push(index);
                tasks.push((child, path));
            }
        }
    }
    Ok(variables)
}

pub(super) fn matches(rule: &NotationRule, args: &[Syntax]) -> Result<bool, &'static str> {
    let Some(pattern) = &rule.pattern else {
        return Ok(true);
    };
    let Some(patterns) = node_args(pattern) else {
        return Err("a quoted macro pattern without a syntax node");
    };
    if patterns.len() != args.len() {
        return Ok(false);
    }
    let mut pending: Vec<_> = patterns
        .iter()
        .zip(args)
        .map(|(p, a)| (p, a, false))
        .collect();
    let mut visited = 0;
    while let Some((pattern, value, literal)) = pending.pop() {
        visited += 1;
        if visited > MAX_TEMPLATE_NODES {
            return Err("quoted macro matching past the node budget");
        }
        if let Some(sequence) = repetition::whole(pattern)? {
            if !sequence.accepts(value, &mut visited)? {
                return Ok(false);
            }
            continue;
        }
        if let Some(tail) = repetition::tail(pattern)? {
            let Some(items) = null_args(value) else {
                return Ok(false);
            };
            if items.len() < tail.prefix.len() || !tail.sequence.accepts(value, &mut visited)? {
                return Ok(false);
            }
            pending.extend(tail.prefix.iter().zip(items).map(|(p, a)| (p, a, false)));
            continue;
        }
        if antiquotation_name(pattern).is_some() {
            // The pin's getHeadInfo checks explicit concrete kinds, even for
            // anonymous captures. A category's pseudo kind (for example term)
            // is not an actual node kind and remains an unconditional capture.
            if !capture_kind_matches(pattern, value)? {
                return Ok(false);
            }
            continue;
        }
        match (pattern, value) {
            (Syntax::Missing, Syntax::Missing) => {}
            (Syntax::Atom { val: a, .. }, Syntax::Atom { val: b, .. }) if !literal || a == b => {}
            (Syntax::Ident { val: a, .. }, Syntax::Ident { val: b, .. })
                if a.erase_macro_scopes() == b.erase_macro_scopes() => {}
            (
                Syntax::Node {
                    kind: a, args: pa, ..
                },
                Syntax::Node {
                    kind: b, args: va, ..
                },
            ) if a == b && pa.len() == va.len() => {
                let literal = ["num", "str", "char", "name", "scientific"]
                    .iter()
                    .any(|name| *a == Name::from_components([*name]));
                pending.extend(pa.iter().zip(va).map(|(p, a)| (p, a, literal)));
            }
            _ => return Ok(false),
        }
    }
    Ok(true)
}

fn capture_kind_matches(pattern: &Syntax, value: &Syntax) -> Result<bool, &'static str> {
    let Syntax::Node { kind, args, .. } = pattern else {
        return Err("a quoted capture without an antiquotation node");
    };
    let [_, _, _, annotation] = args.as_slice() else {
        return Err("a quoted capture with malformed antiquotation children");
    };
    if null_args(annotation).is_some_and(<[Syntax]>::is_empty) {
        return Ok(true);
    }
    if !kind_is(annotation, &["antiquotName"]) {
        return Err("a quoted capture with a malformed kind annotation");
    }
    let expected = kind.parent();
    if components(&expected).last().map(String::as_str) == Some("pseudo") {
        return Ok(true);
    }
    Ok(match value {
        Syntax::Node { kind, .. } => *kind == expected,
        Syntax::Ident { .. } => expected == Name::from_components(["ident"]),
        Syntax::Atom { .. } => expected == Name::from_components(["atom"]),
        Syntax::Missing => expected == Name::from_components(["missing"]),
    })
}
