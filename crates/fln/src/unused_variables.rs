//! The pin's unused-variables linter (`Lean/Linter/UnusedVariables.lean`), for a
//! declaration's own signature binders (bead `fln-default-linters-unused-variables-mtnt`).
//!
//! The pin decides use from its info tree: a binder is used when some elaborated
//! identifier refers to it, or when its free variable occurs in the declaration body
//! instantiated before abstraction. This module reads the command's syntax and its
//! admitted declaration instead. A signature binder counts as used when an identifier
//! with its name appears anywhere else in the command, or when its bound variable occurs
//! in the admitted type after it or in the admitted value. Both over-approximate the
//! pin's uses: a shadowing inner binder of the same name counts, and so does any
//! elaborated occurrence. So a warning printed here is one the pin prints too.
//!
//! A command this increment cannot decide is not linted, exactly as before this
//! module existed: the pin's warning is missing, never invented. That covers a tactic
//! block or `‹_›` (the pin reads the tactic's proof term, which need not match this
//! engine's), `sorry` (the pin skips the whole command), and every binder form other
//! than the four bracket kinds and bare identifiers.
use fln_core::expr::{Expr, ExprNode};
use fln_core::name::{LeafView, Name};
use fln_core::options::KVMap;
use fln_syntax::source::SourceInfo;
use fln_syntax::tree::Syntax;
use std::collections::HashSet;

/// A parser node kind, `Lean.Parser.<components>`.
pub(crate) fn parser_kind(components: &[&str]) -> Name {
    components.iter().fold(
        Name::from_components(["Lean", "Parser"]),
        |name, component| Name::str(name, *component),
    )
}

/// One unused signature binder: its name and its byte offset in the command.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct UnusedBinder {
    pub at: usize,
    pub name: Name,
}

/// The pin's `logLint` text for `linter.unusedVariables`
/// (`Lean/Linter/UnusedVariables.lean`, `Lean/Linter/Util.lean`).
pub(crate) fn message(name: &Name) -> String {
    format!(
        "Variable name `{}` is not explicitly referenced.\n\nThe binding can be removed \
         (if unused) or named `_` (if used implicitly).\n\nNote: This linter can be disabled \
         with `set_option linter.unusedVariables false`",
        name.to_display_string()
    )
}

fn option(options: &KVMap, key: &[&str]) -> Option<bool> {
    let key = Name::from_components(key.iter().copied());
    let on = options.get_bool(&key, true);
    (on == options.get_bool(&key, false)).then_some(on)
}

/// `getLinterValue`: a linter option left unset falls back to `linter.all`, then to `true`,
/// the default of every linter read here.
pub(crate) fn linter_value(options: &KVMap, name: &[&str]) -> bool {
    option(options, name).unwrap_or_else(|| option(options, &["linter", "all"]).unwrap_or(true))
}

/// `getLinterValue linter.unusedVariables` and one of its refinements (`funArgs`,
/// `patternVars`): an unset option falls back to `linter.all`, then to its default `true`.
fn linted(options: &KVMap, refinement: Option<&str>) -> bool {
    let all = option(options, &["linter", "all"]).unwrap_or(true);
    let enabled = option(options, &["linter", "unusedVariables"]).unwrap_or(all);
    enabled
        && refinement.is_none_or(|refinement| {
            option(options, &["linter", "unusedVariables", refinement]).unwrap_or(enabled)
        })
}

fn is_kind(syntax: &Syntax, kind: &[&str]) -> bool {
    syntax.kind() == Some(&parser_kind(kind))
}

fn args(syntax: &Syntax) -> &[Syntax] {
    match syntax {
        Syntax::Node { args, .. } => args,
        _ => &[],
    }
}

fn original_pos(syntax: &Syntax) -> Option<usize> {
    match syntax.info() {
        SourceInfo::Original { pos, .. } => Some(pos.0),
        _ => None,
    }
}

/// Every node and leaf of `syntax`, iteratively.
fn walk<'a>(syntax: &'a Syntax, mut visit: impl FnMut(&'a Syntax) -> bool) -> bool {
    let mut pending = vec![syntax];
    while let Some(node) = pending.pop() {
        if visit(node) {
            return true;
        }
        pending.extend(args(node).iter());
    }
    false
}

fn contains_atom(syntax: &Syntax, atoms: &[&str]) -> bool {
    walk(
        syntax,
        |node| matches!(node, Syntax::Atom { val, .. } if atoms.contains(&val.as_str())),
    )
}

fn root(name: &Name) -> Name {
    let mut current = name.clone();
    while !current.parent().is_anonymous() {
        current = current.parent();
    }
    current
}

/// One telescope slot per binder the signature declares, named where it names one
/// with original syntax. `None` when the signature has a form this increment does not read.
fn signature_slots(binders: &[Syntax]) -> Option<Vec<Option<(Name, usize)>>> {
    let named = |syntax: &Syntax| match syntax {
        Syntax::Ident { val, .. } => Some(original_pos(syntax).map(|pos| (val.clone(), pos))),
        _ if is_kind(syntax, &["Term", "hole"]) => Some(None),
        _ => None,
    };
    let mut slots = Vec::new();
    for binder in binders {
        if let Some(slot) = named(binder) {
            slots.push(slot);
        } else if is_kind(binder, &["Term", "instBinder"]) {
            slots.push(match args(args(binder).get(1)?) {
                [] => None,
                [name, _colon] => named(name)?,
                _ => return None,
            });
        } else if ["explicitBinder", "implicitBinder", "strictImplicitBinder"]
            .iter()
            .any(|kind| is_kind(binder, &["Term", kind]))
        {
            for name in args(args(binder).get(1)?) {
                slots.push(named(name)?);
            }
        } else {
            return None;
        }
    }
    Some(slots)
}

/// A `def`, `theorem`, `abbrev`, `instance` or `example` whose uses this module can decide:
/// its modifiers and declaration, or `None`. A tactic block or `‹_›` makes the pin read a
/// proof term this engine need not share, and the pin never lints a command with `sorry`.
fn decided(command: &Syntax) -> Option<(&Syntax, &Syntax)> {
    if !is_kind(command, &["Command", "declaration"]) {
        return None;
    }
    let [modifiers, declaration] = args(command) else {
        return None;
    };
    (["definition", "theorem", "abbrev", "instance", "example"]
        .iter()
        .any(|kind| is_kind(declaration, &["Command", kind]))
        && !contains_atom(declaration, &["sorry", "admit", "by", "‹"]))
    .then_some((modifiers, declaration))
}

/// The pattern variables a `matchAlt`'s patterns bind, with their positions, or `None`
/// when a pattern has a form this module does not read. An identifier is a variable unless
/// it is qualified, heads an application, or is spelled like some constructor: the pin
/// resolves it against the open namespaces, so any constructor spelling may be one.
fn pattern_variables(
    patterns: &Syntax,
    constructors: &HashSet<String>,
) -> Option<Vec<(Name, usize)>> {
    let mut variables = Vec::new();
    let mut pending = vec![patterns];
    while let Some(pattern) = pending.pop() {
        match pattern {
            Syntax::Ident { val, .. } => {
                if let LeafView::Str(text) = val.leaf_view()
                    && val.parent().is_anonymous()
                    && !constructors.contains(text)
                {
                    variables.push((val.clone(), original_pos(pattern)?));
                }
            }
            Syntax::Atom { .. } | Syntax::Missing => {}
            Syntax::Node { kind, args, .. } => {
                let kind = kind.to_display_string();
                match kind.as_str() {
                    "null"
                    | "Lean.Parser.Term.paren"
                    | "Lean.Parser.Term.anonymousCtor"
                    | "Lean.Parser.Term.tuple"
                    | "term_+_"
                    | "term_::_"
                    | "term[_]" => {
                        pending.extend(args.iter());
                    }
                    // The head is a constructor or a `match_pattern` function, never bound.
                    "Lean.Parser.Term.app" => pending.extend(args.get(1)),
                    "Lean.Parser.Term.namedPattern" => {
                        pending.extend(args.first());
                        pending.extend(args.get(3));
                    }
                    // The ascribed type is a term the pattern's variables may appear in.
                    "Lean.Parser.Term.typeAscription" => pending.extend(args.get(1)),
                    "Lean.Parser.Term.hole"
                    | "Lean.Parser.Term.ellipsis"
                    | "Lean.Parser.Term.dotIdent"
                    | "Lean.Parser.Term.hygienicLParen"
                    | "num"
                    | "str"
                    | "char"
                    | "scientific" => {}
                    _ => return None,
                }
            }
        }
    }
    Some(variables)
}

/// The unused pattern variables of `command`'s `match` alternatives and equations, in source
/// order. The pin reads a pattern variable's uses only from elaborated references: the body
/// it records abstracts every alternative's variables, so a reference in the alternative is
/// the whole evidence, and an identifier with its name anywhere else in the alternative
/// over-approximates it.
pub(crate) fn unused_pattern_variables(
    command: &Syntax,
    options: &KVMap,
    constructors: &HashSet<String>,
) -> Vec<UnusedBinder> {
    let Some((_, declaration)) = decided(command) else {
        return Vec::new();
    };
    if !linted(options, Some("patternVars")) {
        return Vec::new();
    }
    let mut alternatives = Vec::new();
    walk(declaration, |node| {
        if is_kind(node, &["Term", "matchAlt"]) {
            alternatives.push(node);
        }
        false
    });
    let mut unused = Vec::new();
    for alternative in alternatives {
        let Some(patterns) = args(alternative).get(1) else {
            continue;
        };
        let Some(variables) = pattern_variables(patterns, constructors) else {
            continue;
        };
        for (name, at) in variables {
            if matches!(name.leaf_view(), LeafView::Str(text) if text.starts_with('_')) {
                continue;
            }
            let referenced = walk(alternative, |node| {
                matches!(node, Syntax::Ident { val, .. }
                    if root(val) == name && original_pos(node) != Some(at))
            });
            if !referenced {
                unused.push(UnusedBinder { at, name });
            }
        }
    }
    unused.sort_by_key(|binder| binder.at);
    unused
}

/// The binders a `fun`'s binder list names, or `None` when one has a form not read here.
/// An instance binder is left unread: the pin may count resolution as its use.
fn fun_binders(binders: &[Syntax], constructors: &HashSet<String>) -> Option<Vec<(Name, usize)>> {
    // A binder name, a hole, or `x y` written as an application of names.
    fn idents(syntax: &Syntax) -> Option<Vec<(Name, usize)>> {
        let parts: Vec<&Syntax> = if is_kind(syntax, &["Term", "app"]) {
            std::iter::once(args(syntax).first()?)
                .chain(args(args(syntax).get(1)?))
                .collect()
        } else {
            vec![syntax]
        };
        let mut names = Vec::new();
        for part in parts {
            match part {
                Syntax::Ident { val, .. } => names.push((val.clone(), original_pos(part)?)),
                _ if is_kind(part, &["Term", "hole"]) => {}
                _ => return None,
            }
        }
        Some(names)
    }
    let mut names = Vec::new();
    for binder in binders {
        if matches!(binder, Syntax::Ident { .. }) || is_kind(binder, &["Term", "hole"]) {
            names.extend(idents(binder)?);
        } else if is_kind(binder, &["Term", "tuple"]) || is_kind(binder, &["Term", "anonymousCtor"])
        {
            // `fun (x, y) => …` matches on its argument: its names are pattern variables.
            names.extend(pattern_variables(binder, constructors)?);
        } else if is_kind(binder, &["Term", "typeAscription"])
            || is_kind(binder, &["Term", "paren"])
        {
            names.extend(idents(args(binder).get(1)?)?);
        } else if is_kind(binder, &["Term", "implicitBinder"])
            || is_kind(binder, &["Term", "strictImplicitBinder"])
        {
            for name in args(args(binder).get(1)?) {
                names.extend(idents(name)?);
            }
        } else if !is_kind(binder, &["Term", "instBinder"]) {
            return None;
        }
    }
    Some(names)
}

/// The unused binders of `command`'s `fun` terms, in source order. Inside a declaration
/// body the pin counts only elaborated references to them (the recorded body abstracts
/// them), and an identifier with the name anywhere in the `fun` over-approximates those.
pub(crate) fn unused_fun_binders(
    command: &Syntax,
    options: &KVMap,
    constructors: &HashSet<String>,
) -> Vec<UnusedBinder> {
    let Some((_, declaration)) = decided(command) else {
        return Vec::new();
    };
    // The pin's ignore functions for function arguments (`basicFun`) when `funArgs` is off.
    if !linted(options, Some("funArgs")) {
        return Vec::new();
    }
    let mut functions = Vec::new();
    walk(declaration, |node| {
        if is_kind(node, &["Term", "basicFun"]) {
            functions.push(node);
        }
        false
    });
    let mut unused = Vec::new();
    for function in functions {
        let Some(binders) = args(function).first() else {
            continue;
        };
        let Some(names) = fun_binders(args(binders), constructors) else {
            continue;
        };
        for (name, at) in names {
            if matches!(name.leaf_view(), LeafView::Str(text) if text.starts_with('_')) {
                continue;
            }
            let referenced = walk(function, |node| {
                matches!(node, Syntax::Ident { val, .. }
                    if root(val) == name && original_pos(node) != Some(at))
            });
            if !referenced {
                unused.push(UnusedBinder { at, name });
            }
        }
    }
    unused.sort_by_key(|binder| binder.at);
    unused
}

/// The names a binder group declares, or `None` for a form not read here. An instance
/// binder declares nothing read here: the pin may count resolution as its use.
fn group_names(binder: &Syntax) -> Option<Vec<(Name, usize)>> {
    let mut names = Vec::new();
    let mut push = |syntax: &Syntax| -> Option<()> {
        match syntax {
            Syntax::Ident { val, .. } => names.push((val.clone(), original_pos(syntax)?)),
            _ if is_kind(syntax, &["Term", "hole"]) => {}
            _ => return None,
        }
        Some(())
    };
    if matches!(binder, Syntax::Ident { .. }) || is_kind(binder, &["Term", "hole"]) {
        push(binder)?;
    } else if ["explicitBinder", "implicitBinder", "strictImplicitBinder"]
        .iter()
        .any(|kind| is_kind(binder, &["Term", kind]))
    {
        for name in args(args(binder).get(1)?) {
            push(name)?;
        }
    } else if !is_kind(binder, &["Term", "instBinder"]) {
        return None;
    }
    Some(names)
}

/// The unused binders of `command`'s `∀` and dependent arrows, in source order. Such a
/// binder is in scope only in the term it binds, so the pin's whole evidence is a reference
/// there. The pin ignores an explicit dependent arrow's binder (`(x : A) → B`), not an
/// implicit one (`{x : A} → B`).
pub(crate) fn unused_type_binders(command: &Syntax, options: &KVMap) -> Vec<UnusedBinder> {
    let Some((_, declaration)) = decided(command) else {
        return Vec::new();
    };
    if !linted(options, None) {
        return Vec::new();
    }
    let mut scopes: Vec<(&Syntax, Vec<(Name, usize)>)> = Vec::new();
    walk(declaration, |node| {
        let names = if is_kind(node, &["Term", "forall"]) {
            args(node).get(1).and_then(|binders| {
                args(binders)
                    .iter()
                    .map(group_names)
                    .collect::<Option<Vec<_>>>()
                    .map(|groups| groups.concat())
            })
        } else if is_kind(node, &["Term", "depArrow"]) {
            args(node)
                .first()
                .filter(|binder| !is_kind(binder, &["Term", "explicitBinder"]))
                .and_then(group_names)
        } else {
            None
        };
        if let Some(names) = names {
            scopes.push((node, names));
        }
        false
    });
    let mut unused = Vec::new();
    for (scope, names) in scopes {
        for (name, at) in names {
            if matches!(name.leaf_view(), LeafView::Str(text) if text.starts_with('_')) {
                continue;
            }
            let referenced = walk(scope, |node| {
                matches!(node, Syntax::Ident { val, .. }
                    if root(val) == name && original_pos(node) != Some(at))
            });
            if !referenced {
                unused.push(UnusedBinder { at, name });
            }
        }
    }
    unused.sort_by_key(|binder| binder.at);
    unused
}

/// The binders a `∀`/`fun` telescope introduces, by name, outermost first.
fn telescope(mut expr: &Expr, lambda: bool) -> Vec<(&Name, &Expr)> {
    let mut binders = Vec::new();
    loop {
        match expr.node() {
            ExprNode::ForallE {
                binder_name, body, ..
            } if !lambda => {
                binders.push((binder_name, body));
                expr = body;
            }
            ExprNode::Lam {
                binder_name, body, ..
            } if lambda => {
                binders.push((binder_name, body));
                expr = body;
            }
            ExprNode::MData { expr: inner, .. } => expr = inner,
            _ => return binders,
        }
    }
}

/// The unused signature binders of `command`, a parsed `def`, `theorem`, `abbrev`,
/// `instance` or `example`, given its admitted `type_` and `value`, in source order.
pub(crate) fn unused_signature_binders(
    command: &Syntax,
    type_: &Expr,
    value: &Expr,
    options: &KVMap,
) -> Vec<UnusedBinder> {
    let Some((modifiers, declaration)) = decided(command) else {
        return Vec::new();
    };
    // The pin's ignore function for foreign definitions (`@[extern]`, `implemented_by`).
    if !linted(options, Some("funArgs")) || contains_atom(modifiers, &["extern", "implemented_by"])
    {
        return Vec::new();
    }
    let Some(signature) = args(declaration).iter().find(|part| {
        is_kind(part, &["Command", "optDeclSig"]) || is_kind(part, &["Command", "declSig"])
    }) else {
        return Vec::new();
    };
    let Some(slots) = args(signature)
        .first()
        .and_then(|binders| signature_slots(args(binders)))
    else {
        return Vec::new();
    };
    if slots.is_empty() {
        return Vec::new();
    }
    // Align the slots with the admitted telescope: section variables and automatically
    // bound implicits come first, so the signature starts at the earliest matching index.
    let pis = telescope(type_, false);
    let lambdas = telescope(value, true);
    let matches = |names: &[(&Name, &Expr)], start: usize| {
        slots.iter().enumerate().all(|(offset, slot)| {
            names
                .get(start + offset)
                .is_some_and(|(name, _)| slot.as_ref().is_none_or(|(slot, _)| *name == slot))
        })
    };
    let Some(start) =
        (0..pis.len()).find(|&start| matches(&pis, start) && matches(&lambdas, start))
    else {
        return Vec::new();
    };
    let mut unused = Vec::new();
    for (offset, slot) in slots.iter().enumerate() {
        let Some((name, at)) = slot else { continue };
        // `_x` is the suggested way to keep an intentionally unused binder.
        if matches!(name.leaf_view(), LeafView::Str(text) if text.starts_with('_')) {
            continue;
        }
        let referenced = walk(declaration, |node| {
            matches!(node, Syntax::Ident { val, .. }
                if root(val) == *name && original_pos(node) != Some(*at))
        });
        let index = start + offset;
        if referenced || pis[index].1.has_loose_bvar(0) || lambdas[index].1.has_loose_bvar(0) {
            continue;
        }
        unused.push(UnusedBinder {
            at: *at,
            name: name.clone(),
        });
    }
    unused.sort_by_key(|binder| binder.at);
    unused
}
