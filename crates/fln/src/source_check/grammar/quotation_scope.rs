//! Scope-aware quotation pre-resolution. Binder declarations are not global
//! references. Domains see the preceding binders, including earlier names in
//! the same group (the pin's `toBinderViews` / `elabBinders` discipline).
//! The worklist normalizes shared domains while preserving source locations and
//! binder order. It does not elaborate, assign metavariables or admit declarations.

use super::{BINDING, Resolution, TACTIC_BINDING};
use crate::EngineExecutionError;
use fln_core::name::Name;
use fln_parse::extensions::NotationRule;
use fln_syntax::source::SourceInfo;
use fln_syntax::tree::{Preresolved, Syntax};

enum Task<'a> {
    Visit(&'a Syntax),
    Copy(&'a Syntax),
    Emit(Syntax),
    Build(SourceInfo, &'a Name, usize),
    BuildNew(Name, usize),
    Binders(&'a Syntax),
    Binder(&'a Syntax, Option<&'a Syntax>),
    SharedBinders(&'a Syntax, &'a Syntax, &'a Syntax),
    SharedBinder(&'a Syntax, &'a Syntax, &'a Syntax),
    Bind(Vec<Name>),
    Restore(usize),
}

fn unsupported_binder() -> EngineExecutionError {
    EngineExecutionError::NotImplemented {
        feature: "a notation template with an unsupported binder shape",
    }
}

fn term_kind(kind: &Name, leaf: &str) -> bool {
    *kind == Name::from_components(["Lean", "Parser", "Term", leaf])
}

fn term_args<'a>(syntax: &'a Syntax, leaf: &str) -> Result<&'a [Syntax], EngineExecutionError> {
    match syntax {
        Syntax::Node { kind, args, .. } if term_kind(kind, leaf) => Ok(args),
        _ => Err(unsupported_binder()),
    }
}

fn null_args(syntax: &Syntax) -> Result<&[Syntax], EngineExecutionError> {
    match syntax {
        Syntax::Node { kind, args, .. } if *kind == Name::from_components(["null"]) => Ok(args),
        _ => Err(unsupported_binder()),
    }
}

fn atom(syntax: &Syntax, spellings: &[&str]) -> bool {
    matches!(syntax, Syntax::Atom { val, .. } if spellings.contains(&val.as_str()))
}

fn build(syntax: &Syntax) -> Result<Task<'_>, EngineExecutionError> {
    match syntax {
        Syntax::Node { info, kind, args } => Ok(Task::Build(*info, kind, args.len())),
        _ => Err(unsupported_binder()),
    }
}

/// A literal identifier or `_`, not a pattern or an antiquoted binder. The
/// latter needs quotation-pattern scope information, not a guessed local name.
fn binder_name(
    syntax: &Syntax,
    rule: &NotationRule,
    names: &mut Vec<Name>,
) -> Result<(), EngineExecutionError> {
    match syntax {
        Syntax::Ident { val, .. }
            if !val.is_anonymous()
                && !rule.variables.iter().any(|(_, variable)| variable == val) =>
        {
            names.push(val.clone());
            Ok(())
        }
        Syntax::Node { kind, args, .. }
            if term_kind(kind, "hole") && args.len() == 1 && atom(&args[0], &["_"]) =>
        {
            Ok(())
        }
        _ => Err(unsupported_binder()),
    }
}

/// A lambda's explicit `(x y : T)` stores its names in the ordinary
/// application tree, unlike implicit groups, which store a null list.
fn lambda_names(syntax: &Syntax, rule: &NotationRule) -> Result<Vec<Name>, EngineExecutionError> {
    let mut names = Vec::new();
    if let Ok(args) = term_args(syntax, "app") {
        let [head, rest] = args else {
            return Err(unsupported_binder());
        };
        binder_name(head, rule, &mut names)?;
        let rest = null_args(rest)?;
        if rest.is_empty() {
            return Err(unsupported_binder());
        }
        for name in rest {
            binder_name(name, rule, &mut names)?;
        }
    } else {
        binder_name(syntax, rule, &mut names)?;
    }
    Ok(names)
}

fn list_names(syntax: &Syntax, rule: &NotationRule) -> Result<Vec<Name>, EngineExecutionError> {
    let entries = null_args(syntax)?;
    if entries.is_empty() {
        return Err(unsupported_binder());
    }
    let mut names = Vec::new();
    for entry in entries {
        binder_name(entry, rule, &mut names)?;
    }
    Ok(names)
}

fn optional_type(syntax: &Syntax) -> Result<(), EngineExecutionError> {
    match null_args(syntax)? {
        [] => Ok(()),
        [colon, _domain] if atom(colon, &[":"]) => Ok(()),
        _ => Err(unsupported_binder()),
    }
}

fn shared_type(syntax: &Syntax) -> Result<Option<(&Syntax, &Syntax)>, EngineExecutionError> {
    match null_args(syntax)? {
        [] => Ok(None),
        [spec] => match term_args(spec, "typeSpec")? {
            [colon, domain] if atom(colon, &[":"]) => Ok(Some((colon, domain))),
            _ => Err(unsupported_binder()),
        },
        _ => Err(unsupported_binder()),
    }
}

fn lambda<'a>(
    syntax: &'a Syntax,
    tasks: &mut Vec<Task<'a>>,
    scope_depth: usize,
) -> Result<(), EngineExecutionError> {
    let [keyword, basic] = term_args(syntax, "fun")? else {
        return Err(unsupported_binder());
    };
    let [binders, annotation, arrow, body] = term_args(basic, "basicFun")? else {
        return Err(unsupported_binder());
    };
    if !atom(keyword, &["fun", "λ"]) || !atom(arrow, &["=>", "↦"]) || null_args(binders)?.is_empty()
    {
        return Err(unsupported_binder());
    }
    let shared = shared_type(annotation)?;
    if shared.is_some() && !null_args(binders)?.iter().all(bare_binder) {
        return Err(unsupported_binder());
    }
    // `fun x y : T => body` annotates each binder, not the result. Split
    // shared types so a later copy can resolve names in its own local context.
    // LIFO: each binder, then the body. Restore only
    // after the whole lambda, so none of its locals can escape to a sibling.
    tasks.push(Task::Restore(scope_depth));
    tasks.push(build(syntax)?);
    tasks.push(build(basic)?);
    tasks.push(Task::Visit(body));
    tasks.push(Task::Copy(arrow));
    if let Some((colon, domain)) = shared {
        tasks.push(Task::Emit(Syntax::node(
            Name::from_components(["null"]),
            vec![],
        )));
        tasks.push(Task::SharedBinders(binders, colon, domain));
    } else {
        tasks.push(Task::Copy(annotation));
        tasks.push(Task::Binders(binders));
    }
    tasks.push(Task::Copy(keyword));
    Ok(())
}

fn bare_binder(syntax: &Syntax) -> bool {
    matches!(syntax, Syntax::Ident { .. }) || term_args(syntax, "hole").is_ok()
}

/// As at the pin's `expandForall`, the shared type in `∀ x y : T, body`
/// annotates each binder separately, in the context of preceding binders.
fn forall<'a>(
    syntax: &'a Syntax,
    tasks: &mut Vec<Task<'a>>,
    scope_depth: usize,
) -> Result<(), EngineExecutionError> {
    let [keyword, binders, annotation, comma, body] = term_args(syntax, "forall")? else {
        return Err(unsupported_binder());
    };
    let entries = null_args(binders)?;
    if entries.is_empty() || !atom(keyword, &["∀", "forall"]) || !atom(comma, &[","]) {
        return Err(unsupported_binder());
    }
    let shared = shared_type(annotation)?;
    let all_bare = entries.iter().all(bare_binder);
    // Mixed telescopes have shared-type attachment rules that are not modelled
    // here. Refuse them rather than silently placing a name in the wrong scope.
    if !all_bare && (entries.iter().any(bare_binder) || !null_args(annotation)?.is_empty()) {
        return Err(unsupported_binder());
    }
    tasks.push(Task::Restore(scope_depth));
    tasks.push(build(syntax)?);
    tasks.push(Task::Visit(body));
    tasks.push(Task::Copy(comma));
    if let Some((colon, domain)) = shared {
        tasks.push(Task::Emit(Syntax::node(
            Name::from_components(["null"]),
            vec![],
        )));
        tasks.push(Task::SharedBinders(binders, colon, domain));
    } else {
        tasks.push(Task::Copy(annotation));
        tasks.push(Task::Binders(binders));
    }
    tasks.push(Task::Copy(keyword));
    Ok(())
}

fn dependent_arrow<'a>(
    syntax: &'a Syntax,
    tasks: &mut Vec<Task<'a>>,
    scope_depth: usize,
) -> Result<(), EngineExecutionError> {
    let [binder, arrow, body] = term_args(syntax, "depArrow")? else {
        return Err(unsupported_binder());
    };
    let bracketed = matches!(binder, Syntax::Node { kind, .. }
        if ["explicitBinder", "implicitBinder", "strictImplicitBinder", "instBinder"]
            .iter().any(|leaf| term_kind(kind, leaf)));
    if !bracketed || !atom(arrow, &["→", "->"]) {
        return Err(unsupported_binder());
    }
    let binders = split_binders(std::slice::from_ref(binder))?;
    tasks.push(Task::Restore(scope_depth));
    // `(x y : T) → U` becomes nested arrows, each retaining its own
    // independently pre-resolved domain and the original source locations.
    for _ in &binders {
        tasks.push(build(syntax)?);
    }
    tasks.push(Task::Visit(body));
    for binder in binders.into_iter().rev() {
        tasks.push(Task::Copy(arrow));
        tasks.push(binder);
    }
    Ok(())
}

fn binder<'a>(
    syntax: &'a Syntax,
    selected: Option<&'a Syntax>,
    rule: &NotationRule,
    tasks: &mut Vec<Task<'a>>,
) -> Result<(), EngineExecutionError> {
    if bare_binder(syntax) {
        let mut names = Vec::new();
        binder_name(syntax, rule, &mut names)?;
        tasks.push(Task::Bind(names));
        tasks.push(Task::Copy(syntax));
        return Ok(());
    }
    let Syntax::Node { kind, args, .. } = syntax else {
        return Err(unsupported_binder());
    };
    let (mut names, domain) = if term_kind(kind, "typeAscription") {
        let [_open, names, colon, annotation, close] = args.as_slice() else {
            return Err(unsupported_binder());
        };
        if !atom(colon, &[":"]) || !atom(close, &[")"]) || null_args(annotation)?.len() != 1 {
            return Err(unsupported_binder());
        }
        (lambda_names(names, rule)?, Some(3))
    } else if term_kind(kind, "paren") {
        let [_open, names, close] = args.as_slice() else {
            return Err(unsupported_binder());
        };
        if !atom(close, &[")"]) {
            return Err(unsupported_binder());
        }
        (lambda_names(names, rule)?, None)
    } else if term_kind(kind, "explicitBinder") {
        let [open, names, annotation, default, close] = args.as_slice() else {
            return Err(unsupported_binder());
        };
        if !atom(open, &["("]) || !atom(close, &[")"]) || !null_args(default)?.is_empty() {
            return Err(unsupported_binder());
        }
        optional_type(annotation)?;
        (list_names(names, rule)?, Some(2))
    } else if term_kind(kind, "implicitBinder") || term_kind(kind, "strictImplicitBinder") {
        let [open, names, annotation, close] = args.as_slice() else {
            return Err(unsupported_binder());
        };
        let strict = term_kind(kind, "strictImplicitBinder");
        if !atom(open, &[if strict { "⦃" } else { "{" }])
            || !atom(close, &[if strict { "⦄" } else { "}" }])
        {
            return Err(unsupported_binder());
        }
        optional_type(annotation)?;
        (list_names(names, rule)?, Some(2))
    } else if term_kind(kind, "instBinder") {
        let [open, named, _domain, close] = args.as_slice() else {
            return Err(unsupported_binder());
        };
        if !atom(open, &["["]) || !atom(close, &["]"]) {
            return Err(unsupported_binder());
        }
        let mut names = Vec::new();
        match null_args(named)? {
            [] => {}
            [name, colon] if atom(colon, &[":"]) => binder_name(name, rule, &mut names)?,
            _ => return Err(unsupported_binder()),
        }
        (names, Some(2))
    } else {
        return Err(unsupported_binder());
    };
    if let Some(selected) = selected {
        names.clear();
        binder_name(selected, rule, &mut names)?;
    }
    // One name per group, so each domain sees all preceding names. In
    // `(x y : x)` the first domain may be global and the second names local x.
    tasks.push(Task::Bind(names));
    tasks.push(build(syntax)?);
    for (index, child) in args.iter().enumerate().rev() {
        if index == 1
            && let Some(selected) = selected
        {
            if !term_kind(kind, "typeAscription") && !term_kind(kind, "paren") {
                let Syntax::Node { info, kind, .. } = child else {
                    return Err(unsupported_binder());
                };
                tasks.push(Task::Build(*info, kind, 1));
            }
            tasks.push(Task::Copy(selected));
            continue;
        }
        // The hygienic opening parenthesis is structural syntax, not a binder
        // name. Walk it too rather than exempting an arbitrary subtree.
        tasks.push(if Some(index) == domain || index == 0 {
            Task::Visit(child)
        } else {
            Task::Copy(child)
        });
    }
    Ok(())
}

/// Expand grouped binders only where a later domain can change meaning: every
/// multi-name group is emitted as ordered singleton groups. The annotations
/// retain their original source spans, but are pre-resolved independently.
fn split_binders<'a>(binders: &'a [Syntax]) -> Result<Vec<Task<'a>>, EngineExecutionError> {
    let mut result = Vec::new();
    for binder in binders {
        let group = match binder {
            Syntax::Node { kind, args, .. }
                if term_kind(kind, "typeAscription") || term_kind(kind, "paren") =>
            {
                let names = args.get(1).ok_or_else(unsupported_binder)?;
                if let Ok([head, rest]) = term_args(names, "app") {
                    let mut group = vec![head];
                    group.extend(null_args(rest)?);
                    group
                } else {
                    vec![names]
                }
            }
            Syntax::Node { kind, args, .. }
                if ["explicitBinder", "implicitBinder", "strictImplicitBinder"]
                    .iter()
                    .any(|leaf| term_kind(kind, leaf)) =>
            {
                null_args(args.get(1).ok_or_else(unsupported_binder)?)?
                    .iter()
                    .collect()
            }
            _ => vec![],
        };
        if group.len() > 1 {
            result.extend(
                group
                    .into_iter()
                    .map(|name| Task::Binder(binder, Some(name))),
            );
        } else {
            result.push(Task::Binder(binder, None));
        }
    }
    Ok(result)
}

fn shared_binder<'a>(
    name: &'a Syntax,
    colon: &'a Syntax,
    domain: &'a Syntax,
    rule: &NotationRule,
    tasks: &mut Vec<Task<'a>>,
) -> Result<(), EngineExecutionError> {
    let mut names = Vec::new();
    binder_name(name, rule, &mut names)?;
    let null = || Name::from_components(["null"]);
    let atom = |val: &str| {
        Task::Emit(Syntax::Atom {
            info: SourceInfo::None,
            val: val.to_owned(),
        })
    };
    tasks.push(Task::Bind(names));
    tasks.push(Task::BuildNew(
        Name::from_components(["Lean", "Parser", "Term", "explicitBinder"]),
        5,
    ));
    tasks.push(atom(")"));
    tasks.push(Task::Emit(Syntax::node(null(), vec![])));
    tasks.push(Task::BuildNew(null(), 2));
    tasks.push(Task::Visit(domain));
    tasks.push(Task::Copy(colon));
    tasks.push(Task::BuildNew(null(), 1));
    tasks.push(Task::Copy(name));
    tasks.push(atom("("));
    Ok(())
}

pub(super) fn preresolve(
    rule: &NotationRule,
    resolve: &impl Fn(&Name) -> Resolution,
) -> Result<Syntax, EngineExecutionError> {
    let mut tasks = vec![Task::Visit(&rule.rhs)];
    let mut built: Vec<Syntax> = Vec::new();
    let mut locals: Vec<Name> = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            Task::Visit(node @ Syntax::Node { kind, args, .. }) => {
                if term_kind(kind, "fun") {
                    lambda(node, &mut tasks, locals.len())?;
                    continue;
                }
                if term_kind(kind, "forall") {
                    forall(node, &mut tasks, locals.len())?;
                    continue;
                }
                if term_kind(kind, "depArrow") {
                    dependent_arrow(node, &mut tasks, locals.len())?;
                    continue;
                }
                if BINDING.iter().any(|leaf| term_kind(kind, leaf))
                    || TACTIC_BINDING.iter().any(|leaf| {
                        *kind == Name::from_components(["Lean", "Parser", "Tactic", leaf])
                    })
                {
                    return Err(EngineExecutionError::NotImplemented {
                        feature: "a notation whose right-hand side binds names or names a field",
                    });
                }
                tasks.push(build(node)?);
                tasks.extend(args.iter().rev().map(Task::Visit));
            }
            Task::Visit(
                ident @ Syntax::Ident {
                    info, raw_val, val, ..
                },
            ) => {
                if val.is_anonymous()
                    || locals.iter().rev().any(|local| local == val)
                    || rule.variables.iter().any(|(_, variable)| variable == val)
                {
                    built.push(ident.clone());
                    continue;
                }
                match resolve(val) {
                    Resolution::Global(global) => built.push(Syntax::Ident {
                        info: *info,
                        raw_val: *raw_val,
                        val: Name::from_components(["_root_"]).append_core(&global),
                        preresolved: vec![Preresolved::Decl {
                            name: global,
                            fields: Vec::new(),
                        }],
                    }),
                    Resolution::Unchecked => built.push(ident.clone()),
                    Resolution::Nothing if !rule.prechecked => built.push(ident.clone()),
                    Resolution::Nothing => {
                        return Err(EngineExecutionError::ScopeTransition {
                            message: format!("unknown identifier '{}'", val.to_display_string()),
                        });
                    }
                    Resolution::Undetermined => {
                        return Err(EngineExecutionError::NotImplemented {
                            feature: "a notation whose right-hand side names several declarations",
                        });
                    }
                }
            }
            Task::Visit(leaf) | Task::Copy(leaf) => built.push(leaf.clone()),
            Task::Emit(syntax) => built.push(syntax),
            Task::BuildNew(kind, count) => {
                let start = built
                    .len()
                    .checked_sub(count)
                    .ok_or_else(unsupported_binder)?;
                let args = built.split_off(start);
                built.push(Syntax::node(kind, args));
            }
            Task::Build(info, kind, count) => {
                let start = built
                    .len()
                    .checked_sub(count)
                    .ok_or_else(unsupported_binder)?;
                let args = built.split_off(start);
                built.push(Syntax::Node {
                    info,
                    kind: kind.clone(),
                    args,
                });
            }
            Task::Binders(syntax) => {
                let binders = split_binders(null_args(syntax)?)?;
                let Syntax::Node { info, kind, .. } = syntax else {
                    return Err(unsupported_binder());
                };
                tasks.push(Task::Build(*info, kind, binders.len()));
                tasks.extend(binders.into_iter().rev());
            }
            Task::Binder(syntax, selected) => binder(syntax, selected, rule, &mut tasks)?,
            Task::SharedBinders(syntax, colon, domain) => {
                let names = null_args(syntax)?;
                tasks.push(build(syntax)?);
                tasks.extend(
                    names
                        .iter()
                        .rev()
                        .map(|name| Task::SharedBinder(name, colon, domain)),
                );
            }
            Task::SharedBinder(name, colon, domain) => {
                shared_binder(name, colon, domain, rule, &mut tasks)?
            }
            Task::Bind(names) => locals.extend(names),
            Task::Restore(depth) => locals.truncate(depth),
        }
    }
    if built.len() != 1 || !locals.is_empty() {
        return Err(unsupported_binder());
    }
    built.pop().ok_or_else(unsupported_binder)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::source_check::grammar::SourceGrammar;

    fn rule(command: &str) -> NotationRule {
        let mut grammar = SourceGrammar::implicit_init();
        let parsed = grammar
            .enter(|| fln_parse::parse_source_command(command.as_bytes()))
            .expect("notation parses");
        grammar
            .file
            .declare(parsed.syntax())
            .expect("notation declares");
        let rules: Vec<_> = grammar.file.rules().collect();
        assert_eq!(rules.len(), 1, "the fixture declares one notation");
        rules[0].1.clone()
    }

    fn names(syntax: &Syntax) -> Vec<String> {
        let mut result = Vec::new();
        let mut pending = vec![syntax];
        while let Some(node) = pending.pop() {
            match node {
                Syntax::Node { args, .. } => pending.extend(args.iter().rev()),
                Syntax::Ident { val, .. } if !val.is_anonymous() => {
                    result.push(val.to_display_string());
                }
                _ => {}
            }
        }
        result
    }

    fn global(name: &Name) -> Resolution {
        Resolution::Global(Name::from_components(["Declared"]).append_core(name))
    }

    fn unknown(error: EngineExecutionError, expected: &str) {
        assert!(
            matches!(error, EngineExecutionError::ScopeTransition { message }
            if message == format!("unknown identifier '{expected}'"))
        );
    }

    #[test]
    fn literal_lambda_binders_reach_the_production_declaration_door() {
        let mut grammar = SourceGrammar::implicit_init();
        assert!(
            grammar
                .declare(b"notation \"idFn\" => fun x => x", |_| {
                    panic!("a bound identifier must not resolve as a global")
                })
                .expect("scope-aware quotation precheck")
        );
        assert_eq!(grammar.rule_sources.len(), 1);
    }

    #[test]
    fn nested_lambda_shadowing_preserves_the_complete_source_tree() {
        let rule = rule("notation \"idFn\" => fun x => (fun x => x)");
        let checked = preresolve(&rule, &|_| panic!("all identifiers are bound"))
            .expect("bound names need no globals");
        assert_eq!(checked, rule.rhs);
    }

    #[test]
    fn explicit_group_names_are_not_rewritten_but_its_domain_is() {
        let rule = rule("notation \"secondFn\" => fun (x y : Nat) => y");
        let checked = preresolve(&rule, &global).expect("typed lambda");
        assert_eq!(
            names(&checked),
            ["x", "_root_.Declared.Nat", "y", "_root_.Declared.Nat", "y"]
        );
    }

    #[test]
    fn group_domain_does_not_see_its_own_binder() {
        let rule = rule("notation \"idFn\" => fun (x : x) => x");
        let checked = preresolve(&rule, &global).expect("the domain x is global");
        assert_eq!(names(&checked), ["x", "_root_.Declared.x", "x"]);
        unknown(
            preresolve(&rule, &|_| Resolution::Nothing).unwrap_err(),
            "x",
        );
    }

    #[test]
    fn later_group_domains_see_earlier_implicit_binders() {
        for command in [
            "notation \"idFn\" => fun {α : Type} (x : α) => x",
            "notation \"idFn\" => fun ⦃α : Type⦄ (x : α) => x",
        ] {
            let rule = rule(command);
            let checked = preresolve(&rule, &|_| panic!("all names are local"))
                .expect("dependent lambda telescope");
            assert_eq!(checked, rule.rhs);
        }
    }

    #[test]
    fn named_and_anonymous_instance_binders_precheck_their_domains() {
        let named = rule("notation \"instanceFn\" => fun [h : C] => h");
        assert_eq!(
            names(&preresolve(&named, &global).unwrap()),
            ["h", "_root_.Declared.C", "h"]
        );
        let anonymous = rule("notation \"instanceFn\" => fun [C] x => x");
        assert_eq!(
            names(&preresolve(&anonymous, &global).unwrap()),
            ["_root_.Declared.C", "x", "x"]
        );
    }

    #[test]
    fn lambda_shared_annotation_is_a_domain_outside_its_first_binder() {
        let rule = rule("notation \"idFn\" => fun x : x => x");
        assert_eq!(
            names(&preresolve(&rule, &global).unwrap()),
            ["x", "_root_.Declared.x", "x"]
        );
    }

    #[test]
    fn bound_names_cannot_escape_to_a_sibling_expression() {
        let rule = rule("notation \"bad\" => (fun x => x) x");
        unknown(
            preresolve(&rule, &|_| Resolution::Nothing).unwrap_err(),
            "x",
        );
    }

    #[test]
    fn free_names_in_a_lambda_remain_subject_to_precheck() {
        for command in [
            "notation \"bad\" => fun x => missing",
            "notation \"bad\" => fun (x : missing) => x",
        ] {
            unknown(
                preresolve(&rule(command), &|_| Resolution::Nothing).unwrap_err(),
                "missing",
            );
        }
    }

    #[test]
    fn notation_parameters_are_preserved_under_literal_binders() {
        let rule = rule("notation \"constFn\" y => fun x => y");
        assert_eq!(
            preresolve(&rule, &|_| panic!("parameter or local")).unwrap(),
            rule.rhs
        );
    }

    #[test]
    fn antiquoted_binder_names_are_not_guessed() {
        let rule = rule("notation \"bindFn\" x => fun x => x");
        assert!(matches!(
            preresolve(&rule, &global),
            Err(EngineExecutionError::NotImplemented { .. })
        ));
    }

    #[test]
    fn unsupported_binding_constructs_still_fail_closed() {
        let rule = rule("notation \"letFn\" => let x := 1; x");
        assert!(matches!(
            preresolve(&rule, &global),
            Err(EngineExecutionError::NotImplemented { .. })
        ));
    }

    #[test]
    fn macro_unknown_names_keep_the_existing_deferred_resolution_policy() {
        let mut rule = rule("notation \"deferredFn\" => fun x => missing");
        rule.prechecked = false;
        assert_eq!(
            preresolve(&rule, &|_| Resolution::Nothing).unwrap(),
            rule.rhs
        );
    }

    #[test]
    fn ambiguous_free_names_are_not_hidden_by_a_binder() {
        let rule = rule("notation \"ambiguousFn\" => fun x => ambiguous");
        assert!(matches!(
            preresolve(&rule, &|_| Resolution::Undetermined),
            Err(EngineExecutionError::NotImplemented { .. })
        ));
    }

    #[test]
    fn forall_binders_reach_the_production_declaration_door() {
        let mut grammar = SourceGrammar::implicit_init();
        assert!(
            grammar
                .declare(
                    "notation \"allType\" => ∀ (α : Type), α".as_bytes(),
                    |_| { panic!("α is bound in the body") }
                )
                .expect("Pi notation declares")
        );
        assert_eq!(grammar.rule_sources.len(), 1);
    }

    #[test]
    fn bare_forall_shared_domain_resolves_for_each_binder() {
        let rule = rule("notation \"allType\" => ∀ x y : x, y");
        assert_eq!(
            names(&preresolve(&rule, &global).unwrap()),
            ["x", "_root_.Declared.x", "y", "x", "y"]
        );
        unknown(
            preresolve(&rule, &|_| Resolution::Nothing).unwrap_err(),
            "x",
        );
    }

    #[test]
    fn bracketed_forall_telescopes_resolve_domains_left_to_right() {
        for source in [
            "notation \"allType\" => ∀ (α : Type) (x : α), α",
            "notation \"allType\" => ∀ {α : Type} (x : α), α",
            "notation \"allType\" => forall ⦃α : Type⦄ (x : α), α",
        ] {
            let rule = rule(source);
            assert_eq!(
                preresolve(&rule, &|_| panic!("all identifiers are bound")).unwrap(),
                rule.rhs
            );
        }
    }

    #[test]
    fn grouped_forall_domains_see_preceding_names_in_the_same_group() {
        let rule = rule("notation \"allType\" => ∀ (x y : x), y");
        assert_eq!(
            names(&preresolve(&rule, &global).unwrap()),
            ["x", "_root_.Declared.x", "y", "x", "y"]
        );
    }

    #[test]
    fn dependent_arrows_scope_their_body_but_not_their_domain() {
        for source in [
            "notation \"arrowType\" => (x : x) → x",
            "notation \"arrowType\" => {x : x} -> x",
            "notation \"arrowType\" => ⦃x : x⦄ → x",
            "notation \"arrowType\" => [x : x] → x",
        ] {
            assert_eq!(
                names(&preresolve(&rule(source), &global).unwrap()),
                ["x", "_root_.Declared.x", "x"]
            );
        }
    }

    #[test]
    fn dependent_arrows_can_use_an_outer_lambda_local() {
        let rule = rule("notation \"arrowFn\" => fun α => ((x : α) → α)");
        assert_eq!(
            preresolve(&rule, &|_| panic!("all identifiers are bound")).unwrap(),
            rule.rhs
        );
    }

    #[test]
    fn nested_shadowing_restores_the_outer_binding_not_just_an_empty_scope() {
        let rule = rule("notation \"shadowFn\" => fun x => (fun x => x) x");
        assert_eq!(
            preresolve(&rule, &|_| panic!(
                "the final x belongs to the outer lambda"
            ))
            .unwrap(),
            rule.rhs
        );
    }

    #[test]
    fn forall_locals_do_not_escape_to_a_sibling() {
        let rule = rule("notation \"bad\" => (∀ x, x) x");
        unknown(
            preresolve(&rule, &|_| Resolution::Nothing).unwrap_err(),
            "x",
        );
    }

    #[test]
    fn mixed_forall_shared_types_and_defaults_remain_typed_refusals() {
        for source in [
            "notation \"mixedType\" => ∀ (α : Type) x : α, α",
            "notation \"defaultType\" => ∀ (x : Nat := 0), Nat",
        ] {
            assert!(matches!(
                preresolve(&rule(source), &global),
                Err(EngineExecutionError::NotImplemented { .. })
            ));
        }
    }

    #[test]
    fn malformed_binder_nodes_return_an_error_without_indexing_past_their_args() {
        let mut rule = rule("notation \"idFn\" => fun x => x");
        rule.rhs = Syntax::node(
            Name::from_components(["Lean", "Parser", "Term", "fun"]),
            Vec::new(),
        );
        assert!(matches!(
            preresolve(&rule, &global),
            Err(EngineExecutionError::NotImplemented { .. })
        ));
    }
}
