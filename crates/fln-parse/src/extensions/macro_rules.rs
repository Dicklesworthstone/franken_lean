//! Quoted `macro_rules`: clauses run top-to-bottom, registrations newest-first.
//! Unsupported registrations are barriers, never permission to use an older rule.
use super::*;

pub(super) fn declare(file: &mut FileGrammar, args: &[Syntax]) -> Result<(), &'static str> {
    let [_, _, attr_kind, _, opt_kind, alternatives] = args else {
        return Ok(());
    };
    let active = file.expander();
    if ["ident", "str"].iter().any(|kind| {
        active
            .rules
            .get(&Name::from_components([*kind]))
            .is_some_and(|rule| rule.cases().any(atoms::captures_whole_kind))
    }) {
        return Err(
            "macro declarations under atomic rules that rewrite generated references or strings",
        );
    }
    let explicit_requested = null_args(opt_kind).is_some_and(|args| !args.is_empty());
    let explicit = null_args(opt_kind).and_then(|args| match args {
        [_, _, _, kind, _] => ident_name(kind),
        _ => None,
    });
    let explicit =
        explicit.and_then(|name| {
            let mut namespace = file.top().namespace.clone();
            loop {
                let candidate = namespace.append_core(&name);
                let registered = atoms::is_kind(&candidate) || file.imported.iter().chain(&file.native_imported)
                .chain(&file.declared).chain(file.scoped.values().flatten())
                .chain(file.native_scoped.values().flatten())
                .any(|decl| matches!(&decl.descr, Descr::Node { kind, .. } if *kind == candidate));
                if registered {
                    return Some(candidate);
                }
                if namespace.is_anonymous() {
                    return None;
                }
                namespace = namespace.parent();
            }
        });
    let alternatives = node_args(alternatives)
        .and_then(<[Syntax]>::first)
        .and_then(null_args);
    let mut affected = BTreeSet::new();
    affected.extend(explicit.iter().cloned());
    let mut groups: BTreeMap<Name, Vec<NotationRule>> = BTreeMap::new();
    let mut refused = BTreeSet::new();
    let mut malformed = explicit_requested && explicit.is_none();
    for alternative in alternatives.unwrap_or(&[]) {
        let Some([_, patterns, _, rhs]) = node_args(alternative) else {
            malformed = true;
            continue;
        };
        // Record every identifiable kind, even in a clause we cannot translate.
        // This is essential when an unsupported later registration shadows one
        // of our quoted templates or the native interpolation implementation.
        for group in null_args(patterns).unwrap_or(&[]) {
            for pattern in null_args(group).unwrap_or(&[]) {
                if let Ok((kind, _)) = pattern_root(pattern, explicit.as_ref()) {
                    affected.insert(kind);
                }
            }
        }
        let target = null_args(patterns)
            .and_then(|groups| match groups {
                [group] => null_args(group).and_then(|patterns| match patterns {
                    [pattern] => Some(pattern),
                    _ => None,
                }),
                _ => None,
            })
            .and_then(|pattern| pattern_root(pattern, explicit.as_ref()).ok());
        let Some((kind, children)) = target else {
            malformed = true;
            continue;
        };
        if explicit.as_ref().is_some_and(|expected| *expected != kind) {
            malformed = true;
            refused.insert(kind);
            continue;
        }
        let translated = quotation::variables(&children).and_then(|variables| {
            macro_rule_template(rhs, &variables).map(|rhs| NotationRule {
                variables,
                rhs,
                prechecked: false,
                pattern: Some(Syntax::node(kind.clone(), children)),
                source: None,
                fallbacks: Vec::new(),
            })
        });
        match translated {
            Ok(rule) => groups.entry(kind).or_default().push(rule),
            Err(_) => {
                refused.insert(kind);
            }
        }
    }
    // A registration over a kind this door cannot host, or one that names no kind, can be no
    // barrier: dropping it would leave the older meaning in force where the pin runs the new
    // rule, as for `macro_rules (kind := num)` or `$n:num` over numeral literals (upstream
    // tests/elab/414).
    if affected.is_empty() && (malformed || alternatives.is_none()) {
        return Err("a macro_rules registration whose target syntax kind is not read");
    }
    if affected.iter().any(|kind| !atoms::is_kind(kind))
        && active
            .rules
            .get(&Name::from_components(["num"]))
            .is_some_and(|rule| rule.cases().any(atoms::captures_whole_kind))
    {
        return Err(
            "node macro declarations under atomic rules that rewrite generated argument indices",
        );
    }
    let locality = attr_kind_of(attr_kind)?;
    let local = locality == AttrKind::Local;
    let scoped = locality == AttrKind::Scoped;
    let namespace = scoped.then(|| file.top().namespace.clone());
    if namespace.as_ref().is_some_and(Name::is_anonymous) {
        return Err("scoped macro_rules requires a named namespace");
    }
    if alternatives.is_none() || malformed {
        refused.extend(affected.iter().cloned());
    }
    if affected.iter().any(atoms::is_kind)
        && (alternatives.is_none() || malformed || !refused.is_empty())
    {
        // There is a builtin elaborator behind these kinds. Removing a rule
        // would silently reinstate that meaning rather than install a barrier.
        return Err("an unsupported macro_rules registration for atomic syntax");
    }
    // Unknown local code must not leak an erasure outside its lexical boundary;
    // atomic code must not restore a builtin meaning by dropping its chain.
    // Validate all affected kinds before mutating any of them.
    if local || scoped || affected.iter().any(atoms::is_kind) {
        if alternatives.is_none() || malformed || !refused.is_empty() {
            return Err("an unsupported local macro_rules registration");
        }
        // One command can register several kinds. Validate every target and
        // complete chain before changing ANY of them, including interpolation
        // barriers. Otherwise a later refusal could leave an earlier override
        // installed or erase the global rule a local command meant to extend.
        for kind in &affected {
            let owned = atoms::is_kind(kind) || file.declared.iter().any(|decl| decl.decl == *kind);
            let native = file.native_rule_counts.contains_key(kind);
            if (!owned && !native) || file.interpolation_kinds.contains(kind) {
                return Err("local macro_rules requires native source syntax");
            }
            let added = groups.get(kind).map_or(0, Vec::len);
            let previous = file.rules.get(kind).map_or(0, |rule| rule.cases().count());
            if added == 0
                || previous
                    .checked_add(added)
                    .is_none_or(|total| total > MAX_TEMPLATE_NODES)
            {
                return Err("local macro rule alternatives past the budget");
            }
            if file
                .local_rule_depths
                .get(kind)
                .is_some_and(|depths| depths.len() != previous)
            {
                return Err("native macro locality does not match its clause chain");
            }
            file.prepended_rule_scopes(kind, previous, added, namespace.clone())?;
        }
    }
    for kind in affected {
        let interpolation = Arc::make_mut(&mut file.interpolation_kinds).remove(&kind);
        let owned = atoms::is_kind(&kind) || file.declared.iter().any(|decl| decl.decl == kind);
        let native = file.native_rule_counts.contains_key(&kind);
        if interpolation || (!owned && !native && file.constants.contains(&kind)) {
            file.native_export_refusal =
                Some("source module export of macro_rules for imported syntax");
        }
        // A registration we cannot execute is not permission to fall back to
        // an older rule. Native source registrations keep their existing door.
        if (!owned && !native) || refused.contains(&kind) {
            if native {
                file.native_export_refusal =
                    Some("source module export of unsupported imported macro_rules");
            }
            Arc::make_mut(&mut file.rules).remove(&kind);
            file.local_rule_depths.remove(&kind);
            file.rule_scopes.remove(&kind);
            file.generation += 1;
            continue;
        }
        let Some(mut cases) = groups.remove(&kind) else {
            continue;
        };
        if cases.is_empty() {
            continue;
        }
        let added = cases.len();
        let previous_count = file.rules.get(&kind).map_or(0, |rule| rule.cases().count());
        if let Some(previous) = file.rules.get(&kind) {
            let mut previous = previous.as_ref().clone();
            let older = std::mem::take(&mut previous.fallbacks);
            cases.push(previous);
            cases.extend(older);
        }
        if cases.len() > MAX_TEMPLATE_NODES {
            Arc::make_mut(&mut file.rules).remove(&kind);
            file.local_rule_depths.remove(&kind);
            file.rule_scopes.remove(&kind);
            file.native_export_refusal = Some("native macro rule alternatives past the budget");
            file.generation += 1;
            continue;
        }
        let depths = file.prepended_rule_depths(&kind, previous_count, added, local)?;
        let scopes = file.prepended_rule_scopes(&kind, previous_count, added, namespace.clone())?;
        let mut head = cases.remove(0);
        head.fallbacks = cases;
        Arc::make_mut(&mut file.rules).insert(kind.clone(), Arc::new(head));
        if let Some(depths) = depths {
            file.local_rule_depths.insert(kind.clone(), depths);
        }
        if let Some(scopes) = scopes {
            file.rule_scopes.insert(kind, scopes);
        }
        file.generation += 1;
    }
    Ok(())
}

/// Atomic syntax is one operand, including its literal node or identifier.
/// Keeping that operand under the target kind gives it the same nonempty
/// capture paths and lossless journal representation as ordinary node rules.
/// A category antiquotation has a pseudo kind; the pin refuses registering it
/// (`invalid syntax node kind term.pseudo`), so it is not a wildcard dispatch.
fn pattern_root(
    pattern: &Syntax,
    explicit: Option<&Name>,
) -> Result<(Name, Vec<Syntax>), &'static str> {
    if let Some((_, contents)) = quotation_contents(pattern) {
        let kind = match contents {
            Syntax::Node { kind, .. } if antiquotation_name(contents).is_some() => kind.parent(),
            Syntax::Node { kind, .. } => kind.clone(),
            Syntax::Ident { .. } => Name::from_components(["ident"]),
            _ => return Err("a macro pattern without a dispatch kind"),
        };
        if atoms::is_kind(&kind) {
            return Ok((kind, vec![contents.clone()]));
        }
        if antiquotation_name(contents).is_some() {
            return Err("a macro_rules registration whose target syntax kind is not read");
        }
        let Syntax::Node { args, .. } = contents else {
            return Err("a macro pattern without syntax children");
        };
        return Ok((kind, args.clone()));
    }
    let kind = explicit
        .filter(|kind| atoms::is_kind(kind))
        .ok_or("an unquoted macro pattern without an atomic target")?;
    let variable = match pattern {
        Syntax::Ident { .. } => pattern.clone(),
        Syntax::Node { kind, args, .. }
            if *kind == crate::parser_kind(&["Term", "hole"]) && args.len() == 1 =>
        {
            args[0].clone()
        }
        _ => return Err("an unquoted macro pattern that is not a binding"),
    };
    Ok((
        kind.clone(),
        vec![Syntax::node(
            Name::str(kind.clone(), "antiquot"),
            vec![
                Syntax::atom(SourceInfo::None, "$"),
                null_node(Vec::new()),
                variable,
                null_node(Vec::new()),
            ],
        )],
    ))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn file() -> FileGrammar {
        FileGrammar::new(false, &[], Some(Name::from_components(["Atomic"])))
            .unwrap()
            .own_syntax_only()
    }

    fn register(file: &mut FileGrammar, source: &str) -> Result<(), &'static str> {
        let parsed = with_grammar(&file.grammar(), || {
            crate::parse_source_command(source.as_bytes())
        })
        .unwrap();
        file.declare(parsed.syntax()).map(|_| ())
    }

    #[test]
    fn malformed_atomic_registrations_leave_every_previous_rule_intact() {
        let mut file = file();
        register(&mut file, "macro_rules | `(num| 2) => `(\"old\")").unwrap();
        let before = Arc::clone(&file.rules);
        let generation = file.generation;
        for source in [
            "macro_rules | `(num| 2) => do pure `(\"new\")",
            "macro_rules (kind := ident) | `(num| 2) => `(\"new\")",
            "macro_rules | `(num| 2) => `(\"new\") | `($x) => `(\"category\")",
        ] {
            assert!(register(&mut file, source).is_err(), "{source}");
            assert_eq!(file.rules, before);
            assert_eq!(file.generation, generation);
        }
    }

    #[test]
    fn an_atomic_chain_limit_refuses_without_restoring_builtin_meaning() {
        let mut file = file();
        register(&mut file, "macro_rules | `(num| 2) => `(\"old\")").unwrap();
        let key = Name::from_components(["num"]);
        let mut head = file.rules[&key].as_ref().clone();
        head.fallbacks = vec![head.clone(); MAX_TEMPLATE_NODES - 1];
        Arc::make_mut(&mut file.rules).insert(key, Arc::new(head));
        let before = Arc::clone(&file.rules);
        assert!(register(&mut file, "macro_rules | `(num| 2) => `(\"new\")").is_err());
        assert_eq!(file.rules, before);
    }

    #[test]
    fn atomic_imports_require_the_lossless_whole_operand_pattern() {
        let mut producer = file();
        register(&mut producer, "macro_rules | `($n:num) => `(\"number\")").unwrap();
        let module = producer.export_native().unwrap();
        assert!(module.declarations.is_empty());
        let key = Name::from_components(["num"]);
        for pattern in [None, Some(Syntax::node(key.clone(), Vec::new()))] {
            let mut invalid = module.clone();
            let rule = Arc::make_mut(invalid.rules.get_mut(&key).unwrap());
            rule.pattern = pattern;
            rule.variables.clear();
            let mut consumer = file();
            assert!(consumer.import_native(&invalid).is_err());
            assert!(consumer.rules.is_empty());
            assert!(consumer.native_rule_counts.is_empty());
            consumer.import_native(&module).unwrap();
            assert!(consumer.export_native().unwrap().is_empty());
        }
    }
}
