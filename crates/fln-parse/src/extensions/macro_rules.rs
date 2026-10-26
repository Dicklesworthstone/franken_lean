//! Quoted `macro_rules`: clauses run top-to-bottom, registrations newest-first.
//! Unsupported registrations are barriers, never permission to use an older rule.
use super::*;

pub(super) fn declare(file: &mut FileGrammar, args: &[Syntax]) -> Result<(), &'static str> {
    let [_, _, attr_kind, _, opt_kind, alternatives] = args else {
        return Ok(());
    };
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
                let registered = file.imported.iter().chain(&file.native_imported)
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
    let mut antiquoted = false;
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
                if let Some((kind, ..)) = quotation_root(pattern) {
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
            .and_then(quotation_root);
        let Some((kind, _category, children)) = target else {
            malformed = true;
            continue;
        };
        // A pattern that is one antiquotation (`$n:num`, `$x`) targets that antiquotation's
        // own kind, an atom kind or a whole category, not the antiquotation node's kind.
        if matches!(kind.leaf_view(), LeafView::Str("antiquot")) {
            antiquoted = true;
            continue;
        }
        if explicit.as_ref().is_some_and(|expected| *expected != kind) {
            malformed = true;
            refused.insert(kind);
            continue;
        }
        let translated = quotation::variables(children).and_then(|variables| {
            macro_rule_template(rhs, &variables).map(|rhs| NotationRule {
                variables,
                rhs,
                prechecked: false,
                pattern: Some(Syntax::node(kind.clone(), children.to_vec())),
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
    if antiquoted || (affected.is_empty() && (malformed || alternatives.is_none())) {
        return Err("a macro_rules registration whose target syntax kind is not read");
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
    // Unknown local code must not erase an earlier meaning and then leak that
    // erasure outside its lexical boundary. Refuse before mutating any kind.
    if local || scoped {
        if alternatives.is_none() || malformed || !refused.is_empty() {
            return Err("an unsupported local macro_rules registration");
        }
        // One command can register several kinds. Validate every target and
        // complete chain before changing ANY of them, including interpolation
        // barriers. Otherwise a later refusal could leave an earlier override
        // installed or erase the global rule a local command meant to extend.
        for kind in &affected {
            let owned = file.declared.iter().any(|decl| decl.decl == *kind);
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
        let owned = file.declared.iter().any(|decl| decl.decl == kind);
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
