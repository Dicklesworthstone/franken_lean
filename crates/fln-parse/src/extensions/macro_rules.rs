//! Quoted `macro_rules`: clauses run top-to-bottom, registrations newest-first.
//! Unsupported registrations are barriers, never permission to use an older rule.
use super::*;

pub(super) fn declare(file: &mut FileGrammar, args: &[Syntax]) {
    let [_, _, attr_kind, _, opt_kind, alternatives] = args else {
        return;
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
        let Some((kind, category, children)) = target else {
            malformed = true;
            continue;
        };
        if explicit.as_ref().is_some_and(|expected| *expected != kind) {
            malformed = true;
            refused.insert(kind);
            continue;
        }
        let translated = quotation::variables(children).and_then(|variables| {
            macro_template(rhs, &category, &variables).map(|rhs| NotationRule {
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
    let scoped = attr_kind_of(attr_kind) != Ok(AttrKind::Global);
    if scoped {
        file.native_export_refusal = Some("source module export of scoped or local macro_rules");
    }
    if alternatives.is_none() || malformed {
        refused.extend(affected.iter().cloned());
    }
    for kind in affected {
        let interpolation = Arc::make_mut(&mut file.interpolation_kinds).remove(&kind);
        let owned = file.declared.iter().any(|decl| decl.decl == kind);
        let native = file.native_rule_counts.contains_key(&kind);
        if interpolation || (!owned && !native && file.constants.contains(&kind)) {
            file.native_export_refusal =
                Some("source module export of macro_rules for imported syntax");
        }
        let rules = Arc::make_mut(&mut file.rules);
        // Without an executable translation for a registration, a previous rule
        // is not a sound fallback: that registration may match and do anything.
        if (!owned && !native) || scoped || refused.contains(&kind) {
            if native {
                // Removing an inherited rule cannot be represented as an empty
                // export: that would resurrect it in the next module. Unknown
                // registrations remain fail-closed until MacroM is supported.
                file.native_export_refusal =
                    Some("source module export of unsupported imported macro_rules");
            }
            rules.remove(&kind);
            file.generation += 1;
            continue;
        }
        let Some(mut cases) = groups.remove(&kind) else {
            continue;
        };
        if cases.is_empty() {
            continue;
        }
        if let Some(previous) = rules.get(&kind) {
            let mut previous = previous.as_ref().clone();
            let older = std::mem::take(&mut previous.fallbacks);
            cases.push(previous);
            cases.extend(older);
        }
        if cases.len() > MAX_TEMPLATE_NODES {
            rules.remove(&kind);
            file.native_export_refusal = Some("native macro rule alternatives past the budget");
            file.generation += 1;
            continue;
        }
        let mut head = cases.remove(0);
        head.fallbacks = cases;
        rules.insert(kind, Arc::new(head));
        file.generation += 1;
    }
}
