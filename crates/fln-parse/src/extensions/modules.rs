//! Native source-to-source grammar replay. This is a checked source pipeline's
//! data product, not the pin's `.olean` parser or macro-function encoding.
use super::*;

/// A source module's own exported syntax and quoted expansions. Imported entries
/// are not repeated, and `local` declarations never enter this product.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct NativeSyntaxModule {
    pub declarations: Vec<Arc<SyntaxDecl>>,
    pub categories: BTreeMap<Name, IdentBehavior>,
    pub rules: BTreeMap<Name, Arc<NotationRule>>,
    /// Optional namespace for each clause. Missing metadata means global.
    pub rule_scopes: BTreeMap<Name, Vec<Option<Name>>>,
}

impl NativeSyntaxModule {
    pub fn is_empty(&self) -> bool {
        self.declarations.is_empty()
            && self.categories.is_empty()
            && self.rules.is_empty()
            && self.rule_scopes.is_empty()
    }
}

impl FileGrammar {
    /// Capture only this file's global/scoped additions. Scope activation is
    /// lexical state and is deliberately not an exported registration.
    pub fn export_native(&self) -> Result<NativeSyntaxModule, &'static str> {
        if let Some(reason) = self.native_export_refusal {
            return Err(reason);
        }
        let declarations: Vec<_> = self
            .declared
            .iter()
            .filter(|decl| !self.local_declared.contains(&decl.decl))
            .cloned()
            .collect();
        let exported_names: BTreeSet<_> = declarations.iter().map(|decl| &decl.decl).collect();
        let mut rules = BTreeMap::new();
        let mut rule_scopes = BTreeMap::new();
        for (kind, rule) in self.rules.iter() {
            let inherited = self.native_rule_counts.get(kind).copied();
            if !exported_names.contains(kind) && inherited.is_none() {
                continue;
            }
            let Some(rule) = self.exportable_rule(kind, rule)? else {
                continue;
            };
            let count = rule
                .cases()
                .count()
                .checked_sub(inherited.unwrap_or(0))
                .ok_or("native macro rule inheritance exceeds its chain")?;
            if count != 0 {
                if let Some(scopes) = self.exported_rule_scopes(kind, count)? {
                    rule_scopes.insert(kind.clone(), scopes);
                }
                rules.insert(kind.clone(), Arc::new(rule_prefix(&rule, count)));
            }
        }
        Ok(NativeSyntaxModule {
            declarations,
            categories: self.declared_categories.clone(),
            rules,
            rule_scopes,
        })
    }

    /// Replay an exact predecessor's grammar product, in the import graph's
    /// dependency order. A collision is refused before changing this grammar.
    /// No scoped namespace is activated merely by importing its declarations.
    pub fn import_native(&mut self, module: &NativeSyntaxModule) -> Result<(), &'static str> {
        let mut names = BTreeSet::new();
        for name in module.categories.keys() {
            if self.categories.contains_key(name) {
                return Err("an imported syntax category is already declared");
            }
            if !matches!(name.leaf_view(), LeafView::Str(_)) {
                return Err("an imported syntax category has no string name");
            }
        }
        for decl in &module.declarations {
            if self.constants.contains(&decl.decl) || !names.insert(decl.decl.clone()) {
                return Err("an imported syntax declaration is already declared");
            }
            if decl.category.as_ref().is_some_and(|category| {
                !self.categories.contains_key(category) && !module.categories.contains_key(category)
            }) {
                return Err("an imported syntax declaration names an unavailable category");
            }
        }
        if module
            .rules
            .keys()
            .any(|kind| !names.contains(kind) && !self.native_rule_counts.contains_key(kind))
        {
            return Err("an imported macro rule has no native syntax declaration");
        }
        for (kind, scopes) in &module.rule_scopes {
            let rule = module
                .rules
                .get(kind)
                .ok_or("scoped macro metadata without a rule")?;
            if scopes.len() != rule.cases().count()
                || scopes.iter().flatten().any(Name::is_anonymous)
            {
                return Err("invalid imported scoped macro metadata");
            }
        }
        for (kind, rule) in &module.rules {
            if rule.fallbacks.len() >= MAX_TEMPLATE_NODES
                || rule.fallbacks.iter().any(|rule| !rule.fallbacks.is_empty())
            {
                return Err("an imported macro has a nested or oversized fallback chain");
            }
            for rule in rule.cases() {
                if let Some(pattern) = &rule.pattern {
                    let Syntax::Node {
                        kind: pattern_kind,
                        args,
                        ..
                    } = pattern
                    else {
                        return Err("an imported macro pattern is not a syntax node");
                    };
                    if pattern_kind != kind || quotation::variables(args)? != rule.variables {
                        return Err("an imported macro pattern has inconsistent captures");
                    }
                }
            }
        }
        // Prepare all chains before mutation. Imports arrive in dependency
        // order, so later imports precede earlier ones, but never a declaration
        // the caller has already made in this source file.
        let mut merged_rules = Vec::new();
        for (kind, incoming) in &module.rules {
            let previous = self.rules.get(kind);
            let inherited = self.native_rule_counts.get(kind).copied().unwrap_or(0);
            let previous_count = previous.map_or(0, |rule| rule.cases().count());
            let own = previous_count
                .checked_sub(inherited)
                .ok_or("native macro rule inheritance exceeds its chain")?;
            let total = previous_count
                .checked_add(incoming.cases().count())
                .filter(|count| *count <= MAX_TEMPLATE_NODES)
                .ok_or("native macro rule alternatives past the budget")?;
            let mut cases = Vec::with_capacity(total);
            if let Some(previous) = previous {
                cases.extend(previous.cases().take(own).map(flat_case));
            }
            cases.extend(incoming.cases().map(flat_case));
            if let Some(previous) = previous {
                cases.extend(previous.cases().skip(own).map(flat_case));
            }
            let mut head = cases.remove(0);
            head.fallbacks = cases;
            let depths =
                self.imported_rule_depths(kind, previous_count, own, total - previous_count)?;
            let scopes = self.imported_rule_scopes(
                kind,
                previous_count,
                own,
                total - previous_count,
                module.rule_scopes.get(kind),
            )?;
            merged_rules.push((kind.clone(), Arc::new(head), total - own, depths, scopes));
        }
        for (name, behavior) in &module.categories {
            self.categories.insert(name.clone(), *behavior);
            self.native_categories.insert(name.clone());
            let LeafView::Str(suffix) = name.leaf_view() else {
                unreachable!("validated above")
            };
            self.base_tokens.insert(format!("`({suffix}|"));
        }
        for decl in &module.declarations {
            if decl.category.is_some() {
                self.native_rule_counts
                    .entry(decl.decl.clone())
                    .or_insert(0);
            }
            self.constants.insert(decl.decl.clone());
            if decl.category.is_none() {
                self.native_abbreviations.insert(decl.decl.clone());
                self.abbreviations
                    .insert(decl.decl.clone(), decl.descr.clone());
            } else if let Some(namespace) = &decl.scope {
                self.native_scoped
                    .entry(namespace.clone())
                    .or_default()
                    .push(Arc::clone(decl));
            } else {
                decl.descr.collect_tokens(&mut self.base_tokens);
                self.native_imported.push(Arc::clone(decl));
            }
        }
        for (kind, rule, inherited, depths, scopes) in merged_rules {
            self.native_rule_counts.insert(kind.clone(), inherited);
            if let Some(depths) = depths {
                self.local_rule_depths.insert(kind.clone(), depths);
            }
            if let Some(scopes) = scopes {
                self.rule_scopes.insert(kind.clone(), scopes);
            }
            Arc::make_mut(&mut self.rules).insert(kind, rule);
        }
        self.generation += 1;
        self.cache.borrow_mut().clear();
        Ok(())
    }

    /// Namespace anchors supplied by real parser declarations, including a
    /// scoped-only module with no ordinary constant in that namespace.
    pub fn native_namespace_anchors(&self) -> Vec<Name> {
        self.native_imported
            .iter()
            .chain(self.native_scoped.values().flatten())
            .chain(self.declared.iter())
            .map(|decl| decl.decl.clone())
            .chain(self.native_abbreviations.iter().cloned())
            // Scoped rule-only modules have no syntax declaration under their
            // activation namespace. This anchor is for namespace lookup only.
            .chain(
                self.rule_scopes
                    .values()
                    .flatten()
                    .filter_map(|scope| scope.namespace.as_ref())
                    .map(|namespace| Name::str(namespace.clone(), "_native_scoped_macro")),
            )
            .collect()
    }
}

/// Clone only a clause, never its already-flat sibling list.
pub(super) fn flat_case(rule: &NotationRule) -> NotationRule {
    NotationRule {
        variables: rule.variables.clone(),
        rhs: rule.rhs.clone(),
        prechecked: rule.prechecked,
        pattern: rule.pattern.clone(),
        source: rule.source.clone(),
        fallbacks: Vec::new(),
    }
}

fn rule_prefix(rule: &NotationRule, count: usize) -> NotationRule {
    debug_assert!(count > 0);
    let mut head = flat_case(rule);
    head.fallbacks = rule
        .fallbacks
        .iter()
        .take(count - 1)
        .map(flat_case)
        .collect();
    head
}

#[cfg(test)]
mod imported_rules_tests;

#[cfg(test)]
mod tests {
    use super::*;

    pub(super) fn grammar(module: &str) -> FileGrammar {
        FileGrammar::new(false, &[], Some(Name::from_components([module])))
            .unwrap()
            .own_syntax_only()
    }

    pub(super) fn declare(grammar: &mut FileGrammar, source: &str) {
        let control = with_grammar(&grammar.grammar(), || {
            crate::command_scope::parse(source.as_bytes())
        })
        .unwrap();
        if let Some(control) = control {
            grammar.apply(&control);
        } else {
            let parsed = with_grammar(&grammar.grammar(), || {
                crate::parse_source_command(source.as_bytes())
            })
            .unwrap();
            grammar.declare(parsed.syntax()).unwrap();
        }
    }

    pub(super) fn parses(grammar: &FileGrammar, source: &str) -> bool {
        with_grammar(&grammar.grammar(), || {
            crate::parse_source_command(source.as_bytes())
        })
        .is_ok()
    }

    #[test]
    fn native_imports_activate_scoped_parsers_lexically_and_export_only_own_entries() {
        let mut library = grammar("Lib");
        for source in [
            "notation \"⟪\" x \"⟫\" => x",
            "namespace Ops",
            "scoped infixl:65 \" +++ \" => Nat.add",
            "end Ops",
        ] {
            declare(&mut library, source);
        }
        let exported = library.export_native().unwrap();
        assert_eq!(exported.declarations.len(), 2);
        let mut consumer = grammar("Main");
        consumer.import_native(&exported).unwrap();
        assert!(consumer.export_native().unwrap().is_empty());
        assert!(parses(&consumer, "def x := ⟪1⟫"));
        assert!(!parses(&consumer, "def x := 1 +++ 2"));
        declare(&mut consumer, "section");
        declare(&mut consumer, "open scoped Ops");
        assert!(parses(&consumer, "def x := 1 +++ 2"));
        declare(&mut consumer, "end");
        assert!(!parses(&consumer, "def x := 1 +++ 2"));
        assert!(
            consumer
                .native_namespace_anchors()
                .iter()
                .any(|name| name.parent() == Name::from_components(["Ops"]))
        );
    }

    #[test]
    fn native_exports_exclude_local_syntax_and_private_abbreviations() {
        let mut library = grammar("Lib");
        declare(&mut library, "section");
        declare(&mut library, "local notation \"⟪\" x \"⟫\" => x");
        assert!(parses(&library, "def x := ⟪1⟫"));
        declare(&mut library, "end");
        declare(&mut library, "private syntax hidden := \"hidden\"");
        assert!(library.export_native().unwrap().is_empty());
        let mut consumer = grammar("Main");
        consumer
            .import_native(&library.export_native().unwrap())
            .unwrap();
        assert!(!parses(&consumer, "def x := ⟪1⟫"));
    }

    #[test]
    fn malformed_native_import_is_atomic_even_after_a_valid_category() {
        let mut consumer = grammar("Main");
        let mut invalid = NativeSyntaxModule::default();
        invalid
            .categories
            .insert(Name::from_components(["fresh"]), IdentBehavior::Default);
        invalid.categories.insert(
            Name::num(Name::from_components(["z"]), 0),
            IdentBehavior::Default,
        );
        assert!(consumer.import_native(&invalid).is_err());
        invalid
            .categories
            .remove(&Name::num(Name::from_components(["z"]), 0));
        consumer
            .import_native(&invalid)
            .expect("first category did not leak from failed replay");
        assert!(
            consumer.import_native(&invalid).is_err(),
            "real duplicate stays a refusal"
        );
    }

    #[test]
    fn imported_syntax_abbreviations_supply_their_namespace_and_open_lookup() {
        let mut library = grammar("Lib");
        declare(&mut library, "namespace N");
        declare(&mut library, "syntax piece := \"piece\"");
        declare(&mut library, "end N");
        let mut consumer = grammar("Main");
        consumer
            .import_native(&library.export_native().unwrap())
            .unwrap();
        assert_eq!(
            consumer.native_namespace_anchors(),
            [Name::from_components(["N", "piece"])]
        );
        declare(&mut consumer, "open N");
        declare(&mut consumer, "syntax \"wrapped \" piece : term");
        assert!(parses(&consumer, "def x := wrapped piece"));
        assert!(parses(&consumer, "def x := f (wrapped piece)"));
        assert!(!parses(&consumer, "def x := f wrapped piece"));
        assert!(!parses(&consumer, "def x := wrapped piece arg"));
        assert_eq!(consumer.export_native().unwrap().declarations.len(), 1);

        // Resolving an atom-ending abbreviation does not promote its declared precedence.
        // The same leading-parser gate must respect an enclosing `term:max` category.
        declare(&mut consumer, "syntax:lead \"low\" : term");
        declare(&mut consumer, "syntax:max \"take \" term:max : term");
        assert!(parses(&consumer, "def x := low"));
        assert!(!parses(&consumer, "def x := take low"));
        assert!(parses(&consumer, "def x := take (low)"));
    }

    #[test]
    fn imported_rule_extensions_export_without_local_clauses() {
        let mut library = grammar("Lib");
        declare(&mut library, "syntax \"wrap \" term:max : term");
        let mut consumer = grammar("Main");
        consumer
            .import_native(&library.export_native().unwrap())
            .unwrap();
        declare(&mut consumer, "macro_rules | `(wrap $x) => `($x)");
        let exported = consumer.export_native().unwrap();
        assert!(exported.declarations.is_empty());
        assert_eq!(exported.rules.len(), 1);
        assert!(!exported.is_empty());
        declare(&mut library, "local macro_rules | `(wrap $x) => `($x)");
        let local_export = library.export_native().unwrap();
        assert_eq!(local_export.declarations.len(), 1);
        assert!(
            local_export.rules.is_empty(),
            "a file-local rule cannot be replayed"
        );
        assert_eq!(
            library.rules.len(),
            1,
            "the defining file keeps its local rule"
        );
        let mut fresh = grammar("Fresh");
        fresh.import_native(&local_export).unwrap();
        assert!(
            fresh.rules.is_empty(),
            "consumers do not inherit the local expansion"
        );
        assert!(
            parses(&fresh, "def x := wrap 42"),
            "only the syntax was exported"
        );
    }
}
