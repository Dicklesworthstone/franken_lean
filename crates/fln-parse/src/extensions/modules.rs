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
}

impl NativeSyntaxModule {
    pub fn is_empty(&self) -> bool {
        self.declarations.is_empty() && self.categories.is_empty()
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
        let rules = declarations
            .iter()
            .filter_map(|decl| {
                self.rules
                    .get(&decl.decl)
                    .map(|rule| (decl.decl.clone(), Arc::clone(rule)))
            })
            .collect();
        Ok(NativeSyntaxModule {
            declarations,
            categories: self.declared_categories.clone(),
            rules,
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
        if module.rules.keys().any(|kind| !names.contains(kind)) {
            return Err("an imported macro rule has no syntax declaration in its module");
        }
        for (name, behavior) in &module.categories {
            self.categories.insert(name.clone(), *behavior);
            let LeafView::Str(suffix) = name.leaf_view() else {
                unreachable!("validated above")
            };
            self.base_tokens.insert(format!("`({suffix}|"));
        }
        for decl in &module.declarations {
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
        Arc::make_mut(&mut self.rules).extend(
            module
                .rules
                .iter()
                .map(|(kind, rule)| (kind.clone(), Arc::clone(rule))),
        );
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
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn grammar(module: &str) -> FileGrammar {
        FileGrammar::new(false, &[], Some(Name::from_components([module])))
            .unwrap()
            .own_syntax_only()
    }

    fn declare(grammar: &mut FileGrammar, source: &str) {
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

    fn parses(grammar: &FileGrammar, source: &str) -> bool {
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
    fn independent_local_rules_and_imported_rule_overrides_refuse_module_export() {
        let mut library = grammar("Lib");
        declare(&mut library, "syntax \"wrap \" term:max : term");
        let mut consumer = grammar("Main");
        consumer
            .import_native(&library.export_native().unwrap())
            .unwrap();
        declare(&mut consumer, "macro_rules | `(wrap $x) => `($x)");
        assert!(consumer.export_native().is_err());
        declare(&mut library, "local macro_rules | `(wrap $x) => `($x)");
        assert!(library.export_native().is_err());
    }
}
