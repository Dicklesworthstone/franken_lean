//! Read-only environment capability for native imported macro name queries.
//!
//! Semantics: the pinned `Lean.Elab.liftMacroM` in
//! `vendor/lean4-src/src/Lean/Elab/Util.lean` captures the current namespace and
//! implements `hasDecl` using the full, non-exporting environment. Namespace
//! resolution follows `Lean/ResolveName.lean`, using namespace registrations
//! rather than inventing namespaces from declaration or alias prefixes.

use crate::Environment;
use fln_core::name::{LeafView, Name};
use fln_vm::macro_native::{MacroLookup, MacroLookupError};
use std::collections::BTreeSet;
use std::sync::OnceLock;

const MAX_NAMESPACE_WORK: usize = 1 << 20;

/// An invocation's immutable namespace and admitted declaration snapshot.
///
/// `full_environment` must include the caller's admitted private declarations,
/// corresponding to the pin's `env.setExporting false`. A public-only view
/// cannot answer whether a hidden declaration already occupies a name. This
/// capability does not admit declarations, resolve aliases, or run initializers.
#[derive(Debug, Clone)]
pub struct EnvironmentMacroLookup<'a> {
    full_environment: &'a Environment,
    current_namespace: &'a Name,
    /// Simple opens in source order; explicit opens never resolve namespaces.
    opened_namespaces: &'a [Name],
    private_prefix: Name,
    namespaces: OnceLock<Result<BTreeSet<Name>, MacroLookupError>>,
}

impl<'a> EnvironmentMacroLookup<'a> {
    pub fn new(
        full_environment: &'a Environment,
        main_module: &Name,
        current_namespace: &'a Name,
        opened_namespaces: &'a [Name],
    ) -> Self {
        Self {
            full_environment,
            current_namespace,
            opened_namespaces,
            private_prefix: Name::num(
                Name::from_components(["_private"]).append_core(main_module),
                0,
            ),
            namespaces: OnceLock::new(),
        }
    }

    fn namespaces(&self) -> Result<&BTreeSet<Name>, MacroLookupError> {
        self.namespaces
            .get_or_init(|| {
                fln_elab::namespaces::registrations(
                    &Environment::new(),
                    self.full_environment,
                    MAX_NAMESPACE_WORK,
                )
                .map(|rows| rows.names)
                .map_err(|error| match error {
                    fln_elab::instances::InstanceRegistryError::Limit => {
                        MacroLookupError::Exhausted("namespace metadata")
                    }
                    _ => MacroLookupError::Invalid("malformed namespace metadata"),
                })
            })
            .as_ref()
            .map_err(Clone::clone)
    }
}

impl MacroLookup for EnvironmentMacroLookup<'_> {
    fn current_namespace(&self) -> &Name {
        self.current_namespace
    }

    fn has_decl(&self, declaration: &Name) -> bool {
        // `mkPrivateName` first strips any old private prefix and then uses the
        // current main module. A foreign private spelling must not select that
        // other module's hidden declaration merely because it is in the map.
        let user_name = private_to_user_name(declaration);
        self.full_environment
            .contains(&self.private_prefix.append_core(&user_name))
            || self.full_environment.contains(&user_name)
    }

    fn resolve_namespace(&self, requested: &Name) -> Result<Vec<Name>, MacroLookupError> {
        let namespaces = self.namespaces()?;
        let mut work = 0;
        let mut parts = Vec::new();
        let mut cursor = requested.clone();
        while !cursor.is_anonymous() {
            namespace_work(&mut work, 1)?;
            if cursor.component_overflowed() {
                return Err(MacroLookupError::Invalid("overflowed namespace component"));
            }
            if let LeafView::Str(text) = cursor.leaf_view() {
                namespace_work(&mut work, text.len())?;
            }
            parts.push(cursor.clone());
            cursor = cursor.parent();
        }
        let requested_work = work.saturating_add(1);
        // `_root_` is stripped only at the root search. An enclosing namespace
        // or a simple open still receives the original structural name.
        let absolute = if parts
            .last()
            .is_some_and(|part| part.leaf_view() == LeafView::Str("_root_"))
        {
            parts.pop();
            parts
                .iter()
                .rev()
                .fold(Name::anonymous(), |prefix, part| match part.leaf_view() {
                    LeafView::Str(text) => Name::str(prefix, text),
                    LeafView::Num(value) => Name::num(prefix, value),
                    LeafView::Anonymous => unreachable!("anonymous component was excluded"),
                })
        } else {
            requested.clone()
        };
        let mut candidates = Vec::new();
        let mut enclosing = self.current_namespace.clone();
        loop {
            namespace_work(&mut work, requested_work)?;
            let candidate = match enclosing.leaf_view() {
                LeafView::Str(_) => enclosing.append_core(requested),
                LeafView::Anonymous => absolute.clone(),
                LeafView::Num(_) => {
                    return Err(MacroLookupError::Invalid("non-string current namespace"));
                }
            };
            if namespaces.contains(&candidate) {
                candidates.push(candidate);
                break;
            }
            if enclosing.is_anonymous() {
                break;
            }
            enclosing = enclosing.parent();
        }
        // The pin keeps this list's order and duplicates, including a match
        // already returned by the enclosing-namespace search.
        for opened in self.opened_namespaces.iter().rev() {
            namespace_work(&mut work, requested_work)?;
            let candidate = opened.append_core(requested);
            if namespaces.contains(&candidate) {
                candidates.push(candidate);
            }
        }
        Ok(candidates)
    }
}

fn namespace_work(work: &mut usize, amount: usize) -> Result<(), MacroLookupError> {
    *work = work
        .checked_add(amount)
        .filter(|total| *total <= MAX_NAMESPACE_WORK)
        .ok_or(MacroLookupError::Exhausted("namespace query"))?;
    Ok(())
}

/// The pin's `privateToUserName`, over structural names rather than display text.
/// A private prefix ends at the first numeric component only when that component
/// is exactly zero and every preceding component after `_private` is a string.
/// The explicit walk also handles deep names without recursing on the host stack.
fn private_to_user_name(name: &Name) -> Name {
    let mut components = Vec::new();
    let mut cursor = name.clone();
    while !cursor.is_anonymous() {
        components.push(cursor.clone());
        cursor = cursor.parent();
    }
    if !components
        .last()
        .is_some_and(|root| root.leaf_view() == LeafView::Str("_private"))
    {
        return name.clone();
    }
    let mut components = components.into_iter().rev();
    let Some(marker) =
        components.find(|component| matches!(component.leaf_view(), LeafView::Num(_)))
    else {
        return name.clone();
    };
    // A nonzero or overflowed first number prevents every later number from
    // being a private prefix in the original name.
    if marker.leaf_view() != LeafView::Num(0) || marker.component_overflowed() {
        return name.clone();
    }
    let mut user_name = Name::anonymous();
    for suffix in components {
        user_name = match suffix.leaf_view() {
            LeafView::Str(text) => Name::str(user_name, text),
            LeafView::Num(value) if suffix.component_overflowed() => {
                Name::num_overflowing(user_name, value)
            }
            LeafView::Num(value) => Name::num(user_name, value),
            LeafView::Anonymous => unreachable!("anonymous was excluded above"),
        };
    }
    user_name
}

#[cfg(test)]
mod tests {
    use super::*;
    use fln_core::expr::Expr;
    use fln_env::constants::{AxiomVal, ConstantInfo, ConstantVal};

    fn name(text: &str) -> Name {
        Name::from_components(text.split('.'))
    }

    fn private(module: &str, declaration: &Name) -> Name {
        Name::num(name("_private").append_core(&name(module)), 0).append_core(declaration)
    }

    // Synthetic declaration membership fixtures, not an admission test. The
    // production provider only borrows the environment supplied by its caller.
    fn environment(names: impl IntoIterator<Item = Name>) -> Environment {
        names
            .into_iter()
            .fold(Environment::new(), |env, declaration| {
                env.add_decl(ConstantInfo::Axiom(AxiomVal {
                    base: ConstantVal {
                        name: declaration,
                        level_params: Vec::new(),
                        type_: Expr::const_(name("Nat"), Vec::new()),
                    },
                    is_unsafe: false,
                }))
                .unwrap()
            })
    }

    #[test]
    fn namespace_and_declaration_queries_use_the_supplied_snapshot() {
        let main_module = name("Library.Current");
        let namespace = name("Nested.Scope");
        let env = environment([
            name("Public.value"),
            name("Nested.Scope.value"),
            private("Library.Current", &name("Hidden.value")),
            private("Other", &name("Foreign.only")),
        ]);
        let lookup = EnvironmentMacroLookup::new(&env, &main_module, &namespace, &[]);
        assert_eq!(lookup.current_namespace(), &namespace);
        for declaration in ["Public.value", "Nested.Scope.value", "Hidden.value"] {
            assert!(lookup.has_decl(&name(declaration)), "{declaration}");
        }
        for declaration in ["value", "Foreign.only", "Missing", "Nested.Scope"] {
            assert!(!lookup.has_decl(&name(declaration)), "{declaration}");
        }
        assert!(!lookup.has_decl(&Name::anonymous()));
        assert!(!lookup.has_decl(&private("Other", &name("Foreign.only"))));
    }

    #[test]
    fn already_private_inputs_rebind_to_the_current_module_and_public_name() {
        let main_module = name("Current");
        let namespace = Name::anonymous();
        let env = environment([
            private("Current", &name("hidden")),
            name("public"),
            private("Other", &name("foreignOnly")),
        ]);
        let lookup = EnvironmentMacroLookup::new(&env, &main_module, &namespace, &[]);
        assert!(lookup.has_decl(&private("Current", &name("hidden"))));
        assert!(lookup.has_decl(&private("Other", &name("hidden"))));
        assert!(lookup.has_decl(&private("Other", &name("public"))));
        assert!(!lookup.has_decl(&private("Other", &name("foreignOnly"))));
        assert!(!lookup.has_decl(&private("Current", &name("foreignOnly"))));
    }

    #[test]
    fn private_prefixes_follow_name_constructors_and_preserve_suffixes() {
        let user = Name::num(name("field"), 7);
        assert_eq!(private_to_user_name(&private("A.B", &user)), user);
        assert_eq!(
            private_to_user_name(&private("A.B", &Name::anonymous())),
            Name::anonymous()
        );
        let overflowed = Name::num_overflowing(name("field"), u64::MAX);
        let converted = private_to_user_name(&private("A.B", &overflowed));
        assert_eq!(converted, overflowed);
        assert!(converted.component_overflowed());
        for unchanged in [
            name("_private"),
            name("_private.A.B"),
            name("_private.A.B.0.field"),
            Name::str(Name::anonymous(), "_private.A.B.0.field"),
            Name::num(name("_private.A"), 1).append_core(&name("field")),
            Name::num(Name::num(name("_private.A"), 1), 0).append_core(&name("field")),
            Name::num(name("Prefix._private.A"), 0).append_core(&name("field")),
            Name::num_overflowing(name("_private.A"), 0).append_core(&name("field")),
        ] {
            assert_eq!(private_to_user_name(&unchanged), unchanged);
        }
        let main_module = name("A.B");
        let namespace = Name::anonymous();
        let env = environment([private("A.B", &name("field"))]);
        let lookup = EnvironmentMacroLookup::new(&env, &main_module, &namespace, &[]);
        assert!(lookup.has_decl(&name("field")));
        assert!(!lookup.has_decl(&name("_private.A.B.0.field")));
        assert!(!lookup.has_decl(&Name::str(Name::anonymous(), "_private.A.B.0.field")));
    }

    #[test]
    fn a_successor_environment_does_not_change_an_existing_capability() {
        let old = environment([name("first")]);
        let additional = environment([private("Current", &name("later"))]);
        let new = old
            .with_entry(
                additional
                    .entry(&private("Current", &name("later")))
                    .unwrap(),
            )
            .unwrap();
        let module = name("Current");
        let other_module = name("Other");
        let namespace = Name::anonymous();
        let before = EnvironmentMacroLookup::new(&old, &module, &namespace, &[]);
        let after = EnvironmentMacroLookup::new(&new, &module, &namespace, &[]);
        let other = EnvironmentMacroLookup::new(&new, &other_module, &namespace, &[]);
        assert!(before.has_decl(&name("first")));
        assert!(!before.has_decl(&name("later")));
        assert!(after.has_decl(&name("later")));
        assert!(!other.has_decl(&name("later")));
        assert!(!before.has_decl(&name("later")));
    }

    #[test]
    fn deep_private_names_do_not_recurse_on_the_host_stack() {
        let user = (0..4096).fold(Name::anonymous(), |name, _| Name::str(name, "part"));
        assert_eq!(private_to_user_name(&private("Module", &user)), user);
    }

    #[test]
    fn namespace_resolution_preserves_enclosing_open_order_and_duplicates() {
        let env = fln_elab::namespaces::register_module(
            &Environment::new(),
            &[
                name("Current.Child"),
                name("Current.Inner.Child"),
                name("First.Child"),
                name("Second.Child"),
                name("Child"),
            ],
        )
        .unwrap();
        let module = name("Module");
        let namespace = name("Current.Inner.Deep");
        let opened = [
            name("First"),
            name("Second"),
            name("Current.Inner"),
            name("First"),
        ];
        let lookup = EnvironmentMacroLookup::new(&env, &module, &namespace, &opened);
        assert_eq!(
            lookup.resolve_namespace(&name("Child")).unwrap(),
            [
                name("Current.Inner.Child"),
                name("First.Child"),
                name("Current.Inner.Child"),
                name("Second.Child"),
                name("First.Child"),
            ]
        );
        assert_eq!(
            lookup.resolve_namespace(&name("_root_.Child")).unwrap(),
            [name("Child")]
        );
        assert!(
            lookup
                .resolve_namespace(&name("Missing"))
                .unwrap()
                .is_empty()
        );
    }

    #[test]
    fn namespace_identity_comes_from_registrations_and_stays_snapshot_local() {
        let old = environment([
            name("Unregistered.Child.value"),
            private("Other", &name("Hidden.value")),
        ]);
        let old = fln_elab::aliases::register(
            &old,
            &name("AliasOnly.member"),
            &name("Unregistered.Child.value"),
        )
        .unwrap();
        let module = name("Module");
        let namespace = Name::anonymous();
        let before = EnvironmentMacroLookup::new(&old, &module, &namespace, &[]);
        assert!(
            before
                .resolve_namespace(&name("Unregistered.Child"))
                .unwrap()
                .is_empty()
        );
        assert!(
            before
                .resolve_namespace(&name("AliasOnly"))
                .unwrap()
                .is_empty()
        );
        assert!(
            before
                .resolve_namespace(&name("Hidden"))
                .unwrap()
                .is_empty()
        );
        let new =
            fln_elab::namespaces::register_module(&old, &[name("Empty.Child"), Name::anonymous()])
                .unwrap();
        let after = EnvironmentMacroLookup::new(&new, &module, &namespace, &[]);
        assert_eq!(
            after.resolve_namespace(&name("Empty.Child")).unwrap(),
            [name("Empty.Child")]
        );
        assert_eq!(
            after.resolve_namespace(&Name::anonymous()).unwrap(),
            [Name::anonymous()]
        );
        assert!(
            before
                .resolve_namespace(&name("Empty.Child"))
                .unwrap()
                .is_empty()
        );
        assert!(
            after
                .resolve_namespace(&name("Unregistered"))
                .unwrap()
                .is_empty()
        );
    }

    #[test]
    fn malformed_namespace_metadata_and_invalid_context_are_typed_refusals() {
        let base =
            fln_elab::namespaces::register_module(&Environment::new(), &[name("Good")]).unwrap();
        let malformed = base
            .push_extension_entry(
                &fln_elab::namespaces::journal_name(),
                b"bad namespace row".to_vec(),
            )
            .unwrap();
        let module = name("Module");
        let namespace = Name::anonymous();
        let lookup = EnvironmentMacroLookup::new(&malformed, &module, &namespace, &[]);
        for requested in [name("Good"), name("Missing")] {
            assert_eq!(
                lookup.resolve_namespace(&requested),
                Err(MacroLookupError::Invalid("malformed namespace metadata"))
            );
        }
        let invalid = Name::num(name("Current"), 7);
        let lookup = EnvironmentMacroLookup::new(&base, &module, &invalid, &[]);
        assert_eq!(
            lookup.resolve_namespace(&name("Good")),
            Err(MacroLookupError::Invalid("non-string current namespace"))
        );
        let lookup = EnvironmentMacroLookup::new(&base, &module, &namespace, &[]);
        assert_eq!(
            lookup.resolve_namespace(&Name::num_overflowing(Name::anonymous(), 0)),
            Err(MacroLookupError::Invalid("overflowed namespace component"))
        );
        assert_eq!(
            lookup.resolve_namespace(&name("Good")).unwrap(),
            [name("Good")]
        );
    }

    #[test]
    fn namespace_metadata_and_query_limits_cannot_become_empty_answers() {
        let names: Vec<_> = (0..26_000)
            .map(|index| {
                name(&format!(
                    "NamespaceWithEnoughBytesToReachMetadataLimit{index:05}"
                ))
            })
            .collect();
        let large = names
            .chunks(512)
            .try_fold(Environment::new(), |env, names| {
                fln_elab::namespaces::register_module(&env, names)
            })
            .unwrap();
        assert_eq!(
            fln_elab::namespaces::read(&large).unwrap().len(),
            names.len()
        );
        let module = name("Module");
        let namespace = Name::anonymous();
        let lookup = EnvironmentMacroLookup::new(&large, &module, &namespace, &[]);
        assert_eq!(
            lookup.resolve_namespace(&name("Missing")),
            Err(MacroLookupError::Exhausted("namespace metadata"))
        );
        let small =
            fln_elab::namespaces::register_module(&Environment::new(), &[name("Good")]).unwrap();
        let lookup = EnvironmentMacroLookup::new(&small, &module, &namespace, &[]);
        let oversized = Name::str(Name::anonymous(), "n".repeat(MAX_NAMESPACE_WORK + 1));
        assert_eq!(
            lookup.resolve_namespace(&oversized),
            Err(MacroLookupError::Exhausted("namespace query"))
        );
        assert_eq!(
            lookup.resolve_namespace(&name("Good")).unwrap(),
            [name("Good")]
        );
    }
}
