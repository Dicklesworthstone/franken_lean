//! Read-only environment capability for native imported macro name queries.
//!
//! Semantics: the pinned `Lean.Elab.liftMacroM` in
//! `vendor/lean4-src/src/Lean/Elab/Util.lean` captures the current namespace and
//! implements `hasDecl` using the full, non-exporting environment. Namespace
//! resolution follows `Lean/ResolveName.lean`, using namespace registrations
//! rather than inventing namespaces from declaration or alias prefixes.

use crate::Environment;
use fln_core::name::{LeafView, Name};
use fln_elab::aliases::AliasTable;
use fln_elab::protected_names::ProtectedNames;
use fln_vm::macro_native::{MacroLookup, MacroLookupError, ResolvedGlobals};
use std::collections::BTreeSet;
use std::sync::OnceLock;

const MAX_NAMESPACE_WORK: usize = 1 << 20;
const MAX_GLOBAL_WORK: usize = 1 << 20;

#[derive(Debug, Clone)]
struct GlobalTables {
    aliases: AliasTable,
    protected: ProtectedNames,
}

/// An invocation's immutable namespace and admitted declaration snapshot.
///
/// `full_environment` must include the caller's admitted private declarations,
/// corresponding to the pin's `env.setExporting false`. A public-only view
/// cannot answer whether a hidden declaration already occupies a name. This
/// capability does not admit declarations or run initializers. Global resolution
/// reads native aliases, protected declarations and the ported reserved-name
/// predicates; it never executes a reserved name's declaration action.
#[derive(Debug, Clone)]
pub struct EnvironmentMacroLookup<'a> {
    full_environment: &'a Environment,
    current_namespace: &'a Name,
    /// Simple opens in source order; explicit opens never resolve namespaces.
    opened_namespaces: &'a [Name],
    /// Explicit opens with the number of earlier simple opens, in source order.
    explicit_opens: &'a [(usize, Name, Name)],
    private_prefix: Name,
    namespaces: OnceLock<Result<BTreeSet<Name>, MacroLookupError>>,
    globals: OnceLock<Result<GlobalTables, MacroLookupError>>,
}

impl<'a> EnvironmentMacroLookup<'a> {
    pub fn new(
        full_environment: &'a Environment,
        main_module: &Name,
        current_namespace: &'a Name,
        opened_namespaces: &'a [Name],
        explicit_opens: &'a [(usize, Name, Name)],
    ) -> Self {
        Self {
            full_environment,
            current_namespace,
            opened_namespaces,
            explicit_opens,
            private_prefix: Name::num(
                Name::from_components(["_private"]).append_core(main_module),
                0,
            ),
            namespaces: OnceLock::new(),
            globals: OnceLock::new(),
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

    fn globals(&self) -> Result<&GlobalTables, MacroLookupError> {
        self.globals
            .get_or_init(|| {
                let mut bytes = 0usize;
                for journal in [
                    Name::from_components(["FrankenLean", "sourceAliases", "v1"]),
                    fln_elab::protected_names::journal_name(),
                ] {
                    if let Some(extension) = self.full_environment.extension(&journal) {
                        for entry in extension.entries() {
                            bytes = bytes
                                .checked_add(entry.payload.len().saturating_add(1))
                                .filter(|total| *total <= MAX_GLOBAL_WORK)
                                .ok_or(MacroLookupError::Exhausted("global metadata"))?;
                        }
                    }
                }
                let aliases =
                    AliasTable::read(self.full_environment).map_err(|error| match error {
                        fln_elab::aliases::AliasError::Limit => {
                            MacroLookupError::Exhausted("global alias metadata")
                        }
                        _ => MacroLookupError::Invalid("malformed global alias metadata"),
                    })?;
                let protected =
                    ProtectedNames::read(self.full_environment).map_err(|error| match error {
                        fln_elab::protected_names::ProtectedError::Limit => {
                            MacroLookupError::Exhausted("global protected metadata")
                        }
                        _ => MacroLookupError::Invalid("malformed global protected metadata"),
                    })?;
                Ok(GlobalTables { aliases, protected })
            })
            .as_ref()
            .map_err(Clone::clone)
    }

    fn contains_global(&self, name: &Name, work: &mut usize) -> Result<bool, MacroLookupError> {
        global_name_work(work, name)?;
        Ok(self.full_environment.contains(name)
            || fln_elab::source::scope::is_reserved_name(self.full_environment, name))
    }

    fn private_global(
        &self,
        name: &Name,
        work: &mut usize,
    ) -> Result<Option<Name>, MacroLookupError> {
        let candidate = self.private_prefix.append_core(&private_to_user_name(name));
        Ok(self.contains_global(&candidate, work)?.then_some(candidate))
    }

    fn global_aliases(
        &self,
        name: &Name,
        tables: &GlobalTables,
        work: &mut usize,
    ) -> Result<Vec<Name>, MacroLookupError> {
        let atomic = name.parent().is_anonymous();
        let mut found = Vec::new();
        // The native journal stores insertion order; the pin's addAliasEntry
        // prepends each new target. Do not reverse the overloads a second time.
        for target in tables.aliases.targets(name).iter().rev() {
            global_name_work(work, target)?;
            if !atomic || !tables.protected.contains(target) {
                found.push(target.clone());
            }
        }
        Ok(found)
    }

    fn qualified_globals(
        &self,
        namespace: &Name,
        name: &Name,
        tables: &GlobalTables,
        work: &mut usize,
    ) -> Result<Vec<Name>, MacroLookupError> {
        global_name_work(work, namespace)?;
        global_name_work(work, name)?;
        let candidate = namespace.append_core(name);
        let mut found = Vec::new();
        if !name.parent().is_anonymous() || !tables.protected.contains(&candidate) {
            if self.contains_global(&candidate, work)? {
                found.push(candidate.clone());
            } else if let Some(private) = self.private_global(&candidate, work)? {
                found.push(private);
            }
        }
        found.extend(
            self.global_aliases(&candidate, tables, work)?
                .into_iter()
                .filter(|target| {
                    !name.parent().is_anonymous() || !tables.protected.contains(target)
                }),
        );
        Ok(found)
    }

    fn global_candidates(
        &self,
        id: &Name,
        tables: &GlobalTables,
        work: &mut usize,
    ) -> Result<Vec<Name>, MacroLookupError> {
        // Enclosing namespaces win as a tier, before exact or opened names.
        let mut namespace = self.current_namespace.clone();
        while !namespace.is_anonymous() {
            if !matches!(namespace.leaf_view(), LeafView::Str(_)) {
                return Err(MacroLookupError::Invalid("non-string current namespace"));
            }
            let found = self.qualified_globals(&namespace, id, tables, work)?;
            if !found.is_empty() {
                return Ok(found);
            }
            namespace = namespace.parent();
        }
        if !id.parent().is_anonymous() {
            let exact = replace_global_prefix(
                id,
                &Name::from_components(["_root_"]),
                &Name::anonymous(),
                work,
            )?
            .unwrap_or_else(|| id.clone());
            if self.contains_global(&exact, work)? {
                return Ok(vec![exact]);
            }
            if let Some(private) = self.private_global(&exact, work)? {
                return Ok(vec![private]);
            }
        }
        let mut found = Vec::new();
        if let Some(private) = self.private_global(id, work)? {
            found.push(private);
        }
        if self.contains_global(id, work)? {
            found.push(id.clone());
        }
        // The pin walks newest-first OpenDecls and prepends each result, so
        // the final candidates are oldest-first. Construct that order directly.
        let mut opened = Vec::new();
        for position in 0..=self.opened_namespaces.len() {
            for (at, alias, target) in self.explicit_opens {
                global_work(work, 1)?;
                if *at != position {
                    continue;
                }
                if alias == id {
                    opened.push(target.clone());
                } else if let Some(candidate) = replace_global_prefix(id, alias, target, work)?
                    && self.full_environment.contains(&candidate)
                {
                    opened.push(candidate);
                }
            }
            if let Some(namespace) = self.opened_namespaces.get(position) {
                opened.extend(self.qualified_globals(namespace, id, tables, work)?);
            }
        }
        opened.extend(found);
        let mut aliases = self.global_aliases(id, tables, work)?;
        aliases.extend(opened);
        Ok(aliases)
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

    fn resolve_global_name(&self, requested: &Name) -> Result<ResolvedGlobals, MacroLookupError> {
        let mut work = 0;
        global_name_work(&mut work, requested)?;
        global_name_work(&mut work, self.current_namespace)?;
        global_name_work(&mut work, &self.private_prefix)?;
        for opened in self.opened_namespaces {
            global_name_work(&mut work, opened)?;
        }
        for (position, alias, target) in self.explicit_opens {
            global_work(&mut work, 1)?;
            if *position > self.opened_namespaces.len() || alias.is_anonymous() {
                return Err(MacroLookupError::Invalid("malformed explicit open"));
            }
            global_name_work(&mut work, alias)?;
            global_name_work(&mut work, target)?;
        }
        let tables = self.globals()?;
        let mut view = fln_syntax::hygiene::extract_macro_scopes(requested)
            .map_err(|_| MacroLookupError::Invalid("malformed global macro scopes"))?;
        let mut fields = Vec::new();
        while let LeafView::Str(field) = view.name.leaf_view() {
            global_work(&mut work, 1)?;
            let candidates = self.global_candidates(&view.review(), tables, &mut work)?;
            if !candidates.is_empty() {
                let mut seen = BTreeSet::new();
                fields.reverse();
                let mut found = Vec::new();
                for candidate in candidates {
                    if !seen.insert(candidate.clone()) {
                        continue;
                    }
                    global_name_work(&mut work, &candidate)?;
                    for field in &fields {
                        global_work(&mut work, field.len().saturating_add(1))?;
                    }
                    found.push((candidate, fields.clone()));
                }
                return Ok(found);
            }
            fields.push(field.to_owned());
            view.name = view.name.parent();
        }
        Ok(Vec::new())
    }
}

fn global_work(work: &mut usize, amount: usize) -> Result<(), MacroLookupError> {
    *work = work
        .checked_add(amount)
        .filter(|total| *total <= MAX_GLOBAL_WORK)
        .ok_or(MacroLookupError::Exhausted("global query"))?;
    Ok(())
}

fn global_name_work(work: &mut usize, name: &Name) -> Result<(), MacroLookupError> {
    let mut cursor = name.clone();
    while !cursor.is_anonymous() {
        global_work(work, 1)?;
        if cursor.component_overflowed() {
            return Err(MacroLookupError::Invalid("overflowed global component"));
        }
        if let LeafView::Str(text) = cursor.leaf_view() {
            global_work(work, text.len())?;
        }
        cursor = cursor.parent();
    }
    Ok(())
}

fn replace_global_prefix(
    name: &Name,
    prefix: &Name,
    replacement: &Name,
    work: &mut usize,
) -> Result<Option<Name>, MacroLookupError> {
    let mut suffix = Vec::new();
    let mut cursor = name.clone();
    while &cursor != prefix {
        global_work(work, 1)?;
        if cursor.is_anonymous() {
            return Ok(None);
        }
        suffix.push(cursor.clone());
        cursor = cursor.parent();
    }
    let mut result = replacement.clone();
    for component in suffix.into_iter().rev() {
        result = match component.leaf_view() {
            LeafView::Str(text) => Name::str(result, text),
            LeafView::Num(number) => Name::num(result, number),
            LeafView::Anonymous => unreachable!("anonymous was excluded above"),
        };
    }
    Ok(Some(result))
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
        let lookup = EnvironmentMacroLookup::new(&env, &main_module, &namespace, &[], &[]);
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
        let lookup = EnvironmentMacroLookup::new(&env, &main_module, &namespace, &[], &[]);
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
        let lookup = EnvironmentMacroLookup::new(&env, &main_module, &namespace, &[], &[]);
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
        let before = EnvironmentMacroLookup::new(&old, &module, &namespace, &[], &[]);
        let after = EnvironmentMacroLookup::new(&new, &module, &namespace, &[], &[]);
        let other = EnvironmentMacroLookup::new(&new, &other_module, &namespace, &[], &[]);
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
        let lookup = EnvironmentMacroLookup::new(&env, &module, &namespace, &opened, &[]);
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
        let before = EnvironmentMacroLookup::new(&old, &module, &namespace, &[], &[]);
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
        let after = EnvironmentMacroLookup::new(&new, &module, &namespace, &[], &[]);
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
        let lookup = EnvironmentMacroLookup::new(&malformed, &module, &namespace, &[], &[]);
        for requested in [name("Good"), name("Missing")] {
            assert_eq!(
                lookup.resolve_namespace(&requested),
                Err(MacroLookupError::Invalid("malformed namespace metadata"))
            );
        }
        let invalid = Name::num(name("Current"), 7);
        let lookup = EnvironmentMacroLookup::new(&base, &module, &invalid, &[], &[]);
        assert_eq!(
            lookup.resolve_namespace(&name("Good")),
            Err(MacroLookupError::Invalid("non-string current namespace"))
        );
        let lookup = EnvironmentMacroLookup::new(&base, &module, &namespace, &[], &[]);
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
        let lookup = EnvironmentMacroLookup::new(&large, &module, &namespace, &[], &[]);
        assert_eq!(
            lookup.resolve_namespace(&name("Missing")),
            Err(MacroLookupError::Exhausted("namespace metadata"))
        );
        let small =
            fln_elab::namespaces::register_module(&Environment::new(), &[name("Good")]).unwrap();
        let lookup = EnvironmentMacroLookup::new(&small, &module, &namespace, &[], &[]);
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

    #[test]
    fn global_queries_keep_namespace_precedence_overloads_and_projection_suffixes() {
        let module = name("CurrentModule");
        let namespace = name("Current.Inner");
        let opened = [name("First"), name("Second"), name("First")];
        let env = environment([
            name("Current.local"),
            name("local"),
            name("pooled"),
            name("First.pooled"),
            name("Second.pooled"),
            name("First.exact"),
            name("Second.First.exact"),
            name("First.record"),
        ]);
        let lookup = EnvironmentMacroLookup::new(&env, &module, &namespace, &opened, &[]);
        assert_eq!(
            lookup.resolve_global_name(&name("local")).unwrap(),
            [(name("Current.local"), vec![])]
        );
        assert_eq!(
            lookup.resolve_global_name(&name("pooled")).unwrap(),
            [
                (name("First.pooled"), vec![]),
                (name("Second.pooled"), vec![]),
                (name("pooled"), vec![]),
            ]
        );
        assert_eq!(
            lookup.resolve_global_name(&name("First.exact")).unwrap(),
            [(name("First.exact"), vec![])]
        );
        assert_eq!(
            lookup
                .resolve_global_name(&name("record.field.tail"))
                .unwrap(),
            [(name("First.record"), vec!["field".into(), "tail".into()])]
        );
        assert_eq!(
            lookup.resolve_global_name(&name("_root_.local")).unwrap(),
            [(name("local"), vec![])]
        );
        assert!(
            lookup
                .resolve_global_name(&name("Missing"))
                .unwrap()
                .is_empty()
        );
    }

    #[test]
    fn global_aliases_protection_and_private_names_follow_the_captured_environment() {
        let module = name("CurrentModule");
        let namespace = name("Current");
        let opened = [name("First")];
        let env = environment([
            name("Current.value"),
            name("First.protected"),
            name("Target.one"),
            name("Target.two"),
            private("CurrentModule", &name("hidden")),
            private("OtherModule", &name("foreign")),
        ]);
        let env =
            fln_elab::protected_names::register_module(&env, &[name("First.protected")]).unwrap();
        let env =
            fln_elab::aliases::register(&env, &name("Current.value"), &name("Target.one")).unwrap();
        let env = fln_elab::aliases::register(&env, &name("choice"), &name("Target.one")).unwrap();
        let env = fln_elab::aliases::register(&env, &name("choice"), &name("Target.two")).unwrap();
        let env =
            fln_elab::aliases::register(&env, &name("guarded"), &name("First.protected")).unwrap();
        let lookup = EnvironmentMacroLookup::new(&env, &module, &namespace, &opened, &[]);
        assert_eq!(
            lookup.resolve_global_name(&name("value")).unwrap(),
            [
                (name("Current.value"), vec![]),
                (name("Target.one"), vec![])
            ]
        );
        assert_eq!(
            lookup.resolve_global_name(&name("choice")).unwrap(),
            [(name("Target.two"), vec![]), (name("Target.one"), vec![])]
        );
        for query in ["protected", "guarded", "foreign"] {
            assert!(
                lookup.resolve_global_name(&name(query)).unwrap().is_empty(),
                "{query}"
            );
        }
        assert_eq!(
            lookup
                .resolve_global_name(&name("First.protected"))
                .unwrap(),
            [(name("First.protected"), vec![])]
        );
        assert_eq!(
            lookup.resolve_global_name(&name("hidden")).unwrap(),
            [(private("CurrentModule", &name("hidden")), vec![])]
        );
    }

    #[test]
    fn global_projection_search_preserves_hygienic_constant_scopes() {
        let module = name("Module");
        let namespace = Name::anonymous();
        let mut view = fln_syntax::hygiene::MacroScopesView {
            name: name("record"),
            imported: Name::anonymous(),
            context: name("Quotation"),
            scopes: vec![7, 12],
        };
        let constant = view.review();
        let env = environment([constant.clone(), name("record")]);
        let lookup = EnvironmentMacroLookup::new(&env, &module, &namespace, &[], &[]);
        view.name = name("record.field.tail");
        assert_eq!(
            lookup.resolve_global_name(&view.review()).unwrap(),
            [(constant, vec!["field".into(), "tail".into()])]
        );
        assert_eq!(lookup.resolve_global_name(&Name::anonymous()).unwrap(), []);
    }
}
