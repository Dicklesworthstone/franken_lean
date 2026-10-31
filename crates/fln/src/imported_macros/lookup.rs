//! Read-only environment capability for native imported macro name queries.
//!
//! Semantics: the pinned `Lean.Elab.liftMacroM` in
//! `vendor/lean4-src/src/Lean/Elab/Util.lean` captures the current namespace and
//! implements `hasDecl` using the full, non-exporting environment. Private-name
//! conversion follows `Lean/Modifiers.lean` and `Lean/PrivateName.lean`.

use crate::Environment;
use fln_core::name::{LeafView, Name};
use fln_vm::macro_native::MacroLookup;

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
    private_prefix: Name,
}

impl<'a> EnvironmentMacroLookup<'a> {
    pub fn new(
        full_environment: &'a Environment,
        main_module: &Name,
        current_namespace: &'a Name,
    ) -> Self {
        Self {
            full_environment,
            current_namespace,
            private_prefix: Name::num(
                Name::from_components(["_private"]).append_core(main_module),
                0,
            ),
        }
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
        let lookup = EnvironmentMacroLookup::new(&env, &main_module, &namespace);
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
        let lookup = EnvironmentMacroLookup::new(&env, &main_module, &namespace);
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
        let lookup = EnvironmentMacroLookup::new(&env, &main_module, &namespace);
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
        let before = EnvironmentMacroLookup::new(&old, &module, &namespace);
        let after = EnvironmentMacroLookup::new(&new, &module, &namespace);
        let other = EnvironmentMacroLookup::new(&new, &other_module, &namespace);
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
}
