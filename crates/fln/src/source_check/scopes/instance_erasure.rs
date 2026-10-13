//! Lexical instance removal over checked declarations, with separate public and
//! private journal anchors and atomic publication of the complete command.
use super::{Scopes, TransitionError};
use crate::Environment;
use fln_core::name::Name;
use fln_elab::instances::InstanceRegistry;

impl Scopes {
    pub(crate) fn erase_instance_attribute(
        &mut self,
        env: &Environment,
        public_env: Option<&Environment>,
        requested: &[Name],
    ) -> Result<(), TransitionError> {
        if requested.len() > 4096 {
            return Err(TransitionError::Scope(
                "instance erasure declarations limit exceeded".into(),
            ));
        }
        let aliases = fln_elab::aliases::AliasTable::read(env)
            .map_err(|error| TransitionError::Scope(format!("{error:?}")))?;
        let protected = fln_elab::protected_names::ProtectedNames::read(env)
            .map_err(|error| TransitionError::Scope(format!("{error:?}")))?;
        let mut instances = self.current.instance_scopes.clone();
        let mut public_instances = self.public_instances.clone();
        for requested in requested {
            let name = self
                .current
                .resolve_with_aliases(requested, |name| env.contains(name), &aliases, &protected)
                .map_err(|error| TransitionError::Scope(error.to_string()))?
                .ok_or_else(|| {
                    TransitionError::Scope(format!(
                        "Unknown constant `{}`",
                        requested.to_display_string(),
                    ))
                })?;
            instances
                .erase(env, &name)
                .map_err(TransitionError::Registry)?;
            if let Some(public_env) = public_env {
                // A private instance has no selection to erase in the public
                // world. Validate that world's journal even then: unreadable
                // metadata is not evidence that no public instance exists.
                let registry = InstanceRegistry::read_with_scopes(public_env, &public_instances)
                    .map_err(TransitionError::Registry)?;
                if registry.is_instance(&name) {
                    public_instances
                        .erase(public_env, &name)
                        .map_err(TransitionError::Registry)?;
                }
            }
        }
        // A late name, registration, history, or public-world failure reaches
        // neither assignment. The environment itself is never changed here.
        self.current.instance_scopes = instances;
        self.public_instances = public_instances;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use fln_core::{expr::Expr, level::Level};
    use fln_env::constants::{AxiomVal, ConstantInfo, ConstantVal};
    use fln_parse::command_scope::ScopeCommand;

    fn n(name: &str) -> Name {
        Name::from_components(name.split('.'))
    }
    fn axiom(name: &str, type_: Expr) -> ConstantInfo {
        ConstantInfo::Axiom(AxiomVal {
            base: ConstantVal {
                name: n(name),
                level_params: Vec::new(),
                type_,
            },
            is_unsafe: false,
        })
    }
    fn fixture() -> Environment {
        let env = Environment::new()
            .add_decl(axiom("C", Expr::sort(Level::one())))
            .unwrap()
            .add_decl(axiom("N.chosen", Expr::const_(n("C"), Vec::new())))
            .unwrap()
            .add_decl(axiom("ordinary", Expr::const_(n("C"), Vec::new())))
            .unwrap();
        let env = fln_elab::instances::register_class(&env, &n("C")).unwrap();
        fln_elab::instances::register_instance(&env, &n("N.chosen"), 1000).unwrap()
    }
    fn active(
        env: &Environment,
        scopes: &fln_elab::instances::scoped::ActiveScopes,
        name: &str,
    ) -> bool {
        InstanceRegistry::read_with_scopes(env, scopes)
            .unwrap()
            .is_instance(&n(name))
    }

    #[test]
    fn erasure_resolves_namespaces_and_aliases_to_exact_declarations() {
        let env = fln_elab::aliases::register(&fixture(), &n("alias"), &n("N.chosen")).unwrap();
        let mut scopes = Scopes::default();
        scopes.current.namespace = n("N");
        scopes
            .erase_instance_attribute(&env, None, &[n("chosen")])
            .unwrap_or_else(|error| panic!("{}", error.message()));
        assert!(!active(&env, &scopes.current.instance_scopes, "N.chosen"));
        let mut scopes = Scopes::default();
        scopes
            .erase_instance_attribute(&env, None, &[n("alias")])
            .unwrap_or_else(|error| panic!("{}", error.message()));
        assert!(!active(&env, &scopes.current.instance_scopes, "N.chosen"));
    }

    #[test]
    fn a_late_failure_rolls_back_both_worlds() {
        let env = fixture();
        let mut scopes = Scopes::default();
        let private_before = scopes.current.instance_scopes.clone();
        let public_before = scopes.public_instances.clone();
        assert!(
            scopes
                .erase_instance_attribute(&env, Some(&env), &[n("N.chosen"), n("ordinary")])
                .is_err()
        );
        assert_eq!(scopes.current.instance_scopes, private_before);
        assert_eq!(scopes.public_instances, public_before);
        assert!(active(&env, &scopes.current.instance_scopes, "N.chosen"));
        assert!(active(&env, &scopes.public_instances, "N.chosen"));
    }

    #[test]
    fn public_and_private_scopes_restore_their_own_erasure_histories() {
        let public = fixture();
        let private = public
            .add_decl(axiom("privateChoice", Expr::const_(n("C"), Vec::new())))
            .unwrap();
        let private =
            fln_elab::instances::register_instance(&private, &n("privateChoice"), 2000).unwrap();
        let mut scopes = Scopes::default();
        scopes
            .transition_worlds(ScopeCommand::Section(None), &private, Some(&public))
            .unwrap_or_else(|error| panic!("{}", error.message()));
        scopes
            .erase_instance_attribute(
                &private,
                Some(&public),
                &[n("N.chosen"), n("privateChoice")],
            )
            .unwrap_or_else(|error| panic!("{}", error.message()));
        assert!(!active(
            &private,
            &scopes.current.instance_scopes,
            "N.chosen"
        ));
        assert!(!active(
            &private,
            &scopes.current.instance_scopes,
            "privateChoice"
        ));
        assert!(!active(&public, &scopes.public_instances, "N.chosen"));
        scopes
            .transition_worlds(ScopeCommand::End(None), &private, Some(&public))
            .unwrap_or_else(|error| panic!("{}", error.message()));
        assert!(active(
            &private,
            &scopes.current.instance_scopes,
            "privateChoice"
        ));
        assert!(active(&public, &scopes.public_instances, "N.chosen"));
    }

    #[test]
    fn an_unreadable_public_journal_cannot_publish_a_private_erasure() {
        let env = fixture();
        let broken_public = env
            .push_extension_entry(
                &n("FrankenLean.sourceInstances.v1"),
                b"FLNINST\x02".to_vec(),
            )
            .unwrap();
        let mut scopes = Scopes::default();
        let private_before = scopes.current.instance_scopes.clone();
        let public_before = scopes.public_instances.clone();
        let result = scopes.erase_instance_attribute(&env, Some(&broken_public), &[n("N.chosen")]);
        assert!(matches!(result, Err(TransitionError::Registry(_))));
        assert_eq!(scopes.current.instance_scopes, private_before);
        assert_eq!(scopes.public_instances, public_before);
        assert!(active(&env, &scopes.current.instance_scopes, "N.chosen"));
    }

    #[test]
    fn an_unknown_name_and_an_excessive_batch_publish_nothing() {
        let env = fixture();
        let mut scopes = Scopes::default();
        let before = scopes.current.instance_scopes.clone();
        let error = scopes.erase_instance_attribute(&env, None, &[n("absent")]);
        assert!(
            matches!(error, Err(TransitionError::Scope(message)) if message == "Unknown constant `absent`")
        );
        assert!(
            scopes
                .erase_instance_attribute(&env, None, &vec![n("N.chosen"); 4097])
                .is_err()
        );
        assert_eq!(scopes.current.instance_scopes, before);
    }
}
