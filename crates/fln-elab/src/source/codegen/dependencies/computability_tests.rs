//! The compiler may see checked imported code without changing the logical world.
use super::*;
use crate::source::scope::computability::{ComputabilityEnvironment, ComputabilityProvider};
use fln_env::constants::{DefinitionSafety, DefinitionVal, ReducibilityHints};
use std::sync::{Arc, Mutex};

struct Provider<F>(F);

impl<F> ComputabilityEnvironment for Provider<F>
where
    F: Fn(&Environment) -> Result<Environment, NatDefinitionElabError> + Send + Sync,
{
    fn environment(
        &self,
        logical: &Environment,
        charge: &mut dyn FnMut(usize) -> Result<(), NatDefinitionElabError>,
    ) -> Result<Environment, NatDefinitionElabError> {
        charge(1)?;
        (self.0)(logical)
    }
}

fn n(text: &str) -> Name {
    Name::from_components(text.split('.'))
}

fn provider<F>(f: F) -> ComputabilityProvider
where
    F: Fn(&Environment) -> Result<Environment, NatDefinitionElabError> + Send + Sync + 'static,
{
    ComputabilityProvider(Arc::new(Provider(f)))
}

#[test]
fn imported_code_availability_does_not_replace_logical_axioms() {
    let logical = super::tests::axiom_environment();
    let ConstantInfo::Axiom(header) = logical.find(&n("bodyless")).unwrap() else {
        panic!("fixture axiom")
    };
    let executable = crate::seed::bootstrap_nat_environment(Budget::DEFAULT)
        .unwrap()
        .add_decl(ConstantInfo::Defn(DefinitionVal {
            base: header.base.clone(),
            value: Expr::lit(fln_core::expr::Literal::Nat(
                fln_core::expr::NatLit::from_u64(7),
            )),
            hints: ReducibilityHints::Regular(1),
            safety: DefinitionSafety::Safe,
            all: vec![n("bodyless")],
        }))
        .unwrap();
    let expected = logical.clone();
    let mut context = Context::new(&logical, Budget::DEFAULT);
    context.source_scope.computability = Some(provider(move |current| {
        assert_eq!(current, &expected);
        Ok(executable.clone())
    }));
    assert_eq!(
        context.check_definition_codegen(&super::tests::term("bodyless")),
        Ok(false)
    );
    assert_eq!(context.txn.env, logical);
    assert!(matches!(
        context.txn.env.find(&n("bodyless")),
        Some(ConstantInfo::Axiom(_))
    ));
}

#[test]
fn compiler_queries_receive_each_current_noncomputable_suffix() {
    let logical = super::tests::environment();
    let observed = Arc::new(Mutex::new(Vec::new()));
    let observations = Arc::clone(&observed);
    let mut context = Context::new(&logical, Budget::DEFAULT);
    context.source_scope.computability = Some(provider(move |current| {
        observations.lock().unwrap().push(
            crate::noncomputable::read(current)
                .unwrap()
                .contains(&n("usable")),
        );
        Ok(current.clone())
    }));
    assert_eq!(
        context.check_definition_codegen(&super::tests::term("usable")),
        Ok(false)
    );
    context.txn.env = crate::noncomputable::register(&context.txn.env, &n("usable")).unwrap();
    let admitted = context.txn.env.clone();
    assert!(matches!(
        context.check_definition_codegen(&super::tests::term("usable")),
        Err(NatDefinitionElabError::Inference(
            SourceInferenceError::NoncomputableDependency(name)
        )) if name == n("usable")
    ));
    assert_eq!(context.txn.env, admitted);
    assert_eq!(*observed.lock().unwrap(), [false, true]);
}

#[test]
fn import_provider_failure_is_not_a_suppressed_compiler_failure() {
    let logical = super::tests::environment();
    let mut context = Context::new(&logical, Budget::DEFAULT);
    context.source_scope.noncomputable_section = true;
    context.source_scope.computability = Some(provider(|_| {
        Err(failure(SourceInferenceError::ResourceLimit))
    }));
    assert!(matches!(
        context.check_definition_codegen(&super::tests::term("usable")),
        Err(NatDefinitionElabError::Inference(
            SourceInferenceError::ResourceLimit
        ))
    ));
    assert_eq!(context.txn.env, logical);
}

#[test]
fn import_provider_keeps_scopes_off_the_default_fast_path() {
    let scope = SourceScope {
        computability: Some(provider(|logical| Ok(logical.clone()))),
        ..SourceScope::default()
    };
    assert_ne!(scope, SourceScope::default());
    assert_eq!(scope, scope.clone());
    let other = SourceScope {
        computability: Some(provider(|logical| Ok(logical.clone()))),
        ..SourceScope::default()
    };
    assert_ne!(scope, other);
}
