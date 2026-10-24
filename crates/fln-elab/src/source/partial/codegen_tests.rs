//! Failure-atomic publication of effects uses the original command's remaining work.
use super::*;
use fln_core::expr::{Literal, NatLit};

fn n(text: &str) -> Name {
    Name::from_components([text])
}
fn definition(name: &str, value: Expr) -> fln_env::constants::DefinitionVal {
    fln_env::constants::DefinitionVal {
        base: ConstantVal {
            name: n(name),
            level_params: vec![],
            type_: Expr::const_(n("Nat"), vec![]),
        },
        value,
        hints: ReducibilityHints::Regular(1),
        safety: DefinitionSafety::Safe,
        all: vec![n(name)],
    }
}
fn value(v: u64) -> Expr {
    Expr::lit(Literal::Nat(NatLit::from_u64(v)))
}
fn fixture() -> (ElaboratedPartial, Environment) {
    let declarations = vec![
        Declaration::Defn(definition("provider", value(41))),
        Declaration::Defn(definition("consumer", Expr::const_(n("provider"), vec![]))),
    ];
    let mut env = crate::seed::bootstrap_nat_environment(Budget::DEFAULT).unwrap();
    for declaration in &declarations {
        let Declaration::Defn(definition) = declaration else {
            unreachable!()
        };
        env = env
            .add_decl(ConstantInfo::Defn(definition.clone()))
            .unwrap();
    }
    (
        ElaboratedPartial {
            declarations,
            noncomputable: BTreeSet::from([n("provider")]),
            irreducible: BTreeSet::new(),
            scope: SourceScope {
                noncomputable_section: true,
                ..SourceScope::default()
            },
            budget: ElabBudget {
                heartbeats_consumed: 100,
                ..ElabBudget::default()
            },
            kernel: Budget::DEFAULT,
        },
        env,
    )
}

#[test]
fn deferred_effects_spend_the_original_remaining_heartbeat_allowance() {
    let (mut partial, env) = fixture();
    let before = env.clone();
    let expected = BTreeSet::from([n("provider"), n("consumer")]);
    assert_eq!(
        crate::noncomputable::read(&partial.record_codegen(&env).unwrap()).unwrap(),
        expected
    );
    let mut success = None;
    for allowance in partial.budget.heartbeats_consumed..2000 {
        partial.budget.max_heartbeats = allowance;
        match partial.record_codegen(&env) {
            Err(NatDefinitionElabError::Inference(SourceInferenceError::ResourceLimit)) => {}
            Ok(next) => {
                assert_eq!(crate::noncomputable::read(&next).unwrap(), expected);
                success = Some(allowance);
                break;
            }
            other => panic!("allowance {allowance}: {other:?}"),
        }
        assert_eq!(env, before);
        assert!(crate::noncomputable::read(&env).unwrap().is_empty());
    }
    assert!(
        success.is_some_and(|allowance| allowance > 105),
        "analysis must charge work beyond the first tag"
    );
}

#[test]
fn deferred_effects_reject_a_different_admitted_definition_even_after_an_earlier_tag() {
    let (partial, env) = fixture();
    let base = crate::seed::bootstrap_nat_environment(Budget::DEFAULT).unwrap();
    let Declaration::Defn(provider) = &partial.declarations[0] else {
        unreachable!()
    };
    let different = base
        .add_decl(ConstantInfo::Defn(provider.clone()))
        .unwrap()
        .add_decl(ConstantInfo::Defn(definition("consumer", value(7))))
        .unwrap();
    let before = different.clone();
    assert!(matches!(
        partial.record_codegen(&different),
        Err(NatDefinitionElabError::Inference(
            SourceInferenceError::Scope
        ))
    ));
    assert_eq!(different, before);
    assert!(crate::noncomputable::read(&different).unwrap().is_empty());
    assert!(
        partial.record_codegen(&env).is_ok(),
        "a failed successor is not cached"
    );
}

#[test]
fn directly_failed_units_still_validate_the_successor_metadata() {
    let (partial, env) = fixture();
    let tagged = crate::noncomputable::register(&env, &n("provider")).unwrap();
    let broken = tagged
        .push_extension_entry(&crate::noncomputable::journal_name(), b"broken".to_vec())
        .unwrap();
    let before = broken.clone();
    assert!(matches!(
        partial.record_codegen(&broken),
        Err(NatDefinitionElabError::Inference(
            SourceInferenceError::NoncomputableJournal(
                crate::noncomputable::NoncomputableError::Malformed
            )
        ))
    ));
    assert_eq!(broken, before);
}
