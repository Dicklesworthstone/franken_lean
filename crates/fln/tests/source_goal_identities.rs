//! Inspection preserves actual obligation identities without admitting the declaration.
#![forbid(unsafe_code)]
use fln::source_check::inspect::{ObservationKind, ObservedGoal, SourceObservation};
use fln::source_check::modules::{
    SourceModuleCacheLimits, SourceModuleCheckLimits, SourceModuleSession,
};
use fln::{
    Budget, Engine, EngineAdmissionLimits, KVMap, Name, SourceCheckLimits, SourceModuleInput,
};

fn observe(source: &str, offset: usize, kind: ObservationKind) -> Vec<ObservedGoal> {
    let admission = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let engine = Engine::with_source_seed(admission)
        .unwrap()
        .into_complete()
        .unwrap();
    let mut session = SourceModuleSession::new(
        engine,
        KVMap::new(),
        SourceModuleCheckLimits::new(SourceCheckLimits::new(admission)),
        SourceModuleCacheLimits::default(),
    );
    let module = Name::from_components(["Main"]);
    let result = session
        .inspect(
            &[SourceModuleInput {
                name: &module,
                source: source.as_bytes(),
            }],
            &module,
            offset,
            kind,
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert!(
        !result
            .prefix
            .checked
            .checked
            .engine
            .environment()
            .contains(&Name::from_components(["pending"]))
    );
    let Some(SourceObservation::Goals { goals, .. }) = result.observation else {
        panic!("missing native goals")
    };
    goals
}

#[test]
fn sibling_obligations_have_distinct_ids_and_closing_one_preserves_the_other() {
    let source = "theorem pending (P Q : Prop) (h : P) (k : Q) : And P Q := by\n  constructor\n  exact h\n  exact k";
    let before = observe(
        source,
        source.find("exact h").unwrap(),
        ObservationKind::Goals,
    );
    assert_eq!(before.len(), 2);
    assert!(before.iter().all(|goal| goal.id.is_some()));
    assert_ne!(before[0].id, before[1].id);
    let after = observe(
        source,
        source.find("exact k").unwrap(),
        ObservationKind::Goals,
    );
    assert_eq!(after.len(), 1);
    assert_eq!(before[1].id, after[0].id);
    assert_eq!(before[1].target, after[0].target);
}

#[test]
fn inferred_term_types_do_not_fabricate_tactic_obligations() {
    let source = "def pending (A : Type) (x : A) : A := x";
    let found = observe(source, source.len() - 1, ObservationKind::TermGoal);
    assert_eq!(found.len(), 1);
    assert!(found[0].id.is_none());
    assert_eq!(
        found[0]
            .locals
            .find_by_user_name(&Name::from_components(["x"]))
            .unwrap()
            .type_,
        found[0].target
    );
    let source = "theorem pending (P : Prop) : P := by";
    let found = observe(
        source,
        source.find("by").unwrap(),
        ObservationKind::TermGoal,
    );
    assert!(found[0].id.is_some());
}
