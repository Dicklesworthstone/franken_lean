//! Operand-type retry must still produce a proof accepted by both checkers.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, Outcome, SourceCheckLimits};

fn check(source: &str) -> Result<Outcome<fln::SourceFileCheck>, fln::source_check::SourceCheckError> {
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    Engine::with_source_seed(limits)
        .unwrap()
        .into_complete()
        .unwrap()
        .check_source_files(&[source.as_bytes()], &KVMap::new(), SourceCheckLimits::new(limits))
}

#[test]
fn already_rewritten_local_operands_can_be_transported_in_both_directions() {
    for source in [
        "theorem t (P : Nat → Prop) (a b : Nat) (h : a = b) (hp : P b) : P b := h ▸ hp",
        "theorem t (P : Nat → Prop) (a b : Nat) (h : a = b) (hp : P a) : P a := h ▸ hp",
        "theorem t (P : Nat → Prop) (a b : Nat) (h : a = b) (hp : P b) : P b := h ▸ (hp)",
    ] {
        let result = check(source);
        assert!(matches!(result, Ok(Outcome::Complete(_))), "{source}: {result:?}");
    }
}

#[test]
fn retry_rewrites_the_operand_type_not_just_its_outer_constructor() {
    for source in [
        "theorem t (P : Nat → Nat → Prop) (a b : Nat) (h : a = b) (hp : P a b) : P b a := h ▸ hp",
        "theorem t (P : Nat → Nat → Prop) (a b : Nat) (h : a = b) (hp : P a b) : P b a := h ▸ (hp : P a b)",
        "theorem t (P : Nat → Nat → Prop) (a b : Nat) (h : a = b) (hp : (n : Nat) → P b n) : (n : Nat) → P b n := h ▸ hp",
    ] {
        let result = check(source);
        assert!(matches!(result, Ok(Outcome::Complete(_))), "{source}: {result:?}");
    }
}

#[test]
fn annotated_applications_have_an_independent_operand_type() {
    let source = "theorem t (P : Nat → Prop) (a b : Nat) (h : a = b) (hp : Nat → P b) : P b := h ▸ (hp 0 : P b)";
    let result = check(source);
    assert!(matches!(result, Ok(Outcome::Complete(_))), "{result:?}");
}

#[test]
fn ordinary_contextual_operands_keep_their_expected_type() {
    for source in [
        "theorem t (a b : Nat) (h : a = b) : b = b := h ▸ rfl",
        "theorem t (P : Nat → Prop) (a b : Nat) (h : a = b) (hp : P a) : P b := h ▸ hp",
    ] {
        let result = check(source);
        assert!(matches!(result, Ok(Outcome::Complete(_))), "{source}: {result:?}");
    }
}

#[test]
fn an_unrelated_operand_or_invalid_annotation_cannot_be_rescued() {
    for source in [
        "theorem bad (P Q : Nat → Prop) (a b : Nat) (h : a = b) (hp : Q b) : P b := h ▸ hp",
        "theorem bad (P : Nat → Prop) (a b c : Nat) (h : a = b) (hp : P c) : P b := h ▸ hp",
        "theorem bad (P Q : Nat → Prop) (a b : Nat) (h : a = b) (hp : Q b) : P b := h ▸ (hp : P b)",
        "theorem bad (a b : Nat) (h : a = b) : b = b := h ▸ missing",
    ] {
        assert!(check(source).is_err(), "invalid source was admitted: {source}");
    }
}

#[test]
fn a_failed_retry_does_not_poison_tactic_backtracking() {
    let source = "theorem t (P Q : Nat → Prop) (a b : Nat) (h : a = b) (bad : Q b) (good : P b) : P b := by first | exact h ▸ bad | exact h ▸ good";
    let result = check(source);
    assert!(matches!(result, Ok(Outcome::Complete(_))), "{result:?}");
}

#[test]
fn direct_and_retried_casts_preserve_read_only_editor_observations() {
    use fln::source_check::inspect::{ObservationKind, SourceObservation};
    use fln::source_check::modules::{
        SourceModuleCacheLimits, SourceModuleCheckLimits, SourceModuleSession,
    };
    use fln::{Name, SourceModuleInput};

    for source in [
        "theorem pending (P : Nat → Prop) (a b : Nat) (h : a = b) (hp : P a) : P b := h ▸ hp",
        "theorem pending (P : Nat → Prop) (a b : Nat) (h : a = b) (hp : P b) : P b := h ▸ hp",
        "theorem pending (P : Nat → Prop) (a b : Nat) (h : a = b) (hp : P b) : P b := h ▸ (hp : P b)",
    ] {
        for kind in [ObservationKind::Term, ObservationKind::TermGoal] {
            let admission = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
            let base = Engine::with_source_seed(admission).unwrap().into_complete().unwrap();
            let mut session = SourceModuleSession::new(
                base,
                KVMap::new(),
                SourceModuleCheckLimits::new(SourceCheckLimits::new(admission)),
                SourceModuleCacheLimits::default(),
            );
            let name = Name::from_components(["Main"]);
            let result = session.inspect(
                &[SourceModuleInput { name: &name, source: source.as_bytes() }],
                &name,
                source.rfind("hp").unwrap(),
                kind,
            ).unwrap_or_else(|error| panic!("{source}: {error:?}"))
                .into_complete().unwrap();
            assert!(!result.prefix.checked.checked.engine.environment()
                .contains(&Name::from_components(["pending"])));
            match result.observation {
                Some(SourceObservation::Term { type_, locals, range, .. }) => {
                    assert_eq!(&source[range], "hp");
                    assert_eq!(type_, locals.find_by_user_name(&Name::from_components(["hp"])).unwrap().type_);
                }
                Some(SourceObservation::Goals { goals, range }) => {
                    assert_eq!(&source[range], "hp");
                    assert_eq!(goals.len(), 1);
                    assert_eq!(goals[0].target, goals[0].locals.find_by_user_name(&Name::from_components(["hp"])).unwrap().type_);
                }
                None => panic!("cast trial discarded its observation: {source}"),
            }
        }
    }
}
