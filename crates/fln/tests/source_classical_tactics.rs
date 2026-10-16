//! Classical tactic scopes select admitted dictionaries, never install axioms.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, SourceCheckLimits};

const SCOPED_DECISION: &str = r#"
inductive ChoiceP : Prop where | intro
namespace Classical
scoped instance choicePDecision : Decidable ChoiceP := Decidable.isTrue ChoiceP.intro
end Classical
"#;

fn limits() -> SourceCheckLimits {
    SourceCheckLimits::new(EngineAdmissionLimits::new(Budget::for_stack_bytes(
        2 * 1024 * 1024,
    )))
}

fn base() -> Engine {
    Engine::with_source_seed(limits().admission)
        .unwrap()
        .into_complete()
        .unwrap()
        .check_source_files(&[SCOPED_DECISION.as_bytes()], &KVMap::new(), limits())
        .unwrap()
        .into_complete()
        .unwrap()
        .engine
}

fn check(engine: &Engine, source: &str) {
    engine
        .check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .unwrap();
}

#[test]
fn by_cases_activates_admitted_classical_scoped_decisions() {
    check(
        &base(),
        r#"
        theorem classicalSplit : ChoiceP := by
          by_cases h : ChoiceP
          · exact h
          · exact ChoiceP.intro
        def branchValue : Nat := by
          by_cases h : ChoiceP
          · exact 31
          · exact 47
        theorem computed : branchValue = 31 := by rfl
        theorem unnamed : ChoiceP := by
          by_cases ChoiceP
          · assumption
          · exact ChoiceP.intro
        "#,
    );
}

#[test]
fn by_cases_scope_ends_before_either_branch_and_after_failed_attempts() {
    check(
        &base(),
        r#"
        theorem scopeBoundaries : ChoiceP := by
          by_cases h : ChoiceP
          · fail_if_success (have d : Decidable ChoiceP := by infer_instance)
            exact h
          · fail_if_success (have d : Decidable ChoiceP := by infer_instance)
            exact ChoiceP.intro
        theorem restored : ChoiceP := by
          first | (by_cases h : ChoiceP; exact h; fail) | skip
          fail_if_success (have d : Decidable ChoiceP := by infer_instance)
          exact ChoiceP.intro
        theorem nextCommand : ChoiceP := by
          fail_if_success (have d : Decidable ChoiceP := by infer_instance)
          exact ChoiceP.intro
        "#,
    );
}

#[test]
fn by_cases_does_not_invent_instances_or_discard_bad_branches() {
    let engine = base();
    let root = engine.logical_root(&KVMap::new());
    for source in [
        "theorem bad (p : Prop) : True := by by_cases h : p <;> exact True.intro",
        "theorem bad : True := by by_cases h : Nat <;> exact True.intro",
        "theorem bad : False := by by_cases h : ChoiceP <;> exact h",
        "def bad : Nat := by by_cases h : ChoiceP; exact 31; exact (1 : String)",
        "theorem bad : ChoiceP := by decide",
    ] {
        assert!(
            engine
                .check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
                .is_err(),
            "accepted: {source}"
        );
        assert_eq!(engine.logical_root(&KVMap::new()), root);
    }
    check(
        &engine,
        "theorem recovered : ChoiceP := by by_cases h : ChoiceP <;> exact ChoiceP.intro",
    );
}

// This checked, monomorphic dictionary exercises the scope without importing
// classical axioms. The same fixture runs at the pin after `import Init.Core`,
// where the name is still available. The tactic must register the declaration
// it finds, exactly as Meta.addInstance does, rather than inventing its body.
const CLASSICAL_DECLARATION: &str = r#"
abbrev Classical.propDecidable : Decidable ChoiceP := Decidable.isTrue ChoiceP.intro
inductive ChoiceQ : Prop where | intro
namespace Classical
scoped instance choiceQDecision : Decidable ChoiceQ := Decidable.isTrue ChoiceQ.intro
end Classical
"#;

fn classical_base() -> Engine {
    base()
        .check_source_files(&[CLASSICAL_DECLARATION.as_bytes()], &KVMap::new(), limits())
        .unwrap()
        .into_complete()
        .unwrap()
        .engine
}

#[test]
fn classical_runs_nested_bodies_and_the_whole_visible_frontier() {
    check(
        &classical_base(),
        r#"
        theorem nativeChoice : ChoiceP := by classical decide
        theorem nestedChoice : ChoiceP := by
          classical
          have witness : ChoiceP := by classical decide
          exact witness
        inductive ChoiceBoth (p q : Prop) : Prop where | intro (left : p) (right : q)
        theorem frontier : ChoiceBoth ChoiceP ChoiceP := by
          constructor
          classical all_goals decide
        theorem noGoals : ChoiceP := by
          exact ChoiceP.intro
          classical skip
        theorem returnedGoal : ChoiceP := by
          (classical skip)
          fail_if_success (have d : Decidable ChoiceP := by infer_instance)
          exact ChoiceP.intro
        "#,
    );
}

#[test]
fn classical_restores_siblings_backtracking_and_nested_option_scopes() {
    check(
        &classical_base(),
        r#"
        inductive ChoiceBoth (p q : Prop) : Prop where | intro (left : p) (right : q)
        theorem siblings : ChoiceBoth ChoiceP ChoiceP := by
          constructor
          · classical decide
          · fail_if_success (have d : Decidable ChoiceP := by infer_instance)
            exact ChoiceP.intro
        theorem failedAttempt : ChoiceP := by
          first | (classical fail) | skip
          fail_if_success (have d : Decidable ChoiceP := by infer_instance)
          exact ChoiceP.intro
        theorem optionsInside : ChoiceP := by
          classical
          set_option maxRecDepth 1024 in decide
        theorem optionsOutside : ChoiceP := by
          set_option maxRecDepth 1024 in classical decide
        theorem nextDeclaration : ChoiceP := by
          fail_if_success (have d : Decidable ChoiceP := by infer_instance)
          exact ChoiceP.intro
        "#,
    );
}

#[test]
fn classical_registers_only_the_selected_declaration_without_opening_namespace() {
    check(
        &classical_base(),
        r#"
        theorem onlySelected : ChoiceP := by
          classical
          fail_if_success (have d : Decidable ChoiceQ := by infer_instance)
          fail_if_success (have d : Decidable ChoiceP := propDecidable)
          decide
        "#,
    );
    let engine = classical_base();
    let root = engine.logical_root(&KVMap::new());
    for source in [
        "theorem noProof : False := by classical exact ChoiceP.intro",
        "theorem noOtherDecision : ChoiceQ := by classical decide",
        "theorem unfinished : ChoiceP := by classical skip",
    ] {
        assert!(
            engine
                .check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
                .is_err(),
            "accepted: {source}"
        );
        assert_eq!(engine.logical_root(&KVMap::new()), root);
    }
    assert!(
        base()
            .check_source_files(
                &[b"theorem missingProvider : ChoiceP := by classical exact ChoiceP.intro"],
                &KVMap::new(),
                limits()
            )
            .is_err()
    );
}

#[test]
fn classical_uses_priority_ten_and_restores_existing_registration() {
    let seed = Engine::with_source_seed(limits().admission)
        .unwrap()
        .into_complete()
        .unwrap();
    // A data class makes candidate selection observable without asserting
    // different proofs of the same proposition. The pin accepts this fixture.
    check(
        &seed,
        r#"
        class ScopePick where
          value : Nat
        abbrev Classical.propDecidable : ScopePick := ScopePick.mk 17
        instance (priority := 1) lowerPick : ScopePick := ScopePick.mk 5
        def chosenPick [p : ScopePick] : Nat := p.value
        def insidePick : Nat := by classical exact chosenPick
        def outsidePick : Nat := chosenPick
        theorem insideTen : insidePick = 17 := by rfl
        theorem outsideOne : outsidePick = 5 := by rfl
        instance (priority := 20) higherPick : ScopePick := ScopePick.mk 23
        def higherWinner : Nat := by classical exact chosenPick
        theorem higherWins : higherWinner = 23 := by rfl
        attribute [instance 1000] Classical.propDecidable
        def originalWinner : Nat := chosenPick
        def loweredWinner : Nat := by classical exact chosenPick
        def restoredWinner : Nat := chosenPick
        theorem originalPriority : originalWinner = 17 := by rfl
        theorem localPriority : loweredWinner = 23 := by rfl
        theorem restoredPriority : restoredWinner = 17 := by rfl
        "#,
    );
}

#[test]
fn classical_resource_stops_are_not_caught_as_success() {
    let engine = classical_base();
    let root = engine.logical_root(&KVMap::new());
    let source = b"theorem limitedChoice : ChoiceP := by try (classical decide)";
    let mut low = limits();
    low.admission.kernel = low.admission.kernel.narrowed(0, 32);
    match engine.check_source_files(&[source], &KVMap::new(), low) {
        Ok(fln::Outcome::Inconclusive(_)) => {}
        Err(error) => assert!(
            matches!(error.disposition(), ("resource" | "inconclusive", false, 3)),
            "{error:?}"
        ),
        other => panic!("resource exhaustion became an answer: {other:?}"),
    }
    assert_eq!(engine.logical_root(&KVMap::new()), root);
    check(&engine, std::str::from_utf8(source).unwrap());
}

#[test]
fn a_missing_classical_provider_is_an_ordinary_recoverable_elaboration_error() {
    check(
        &base(),
        "theorem missingProviderFallback : ChoiceP := by first | (classical exact ChoiceP.intro) | exact ChoiceP.intro",
    );
}
