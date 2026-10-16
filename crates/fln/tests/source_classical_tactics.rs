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
