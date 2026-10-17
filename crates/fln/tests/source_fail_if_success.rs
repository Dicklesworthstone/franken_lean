//! `fail_if_success t` (`syntax (name := failIfSuccess) "fail_if_success " tacticSeq : tactic`,
//! Init/Tactics.lean:345; `evalFailIfSuccess`, Lean/Elab/Tactic/BuiltinTactic.lean:273-277): it
//! succeeds, leaving the goals as they were, exactly when `t` fails. Every program here was run
//! through the pinned `lean` v4.32.0 first (2026-10-11).
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, Outcome, SourceCheckLimits};

fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}
fn engine() -> Engine {
    Engine::with_source_seed(limits())
        .unwrap()
        .into_complete()
        .unwrap()
}
fn accepted(source: &str) -> bool {
    matches!(
        engine().check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits())
        ),
        Ok(Outcome::Complete(_))
    )
}

#[test]
fn it_succeeds_exactly_when_its_tactic_fails() {
    for source in [
        "theorem t (p : Prop) (h : p) : p := by\n  fail_if_success exact True.intro\n  exact h\n",
        "theorem t (p : Prop) (h : p) : p := by\n  fail_if_success\n    exact True.intro\n  exact h\n",
        "theorem t (p : Prop) (h : p) : p := by\n  fail_if_success fail\n  exact h\n",
        // The goals are as they were: the failed `exact hp` changed nothing.
        "theorem t (p q : Prop) (hp : p) (hq : q) : p ∧ q := by\n  fail_if_success exact hp\n  constructor\n  exact hp\n  exact hq\n",
        // Its own failure is an ordinary tactic failure, which `first` catches.
        "theorem t (p : Prop) (h : p) : p := by\n  first | fail_if_success exact h | exact h\n",
    ] {
        assert!(accepted(source), "{source}");
    }
    for source in [
        "theorem t (p : Prop) (h : p) : p := by\n  fail_if_success exact h\n  exact h\n",
        "theorem t (p : Prop) (h : p) : p := by\n  fail_if_success skip\n  exact h\n",
        // A failing `t` closes nothing.
        "theorem t (p : Prop) (h : p) : p := by\n  fail_if_success exact True.intro\n",
    ] {
        assert!(!accepted(source), "{source}");
    }
}
