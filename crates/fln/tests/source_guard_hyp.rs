//! Native hypothesis guards through parsing, elaboration, and ordinary admission.
//! Expected behavior follows the pinned Init/Guard.lean and
//! Lean/Elab/Tactic/Guard.lean. These are regression cases, not a record that the
//! pinned Reference was executed when this file was authored.
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

fn accepted(source: &str) {
    let result = engine().check_source_files(
        &[source.as_bytes()],
        &KVMap::new(),
        SourceCheckLimits::new(limits()),
    );
    match result {
        Ok(Outcome::Complete(_)) => {}
        Err(error) => panic!("expected admission:\n{source}\n{error:?}"),
        Ok(_) => panic!("expected completed admission, not a nonanswer:\n{source}"),
    }
}

fn refused_by_guard(source: &str, reason: &str) {
    let result = engine().check_source_files(
        &[source.as_bytes()],
        &KVMap::new(),
        SourceCheckLimits::new(limits()),
    );
    match result {
        Err(error) => assert!(
            format!("{error:?}").contains(reason),
            "expected {reason}, not a parser or unrelated failure:\n{source}\n{error:?}"
        ),
        Ok(_) => panic!("expected a completed guard refusal, not admission/nonanswer:\n{source}"),
    }
}

#[test]
fn all_type_relations_check_the_hypothesis_without_solving_the_goal() {
    for relation in [":", ":~", ":ₛ", ":ₐ"] {
        accepted(&format!(
            "theorem t (p : Prop) (h : p) : p := by\n  guard_hyp h {relation} p\n  exact h\n"
        ));
        refused_by_guard(
            &format!(
                "theorem t (p q : Prop) (h : p) : p := by\n  guard_hyp h {relation} q\n  exact h\n"
            ),
            "GuardHypTypeMismatch",
        );
    }
    accepted("theorem t (p : Prop) (h : p) : p := by\n  guard_hyp h\n  exact h\n");
    refused_by_guard(
        "theorem t (p : Prop) (h : p) : p := by\n  guard_hyp h : p\n",
        "UnsolvedGoals",
    );
}

#[test]
fn every_value_relation_checks_the_value_and_uses_its_expected_type() {
    for relation in [":=", ":=~", ":=ₛ", ":=ₐ"] {
        for annotation in ["", " : Nat"] {
            accepted(&format!(
                "theorem t : True := by\n  let n : Nat := 7\n  guard_hyp n{annotation} {relation} 7\n  exact True.intro\n"
            ));
            refused_by_guard(
                &format!(
                    "theorem t : True := by\n  let n : Nat := 7\n  guard_hyp n{annotation} {relation} 8\n  exact True.intro\n"
                ),
                "GuardHypValueMismatch",
            );
        }
    }
}

#[test]
fn parameters_are_not_let_bindings_and_lets_require_a_value_clause() {
    refused_by_guard(
        "theorem t (n : Nat) : True := by\n  guard_hyp n := 7\n  exact True.intro\n",
        "GuardHypNotLet",
    );
    for annotation in ["", " : Nat"] {
        refused_by_guard(
            &format!(
                "theorem t : True := by\n  let n : Nat := 7\n  guard_hyp n{annotation}\n  exact True.intro\n"
            ),
            "GuardHypMissingValue",
        );
    }
}

#[test]
fn transparency_is_not_silently_strengthened() {
    refused_by_guard(
        "def P : Prop := True\ntheorem t (h : P) : P := by\n  guard_hyp h : True\n  exact h\n",
        "GuardHypTypeMismatch",
    );
    accepted(
        "def P : Prop := True\ntheorem t (h : P) : P := by\n  guard_hyp h :~ True\n  exact h\n",
    );
    accepted(
        "abbrev P : Prop := True\ntheorem t (h : P) : P := by\n  guard_hyp h : True\n  exact h\n",
    );
    refused_by_guard(
        "def P : Prop := True\ntheorem t (h : P) : P := by\n  guard_hyp h :ₛ True\n  exact h\n",
        "GuardHypTypeMismatch",
    );
}

#[test]
fn parenthesized_subjects_nested_terms_and_shadowing_use_local_identity() {
    accepted(
        "theorem t (n : Nat) : True := by\n  let n : Bool := true\n  guard_hyp (n) : Bool := true\n  exact True.intro\n",
    );
    accepted(
        "theorem t : True := by\n  let f : Nat → Nat := fun x => x\n  guard_hyp f : (Nat → Nat) :=ₐ (fun y => y)\n  exact True.intro\n",
    );
    accepted("theorem t (p : Prop) : p → p := by\n  intro h\n  guard_hyp h : p\n  exact h\n");
    refused_by_guard(
        "theorem t : True := by\n  guard_hyp True\n  exact True.intro\n",
        "GuardHypExpectedLocal",
    );
}

#[test]
fn unsuccessful_guards_backtrack_without_discarding_the_original_context() {
    accepted(
        "theorem t (p q : Prop) (h : p) : p := by\n  first\n  | guard_hyp h : q\n    exact h\n  | guard_hyp h : p\n    exact h\n",
    );
    accepted(
        "theorem t : True := by\n  let n : Nat := 7\n  first\n  | guard_hyp n := 8\n    exact True.intro\n  | guard_hyp n : Nat := 7\n    exact True.intro\n",
    );
}

#[test]
fn guards_do_not_change_goal_order_or_allow_execution_after_completion() {
    accepted(
        "theorem t (p q : Prop) (hp : p) (hq : q) : p ∧ q := by\n  constructor\n  · guard_hyp hp : p\n    exact hp\n  · guard_hyp hq : q\n    exact hq\n",
    );
    refused_by_guard(
        "theorem t (p : Prop) (h : p) : p := by\n  exact h\n  guard_hyp h : p\n",
        "NoGoals",
    );
}
