//! `intros`, `rename_i`, `clear`, `specialize`, `replace`, `suffices`, `trivial` and `next`.
//! Every program here was run through the pinned `lean` v4.32.0 first (2026-10-21), with its full
//! `Init`: each traced goal is the pin's `trace_state` output verbatim, and each refusal is one
//! the pin makes, quoting its message where this engine words it the same.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap};

fn engine() -> Engine {
    Engine::with_source_seed(EngineAdmissionLimits::new(Budget::for_stack_bytes(
        2 * 1024 * 1024,
    )))
    .unwrap()
    .into_complete()
    .unwrap()
}

/// The traced goals of an accepted program, or the refusal's text.
fn run(source: &str) -> Result<Vec<String>, String> {
    match engine().execute_source_commands_with_checks(
        source.as_bytes(),
        &KVMap::new(),
        EngineExecutionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024)),
    ) {
        Ok(outcome) => Ok(outcome
            .into_complete()
            .unwrap()
            .traces
            .iter()
            .map(|row| row.message.clone())
            .collect()),
        Err(error) => Err(error.to_string()),
    }
}

fn traces(source: &str) -> Vec<String> {
    run(source).unwrap_or_else(|error| panic!("{source}\nrefused: {error}"))
}

fn refusal(source: &str) -> String {
    match run(source) {
        Ok(traces) => panic!("{source}\naccepted, traces {traces:?}"),
        Err(error) => error,
    }
}

#[test]
fn intros_and_rename_i_name_the_pins_inaccessible_hypotheses() {
    assert_eq!(
        traces(
            "example : ∀ (a b : Nat), a = b → a = b := by\n  intros\n  trace_state\n  rename_i x y h\n  trace_state\n  exact h\n"
        ),
        [
            "a✝¹ b✝ : Nat\na✝ : a✝¹ = b✝\n⊢ a✝¹ = b✝",
            "x y : Nat\nh : x = y\n⊢ x = y"
        ]
    );
    // A written name is kept and `_` stays inaccessible; `rename_i` then names only that one.
    assert_eq!(
        traces(
            "example : ∀ (a b : Nat), a = b → a = b := by\n  intros x _ h\n  trace_state\n  rename_i y\n  trace_state\n  exact h\n"
        ),
        [
            "x b✝ : Nat\nh : x = b✝\n⊢ x = b✝",
            "x y : Nat\nh : x = y\n⊢ x = y"
        ]
    );
    assert!(
        refusal("example : ∀ (a : Nat), a = a := by\n  intros\n  rename_i x y\n  rfl\n")
            .contains("too many variable names provided")
    );
}

#[test]
fn clear_removes_only_what_nothing_reads() {
    assert_eq!(
        traces(
            "example (p q : Prop) (hp : p) (hq : q) : p := by\n  clear hq\n  trace_state\n  exact hp\n"
        ),
        ["p q : Prop\nhp : p\n⊢ p"]
    );
    assert!(
        refusal("example (n : Nat) (h : n = n) : True := by\n  clear n\n  trivial\n")
            .contains("Tactic `clear` failed: variable 'h' depends on 'n'")
    );
    // The latest goes first: `h` leaves, then `n` is still read by the target.
    assert!(
        refusal("example (n : Nat) (h : 0 = n) : n = n := by\n  clear h n\n  rfl\n")
            .contains("Tactic `clear` failed: target depends on 'n'")
    );
    assert!(
        refusal("example (p : Prop) (hp : p) : p := by\n  clear hp\n  exact hp\n")
            .contains("Unknown identifier `hp`")
    );
}

#[test]
fn specialize_replaces_its_hypothesis_where_it_stood() {
    assert_eq!(
        traces(
            "example (f : Nat → Nat) (h : ∀ x, f x = x) (k : Nat) : f 2 = 2 := by\n  specialize h 2\n  trace_state\n  exact h\n"
        ),
        ["f : Nat → Nat\nh : f 2 = 2\nk : Nat\n⊢ f 2 = 2"]
    );
    // The new type reads `k`, so the hypothesis moves after it.
    assert_eq!(
        traces(
            "example (f : Nat → Nat) (h : ∀ x, f x = x) (k : Nat) : f k = k := by\n  specialize h k\n  trace_state\n  exact h\n"
        ),
        ["f : Nat → Nat\nk : Nat\nh : f k = k\n⊢ f k = k"]
    );
    assert!(
        refusal("example (p : Prop) (hp : p) : p := by\n  specialize Eq.refl 1\n  exact hp\n")
            .contains("'specialize' requires a term of the form `h x_1 .. x_n` where `h` appears in the local context")
    );
}

#[test]
fn replace_appends_and_clears_what_it_supersedes() {
    assert_eq!(
        traces(
            "example (p q : Prop) (hp : p) (hpq : p → q) : q := by\n  replace hp : q := hpq hp\n  trace_state\n  exact hp\n"
        ),
        ["p q : Prop\nhpq : p → q\nhp : q\n⊢ q"]
    );
    // `h` still reads the old `n`, which therefore stays, shadowed.
    assert_eq!(
        traces(
            "example (n : Nat) (h : n = n) : True := by\n  replace n : Nat := 3\n  trace_state\n  trivial\n"
        ),
        ["n✝ : Nat\nh : n✝ = n✝\nn : Nat\n⊢ True"]
    );
}

#[test]
fn suffices_makes_the_stated_fact_the_main_goal() {
    for source in [
        "example (p q : Prop) (hp : p) (hpq : p → q) : q := by\n  suffices h : p by exact hpq h\n  trace_state\n  exact hp\n",
        "example (p q : Prop) (hp : p) (hpq : p → q) : q := by\n  suffices p from hpq this\n  trace_state\n  exact hp\n",
    ] {
        assert_eq!(
            traces(source),
            ["p q : Prop\nhp : p\nhpq : p → q\n⊢ p"],
            "{source}"
        );
    }
}

#[test]
fn trivial_tries_the_pins_expansions_until_one_closes_the_goal() {
    for source in [
        // `apply And.intro <;> trivial`, then `apply True.intro` and `rfl` on the conjuncts.
        "example : True ∧ 2 = 2 := by trivial\n",
        // `contradiction`.
        "example (h : False) : 1 = 2 := by trivial\n",
        // `assumption`.
        "example (p : Prop) (h : p) : p := by trivial\n",
        // Splitting fails on `p`, is undone, and `assumption` closes the conjunction whole.
        "example (p q : Prop) (h : p ∧ q) : p ∧ q := by trivial\n",
    ] {
        traces(source);
    }
    refusal("example (p : Prop) : p := by trivial\n");
}

#[test]
fn next_focuses_on_the_main_goal_and_must_close_it() {
    traces(
        "example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by\n  constructor\n  next => exact hp\n  next => exact hq\n",
    );
    assert_eq!(
        traces(
            "example : ∀ (a : Nat), a = a := by\n  intro\n  next x =>\n    trace_state\n    rfl\n"
        ),
        ["x : Nat\n⊢ x = x"]
    );
    // The pin: "unsolved goals" at `next`.
    refusal(
        "example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by\n  constructor\n  next => skip\n  exact hq\n",
    );
}
