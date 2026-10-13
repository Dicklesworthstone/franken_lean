//! `guard_target` with each relation (`syntax (name := guardTarget) "guard_target " equal term :
//! tactic`, Init/Guard.lean:75; `evalGuardTarget`, Lean/Elab/Tactic/Guard.lean:99-110). Every
//! program here was run through the pinned `lean` v4.32.0 first (2026-10-11); a refusal is the
//! pin's "The main goal is … but was expected to be …".
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
fn each_relation_compares_the_main_goal_and_leaves_it() {
    for relation in ["=", "=~", "=ₛ", "=ₐ"] {
        let source = format!(
            "theorem a (p : Prop) (h : p) : p := by\n  guard_target {relation} p\n  exact h\n"
        );
        assert!(accepted(&source), "{source}");
        let source = format!(
            "theorem a (p q : Prop) (h : p) : p := by\n  guard_target {relation} q\n  exact h\n"
        );
        assert!(!accepted(&source), "{source}");
    }
    // After `intro`, the main goal is the new one.
    assert!(accepted(
        "theorem t (p q : Prop) (hq : q) : p → q := by\n  intro hp\n  guard_target = q\n  exact hq\n"
    ));
}

#[test]
fn transparency_and_syntax_decide_as_at_the_pin() {
    // `=` is reducible transparency: a plain definition does not unfold, an abbreviation does.
    assert!(!accepted(
        "def P : Prop := True\ntheorem t : P := by\n  guard_target = True\n  exact True.intro\n"
    ));
    assert!(accepted(
        "abbrev Q : Prop := True\ntheorem t : Q := by\n  guard_target = True\n  exact True.intro\n"
    ));
    // `=~` is default transparency: the definition unfolds.
    assert!(accepted(
        "def P : Prop := True\ntheorem t : P := by\n  guard_target =~ True\n  exact True.intro\n"
    ));
    // `=ₛ` unfolds nothing, and ignores binder names (`Expr.eqv`).
    assert!(!accepted(
        "def P : Prop := True\ntheorem t : P := by\n  guard_target =ₛ True\n  exact True.intro\n"
    ));
    assert!(accepted(
        "theorem t : ∀ x : Nat, x = x := by\n  guard_target =ₛ ∀ y : Nat, y = y\n  intro x\n  rfl\n"
    ));
    assert!(accepted(
        "theorem t (n : Nat) : n + 0 = n := by\n  guard_target =ₛ n + 0 = n\n  rfl\n"
    ));
    assert!(!accepted(
        "theorem t (n : Nat) : n + 0 = n := by\n  guard_target =ₛ n = n\n  rfl\n"
    ));
}
