//! Ordered quoted macro selection crosses the ordinary two-checker source door.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, SourceCheckLimits};

fn check(source: &str) -> Result<usize, String> {
    let admission = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let engine = Engine::with_source_seed(admission)
        .unwrap()
        .into_complete()
        .unwrap();
    engine
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(admission),
        )
        .map_err(|error| format!("{error:?}"))
        .map(|outcome| outcome.into_complete().unwrap().theorems)
}

#[test]
fn clauses_select_the_first_match_in_source_order() {
    let source = r#"
syntax "classify! " term:max : term
macro_rules
  | `(classify! 0) => `((10 : Nat))
  | `(classify! $x) => `(Nat.add $x 1)
theorem a : classify! 0 = 10 := rfl
theorem b : classify! 6 = 7 := rfl
"#;
    assert_eq!(check(source).unwrap(), 2);
    assert!(check(&source.replace("classify! 0 = 10", "classify! 0 = 1")).is_err());
}

#[test]
fn newer_registrations_fall_back_to_older_patterns() {
    let source = r#"
syntax "select! " term:max : term
macro_rules | `(select! $x) => `(Nat.add $x 3)
macro_rules | `(select! 0) => `((20 : Nat))
macro_rules | `(select! 1) => `((30 : Nat))
theorem a : select! 0 = 20 := rfl
theorem b : select! 1 = 30 := rfl
theorem c : select! 4 = 7 := rfl
"#;
    assert_eq!(check(source).unwrap(), 3);
    assert!(check(&source.replace("select! 1 = 30", "select! 1 = 4")).is_err());
}

#[test]
fn alternatives_can_target_different_declared_kinds() {
    let source = r#"
syntax "left! " term:max : term
syntax "right! " term:max : term
macro_rules
  | `(left! $x) => `($x)
  | `(right! $x) => `(Nat.succ $x)
theorem a : left! 4 = (4 : Nat) := rfl
theorem b : right! 4 = (5 : Nat) := rfl
"#;
    assert_eq!(check(source).unwrap(), 2);
}

#[test]
fn nested_patterns_and_wildcards_fall_through_without_losing_bindings() {
    let source = r#"
syntax "pick! " term:max : term
macro_rules
  | `(pick! (Nat.add 0 $y)) => `($y)
  | `(pick! (Nat.add $x $_)) => `($x)
  | `(pick! $_) => `((99 : Nat))
theorem a : pick! (Nat.add 0 8) = (8 : Nat) := rfl
theorem b : pick! (Nat.add 7 8) = (7 : Nat) := rfl
theorem c : pick! (Nat.mul 7 8) = (99 : Nat) := rfl
"#;
    assert_eq!(check(source).unwrap(), 3);
}

#[test]
fn older_templates_keep_their_original_definition_scope() {
    let source = r#"
namespace Original
def offset : Nat := 10
syntax "scoped! " term:max : term
macro_rules | `(scoped! $x) => `(Nat.add $x offset)
end Original
namespace Later
def offset : Nat := 90
macro_rules | `(scoped! 0) => `((17 : Nat))
end Later
theorem a : scoped! 1 = 11 := rfl
theorem b : scoped! 0 = 17 := rfl
"#;
    assert_eq!(check(source).unwrap(), 2);
    assert!(check(&source.replace("scoped! 1 = 11", "scoped! 1 = 91")).is_err());
}

#[test]
fn an_unsupported_registration_blocks_older_successes() {
    let prefix =
        "syntax \"blocked! \" term:max : term\nmacro_rules | `(blocked! $x) => `((8 : Nat))\n";
    for newer in [
        "macro_rules | `(blocked! $x) => do pure `((9 : Nat))\n",
        "macro_rules\n | `(blocked! 0) => `((8 : Nat))\n | `(blocked! $x) => do pure `((9 : Nat))\n",
    ] {
        let source = format!("{prefix}{newer}theorem t : blocked! 0 = 8 := rfl\n");
        assert!(
            check(&source).is_err(),
            "unsupported code must not select an older meaning"
        );
    }
}

#[test]
fn a_matching_but_invalid_expansion_is_not_a_pattern_mismatch() {
    let source = r#"
syntax "typed! " term:max : term
macro_rules | `(typed! $x) => `((8 : Nat))
macro_rules | `(typed! 0) => `((true : Nat))
theorem t : typed! 0 = 8 := rfl
"#;
    assert!(check(source).is_err());
}

#[test]
fn an_explicit_registered_kind_obeys_the_same_clause_order() {
    let source = r#"
syntax (name := chooseKind) "named! " term:max : term
macro_rules (kind := chooseKind)
  | `(named! 0) => `((10 : Nat))
  | `(named! $x) => `($x)
theorem a : named! 0 = (10 : Nat) := rfl
theorem b : named! 4 = (4 : Nat) := rfl
"#;
    assert_eq!(check(source).unwrap(), 2);
}

#[test]
fn no_matching_case_remains_a_refusal() {
    let source = r#"
syntax "limited! " term:max : term
macro_rules
  | `(limited! 0) => `((10 : Nat))
  | `(limited! 1) => `((11 : Nat))
theorem t : limited! 2 = 11 := rfl
"#;
    assert!(check(source).is_err());
}
