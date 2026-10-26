//! Explicit quotation capture kinds choose clauses, not just capture names.
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
        .map(|result| result.into_complete().unwrap().theorems)
}

#[test]
fn numeric_captures_do_not_match_identifiers_or_parenthesized_terms() {
    let source = r#"
syntax "numeric! " term:max : term
macro_rules
  | `(numeric! $x:num) => `((10 : Nat))
  | `(numeric! $_) => `((20 : Nat))
theorem a : numeric! 4 = (10 : Nat) := rfl
theorem b : numeric! Nat.zero = (20 : Nat) := rfl
theorem c : numeric! (4) = (20 : Nat) := rfl
"#;
    assert_eq!(check(source).unwrap(), 3);
    assert!(check(&source.replace("numeric! Nat.zero = (20", "numeric! Nat.zero = (10")).is_err());
}

#[test]
fn identifier_captures_do_not_match_numeric_or_string_literals() {
    let source = r#"
syntax "identifier! " term:max : term
macro_rules
  | `(identifier! $x:ident) => `((10 : Nat))
  | `(identifier! $_) => `((20 : Nat))
theorem a : identifier! Nat.zero = (10 : Nat) := rfl
theorem b : identifier! 4 = (20 : Nat) := rfl
theorem c : identifier! "value" = (20 : Nat) := rfl
"#;
    assert_eq!(check(source).unwrap(), 3);
    assert!(check(&source.replace("identifier! 4 = (20", "identifier! 4 = (10")).is_err());
}

#[test]
fn string_captures_do_not_match_identifiers_or_numeric_literals() {
    let source = r#"
syntax "stringKind! " term:max : term
macro_rules
  | `(stringKind! $x:str) => `((10 : Nat))
  | `(stringKind! $_) => `((20 : Nat))
theorem a : stringKind! "value" = (10 : Nat) := rfl
theorem b : stringKind! Nat.zero = (20 : Nat) := rfl
theorem c : stringKind! 4 = (20 : Nat) := rfl
"#;
    assert_eq!(check(source).unwrap(), 3);
    assert!(check(&source.replace("stringKind! 4 = (20", "stringKind! 4 = (10")).is_err());
}

#[test]
fn anonymous_annotated_captures_still_check_their_kind() {
    let source = r#"
syntax "wildKind! " term:max : term
macro_rules
  | `(wildKind! $_:num) => `((10 : Nat))
  | `(wildKind! $_:ident) => `((20 : Nat))
  | `(wildKind! $_) => `((30 : Nat))
theorem a : wildKind! 4 = (10 : Nat) := rfl
theorem b : wildKind! Nat.zero = (20 : Nat) := rfl
theorem c : wildKind! (4) = (30 : Nat) := rfl
"#;
    assert_eq!(check(source).unwrap(), 3);
}

#[test]
fn pseudo_term_annotations_remain_unconditional_captures() {
    let source = r#"
syntax "anyTerm! " term:max : term
macro_rules | `(anyTerm! $x:term) => `((10 : Nat))
theorem a : anyTerm! 4 = (10 : Nat) := rfl
theorem b : anyTerm! Nat.zero = (10 : Nat) := rfl
theorem c : anyTerm! "value" = (10 : Nat) := rfl
theorem d : anyTerm! (Nat.add 2 3) = (10 : Nat) := rfl
"#;
    assert_eq!(check(source).unwrap(), 4);
}

#[test]
fn nested_capture_kinds_guard_the_exact_child_before_binding() {
    let source = r#"
syntax "nestedKind! " term:max : term
macro_rules
  | `(nestedKind! (Nat.add $x:num $y)) => `($x)
  | `(nestedKind! $_) => `((20 : Nat))
theorem a : nestedKind! (Nat.add 4 5) = (4 : Nat) := rfl
theorem b : nestedKind! (Nat.add Nat.zero 5) = (20 : Nat) := rfl
"#;
    assert_eq!(check(source).unwrap(), 2);
    assert!(
        check(&source.replace(
            "nestedKind! (Nat.add Nat.zero 5) = (20",
            "nestedKind! (Nat.add Nat.zero 5) = (0"
        ))
        .is_err()
    );
}

#[test]
fn a_kind_mismatch_without_a_fallback_refuses_instead_of_expanding() {
    let source = r#"
syntax "onlyNumber! " term:max : term
macro_rules | `(onlyNumber! $x:num) => `((10 : Nat))
theorem a : onlyNumber! 4 = (10 : Nat) := rfl
"#;
    assert_eq!(check(source).unwrap(), 1);
    assert!(check(&source.replace("onlyNumber! 4 =", "onlyNumber! Nat.zero =")).is_err());
}

#[test]
fn imported_and_replayed_rules_keep_explicit_capture_kind_guards() {
    use fln::source_check::modules::SourceModuleCheckLimits;
    use fln::{Name, SourceModuleInput};
    let admission = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let source_limits = SourceCheckLimits::new(admission);
    let engine = Engine::with_source_seed(admission)
        .unwrap()
        .into_complete()
        .unwrap();
    let library = Name::from_components(["Lib"]);
    let main = Name::from_components(["Main"]);
    let result = engine
        .check_source_modules(
            &[
                SourceModuleInput {
                    name: &library,
                    source: br#"
syntax "fromModule! " term:max : term
macro_rules
  | `(fromModule! $x:num) => `((10 : Nat))
  | `(fromModule! $_) => `((20 : Nat))
"#,
                },
                SourceModuleInput {
                    name: &main,
                    source: b"import Lib\ntheorem t : fromModule! Nat.zero = (20 : Nat) := rfl",
                },
            ],
            &main,
            &KVMap::new(),
            SourceModuleCheckLimits::new(source_limits),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    let resumed = result.checked.engine;
    assert_eq!(
        resumed
            .check_source_files(
                &[b"theorem t2 : fromModule! 4 = (10 : Nat) := rfl\ntheorem t3 : fromModule! Nat.zero = (20 : Nat) := rfl"],
                &KVMap::new(),
                source_limits,
            )
            .unwrap()
            .into_complete()
            .unwrap()
            .theorems,
        2
    );
    assert!(
        resumed
            .check_source_files(
                &[b"theorem wrong : fromModule! Nat.zero = (10 : Nat) := rfl"],
                &KVMap::new(),
                source_limits,
            )
            .is_err()
    );
}

/// A rule whose pattern is a bare capture names an atom kind (`num`, `ident`, `str`) as its
/// target. Such a rule would rewrite every literal of that kind (upstream `tests/elab/414`,
/// where `2` elaborates to `"world"`). This door cannot install it, and dropping it would leave
/// the native meaning in force where the pin runs the rule, so it is refused.
#[test]
fn a_rule_over_an_atom_kind_is_refused_rather_than_dropped() {
    for registration in [
        "macro_rules (kind := num)\n  | `($n:num) => `((7 : Nat))\n",
        "macro_rules\n  | `($n:num) => `((7 : Nat))\n",
        "macro_rules (kind := num)\n  | n => `((7 : Nat))\n",
    ] {
        let source = format!("{registration}theorem t : 2 = (2 : Nat) := rfl\n");
        let error = check(&source).unwrap_err();
        assert!(
            error.contains("a macro_rules registration whose target syntax kind is not read"),
            "{registration}: {error}"
        );
    }
    assert_eq!(check("theorem t : 2 = (2 : Nat) := rfl\n").unwrap(), 1);
}
