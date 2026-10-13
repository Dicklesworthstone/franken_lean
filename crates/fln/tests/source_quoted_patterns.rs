//! Quoted macro patterns through parsing, hygienic expansion and dual admission.
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
fn nested_pattern_captures_reach_their_exact_syntax_children() {
    let source = r#"
syntax "pick! " term:max : term
macro_rules | `(pick! (Nat.add $x $y)) => `($x)
theorem a : pick! (Nat.add 2 3) = (2 : Nat) := rfl
theorem b (x : Nat) : pick! (Nat.add x 3) = x := rfl
"#;
    assert_eq!(check(source).unwrap(), 2);
    assert!(check(&source.replace("= (2 : Nat)", "= (3 : Nat)")).is_err());
    assert!(check(&source.replace("pick! (Nat.add 2 3) =", "pick! (Nat.mul 2 3) =")).is_err());
}

#[test]
fn literal_patterns_match_spelling_not_numeric_conversion() {
    let prefix = "syntax \"zero! \" term:max : term\nmacro_rules | `(zero! 0) => `((11 : Nat))\n";
    assert_eq!(
        check(&format!("{prefix}theorem t : zero! 0 = 11 := rfl")).unwrap(),
        1
    );
    assert!(check(&format!("{prefix}theorem t : zero! 1 = 11 := rfl")).is_err());
    assert!(check(&format!("{prefix}theorem t : zero! (0 : Nat) = 11 := rfl")).is_err());
}

#[test]
fn an_outer_pattern_observes_unexpanded_inner_syntax() {
    let source = r#"
macro "inside!" : term => `((2 : Nat))
syntax "outside! " term:max : term
macro_rules | `(outside! inside!) => `((1 : Nat))
theorem t : outside! inside! = 1 := rfl
"#;
    assert_eq!(check(source).unwrap(), 1);
    assert!(check(&source.replace("outside! inside! = 1", "outside! (2 : Nat) = 1")).is_err());
}

#[test]
fn discarded_macro_arguments_are_not_expanded_but_selected_loops_are_bounded() {
    let prefix = r#"
syntax "loop!" : term
macro_rules | `(loop!) => `(loop!)
macro "discard! " x:term:max : term => `((7 : Nat))
"#;
    assert_eq!(
        check(&format!("{prefix}theorem t : discard! loop! = 7 := rfl")).unwrap(),
        1
    );
    assert!(check(&format!("{prefix}theorem t : loop! = (7 : Nat) := rfl")).is_err());
}

#[test]
fn captured_syntax_and_definition_site_names_remain_hygienic() {
    let source = r#"
namespace DefSite
def offset : Nat := 10
syntax "bump! " term:max : term
macro_rules | `(bump! ($x)) => `(Nat.add $x offset)
end DefSite
theorem t (offset : Nat) : bump! (offset) = Nat.add offset 10 := rfl
"#;
    assert_eq!(check(source).unwrap(), 1);
}

#[test]
fn string_literal_patterns_distinguish_the_literal_payload() {
    let source = r#"
syntax "greet! " term:max : term
macro_rules | `(greet! "hello") => `((42 : Nat))
theorem t : greet! "hello" = 42 := rfl
"#;
    assert_eq!(check(source).unwrap(), 1);
    assert!(check(&source.replace("greet! \"hello\" =", "greet! \"goodbye\" =")).is_err());
}

#[test]
fn a_quoted_wildcard_does_not_introduce_a_template_binding() {
    let source = r#"
syntax "forget! " term:max : term
macro_rules | `(forget! $_) => `((8 : Nat))
theorem t : forget! (Nat.add 1 2) = 8 := rfl
"#;
    assert_eq!(check(source).unwrap(), 1);
}
