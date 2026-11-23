//! Native command-producing macros still enter ordinary elaboration and kernel admission.
#![forbid(unsafe_code)]

use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, SourceCheckLimits};

fn check(source: &str) -> Result<usize, String> {
    let admission = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    Engine::with_source_seed(admission)
        .unwrap()
        .into_complete()
        .unwrap()
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(admission),
        )
        .map_err(|error| format!("{error:?}"))
        .map(|result| result.into_complete().unwrap().theorems)
}

#[test]
fn command_macros_admit_named_definitions_and_theorems() {
    let source = r#"
macro "named_value " n:ident " := " v:term : command =>
  `(def $n : Nat := $v)
named_value answer := 42
theorem answer_ok : answer = 42 := rfl
macro "named_theorem " n:ident " : " ty:term " := " proof:term : command =>
  `(theorem $n : $ty := $proof)
named_theorem generated_identity : (∀ (p : Prop), p → p) := fun _ h => h
theorem use_generated (p : Prop) (h : p) : p := generated_identity p h
"#;
    assert_eq!(check(source).unwrap(), 3);
    assert!(check(&source.replace("answer = 42", "answer = 43")).is_err());
    assert!(check(&source.replace("p → p", "p → False")).is_err());
}

#[test]
fn command_macro_rules_match_and_expand_without_reparsing_generated_text() {
    let source = r#"
syntax "quoted_def " ident " := " term : command
macro_rules
  | `(quoted_def $n:ident := $v) => `(def $n := $v)
quoted_def number := (43 : Nat)
quoted_def message := "kept bytes"
theorem number_ok : number = 43 := rfl
theorem message_ok : message = "kept bytes" := rfl
"#;
    assert_eq!(check(source).unwrap(), 2);
    assert!(check(&source.replace("number = 43", "number = 44")).is_err());
    assert!(check(&source.replace("message = \"kept bytes\"", "message = \"wrong\"")).is_err());
}

#[test]
fn grouped_command_heads_reach_native_kernel_admission() {
    let source = r#"
def before : Nat := 0
syntax ("left_value " <|> "right_value ") ident " := " term : command
macro_rules
  | `(left_value $n:ident := $v:term) => `(def $n : Nat := $v)
  | `(right_value $n:ident := $v:term) => `(def $n : Nat := $v)
left_value leftValue := 11
right_value rightValue := 31
theorem left_ok : leftValue = 11 := rfl
theorem right_ok : rightValue = 31 := rfl
macro ("pass_first " <|> "pass_second ") c:command : command => `($c:command)
pass_first def forwarded : Nat := 43
pass_second
  theorem forwarded_ok : forwarded = 43 := rfl
"#;
    assert_eq!(check(source).unwrap(), 3);
    assert!(check(&source.replace("leftValue = 11", "leftValue = 12")).is_err());
    assert!(check(&source.replace("rightValue = 31", "rightValue = 32")).is_err());
    assert!(check(&source.replace("forwarded = 43", "forwarded = 44")).is_err());
}

#[test]
fn pure_command_macro_bodies_apply_declaration_name_coercions() {
    let source = r#"
macro "pure_named " n:ident " := " v:term : command => do
  let alias := n
  `(def $alias : Nat := $v)
macro "bound_named " n:ident " := " v:term : command => do
  let command ← `(def $n : Nat := $v)
  return command
pure_named first := 46
bound_named second := 47
theorem first_ok : first = 46 := rfl
theorem second_ok : second = 47 := rfl
"#;
    assert_eq!(check(source).unwrap(), 2);
    assert!(check(&source.replace("first = 46", "first = 47")).is_err());
}

#[test]
fn whole_command_captures_keep_caller_names_and_scopes() {
    let source = r#"
macro "pass_command " c:command : command => `($c:command)
namespace Values
pass_command def original : Nat := 44
end Values
theorem original_ok : Values.original = 44 := rfl
macro "nested_command " c:command : command => `(pass_command $c:command)
nested_command def another : Nat := 45
theorem another_ok : another = 45 := rfl
"#;
    assert_eq!(check(source).unwrap(), 2);
    assert!(check(&source.replace("Values.original = 44", "Values.original = 45")).is_err());
}

#[test]
fn command_macros_cannot_bypass_elaboration_or_admit_the_wrong_command_kind() {
    for source in [
        "macro \"bad_decl\" : command => `(def broken : Nat := True)\nbad_decl\n",
        "macro \"false_proof\" : command => `(theorem broken : False := True.intro)\nfalse_proof\n",
        "macro \"query_only\" : command => `(#check Nat)\nquery_only\n",
        "syntax \"unexpanded\" : command\nunexpanded\n",
    ] {
        assert!(check(source).is_err(), "{source}");
    }
}
