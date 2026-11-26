//! Native command-producing macros still enter ordinary elaboration and kernel admission.
#![forbid(unsafe_code)]

use fln::{Budget, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap, SourceCheckLimits};

fn check(source: &str) -> Result<usize, String> {
    check_file(source).map(|result| result.theorems)
}

fn check_file(source: &str) -> Result<fln::source_check::SourceFileCheck, String> {
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
        .map(|result| result.into_complete().unwrap())
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
fn command_macros_admit_mutual_forward_references_and_recursive_definitions() {
    let source = r#"
def n : Nat := 99
macro "mutual_values " first:ident second:ident : command =>
  `(mutual
      def $first : Nat := $second + 1
      def $second : Nat := 41
    end)
macro "mutual_counts " left:ident right:ident : command =>
  `(mutual
      def $left : Nat -> Nat
        | 0 => 7
        | n+1 => $right n + 1
      def $right : Nat -> Nat
        | 0 => 13
        | n+1 => $left n + 2
    end)
namespace Generated
mutual_values answer predecessor
mutual_counts countLeft countRight
theorem answer_ok : answer = 42 := rfl
theorem count_left_ok : countLeft 4 = 13 := rfl
theorem count_right_ok : countRight 4 = 19 := rfl
end Generated
theorem exported_ok : Generated.answer = 42 := rfl
"#;
    assert_eq!(check(source).unwrap(), 4);
    assert!(check(&source.replace("countLeft 4 = 13", "countLeft 4 = 14")).is_err());
}

#[test]
fn quoted_mutual_headers_and_constructor_siblings_keep_their_own_scopes() {
    let source = r#"
abbrev Carrier : Type := Nat
def peer : Nat := 99
macro "scoped_group " result:ident : command =>
  `(mutual
      def Carrier : Nat := 1
      def peer : Nat := 42
      def $result : Carrier := peer
    end)
scoped_group answer
theorem answer_ok : answer = 42 := rfl
macro "scoped_inductive " family:ident poly:ident mono:ident : command =>
  `(inductive $family where
      | $poly:ident (Carrier : Type) (value : Carrier)
      | $mono:ident (value : Carrier))
scoped_inductive ScopedFamily poly mono
def constructor_type : Nat -> ScopedFamily := @ScopedFamily.mono
theorem constructor_ok : constructor_type 7 = ScopedFamily.mono 7 := rfl
"#;
    assert_eq!(check(source).unwrap(), 2);
    assert!(check(&source.replace("answer = 42", "answer = 99")).is_err());
}

#[test]
fn command_macros_admit_mutually_inductive_types() {
    let source = r#"
macro "mutual_types " tree:ident forest:ident leaf:ident node:ident nil:ident cons:ident : command =>
  `(mutual
      inductive $tree where
        | $leaf:ident (value : Nat)
        | $node:ident (children : $forest)
      inductive $forest where
        | $nil:ident
        | $cons:ident (head : $tree) (tail : $forest)
    end)
mutual_types MacroTree MacroForest leaf node nil cons
def unpack (tree : MacroTree) : Nat := match tree with
  | MacroTree.leaf n => n
  | MacroTree.node _ => 0
theorem unpack_ok : unpack (MacroTree.leaf 11) = 11 := rfl
"#;
    let checked = check_file(source).unwrap();
    assert_eq!(checked.theorems, 1);
    for declaration in ["MacroTree", "MacroForest"] {
        let name = fln::Name::from_components([declaration]);
        assert!(matches!(
            checked.engine.environment().find(&name),
            Some(fln_env::constants::ConstantInfo::Induct(info)) if info.all.len() == 2
        ));
    }
    assert!(check(&source.replace("= 11 := rfl", "= 12 := rfl")).is_err());
}

#[test]
fn command_macro_mutual_groups_execute_through_the_checked_batch() {
    let limits = EngineExecutionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let engine = Engine::with_source_seed(EngineAdmissionLimits::new(limits.kernel))
        .unwrap()
        .into_complete()
        .unwrap();
    let options = KVMap::new();
    let root = engine.logical_root(&options);
    let source = br#"
macro "mutual_values " first:ident second:ident : command =>
  `(mutual
      def $first : Nat := $second + 1
      def $second : Nat := 41
    end)
mutual_values answer predecessor
example : answer = 42 := rfl
#eval answer
"#;
    let completed = engine
        .execute_source_commands_with_checks(source, &options, limits)
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(completed.batch.executions.len(), 1);
    let fln::VmExit::Returned(returned) = &completed.batch.executions[0].exit else {
        panic!("the evaluation following a macro-generated mutual group must return")
    };
    assert_eq!(fln::nat_decimal(&returned.value).as_deref(), Some("42"));
    for declaration in ["answer", "predecessor"] {
        let name = fln::Name::from_components([declaration]);
        assert!(completed.batch.engine.environment().contains(&name));
        assert!(!engine.environment().contains(&name));
    }
    assert_eq!(engine.logical_root(&options), root);
}

#[test]
fn command_macro_mutual_groups_reject_invalid_members_without_a_successor() {
    let limits = EngineExecutionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let admission = EngineAdmissionLimits::new(limits.kernel);
    let engine = Engine::with_source_seed(admission)
        .unwrap()
        .into_complete()
        .unwrap();
    let options = KVMap::new();
    let root = engine.logical_root(&options);
    let macros = r#"
macro "mutual_values " first:ident second:ident " := " value:term : command =>
  `(mutual
      def $first : Nat := 42
      def $second : Nat := $value
    end)
macro "mutual_proofs " first:ident second:ident : command =>
  `(mutual
      theorem $first : True := True.intro
      theorem $second : False := True.intro
    end)
def checkedPrefix : Nat := 7
"#;
    for command in [
        "mutual_values first second := True",
        "mutual_proofs first second",
        "mutual_values first first := 42",
    ] {
        let source = format!("{macros}\n{command}\n");
        let checked = engine.check_source_files(
            &[source.as_bytes()],
            &options,
            SourceCheckLimits::new(admission),
        );
        assert!(checked.is_err(), "{command}: {checked:?}");
        let executed = engine.execute_source_commands_with_checks(
            format!("{source}\n#eval checkedPrefix").as_bytes(),
            &options,
            limits,
        );
        assert!(executed.is_err(), "{command}: {executed:?}");
        for declaration in ["checkedPrefix", "first", "second"] {
            assert!(
                !engine
                    .environment()
                    .contains(&fln::Name::from_components([declaration]))
            );
        }
        assert_eq!(engine.logical_root(&options), root);
    }
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
fn command_macros_check_anonymous_examples_without_publishing_declarations() {
    let macros = r#"
macro "checked " ty:term " := " proof:term : command =>
  `(example : $ty := $proof)
syntax "checked_proof " term " := " term : command
macro_rules
  | `(checked_proof $ty := $proof) => `(example : $ty := $proof)
macro "pass_command " c:command : command => `($c:command)
macro "nested_command " c:command : command => `(pass_command $c:command)
macro "checked_shadow " ty:term " := " proof:term : command =>
  `(example (h : Nat) : $ty := $proof)
"#;
    // Namespace declarations persist independently of the examples they contain.
    let baseline = check_file(&format!("{macros}\nnamespace Scoped\nend Scoped\n")).unwrap();
    let source = format!(
        r#"{macros}
checked (∀ (P : Prop), P → P) := fun _ h => h
checked_proof (0 = 0) := rfl
pass_command example : Nat := 42
nested_command example (n : Nat) : n = n := by rfl
namespace Scoped
variable (P : Prop) (h : P)
checked_shadow P := h
end Scoped
"#
    );
    let checked = check_file(&source).unwrap();
    assert_eq!(checked.theorems, 0);
    assert_eq!(checked.result_logical_root, baseline.result_logical_root);
    assert_eq!(
        checked.engine.environment().len(),
        baseline.engine.environment().len(),
        "neither the example nor its local proof may be published"
    );
    assert!(check(&format!("{source}\ndef leaked : Nat := _example")).is_err());
}

#[test]
fn command_macro_examples_are_checked_and_discarded_in_program_execution() {
    let limits = EngineExecutionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let engine = Engine::with_source_seed(EngineAdmissionLimits::new(limits.kernel))
        .unwrap()
        .into_complete()
        .unwrap();
    let options = KVMap::new();
    let root = engine.logical_root(&options);
    let macros = r#"
macro "checked " ty:term " := " proof:term : command =>
  `(example : $ty := $proof)
macro "pass_command " c:command : command => `($c:command)
"#;
    let baseline = engine
        .execute_source_commands_with_checks(macros.as_bytes(), &options, limits)
        .unwrap()
        .into_complete()
        .unwrap();
    let examples = format!(
        "{macros}\nchecked Nat := 42\n\
         pass_command example (n : Nat) : n = n := by rfl"
    );
    let checked = engine
        .execute_source_commands_with_checks(examples.as_bytes(), &options, limits)
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(checked.checks.len(), 2);
    assert!(checked.batch.executions.is_empty());
    assert!(checked.batch.source_admissions.is_empty());
    assert_eq!(checked.batch.result_logical_root, root);
    assert_eq!(
        checked.batch.result_logical_root,
        baseline.batch.result_logical_root
    );
    // Raw #eval retains its generated evaluator, whose name includes its command
    // index. Check its result separately from the examples' scratch-only root.
    let source = format!("{examples}\n#eval (43 : Nat)");
    let completed = engine
        .execute_source_commands_with_checks(source.as_bytes(), &options, limits)
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(completed.checks.len(), 2);
    assert_eq!(completed.batch.executions.len(), 1);
    assert_eq!(completed.batch.source_evaluation_indices, [0]);
    assert!(completed.batch.source_admissions.is_empty());
    for check in &completed.checks {
        let fln::Declaration::Defn(candidate) = &check.declaration else {
            panic!("an example must produce only a scratch checking candidate")
        };
        assert!(
            !completed
                .batch
                .engine
                .environment()
                .contains(&candidate.base.name)
        );
    }
    let fln::VmExit::Returned(returned) = &completed.batch.executions[0].exit else {
        panic!("the ordinary evaluation following the examples must return")
    };
    assert_eq!(fln::nat_decimal(&returned.value).as_deref(), Some("43"));
    assert!(
        engine
            .execute_source_commands_with_checks(
                format!("{macros}\nchecked False := True.intro\n#eval (43 : Nat)").as_bytes(),
                &options,
                limits,
            )
            .is_err()
    );
    assert_eq!(engine.logical_root(&options), root);
}

#[test]
fn command_macro_examples_reject_invalid_proofs_after_expansion() {
    let macros = r#"
macro "checked " ty:term " := " proof:term : command =>
  `(example : $ty := $proof)
macro "pass_command " c:command : command => `($c:command)
"#;
    for command in [
        "checked False := True.intro",
        "checked Nat := True",
        "pass_command example : 0 = 1 := by rfl",
    ] {
        let error = check(&format!("{macros}\n{command}")).unwrap_err();
        assert!(
            error.contains("Elaborate"),
            "{command}: the expanded example must reach ordinary checking: {error}"
        );
    }
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
