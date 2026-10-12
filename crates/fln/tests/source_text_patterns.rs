//! String and character value patterns over the retained, council-admitted Prelude.
#![forbid(unsafe_code)]

use fln::source_check::modules::execution::SourceProgramLimits;
use fln::source_check::modules::imported::{SourceOleanImport, SourceOleanImportLimits};
use fln::{
    Budget, ClosedVmValue, Engine, EngineExecutionLimits, KVMap, Name, OleanCheckLimits,
    OleanModuleInput, SourceModuleInput,
};
use std::sync::OnceLock;

const STACK: usize = 128 * 1024 * 1024;

fn name(text: &str) -> Name {
    Name::from_components(text.split('.'))
}

fn imported() -> &'static SourceOleanImport {
    static PRELUDE: OnceLock<SourceOleanImport> = OnceLock::new();
    PRELUDE.get_or_init(|| {
        let module = name("Init.Prelude");
        Engine::builder()
            .build_empty()
            .import_olean_modules_for_source(
                &[OleanModuleInput {
                    name: &module,
                    artifact: include_bytes!(
                        "../../fln-conformance/fixtures/tag_attributes/prelude.olean"
                    ),
                    server_artifact: Some(include_bytes!(
                        "../../fln-conformance/fixtures/tag_attributes/prelude.olean.server"
                    )),
                    private_artifact: Some(include_bytes!(
                        "../../fln-conformance/fixtures/tag_attributes/prelude.olean.private"
                    )),
                }],
                std::slice::from_ref(&module),
                &KVMap::new(),
                SourceOleanImportLimits::new(OleanCheckLimits::new(
                    16 << 20,
                    Budget::for_stack_bytes(STACK),
                )),
            )
            .expect("the real pinned Prelude chain decodes")
            .into_complete()
            .expect("both checking seats admit the retained Prelude")
    })
}

fn on_stack(test: impl FnOnce() + Send + 'static) {
    std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(test)
        .unwrap()
        .join()
        .unwrap();
}

fn run(source: &str) -> Vec<usize> {
    let module = name("TextPatterns");
    let result = imported()
        .execute_source_modules(
            &[SourceModuleInput {
                name: &module,
                source: source.as_bytes(),
            }],
            &module,
            &KVMap::new(),
            SourceProgramLimits::new(EngineExecutionLimits::new(Budget::for_stack_bytes(STACK))),
            None,
        )
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .expect("the source executes completely");
    result
        .modules
        .iter()
        .flat_map(|module| {
            module
                .commands
                .batch
                .source_evaluation_indices
                .iter()
                .map(|index| {
                    match fln::closed_vm_value(&module.commands.batch.executions[*index].exit)
                        .unwrap()
                    {
                        Some(ClosedVmValue::Scalar(value)) => value,
                        other => panic!("expected a Nat evaluation, got {other:?}"),
                    }
                })
        })
        .collect()
}

#[test]
fn string_and_char_patterns_execute_from_admitted_definitions() {
    on_stack(|| {
        assert_eq!(
            run(r#"
prelude
import Init.Prelude
def word : String -> Nat
  | "" => 0
  | "a\nb" => 7
  | "λ" => 9
  | _ => 11
def letter : Char -> Nat
  | 'a' => 1
  | '\n' => 2
  | 'λ' => 3
  | _ => 4
#eval word ""
#eval word "a\nb"
#eval word "λ"
#eval word "other"
#eval letter 'a'
#eval letter '\n'
#eval letter 'λ'
#eval letter '🙂'
"#),
            vec![0, 7, 9, 11, 1, 2, 3, 4]
        );
    });
}

#[test]
fn escaped_raw_and_unicode_values_keep_ordered_matrix_semantics() {
    on_stack(|| {
        assert_eq!(
            run(r##"
prelude
import Init.Prelude
def text : String -> Bool -> Nat
  | "a\nb", true => 1
  | r#"a
b"#, false => 2
  | "🙂", _ => 3
  | _, _ => 4
def character : Char -> Bool -> Nat
  | 'a', true => 5
  | '\x61', false => 6
  | '🙂', _ => 7
  | '\x00', _ => 8
  | _, _ => 9
#eval text "a\nb" true
#eval text "a\nb" false
#eval text "🙂" false
#eval text "a" false
#eval character 'a' true
#eval character 'a' false
#eval character '🙂' true
#eval character '\uD800' false
#eval character 'λ' false
"##),
            vec![1, 2, 3, 4, 5, 6, 7, 8, 9]
        );
    });
}

#[test]
fn nested_payloads_captured_arguments_and_fallback_bindings_execute() {
    on_stack(|| {
        assert_eq!(
            run(r#"
prelude
import Init.Prelude
def text : Option String -> Nat
  | .some "yes" => 1
  | .some _ => 2
  | .none => 3
def letter : Option Char -> Nat
  | .some 'y' => 4
  | .some _ => 5
  | .none => 6
def first (bias : Nat) (s : String) : Nat :=
  match s with
  | "yes" => bias
  | _ => bias + 1
def use (f : String -> Nat) : Nat := f "no"
#eval text (.some "yes")
#eval text (.some "no")
#eval text .none
#eval letter (.some 'y')
#eval letter (.some 'n')
#eval letter .none
#eval use (first 10)
#eval first 10 "yes"
"#),
            vec![1, 2, 3, 4, 5, 6, 11, 10]
        );
    });
}

#[test]
fn user_beq_and_decide_names_cannot_redefine_value_patterns() {
    on_stack(|| {
        assert_eq!(
            run(r#"
prelude
import Init.Prelude
instance : BEq String where
  beq _ _ := true
instance : BEq Char where
  beq _ _ := false
namespace Shadow
def decide (p : Prop) [Decidable p] : Bool := false
def word (decide : Nat) (s : String) : Nat :=
  match s with
  | "yes" => decide
  | _ => decide + 1
def letter : Char -> Nat
  | 'y' => 1
  | _ => 2
end Shadow
#eval Shadow.word 5 "yes"
#eval Shadow.word 5 "no"
#eval Shadow.letter 'y'
#eval Shadow.letter 'n'
"#),
            vec![5, 6, 1, 2]
        );
    });
}

#[test]
fn text_patterns_reject_uncovered_domains_ill_typed_rows_and_false_refinements() {
    on_stack(|| {
        let engine = &imported().engine;
        let before = engine.environment().logical_root(&KVMap::new());
        for source in [
            "def bad : String -> Nat | \"x\" => 1",
            "def bad : Char -> Nat | 'x' => 1",
            "def bad : Nat -> Nat | \"x\" => 1 | _ => 2",
            "def bad : String -> Nat | 'x' => 1 | _ => 2",
            "def bad : Char -> Nat | \"x\" => 1 | _ => 2",
            "def bad : Char -> Nat | 'x' => 1 | 0 => 2 | _ => 3",
            "def bad : String -> Nat | \"x\" => true | _ => 2",
            "def bad : String -> Nat | \"x\" => 1 | \"\\x78\" => 2 | _ => 3",
            "def bad : Char -> Nat | 'x' => 1 | '\\x78' => 2 | _ => 3",
            "def bad (s : String) : s = \"x\" := match s with | \"x\" => rfl | _ => rfl",
            "def bad (s : Char) : s = 'x' := match s with | 'x' => rfl | _ => rfl",
            "def bad (s : String) : Nat := match s with | \"x\" => 0 | _ => bad s",
        ] {
            let result = engine.check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                fln::SourceCheckLimits::new(fln::EngineAdmissionLimits::new(
                    Budget::for_stack_bytes(STACK),
                )),
            );
            assert!(
                result.is_err(),
                "must reject rather than admit an uncovered or false row: {source}\n{result:?}"
            );
            assert_eq!(before, engine.environment().logical_root(&KVMap::new()));
        }
    });
}

#[test]
fn text_pattern_definitions_remain_kernel_checkable_without_native_evaluation() {
    on_stack(|| {
        let source = r#"
def text : String -> Nat | "x" => 1 | _ => 2
def character : Char -> Nat | 'x' => 1 | _ => 2
theorem text_proof (s : String) : True :=
  match s with | "x" => True.intro | _ => True.intro
theorem character_proof (s : Char) : True :=
  match s with | 'x' => True.intro | _ => True.intro
"#;
        let checked = imported()
            .engine
            .check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                fln::SourceCheckLimits::new(fln::EngineAdmissionLimits::new(
                    Budget::for_stack_bytes(STACK),
                )),
            )
            .unwrap()
            .into_complete()
            .unwrap();
        assert_eq!(checked.theorems, 2);
    });
}
