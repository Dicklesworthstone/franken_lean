//! Checked native Repr declarations and replay against the actual pinned library.
#![forbid(unsafe_code)]
use fln::source_check::modules::SourceModuleCheckLimits;
use fln::source_check::modules::imported::{SourceOleanImport, SourceOleanImportLimits};
use fln::{
    Budget, Engine, EngineAdmissionLimits, Environment, KVMap, Name, OleanCheckLimits,
    OleanDecodeLimits, OleanFrontierJobs, OleanModuleInput, SourceCheckLimits, SourceModuleInput,
};
use fln_core::expr::{Expr, ExprNode};
use fln_env::constants::ConstantInfo;
use std::collections::BTreeMap;
use std::num::NonZeroUsize;
use std::path::PathBuf;
use std::sync::OnceLock;

const STACK: usize = 256 * 1024 * 1024;
const BYTES: usize = 512 * 1024 * 1024;
const DECLARATIONS: &str = r#"
structure Packet (A B : Type) where
  value : A
  count : Nat
  proof : True
  kind : Type
deriving Repr
structure Marker : Type where
deriving Repr
namespace Wire
inductive Signal where
  | red
  | named (label : String)
  | numbered (value : Nat)
deriving Repr
inductive Message where
  | wrap (signal : Signal) (code : Nat)
deriving Repr
end Wire
inductive Promote : (loc : Nat) → (state : Nat) → Type where
  | mk : (loc : Nat) → (state : Nat) → (id : Nat) → Promote loc state
deriving Repr
inductive PromoteType : Type → Type 1 where
  | mk : (A : Type) → PromoteType A
deriving Repr
structure Base where
  n : Nat
deriving Repr
structure Child extends Base where
  flag : Bool
deriving Repr
def packet : Packet Nat String :=
  { value := 7, count := 2, proof := True.intro, kind := Nat }
"#;

fn name(text: &str) -> Name {
    Name::from_components(text.split('.'))
}

fn admission() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(STACK))
}

fn imported() -> Option<&'static SourceOleanImport> {
    static IMPORT: OnceLock<Option<SourceOleanImport>> = OnceLock::new();
    IMPORT
        .get_or_init(|| {
            let lib = std::env::var_os("FLN_REFERENCE_LIB")
                .map(PathBuf::from)
                .or_else(|| {
                    std::env::var_os("HOME").map(|home| {
                        PathBuf::from(home)
                            .join(".elan/toolchains/leanprover--lean4---v4.32.0/lib/lean")
                    })
                })
                .filter(|lib| lib.is_dir());
            let Some(lib) = lib else {
                assert!(
                    std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
                    "the pinned Reference is required"
                );
                eprintln!("SKIP: pinned Reference lib/lean absent");
                return None;
            };
            let root = name("Init.Data.Repr");
            let mut pending = vec![root.clone()];
            let mut artifacts = BTreeMap::new();
            while let Some(module) = pending.pop() {
                if artifacts.contains_key(&module) {
                    continue;
                }
                let path = lib
                    .join(module.to_display_string().replace('.', "/"))
                    .with_extension("olean");
                let parts = [
                    std::fs::read(&path).unwrap(),
                    std::fs::read(path.with_extension("olean.server")).unwrap(),
                    std::fs::read(path.with_extension("olean.private")).unwrap(),
                ];
                pending.extend(
                    fln::olean_module_imports(&parts[0], OleanDecodeLimits::new(BYTES)).unwrap(),
                );
                artifacts.insert(module, parts);
            }
            let modules: Vec<_> = artifacts
                .iter()
                .map(|(name, parts)| OleanModuleInput {
                    name,
                    artifact: &parts[0],
                    server_artifact: Some(&parts[1]),
                    private_artifact: Some(&parts[2]),
                })
                .collect();
            let mut limits = SourceOleanImportLimits::new(OleanCheckLimits::new(
                BYTES,
                Budget::for_stack_bytes(STACK),
            ));
            limits.jobs = OleanFrontierJobs {
                threads: NonZeroUsize::new(1).unwrap(),
                worker_stack_bytes: STACK,
            };
            Some(
                Engine::from_environment(Environment::new())
                    .import_olean_modules_for_source(&modules, &[root], &KVMap::new(), limits)
                    .expect("import the actual pinned Repr dependency closure")
                    .into_complete()
                    .expect("the actual closure passes both checking engines"),
            )
        })
        .as_ref()
}

fn checked(engine: &Engine, source: &str) -> Engine {
    engine
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(admission()),
        )
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .expect("generated declarations pass both checking engines")
        .engine
}

fn alpha_type(expr: &Expr) -> Expr {
    match expr.node() {
        ExprNode::ForallE {
            binder_type,
            body,
            binder_info,
            ..
        } => Expr::forall_e(
            Name::anonymous(),
            alpha_type(binder_type),
            alpha_type(body),
            *binder_info,
        ),
        ExprNode::App { f, a } => Expr::app(alpha_type(f), alpha_type(a)),
        _ => expr.clone(),
    }
}

#[test]
fn repr_helpers_are_checked_and_match_reference_statements_and_module_replay() {
    std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(|| {
            let Some(imported) = imported() else {
                return;
            };
            let base = &imported.engine;
            let root = base.logical_root(&KVMap::new());
            let source = format!(
                "{DECLARATIONS}\n\
                 def packetStatement {{A B : Type}} [Repr A] [Repr B] : Repr (Packet A B) := inferInstance\n\
                 def packetHelperStatement {{A B : Type}} [Repr A] [Repr B] : Packet A B → Nat → Std.Format := instReprPacket.repr\n\
                 def signalStatement : Repr Wire.Signal := inferInstance\n\
                 def signalHelperStatement : Wire.Signal → Nat → Std.Format := Wire.instReprSignal.repr\n\
                 def promotedStatement {{loc state : Nat}} : Repr (Promote loc state) := inferInstance"
            );
            let result = checked(base, &source);
            // These complete statements, including the unused Repr B binder,
            // were observed with #print on the pinned v4.32.0 Reference.
            for (generated, expected) in [
                ("instReprPacket", "packetStatement"),
                ("instReprPacket.repr", "packetHelperStatement"),
                ("Wire.instReprSignal", "signalStatement"),
                ("Wire.instReprSignal.repr", "signalHelperStatement"),
                ("instReprPromote", "promotedStatement"),
            ] {
                let Some(ConstantInfo::Defn(actual)) = result.environment().find(&name(generated))
                else {
                    panic!("missing checked generated definition {generated}");
                };
                let expected = result.environment().find(&name(expected)).unwrap().constant_val();
                assert_eq!(actual.base.level_params, expected.level_params, "{generated}");
                assert_eq!(alpha_type(&actual.base.type_), alpha_type(&expected.type_), "{generated}");
            }
            assert_eq!(root, base.logical_root(&KVMap::new()));
            assert!(!base.environment().contains(&name("instReprPacket")));
            let again = checked(base, &source);
            assert_eq!(result.logical_root(&KVMap::new()), again.logical_root(&KVMap::new()));

            // Multiple deriving handlers share the same checked command batch.
            // Exercise both equality handlers against actual imported classes and recursors,
            // including a structurally recursive helper, beyond the source seed.
            checked(base, r#"
structure Comparable (A : Type) where
  value : A
  proof : True
deriving Repr, BEq, DecidableEq
theorem comparable_yes : (Comparable.mk 7 True.intro == Comparable.mk 7 True.intro) = true := by rfl
theorem comparable_no : (Comparable.mk 7 True.intro == Comparable.mk 8 True.intro) = false := by rfl
theorem comparable_eq : Comparable.mk 7 True.intro = Comparable.mk 7 True.intro := by decide
theorem comparable_ne : Not (Comparable.mk 7 True.intro = Comparable.mk 8 True.intro) := by decide
inductive Chain (A : Type) where
  | nil
  | cons (head : A) (tail : Chain A)
deriving BEq, DecidableEq
theorem chain_yes : (Chain.cons 7 (Chain.cons 9 Chain.nil) == Chain.cons 7 (Chain.cons 9 Chain.nil)) = true := by rfl
theorem chain_no : (Chain.cons 7 (Chain.cons 9 Chain.nil) == Chain.cons 7 (Chain.cons 8 Chain.nil)) = false := by rfl
theorem chain_eq : Chain.cons 7 (Chain.cons 9 Chain.nil) = Chain.cons 7 (Chain.cons 9 Chain.nil) := by decide
theorem chain_ne : Not (Chain.cons 7 (Chain.cons 9 Chain.nil) = Chain.cons 7 (Chain.cons 8 Chain.nil)) := by decide
"#);

            // Preserve the former unsupported command as a checked positive,
            // then execute its comparison over the actual imported library.
            let combined = checked(base, "structure Partial where\n n : Nat\nderiving Repr, BEq");
            for generated in [
                "instReprPartial",
                "instReprPartial.repr",
                "instBEqPartial",
                "instBEqPartial.beq",
            ] {
                assert!(
                    matches!(combined.environment().find(&name(generated)), Some(ConstantInfo::Defn(_))),
                    "{generated}",
                );
            }
            let execution = combined
                .execute_source_definitions(
                    &[b"#eval if Partial.mk 7 == Partial.mk 7 then 42 else 0\n#eval if Partial.mk 7 == Partial.mk 8 then 1 else 0"],
                    &KVMap::new(),
                    fln::EngineExecutionLimits::new(admission().kernel),
                )
                .unwrap()
                .into_complete()
                .expect("derived BEq executes over the actual imported library");
            assert_eq!(execution.executions.len(), 2);
            for (execution, expected) in execution.executions.iter().zip(["42", "0"]) {
                let fln::VmExit::Returned(value) = &execution.exit else {
                    panic!("imported-library comparison did not return")
                };
                assert_eq!(fln::nat_decimal(&value.value).as_deref(), Some(expected));
                let replay = fln::execute_flbc_artifact(
                    &execution.flbc_artifact,
                    &KVMap::new(),
                    Default::default(),
                )
                .unwrap()
                .into_complete()
                .expect("the imported comparison's serialized bytecode executes");
                let fln::VmExit::Returned(value) = replay else {
                    panic!("imported-library bytecode did not return")
                };
                assert_eq!(fln::nat_decimal(&value.value).as_deref(), Some(expected));
            }

            for invalid in [
                "structure Bad where\n  run : Nat → Nat\nderiving Repr",
                "structure DictBox (A : Type) [Repr A] where\n  val : A\nderiving Repr",
                "inductive HigherOrder where\n | node (next : Nat → HigherOrder)\nderiving Repr",
                "inductive Indexed : Nat → Type where\n | zero : Indexed 0\nderiving Repr",
                "structure Partial where\n n : Nat\nderiving Repr, BEq, UnknownHandler",
            ] {
                assert!(
                    base.check_source_files(
                        &[invalid.as_bytes()],
                        &KVMap::new(),
                        SourceCheckLimits::new(admission()),
                    ).is_err(),
                    "unsupported or unprintable family must not publish: {invalid}"
                );
                assert_eq!(root, base.logical_root(&KVMap::new()));
            }
            let library = name("Library");
            let main = name("Main");
            let modules = [
                SourceModuleInput {
                    name: &library,
                    source: b"prelude\nimport Init.Data.Repr\nstructure Box (A : Type) where\n value : A\nderiving Repr",
                },
                SourceModuleInput {
                    name: &main,
                    source: b"prelude\nimport Library\ndef importedPrinter : Repr (Box Nat) := inferInstance",
                },
            ];
            let replayed = imported
                .check_source_modules(
                    &modules,
                    &main,
                    &KVMap::new(),
                    SourceModuleCheckLimits::new(SourceCheckLimits::new(admission())),
                    None,
                )
                .unwrap()
                .into_complete()
                .unwrap();
            for generated in ["instReprBox", "instReprBox.repr", "importedPrinter"] {
                assert!(replayed.checked.engine.environment().contains(&name(generated)));
            }

            // The same checked expansion must use private core names in a
            // module-system file, including the generated printer helper.
            let private_source = b"module\nprelude\nimport Init.Data.Repr\nnamespace Wire\nstructure Box where\n value : Nat\nderiving Repr, DecidableEq\ndef printer : Repr Box := inferInstance\ndef helper : Box -> Nat -> Std.Format := instReprBox.repr\ninductive Chain where\n | nil\n | cons (head : Nat) (tail : Chain)\nderiving DecidableEq\ndef dictionary : DecidableEq Chain := inferInstance\ntheorem same : Chain.cons 7 Chain.nil = Chain.cons 7 Chain.nil := by decide\ntheorem different : Not (Chain.cons 7 Chain.nil = Chain.cons 8 Chain.nil) := by decide\nend Wire";
            let private_input = SourceModuleInput { name: &library, source: private_source };
            let local = imported
                .check_source_modules(
                    &[private_input],
                    &library,
                    &KVMap::new(),
                    SourceModuleCheckLimits::new(SourceCheckLimits::new(admission())),
                    None,
                )
                .unwrap()
                .into_complete()
                .unwrap();
            for generated in ["Wire.instReprBox", "Wire.instReprBox.repr", "Wire.printer", "Wire.helper", "Wire.instDecidableEqBox", "Wire.instDecidableEqChain", "Wire.instDecidableEqChain.decEq", "Wire.dictionary", "Wire.same", "Wire.different"] {
                let private = Name::num(name("_private.Library"), 0).append_core(&name(generated));
                assert!(local.checked.engine.environment().contains(&private), "{generated}");
                assert!(!local.checked.engine.environment().contains(&name(generated)), "{generated}");
            }
            let hidden = imported
                .check_source_modules(
                    &[private_input, SourceModuleInput { name: &main, source: b"prelude\nimport Library" }],
                    &main,
                    &KVMap::new(),
                    SourceModuleCheckLimits::new(SourceCheckLimits::new(admission())),
                    None,
                )
                .unwrap()
                .into_complete()
                .unwrap();
            assert!(hidden.checked.engine.environment().is_empty());
            checked(base, "structure Retry where\n value : Nat\nderiving Repr");
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn recursive_repr_uses_checked_induction_hypotheses_and_executes_actual_formats() {
    std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(|| {
            let Some(imported) = imported() else {
                return;
            };
            let base = &imported.engine;
            let original = base.logical_root(&KVMap::new());
            // The pin's Deriving/Repr.lean sends each explicit same-family
            // field to the recursive helper at max_prec. These checks use the
            // actual admitted Repr, Format and Bool printer, not replacement
            // classes or an unchecked mirror of their declarations.
            let source = r#"
namespace Recursive
inductive Tree (A B : Type) where
  | leaf (value : A)
  | branch (left right : Tree A B)
deriving Repr
inductive Chain where
  | nil
  | cons (head : Bool) (tail : Chain) (proof : True) (kind : Type)
deriving Repr
inductive Hidden where
  | stop
  | next {child : Hidden} (visible : Bool)
deriving Repr
def sample : Tree Bool Nat := .branch (.leaf true) (.leaf false)
def chain : Chain := .cons true .nil True.intro Bool
def hidden : Hidden := @Hidden.next (@Hidden.next Hidden.stop false) true
def dictionaryExpected {A B : Type} [Repr A] [Repr B] : Repr (Tree A B) := inferInstance
def helperExpected {A B : Type} [Repr A] [Repr B] : Tree A B → Nat → Std.Format := instReprTree.repr
end Recursive

def formatTokens : Std.Format → List String
  | .nil => []
  | .line => [" "]
  | .align _ => []
  | .text text => [text]
  | .nest _ body => formatTokens body
  | .append left right => List.append (formatTokens left) (formatTokens right)
  | .group body _ => formatTokens body
  | .tag _ body => formatTokens body

theorem recursive_tokens :
    formatTokens (Repr.reprPrec Recursive.sample 0) =
      ["Recursive.Tree.branch", " ", "(", "Recursive.Tree.leaf", " ", "true", ")",
       " ", "(", "Recursive.Tree.leaf", " ", "false", ")"] := by rfl
theorem recursive_precedence :
    formatTokens (Repr.reprPrec Recursive.sample 1024) =
      ["(", "Recursive.Tree.branch", " ", "(", "Recursive.Tree.leaf", " ", "true", ")",
       " ", "(", "Recursive.Tree.leaf", " ", "false", ")", ")"] := by rfl
theorem recursive_erased_fields :
    formatTokens (Repr.reprPrec Recursive.chain 0) =
      ["Recursive.Chain.cons", " ", "true", " ", "(", "Recursive.Chain.nil", ")",
       " ", "_", " ", "_"] := by rfl
theorem implicit_recursive_field_is_not_printed :
    formatTokens (Repr.reprPrec Recursive.hidden 0) = ["Recursive.Hidden.next", " ", "true"] := by rfl
"#;
            let checked = checked(base, source);
            for (generated, expected) in [
                ("Recursive.instReprTree", "Recursive.dictionaryExpected"),
                ("Recursive.instReprTree.repr", "Recursive.helperExpected"),
            ] {
                let actual = checked.environment().find(&name(generated)).unwrap().constant_val();
                let expected = checked.environment().find(&name(expected)).unwrap().constant_val();
                assert_eq!(actual.level_params, expected.level_params, "{generated}");
                assert_eq!(alpha_type(&actual.type_), alpha_type(&expected.type_), "{generated}");
            }
            // Execute the checked printers and compare every resulting token,
            // independently of the logical reductions above. Their Format
            // constructors and the consumer's List String values are native.
            let program = b"#eval formatTokens (Repr.reprPrec Recursive.sample 0)\n#eval formatTokens (Repr.reprPrec Recursive.sample 1024)\n#eval formatTokens (Repr.reprPrec Recursive.chain 0)\n#eval formatTokens (Repr.reprPrec Recursive.hidden 0)";
            let executed = checked
                .execute_source_definitions(
                    &[program],
                    &KVMap::new(),
                    fln::EngineExecutionLimits::new(admission().kernel),
                )
                .expect("derived recursive printers compile against the actual imported library")
                .into_complete()
                .expect("derived recursive printers execute within the budget");
            assert_eq!(executed.executions.len(), 4);
            let expected: &[&[&str]] = &[
                &["Recursive.Tree.branch", " ", "(", "Recursive.Tree.leaf", " ", "true", ")",
                  " ", "(", "Recursive.Tree.leaf", " ", "false", ")"],
                &["(", "Recursive.Tree.branch", " ", "(", "Recursive.Tree.leaf", " ", "true", ")",
                  " ", "(", "Recursive.Tree.leaf", " ", "false", ")", ")"],
                &["Recursive.Chain.cons", " ", "true", " ", "(", "Recursive.Chain.nil", ")",
                  " ", "_", " ", "_"],
                &["Recursive.Hidden.next", " ", "true"],
            ];
            let shape = fln::ClosedValueShape::List(Box::new(fln::ClosedValueShape::String));
            for (execution, tokens) in executed.executions.iter().zip(expected) {
                let expected = fln::ClosedShapedValue::List(
                    tokens.iter().map(|token| fln::ClosedShapedValue::String((*token).to_owned())).collect(),
                );
                assert_eq!(
                    fln::closed_vm_shaped_value(&execution.exit, &shape, 1_000).unwrap(),
                    expected,
                );
                let replay = fln::execute_flbc_artifact(
                    &execution.flbc_artifact,
                    &KVMap::new(),
                    Default::default(),
                )
                .unwrap()
                .into_complete()
                .expect("serialized recursive printers decode, validate and execute");
                assert_eq!(
                    fln::closed_vm_shaped_value(&replay, &shape, 1_000).unwrap(),
                    expected,
                );
            }

            for invalid in [
                "inductive Nested where\n | node (children : List Nested)\nderiving Repr",
                "inductive HigherOrder where\n | node (next : Nat → HigherOrder)\nderiving Repr",
                "inductive Rollback where\n | nil\n | cons (tail : Rollback)\nderiving Repr, UnknownHandler",
            ] {
                assert!(
                    base.check_source_files(
                        &[invalid.as_bytes()],
                        &KVMap::new(),
                        SourceCheckLimits::new(admission()),
                    ).is_err(),
                    "the unsupported recursive family or handler must refuse atomically: {invalid}",
                );
                assert_eq!(base.logical_root(&KVMap::new()), original);
                for generated in ["Nested", "HigherOrder", "Rollback", "instReprRollback.repr"] {
                    assert!(!base.environment().contains(&name(generated)), "{generated}");
                }
            }
            assert_eq!(base.logical_root(&KVMap::new()), original);
        })
        .unwrap()
        .join()
        .unwrap();
}
