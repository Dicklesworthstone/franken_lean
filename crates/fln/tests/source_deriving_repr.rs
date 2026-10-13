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
            let roots = [name("Init.Data.Repr"), name("Init.Data.ToString.Basic")];
            let mut pending = roots.to_vec();
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
                    .import_olean_modules_for_source(&modules, &roots, &KVMap::new(), limits)
                    .expect("import the actual pinned Repr and ToString dependency closure")
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
fn admitted_numeric_printers_preserve_logical_values_and_replay_native_printing() {
    std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(|| {
            let Some(imported) = imported() else {
                return;
            };
            let engine = &imported.engine;
            let options = KVMap::new();
            let original_root = engine.logical_root(&options);
            // The actual transitive library has passed both module checkers.
            // These expressions retain logical USize and Subtype values at
            // source boundaries, including first-class uses of both leaves.
            let source = br#"
#eval USize.repr (USize.ofNat 0)
#eval USize.repr (USize.ofNat 42)
#eval USize.repr (USize.ofNat 18446744073709551615)
#eval USize.repr (USize.ofNat 18446744073709551616)
#eval let print := USize.repr; print (USize.ofNat 7)
#eval let ofNat := USize.ofNat; USize.repr (ofNat 9)
#eval USize.repr (USize.ofNat (USize.toNat (USize.ofNat 123)))
#eval USize.repr (USize.ofNat System.Platform.numBits)
#eval let width := System.Platform.getNumBits; USize.repr (USize.ofNat (width ()).val)
#eval Nat.repr 0
#eval Nat.repr 127
#eval Nat.repr 128
#eval Nat.repr 18446744073709551615
#eval Nat.repr 18446744073709551616
#eval Nat.repr 123456789012345678901234567890
#eval let print := Nat.repr; print 256
#eval reprStr (42 : Nat)
"#;
            let expected = [
                "0",
                "42",
                "18446744073709551615",
                "0",
                "7",
                "9",
                "123",
                "64",
                "64",
                "0",
                "127",
                "128",
                "18446744073709551615",
                "18446744073709551616",
                "123456789012345678901234567890",
                "256",
                "42",
            ];
            let execute = || {
                engine
                    .execute_source_definitions(
                        &[source],
                        &options,
                        fln::EngineExecutionLimits::new(admission().kernel),
                    )
                    .expect("actual native word printing compiles within default ingress limits")
                    .into_complete()
                    .expect("actual native word printing executes within default VM limits")
            };
            let first = execute();
            assert_eq!(first.executions.len(), expected.len());
            let mut rows = std::collections::BTreeSet::new();
            for (execution, expected) in first.executions.iter().zip(expected) {
                assert_eq!(
                    execution.checker.ground,
                    fln::CheckerAdmissionGround::BodyCheckedAgainstDeclaredType
                );
                let expected = Some(fln::ClosedVmValue::String(expected.to_owned()));
                assert_eq!(fln::closed_vm_value(&execution.exit).unwrap(), expected);
                let decoded =
                    fln_comp::flbc::decode_canonical(&execution.flbc_artifact, Default::default())
                        .unwrap();
                assert_eq!(
                    fln_comp::flbc::encode_canonical(&decoded, Default::default()).unwrap(),
                    execution.flbc_artifact
                );
                for instruction in decoded
                    .functions()
                    .iter()
                    .flat_map(|function| &function.code)
                {
                    if let fln_comp::flbc::Instruction::Intrinsic { row, .. } = instruction {
                        rows.insert(row.clone());
                    }
                }
                let replay = fln::execute_flbc_artifact(
                    &execution.flbc_artifact,
                    &options,
                    Default::default(),
                )
                .unwrap()
                .into_complete()
                .expect("canonical numeric-printer bytecode replays without the source engine");
                assert_eq!(fln::closed_vm_value(&replay).unwrap(), expected);
            }
            for row in [
                "extern:USize.ofNat",
                "extern:USize.toNat",
                "extern:USize.repr",
                "extern:System.Platform.getNumBits",
                "extern:Nat.div",
                "extern:Nat.mod",
            ] {
                assert!(
                    rows.contains(row),
                    "the genuine native leaf remains in bytecode: {row}"
                );
            }
            assert!(!rows.iter().any(|row| row.starts_with("extern:IO.")));
            let repeated = execute();
            for (first, repeated) in first.executions.iter().zip(&repeated.executions) {
                assert_eq!(first.flbc_artifact, repeated.flbc_artifact);
            }
            assert_eq!(engine.logical_root(&options), original_root);
        })
        .unwrap()
        .join()
        .unwrap();
}

fn rendered(engine: &Engine, expression: &str, expected: &str) {
    let source = format!("#eval {expression}");
    let execution = engine
        .execute_source_definitions(
            &[source.as_bytes()],
            &KVMap::new(),
            fln::EngineExecutionLimits::new(admission().kernel),
        )
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .expect("the actual imported Format renderer completes");
    assert_eq!(execution.executions.len(), 1);
    let execution = &execution.executions[0];
    let expected = Some(fln::ClosedVmValue::String(expected.to_owned()));
    assert_eq!(fln::closed_vm_value(&execution.exit).unwrap(), expected);
    let replay =
        fln::execute_flbc_artifact(&execution.flbc_artifact, &KVMap::new(), Default::default())
            .expect("the emitted printer artifact decodes and validates")
            .into_complete()
            .expect("the serialized printer executes without the source engine");
    assert_eq!(fln::closed_vm_value(&replay).unwrap(), expected);
}

#[test]
fn k1_checked_alias_recursive_fields_keep_the_reference_deriving_boundary() {
    use fln_core::expr::{BinderInfo, FVarId};
    use fln_core::level::Level;
    use fln_elab::NatDefinitionElabError;
    use fln_elab::inductive::{ConstructorSpec, InductiveSpec, inductive_declaration};
    use fln_elab::lctx::LocalDecl;
    use fln_elab::records::RecordBudget;
    use fln_elab::source::SourceInferenceError;
    use fln_elab::source::deriving::{DerivingError, elaborate_handler};
    use fln_elab::source::scope::SourceScope;

    // The public elaborator accepts an Environment without admission authority.
    // Build a K1-checked alias signature for that API; the independent checker
    // currently defers this family, so this fixture must never become an Engine.
    fn preserve_child_alias(source: &Expr, family: &Expr, alias: &Expr) -> Expr {
        match source.node() {
            ExprNode::App { f, a } => Expr::app(
                preserve_child_alias(f, family, alias),
                preserve_child_alias(a, family, alias),
            ),
            ExprNode::Lam {
                binder_name,
                binder_type,
                body,
                binder_info,
            }
            | ExprNode::ForallE {
                binder_name,
                binder_type,
                body,
                binder_info,
            } => {
                let domain = if binder_name == &name("child") && binder_type == family {
                    alias.clone()
                } else {
                    preserve_child_alias(binder_type, family, alias)
                };
                let body = preserve_child_alias(body, family, alias);
                if matches!(source.node(), ExprNode::Lam { .. }) {
                    Expr::lam(binder_name.clone(), domain, body, *binder_info)
                } else {
                    Expr::forall_e(binder_name.clone(), domain, body, *binder_info)
                }
            }
            _ => source.clone(),
        }
    }

    fn candidate(label: &str, preserve_alias: bool) -> fln::Declaration {
        let family = Expr::const_(name(label), vec![]);
        let spec = InductiveSpec {
            name: name(label),
            parameters: vec![],
            indices: vec![],
            level_params: vec![],
            result_level: Level::one(),
            constructors: vec![
                ConstructorSpec {
                    name: name("leaf"),
                    fields: vec![],
                    result_indices: vec![],
                },
                ConstructorSpec {
                    name: name("node"),
                    fields: vec![LocalDecl {
                        id: FVarId(name("child")),
                        user_name: name("child"),
                        type_: family.clone(),
                        value: None,
                        binder_info: BinderInfo::Default,
                        index: 0,
                    }],
                    result_indices: vec![],
                },
            ],
        };
        let fln::Declaration::Inductive(mut block) =
            inductive_declaration(&spec, RecordBudget::default()).unwrap()
        else {
            unreachable!()
        };
        if preserve_alias {
            let alias = Expr::app(
                Expr::const_(name("Id"), vec![Level::zero()]),
                family.clone(),
            );
            for constructor in &mut block.ctors {
                constructor.base.type_ =
                    preserve_child_alias(&constructor.base.type_, &family, &alias);
            }
            for recursor in &mut block.recursors {
                recursor.base.type_ = preserve_child_alias(&recursor.base.type_, &family, &alias);
                for rule in &mut recursor.rules {
                    rule.rhs = preserve_child_alias(&rule.rhs, &family, &alias);
                }
            }
        }
        fln::Declaration::Inductive(block)
    }

    std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(|| {
            let Some(imported) = imported() else {
                return;
            };
            let engine = imported
                .engine
                .admit_declaration(
                    candidate("DirectReprChild", false),
                    &KVMap::new(),
                    admission(),
                )
                .unwrap()
                .into_complete()
                .expect("both checkers admit the ordinary recursive control")
                .engine;
            let alias = candidate("AliasedReprChild", true);
            let verdict = fln_kernel::check(engine.environment(), &alias, admission().kernel);
            assert!(
                matches!(
                    &verdict,
                    fln::Outcome::Complete(fln_kernel::verdict::Verdict::Accepted { .. })
                ),
                "the alias and its complete recursor must be K1-checked: {verdict:?}"
            );
            let fln::Declaration::Inductive(block) = alias else {
                unreachable!()
            };
            // This scratch environment is only an elaborator input. It is
            // neither an Engine admission result nor an executable snapshot.
            let mut alias_environment = engine.environment().clone();
            for info in block
                .types
                .into_iter()
                .map(ConstantInfo::Induct)
                .chain(block.ctors.into_iter().map(ConstantInfo::Ctor))
                .chain(block.recursors.into_iter().map(ConstantInfo::Rec))
            {
                alias_environment = alias_environment.add_decl(info).unwrap();
            }
            let constructor = alias_environment
                .find(&name("AliasedReprChild.node"))
                .unwrap()
                .constant_val();
            let ExprNode::ForallE { binder_type, .. } = constructor.type_.node() else {
                unreachable!()
            };
            assert_eq!(
                binder_type,
                &Expr::app(
                    Expr::const_(name("Id"), vec![Level::zero()]),
                    Expr::const_(name("AliasedReprChild"), vec![]),
                ),
                "the elaborator sees the original checked child domain"
            );
            let root = engine.logical_root(&KVMap::new());
            let refused = elaborate_handler(
                &name("Repr"),
                &name("AliasedReprChild"),
                false,
                &alias_environment,
                admission().kernel,
                &SourceScope::default(),
            );
            // The bounded direct-child handler refuses this preserved alias
            // head as an unsupported family before constructing its printer.
            assert!(
                matches!(&refused,
                    Err(NatDefinitionElabError::Inference(SourceInferenceError::Deriving(
                        DerivingError::UnsupportedFamily(family)
                    ))) if family == &name("AliasedReprChild")),
                "the preserved Id child must produce the explicit family refusal: {refused:?}"
            );
            assert_eq!(engine.logical_root(&KVMap::new()), root);
            assert!(!engine.environment().contains(&name("AliasedReprChild")));
            assert!(!alias_environment.contains(&name("instReprAliasedReprChild")));
            assert!(!alias_environment.contains(&name("instReprAliasedReprChild.repr")));
            let direct = elaborate_handler(
                &name("Repr"),
                &name("DirectReprChild"),
                false,
                engine.environment(),
                admission().kernel,
                &SourceScope::default(),
            )
            .expect("ordinary direct recursion still derives after the refusal");
            let admitted = engine
                .admit_declarations(&direct.declarations, &KVMap::new(), admission())
                .unwrap()
                .into_complete()
                .expect("the complete direct printer and dictionary pass both checkers");
            assert!(admitted.engine.environment().contains(&direct.instance));
            assert!(!engine.environment().contains(&direct.instance));
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn admitted_string_quote_executes_escaping_callbacks_and_replays_native_bytecode() {
    std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(|| {
            let Some(imported) = imported() else {
                return;
            };
            let engine = &imported.engine;
            let options = KVMap::new();
            let original_root = engine.logical_root(&options);
            // Init/Data/Repr.lean: String.quote composes the opaque empty test
            // and fold with the ordinary Char.quoteCore body. Control bytes
            // additionally exercise its checked Nat.div/mod and hexadecimal
            // digit helpers; no printer-specific native shortcut is involved.
            let source = r#"
#eval String.quote ""
#eval String.quote "λ😀é'"
#eval String.quote "\n\t\"\\"
#eval String.quote "\x00\x01\x1f\x7f"
"#;
            let expected = [
                "\"\"",
                "\"λ😀é'\"",
                "\"\\n\\t\\\"\\\\\"",
                "\"\\x00\\x01\\x1f\\x7f\"",
            ];
            let execute = || {
                engine
                    .execute_source_definitions(
                        &[source.as_bytes()],
                        &options,
                        fln::EngineExecutionLimits::new(admission().kernel),
                    )
                    .expect("actual String.quote compiles within the default native ingress budget")
                    .into_complete()
                    .expect("actual String.quote executes its source callback natively")
            };
            let first = execute();
            assert_eq!(first.executions.len(), expected.len());
            let mut rows = std::collections::BTreeSet::new();
            for (execution, expected) in first.executions.iter().zip(expected) {
                let expected = Some(fln::ClosedVmValue::String(expected.to_owned()));
                assert_eq!(
                    execution.checker.ground,
                    fln::CheckerAdmissionGround::BodyCheckedAgainstDeclaredType
                );
                assert_eq!(fln::closed_vm_value(&execution.exit).unwrap(), expected);
                let decoded =
                    fln_comp::flbc::decode_canonical(&execution.flbc_artifact, Default::default())
                        .unwrap();
                assert_eq!(
                    fln_comp::flbc::encode_canonical(&decoded, Default::default()).unwrap(),
                    execution.flbc_artifact
                );
                for instruction in decoded
                    .functions()
                    .iter()
                    .flat_map(|function| &function.code)
                {
                    if let fln_comp::flbc::Instruction::Intrinsic { row, .. } = instruction {
                        rows.insert(row.clone());
                    }
                }
                let replay = fln::execute_flbc_artifact(
                    &execution.flbc_artifact,
                    &options,
                    Default::default(),
                )
                .unwrap()
                .into_complete()
                .expect("canonical quoted-string bytecode executes independently of source state");
                assert_eq!(fln::closed_vm_value(&replay).unwrap(), expected);
            }
            for operation in ["foldl", "isEmpty", "append"] {
                assert!(rows.contains(&format!("extern:String.Internal.{operation}")));
            }
            let repeated = execute();
            for (first, repeated) in first.executions.iter().zip(&repeated.executions) {
                assert_eq!(first.flbc_artifact, repeated.flbc_artifact);
            }
            assert_eq!(engine.logical_root(&options), original_root);
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn recursive_repr_uses_child_hypotheses_and_executes_the_real_format_renderer() {
    std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(|| {
            let Some(imported) = imported() else {
                return;
            };
            // The Expr declaration is the unmodified data definition in the
            // pinned Init/Grind/AC.lean, including its three deriving handlers.
            let source = r#"
namespace Lean.Grind.AC
abbrev Var := Nat
inductive Expr where
  | var (x : Var)
  | op (lhs rhs : Expr)
  deriving Inhabited, Repr, BEq
end Lean.Grind.AC
universe u
inductive Chain (A : Type u) where
  | nil
  | cons (head : A) (tail : Chain A)
deriving Repr
inductive Tree (A : Type) where
  | leaf (value : A)
  | branch (left right : Tree A)
deriving Repr
inductive ErasedTree : Type 1 where
  | leaf
  | node (kind : Type) (proof : True) (child : ErasedTree)
deriving Repr
inductive Hidden where
  | leaf
  | node {child : Hidden}
deriving Repr
def generic {A : Type u} [Repr A] : Repr (Chain A) := inferInstance
def genericHelper {A : Type u} [Repr A] : Chain A -> Nat -> Std.Format := instReprChain.repr
theorem boolean :
  (Lean.Grind.AC.Expr.op (.var 7) (.var 9) == Lean.Grind.AC.Expr.op (.var 7) (.var 9)) = true := by rfl
"#;
            let base = &imported.engine;
            let root = base.logical_root(&KVMap::new());
            let result = checked(base, source);
            for (generated, expected) in [
                ("instReprChain", "generic"),
                ("instReprChain.repr", "genericHelper"),
            ] {
                let actual = result.environment().find(&name(generated)).unwrap().constant_val();
                let expected = result.environment().find(&name(expected)).unwrap().constant_val();
                assert_eq!(actual.level_params, expected.level_params);
                assert_eq!(alpha_type(&actual.type_), alpha_type(&expected.type_));
            }
            for (expression, expected) in [
                (
                    "reprStr (Lean.Grind.AC.Expr.op (.var 7) (.var 9))",
                    "Lean.Grind.AC.Expr.op (Lean.Grind.AC.Expr.var 7) (Lean.Grind.AC.Expr.var 9)",
                ),
                (
                    "reprStr (Chain.cons 7 (Chain.cons 9 Chain.nil))",
                    "Chain.cons 7 (Chain.cons 9 (Chain.nil))",
                ),
                (
                    "reprStr (Tree.branch (Tree.leaf 1) (Tree.branch (Tree.leaf 2) (Tree.leaf 3)))",
                    "Tree.branch (Tree.leaf 1) (Tree.branch (Tree.leaf 2) (Tree.leaf 3))",
                ),
                (
                    "reprStr (Tree.leaf (Tree.leaf 7))",
                    "Tree.leaf (Tree.leaf 7)",
                ),
                (
                    "reprStr (ErasedTree.node Nat True.intro ErasedTree.leaf)",
                    "ErasedTree.node _ _ (ErasedTree.leaf)",
                ),
                ("reprStr (@Hidden.node Hidden.leaf)", "Hidden.node"),
            ] {
                rendered(&result, expression, expected);
            }
            assert_eq!(base.logical_root(&KVMap::new()), root);
            assert!(!base.environment().contains(&name("instReprChain")));
            let again = checked(base, source);
            assert_eq!(result.logical_root(&KVMap::new()), again.logical_root(&KVMap::new()));
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn indexed_repr_refines_constructor_indices_and_preserves_the_generic_statement() {
    std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(|| {
            let Some(imported) = imported() else {
                return;
            };
            let result = checked(
                &imported.engine,
                r#"
universe u
inductive Vec (A : Type u) : Nat -> Type u where
  | nil : Vec A 0
  | cons {n : Nat} (head : A) (tail : Vec A n) : Vec A (n + 1)
deriving Repr
inductive Mark : Nat -> Type where
  | zero : Mark 0
  | succ (n : Nat) : Mark (n + 1)
deriving Repr
inductive Grid (A : Type) : Nat -> Nat -> Type where
  | empty : Grid A 0 0
  | step {m n : Nat} (value : A) (child : Grid A m n) : Grid A (m + 1) (n + 2)
deriving Repr
def vecPrinter {A : Type u} {n : Nat} [Repr A] : Repr (Vec A n) := inferInstance
def vecHelper {A : Type u} {n : Nat} [Repr A] : Vec A n -> Nat -> Std.Format := instReprVec.repr
def gridPrinter {A : Type} {m n : Nat} [Repr A] : Repr (Grid A m n) := inferInstance
"#,
            );
            for (generated, expected) in [
                ("instReprVec", "vecPrinter"),
                ("instReprVec.repr", "vecHelper"),
                ("instReprGrid", "gridPrinter"),
            ] {
                let actual = result
                    .environment()
                    .find(&name(generated))
                    .unwrap()
                    .constant_val();
                let expected = result
                    .environment()
                    .find(&name(expected))
                    .unwrap()
                    .constant_val();
                assert_eq!(actual.level_params, expected.level_params);
                assert_eq!(alpha_type(&actual.type_), alpha_type(&expected.type_));
            }
            for (expression, expected) in [
                (
                    "reprStr (Vec.cons 7 (Vec.cons 9 Vec.nil))",
                    "Vec.cons 7 (Vec.cons 9 (Vec.nil))",
                ),
                ("reprStr Mark.zero", "Mark.zero"),
                ("reprStr (Mark.succ 4)", "Mark.succ 4"),
                (
                    "reprStr (Grid.step 7 (Grid.step 9 Grid.empty))",
                    "Grid.step 7 (Grid.step 9 (Grid.empty))",
                ),
            ] {
                rendered(&result, expression, expected);
            }
        })
        .unwrap()
        .join()
        .unwrap();
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
                "inductive Nested where\n | node (children : List Nested)\nderiving Repr",
                "inductive Indexed : Type -> Type 1 where\n | nat : Indexed Nat\n | bool : Indexed Bool\nderiving Repr",
                "structure Partial where\n n : Nat\nderiving Repr, BEq, UnknownHandler",
                "inductive Partial where\n | leaf\n | node (child : Partial)\nderiving Repr, BEq, UnknownHandler",
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

#[test]
fn lean_presentation_executes_actual_printers_and_replays_exact_formats() {
    std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(|| {
            let Some(imported) = imported() else {
                return;
            };
            let engine = checked(
                &imported.engine,
                r#"
inductive PrintTree where
  | leaf (value : Bool)
  | branch (left right : PrintTree)
deriving Repr
structure PrintRecord where
  value : Bool
deriving Repr
inductive Both where | mk
instance : Repr Both where
  reprPrec _ _ := Std.Format.text "selected Repr"
instance : ToString Both where
  toString _ := "incorrect ToString"
inductive StringOnly where | mk
instance : ToString StringOnly where
  toString _ := "unquoted λ\nsecond line"
inductive Counted where | done
instance : Repr Counted where
  reprPrec _ _ := Std.Format.text "done"
def counted : Nat → Counted
  | 0 => .done
  | n + 1 => counted n
"#,
            );
            let limits = fln::EngineExecutionLimits::for_user_program(admission().kernel);
            let original = engine.logical_root(&KVMap::new());
            let mut failures = Vec::new();
            let mut failed = |label: &str, phase: &str, detail: String| {
                let message = format!("{label} {phase}: {detail}");
                eprintln!("checked presentation failure: {message}");
                failures.push(message);
            };
            for (label, source, expected) in [
                ("Bool", "#eval true", "true"),
                ("Nat", "#eval 42", "42"),
                ("String", r#"#eval "λ\n\"quoted\"""#, r#""λ\n\"quoted\"""#),
                ("List", "#eval [true, false]", "[true, false]"),
                ("record", "#eval PrintRecord.mk true", "{ value := true }"),
                (
                    "recursive data",
                    "#eval PrintTree.branch (PrintTree.leaf true) (PrintTree.leaf false)",
                    "PrintTree.branch (PrintTree.leaf true) (PrintTree.leaf false)",
                ),
                ("printer priority", "#eval Both.mk", "selected Repr"),
                ("fallback", "#eval StringOnly.mk", "unquoted λ\nsecond line"),
            ] {
                eprintln!("checked presentation: {label}");
                let executed = match engine.execute_source_commands_with_presentation(
                    source.as_bytes(),
                    &KVMap::new(),
                    limits,
                    fln::EvaluationPresentation::Lean,
                ) {
                    Ok(fln::Outcome::Complete(executed)) => executed,
                    other => {
                        failed(label, "execution", format!("{other:?}"));
                        continue;
                    }
                };
                assert_eq!(executed.batch.executions.len(), 1, "{label}");
                assert_eq!(executed.batch.engine.logical_root(&KVMap::new()), original);
                let execution = &executed.batch.executions[0];
                assert_eq!(execution.evaluation_format_width(), Some(120));
                assert!(execution.io_evaluation_outcome().unwrap().is_none());
                let fln::Declaration::Defn(candidate) = &execution.declaration else {
                    panic!("evaluation creates an ordinary checked definition");
                };
                assert!(!engine.environment().contains(&candidate.base.name));
                assert!(
                    execution
                        .engine
                        .environment()
                        .contains(&candidate.base.name)
                );
                match fln::source_format::render(execution, 120, Default::default()) {
                    Ok(actual) if actual == expected => {}
                    other => {
                        failed(
                            label,
                            "render",
                            format!("expected {expected:?}, got {other:?}"),
                        );
                        continue;
                    }
                }
                let replay = match fln::execute_flbc_artifact(
                    &execution.flbc_artifact,
                    &KVMap::new(),
                    fln::FlbcExecutionLimits {
                        codec: limits.flbc_codec,
                        vm: limits.vm,
                    },
                ) {
                    Ok(fln::Outcome::Complete(replay)) => replay,
                    other => {
                        failed(label, "FLBC replay", format!("{other:?}"));
                        continue;
                    }
                };
                match fln::source_format::render_vm(
                    execution.engine.environment(),
                    &execution.runtime_type,
                    &replay,
                    120,
                    Default::default(),
                ) {
                    Ok(actual) if actual == expected => {}
                    other => {
                        failed(
                            label,
                            "replay render",
                            format!("expected {expected:?}, got {other:?}"),
                        );
                    }
                }
            }

            // A constant printer must neither discard its strict operand nor
            // duplicate it. Compare the VM work added by the same recursive
            // value computation with an existing, explicitly strict raw let.
            let steps = |source: &str, presentation| {
                let executed = engine
                    .execute_source_commands_with_presentation(
                        source.as_bytes(),
                        &KVMap::new(),
                        limits,
                        presentation,
                    )
                    .unwrap()
                    .into_complete()
                    .unwrap();
                let execution = &executed.batch.executions[0];
                assert_eq!(
                    fln::source_format::render(execution, 120, Default::default()).unwrap(),
                    "done",
                );
                let fln::VmExit::Returned(returned) = &execution.exit else {
                    panic!("the strict value computation must return");
                };
                returned.usage.steps
            };
            let lean_zero = steps("#eval counted 0", fln::EvaluationPresentation::Lean);
            let lean_many = steps("#eval counted 40", fln::EvaluationPresentation::Lean);
            let raw_zero = steps(
                "#eval let value := counted 0; Std.Format.text \"done\"",
                fln::EvaluationPresentation::Raw,
            );
            let raw_many = steps(
                "#eval let value := counted 40; Std.Format.text \"done\"",
                fln::EvaluationPresentation::Raw,
            );
            assert!(
                raw_many > raw_zero,
                "the existing raw let retains strict work"
            );
            assert_eq!(lean_many - lean_zero, raw_many - raw_zero);

            let raw = engine
                .execute_source_commands_with_checks(b"#eval true", &KVMap::new(), limits)
                .unwrap()
                .into_complete()
                .unwrap();
            assert_eq!(raw.batch.executions[0].evaluation_format_width(), None);
            assert_eq!(
                fln::closed_vm_shaped_value(
                    &raw.batch.executions[0].exit,
                    &fln::ClosedValueShape::Bool,
                    10,
                )
                .unwrap(),
                fln::ClosedShapedValue::Bool(true),
            );
            assert_eq!(engine.logical_root(&KVMap::new()), original);
            assert!(failures.is_empty(), "{}", failures.join("\n"));
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn lean_presentation_preserves_original_obligations_and_source_transactions() {
    use fln::source_check::modules::execution::SourceProgramLimits;
    use fln_elab::source::SourceInferenceError;
    use fln_elab::source::evaluation::PrintingError;

    fn reason(mut error: &fln::EngineExecutionError) -> &SourceInferenceError {
        while let fln::EngineExecutionError::BatchCommand { error: inner, .. } = error {
            error = inner;
        }
        let fln::EngineExecutionError::Frontend(fln::NatDefinitionFrontendError::Elaborate(
            fln_elab::NatDefinitionElabError::Inference(reason),
        )) = error
        else {
            panic!("expected typed elaboration refusal: {error:?}");
        };
        reason
    }

    std::thread::Builder::new().stack_size(STACK).spawn(|| {
        let Some(imported) = imported() else { return; };
        let engine = checked(&imported.engine, r#"
inductive MissingPrinter where | mk
class Need where
  bit : Bool
def needs [Need] : Bool := true
"#);
        let original = engine.logical_root(&KVMap::new());
        let limits = fln::EngineExecutionLimits::for_user_program(admission().kernel);
        let run = |source: &[u8], options: &KVMap| {
            engine.execute_source_commands_with_presentation(
                source, options, limits, fln::EvaluationPresentation::Lean,
            )
        };
        let missing = run(b"#eval MissingPrinter.mk", &KVMap::new()).unwrap_err();
        assert!(matches!(reason(&missing), SourceInferenceError::EvaluationPrinting(
            PrintingError::MissingPrinter,
        )));
        // The original query has an unsolved dictionary, even though its Bool
        // result has both valid printers. Printer fallback must not catch it.
        let unresolved = run(b"#eval needs", &KVMap::new()).unwrap_err();
        assert!(matches!(reason(&unresolved), SourceInferenceError::InstanceSynthesisRequired));
        let mut options = KVMap::new();
        options.insert(name("format.width"), fln_core::options::DataValue::OfNat(80));
        let width = run(b"#eval true", &options).unwrap_err();
        assert!(matches!(reason(&width), SourceInferenceError::EvaluationPrinting(
            PrintingError::UnsupportedOption(option),
        ) if option == &name("format.width")));
        assert!(run(b"#eval true\n#eval MissingPrinter.mk", &KVMap::new()).is_err());
        assert_eq!(engine.logical_root(&KVMap::new()), original);

        // Receipts select instances in each actual module world and never
        // replay the auxiliary candidates as another source module's exports.
        let library = name("PrintingLibrary");
        let main = name("PrintingMain");
        let library_source = b"prelude\nimport Init.Data.ToString.Basic\ninductive Visible where | mk\ninstance : ToString Visible where\n toString _ := \"receipt fallback\"\n#eval Visible.mk";
        let main_source = b"prelude\nimport PrintingLibrary\n#eval Visible.mk\n#check Visible";
        let modules = [
            SourceModuleInput { name: &main, source: main_source },
            SourceModuleInput { name: &library, source: library_source },
        ];
        let program = imported.execute_source_modules_with_presentation(
            &modules, &main, &KVMap::new(), SourceProgramLimits::new(limits), None,
            fln::EvaluationPresentation::Lean,
        ).unwrap().into_complete().unwrap();
        assert_eq!(program.modules.len(), 2);
        for module in &program.modules {
            let candidate = module.commands.batch.executions.last().unwrap();
            assert_eq!(candidate.evaluation_format_width(), Some(120));
            assert_eq!(
                fln::source_format::render(candidate, 120, Default::default()).unwrap(),
                "receipt fallback",
            );
            let fln::Declaration::Defn(definition) = &candidate.declaration else {
                panic!("checked query candidate");
            };
            assert!(!module.commands.batch.engine.environment().contains(&definition.base.name));
        }
        assert_eq!(program.modules[1].commands.checks.len(), 1);
        assert!(!imported.engine.environment().contains(&name("Visible")));

        let refusal = imported.execute_source_modules_with_presentation(
            &[SourceModuleInput {
                name: &main,
                source: b"prelude\nimport Init.Data.Repr\ninductive NoPrinter where | mk\n#eval NoPrinter.mk",
            }],
            &main, &KVMap::new(), SourceProgramLimits::new(limits), None,
            fln::EvaluationPresentation::Lean,
        ).unwrap_err();
        assert_eq!(refusal.disposition(), ("capability", false, 5));
        assert!(!imported.engine.environment().contains(&name("NoPrinter")));
    }).unwrap().join().unwrap();
}
