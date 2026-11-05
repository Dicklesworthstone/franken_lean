//! Native Hashable deriving against the checked pinned library and Golem.
//!
//! Constructor order, field order, proof hashing and parameter dictionaries
//! follow Lean/Elab/Deriving/Hashable.lean and Deriving/Util.lean at SUITE.lock.
//! Numeric expectations were collected from that pinned executable; the tests
//! execute the independently generated native code and its serialized artifact.
#![forbid(unsafe_code)]

use fln::source_check::modules::imported::{SourceOleanImport, SourceOleanImportLimits};
use fln::{
    Budget, Engine, EngineAdmissionLimits, EngineExecutionLimits, Environment, KVMap, Name,
    OleanCheckLimits, OleanDecodeLimits, OleanFrontierJobs, OleanModuleInput, SourceCheckLimits,
    VmExit,
};
use fln_core::expr::{Expr, ExprNode};
use fln_env::constants::{ConstantInfo, DefinitionSafety};
use std::collections::{BTreeMap, BTreeSet};
use std::num::NonZeroUsize;
use std::path::PathBuf;
use std::sync::OnceLock;

const STACK: usize = 256 * 1024 * 1024;
const BYTES: usize = 512 * 1024 * 1024;

const BASIC: &str = r#"
inductive Color where
  | red
  | green
  | blue
deriving Hashable
structure Marker : Type where
deriving Hashable
inductive Single where
  | field (value : Nat)
deriving Hashable
structure Pair where
  first : Nat
  second : Nat
deriving Hashable
structure Proven where
  first : Nat
  second : Nat
  proof : first = first
deriving Hashable
theorem redHash : hash Color.red = (0 : UInt64) := by rfl
theorem greenHash : hash Color.green = (1 : UInt64) := by rfl
theorem blueHash : hash Color.blue = (2 : UInt64) := by rfl
theorem markerHash : hash Marker.mk = (0 : UInt64) := by rfl
theorem singleHash (n : Nat) : hash (Single.field n) = mixHash 0 (hash n) := by rfl
theorem pairHash (a b : Nat) :
    hash (Pair.mk a b) = mixHash (mixHash 0 (hash a)) (hash b) := by rfl
theorem proofHash (a b : Nat) (h : a = a) :
    hash (Proven.mk a b h) = mixHash (mixHash (mixHash 0 (hash a)) (hash b)) 0 := by rfl
"#;

const BASIC_EVAL: &str = r#"
#eval UInt64.toNat (hash Color.red)
#eval UInt64.toNat (hash Color.green)
#eval UInt64.toNat (hash Color.blue)
#eval UInt64.toNat (hash Marker.mk)
#eval UInt64.toNat (hash (Single.field 5))
#eval UInt64.toNat (hash (Pair.mk 7 11))
#eval UInt64.toNat (hash (Pair.mk 11 7))
#eval UInt64.toNat (hash (Proven.mk 7 11 rfl))
"#;

const CUSTOM: &str = r#"
inductive Token where
  | left
  | right
instance tokenHash : Hashable Token where
  hash _ := 37
structure Capsule where
  token : Token
deriving Hashable
theorem customField : hash (Capsule.mk Token.left) = mixHash 0 37 := by rfl
structure Generic (A : Type) where
  value : A
deriving Hashable
def suppliedHash : Hashable Nat := { hash := fun _ => 19 }
theorem callerDictionary :
    @instHashableGeneric.hash Nat suppliedHash (Generic.mk 7) = mixHash 0 19 := by rfl
theorem ordinaryDictionary : hash (Generic.mk 7) = mixHash 0 (hash (7 : Nat)) := by rfl
instance truthHash : Hashable True where
  hash _ := 23
structure Evidence where
  proof : True
deriving Hashable
theorem customProof : hash (Evidence.mk True.intro) = mixHash 0 23 := by rfl
"#;

const CUSTOM_EVAL: &str = r#"
#eval UInt64.toNat (hash (Capsule.mk Token.left))
#eval UInt64.toNat (hash (Capsule.mk Token.right))
#eval UInt64.toNat (@instHashableGeneric.hash Nat suppliedHash (Generic.mk 7))
#eval UInt64.toNat (hash (Generic.mk 7))
#eval UInt64.toNat (hash (Evidence.mk True.intro))
"#;

const RECURSIVE: &str = r#"
namespace Wire
inductive Tree (A : Type) where
  | leaf (value : A)
  | branch (left right : Tree A)
deriving Hashable
def tree : Tree Nat := .branch (.leaf 7) (.branch (.leaf 11) (.leaf 13))
theorem leafHash (n : Nat) : hash (Tree.leaf n) = mixHash 0 (hash n) := by rfl
theorem branchHash (left right : Tree Nat) :
    hash (Tree.branch left right) = mixHash (mixHash 1 (hash left)) (hash right) := by rfl
inductive Indexed (A : Type) : Nat -> Type where
  | leaf (value : A) : Indexed A 0
  | next {n : Nat} (previous : Indexed A n) : Indexed A (Nat.succ n)
deriving Hashable
theorem nextHash (n : Nat) (previous : Indexed Nat n) :
    hash (Indexed.next previous) = mixHash (mixHash 1 (hash n)) (hash previous) := by rfl
inductive Tagged : Nat -> Type where
  | mk (index value : Nat) : Tagged index
deriving Hashable
-- The uniform index is promoted to a parameter, so it is not a hashed field.
theorem taggedHash (index value : Nat) :
    hash (Tagged.mk index value) = mixHash 0 (hash value) := by rfl
end Wire
"#;

const RECURSIVE_EVAL: &str = r#"
#eval UInt64.toNat (hash Wire.tree)
#eval UInt64.toNat (hash (Wire.Tree.branch (.leaf 11) (.leaf 7)))
#eval UInt64.toNat (hash (Wire.Tree.branch (.leaf 7) (.leaf 11)))
#eval UInt64.toNat (hash (Wire.Tree.leaf (Wire.Tree.leaf 7)))
#eval UInt64.toNat (hash (Wire.Indexed.next (Wire.Indexed.next (Wire.Indexed.leaf 5))))
#eval UInt64.toNat (hash (Wire.Tagged.mk 3 5))
"#;

const HEADERS: &str = r#"
namespace Library
structure Box (A B : Type) where
  value : A
deriving Hashable
def expected {A B : Type} [Hashable A] [Hashable B] : Hashable (Box A B) := inferInstance
def expectedHelper {A B : Type} [Hashable A] [Hashable B] : Box A B -> UInt64 := instHashableBox.hash
end Library
inductive Poly.{u} (A : Type u) where
  | value (a : A)
deriving Hashable
def polyExpected.{u} {A : Type u} [Hashable A] : Hashable (Poly A) := inferInstance
structure ProofBox (P : Prop) where
  proof : P
deriving Hashable
def proofExpected {P : Prop} [Hashable P] : Hashable (ProofBox P) := inferInstance
inductive NoValues where
deriving Hashable
def emptyExpected : Hashable NoValues := inferInstance
def emptyHelper : NoValues -> UInt64 := instHashableNoValues.hash
"#;

const LOCAL_NUMERAL: &str = r#"
namespace LiteralScope
local instance (priority := 2000) customZero : OfNat UInt64 0 where
  ofNat := UInt64.ofNat 23
inductive Altered where
  | first
  | second
deriving Hashable
structure Carry where
  value : Nat
deriving Hashable
theorem firstHash : hash Altered.first = UInt64.ofNat 23 := by rfl
theorem secondHash : hash Altered.second = UInt64.ofNat 1 := by rfl
theorem fieldHash : hash (Carry.mk 5) = mixHash (UInt64.ofNat 23) (hash (5 : Nat)) := by rfl
end LiteralScope
"#;

const LOCAL_NUMERAL_EVAL: &str = r#"
#eval UInt64.toNat (hash LiteralScope.Altered.first)
#eval UInt64.toNat (hash LiteralScope.Altered.second)
#eval UInt64.toNat (hash (LiteralScope.Carry.mk 5))
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
                    "the pinned Reference library is required"
                );
                eprintln!("SKIP: pinned Reference lib/lean absent");
                return None;
            };
            let roots = [name("Init.Data.Hashable")];
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
                    .expect("import the actual pinned Hashable and UInt64 dependency closure")
                    .into_complete()
                    .expect("the original library closure passes both checking engines"),
            )
        })
        .as_ref()
}

fn with_imported(run: impl FnOnce(&Engine) + Send + 'static) {
    std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(move || {
            if let Some(imported) = imported() {
                run(&imported.engine);
            }
        })
        .unwrap()
        .join()
        .unwrap();
}

fn checked(base: &Engine, source: &str) -> Engine {
    base.check_source_files(
        &[source.as_bytes()],
        &KVMap::new(),
        SourceCheckLimits::new(admission()),
    )
    .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
    .into_complete()
    .expect("the generated helper and dictionary pass both checking engines")
    .engine
}

fn assert_generated(engine: &Engine, base: &Engine, names: &[&str]) {
    for generated in names {
        let Some(ConstantInfo::Defn(definition)) = engine.environment().find(&name(generated))
        else {
            panic!("missing checked generated declaration {generated}");
        };
        assert_eq!(definition.safety, DefinitionSafety::Safe);
        assert!(!definition.value.has_expr_mvar());
        assert!(!definition.value.has_level_mvar());
        assert!(!definition.value.has_fvar());
        assert!(!definition.value.has_loose_bvars());
        assert!(!base.environment().contains(&name(generated)));
    }
}

fn execute_and_replay(engine: &Engine, source: &str, expected: &[&str]) -> Vec<Vec<u8>> {
    let report = engine
        .execute_source_definitions(
            &[source.as_bytes()],
            &KVMap::new(),
            EngineExecutionLimits::new(admission().kernel),
        )
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .expect("hashing completes within the default native ingress and VM budgets");
    assert_eq!(report.executions.len(), expected.len());
    let mut artifacts = Vec::new();
    let mut rows = BTreeSet::new();
    for (execution, expected) in report.executions.iter().zip(expected) {
        let VmExit::Returned(value) = &execution.exit else {
            panic!("hashing did not return normally");
        };
        assert_eq!(fln::nat_decimal(&value.value).as_deref(), Some(*expected));
        let decoded =
            fln_comp::flbc::decode_canonical(&execution.flbc_artifact, Default::default()).unwrap();
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
        let replay =
            fln::execute_flbc_artifact(&execution.flbc_artifact, &KVMap::new(), Default::default())
                .expect("the emitted hash artifact decodes and validates")
                .into_complete()
                .expect("the hash artifact executes independently of the source engine");
        let VmExit::Returned(value) = replay else {
            panic!("hash artifact replay did not return normally");
        };
        assert_eq!(fln::nat_decimal(&value.value).as_deref(), Some(*expected));
        artifacts.push(execution.flbc_artifact.clone());
    }
    assert!(rows.contains("extern:mixHash"));
    assert!(rows.contains("extern:UInt64.toNat"));
    artifacts
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
fn constructor_tags_fields_and_proofs_match_the_pinned_hashes() {
    with_imported(|base| {
        let before = base.logical_root(&KVMap::new());
        let engine = checked(base, BASIC);
        assert_generated(
            &engine,
            base,
            &[
                "instHashableColor",
                "instHashableColor.hash",
                "instHashableMarker",
                "instHashableSingle.hash",
                "instHashablePair.hash",
                "instHashableProven.hash",
            ],
        );
        let expected = [
            "0",
            "1",
            "2",
            "0",
            "5501096720095961210",
            "6296794202839683667",
            "11814235083094005023",
            "4195240386091499582",
        ];
        let first = execute_and_replay(&engine, BASIC_EVAL, &expected);
        assert_eq!(first, execute_and_replay(&engine, BASIC_EVAL, &expected));
        assert_eq!(
            engine.logical_root(&KVMap::new()),
            checked(base, BASIC).logical_root(&KVMap::new())
        );
        assert_eq!(base.logical_root(&KVMap::new()), before);
    });
}

#[test]
fn custom_field_and_caller_dictionaries_control_every_hash_step() {
    with_imported(|base| {
        let engine = checked(base, CUSTOM);
        execute_and_replay(
            &engine,
            CUSTOM_EVAL,
            &[
                "13989847278829940948",
                "13989847278829940948",
                "3106170259298582834",
                "483365771082190995",
                "8486839563459890144",
            ],
        );
    });
}

#[test]
fn recursive_children_and_data_indices_have_native_replayable_hashes() {
    with_imported(|base| {
        let engine = checked(base, RECURSIVE);
        assert_generated(
            &engine,
            base,
            &[
                "Wire.instHashableTree.hash",
                "Wire.instHashableIndexed.hash",
                "Wire.instHashableTagged.hash",
            ],
        );
        execute_and_replay(
            &engine,
            RECURSIVE_EVAL,
            &[
                "5240817053524270926",
                "14398943243567572361",
                "11046233873854671177",
                "12700993116076150231",
                "7631423895461570371",
                "5501096720095961210",
            ],
        );
    });
}

#[test]
fn phantom_universe_and_proposition_parameters_and_empty_types_keep_the_pin_header() {
    with_imported(|base| {
        let engine = checked(base, HEADERS);
        for (generated, expected) in [
            ("Library.instHashableBox", "Library.expected"),
            ("Library.instHashableBox.hash", "Library.expectedHelper"),
            ("instHashablePoly", "polyExpected"),
            ("instHashableProofBox", "proofExpected"),
            ("instHashableNoValues", "emptyExpected"),
            ("instHashableNoValues.hash", "emptyHelper"),
        ] {
            let generated = engine
                .environment()
                .find(&name(generated))
                .unwrap()
                .constant_val();
            let expected = engine
                .environment()
                .find(&name(expected))
                .unwrap()
                .constant_val();
            assert_eq!(generated.level_params, expected.level_params);
            assert_eq!(alpha_type(&generated.type_), alpha_type(&expected.type_));
        }
        assert_generated(
            &engine,
            base,
            &["instHashableNoValues", "instHashableNoValues.hash"],
        );
    });
}

#[test]
fn constructor_ordinals_respect_the_scoped_numeric_instance() {
    with_imported(|base| {
        let engine = checked(base, LOCAL_NUMERAL);
        execute_and_replay(
            &engine,
            LOCAL_NUMERAL_EVAL,
            &["23", "1", "3889790485765161961"],
        );
    });
}

#[test]
fn standalone_hashable_deriving_preserves_field_order_and_deterministic_replay() {
    with_imported(|base| {
        let engine = checked(
            base,
            r#"
structure Pair where
  first : Nat
  second : Nat
deriving instance Hashable for Pair
theorem orderedHash (a b : Nat) :
    hash (Pair.mk a b) = mixHash (mixHash 0 (hash a)) (hash b) := by rfl
"#,
        );
        assert_generated(
            &engine,
            base,
            &["instHashablePair", "instHashablePair.hash"],
        );
        let program =
            "#eval UInt64.toNat (hash (Pair.mk 7 11))\n#eval UInt64.toNat (hash (Pair.mk 11 7))";
        let expected = ["6296794202839683667", "11814235083094005023"];
        let first = execute_and_replay(&engine, program, &expected);
        assert_eq!(first, execute_and_replay(&engine, program, &expected));
    });
}

#[test]
fn missing_field_instances_invalid_hash_proofs_and_unfinished_batches_do_not_publish() {
    with_imported(|base| {
        let before = base.logical_root(&KVMap::new());
        for source in [
            "structure Missing where\n run : Nat -> Nat\nderiving Hashable",
            "structure TypeField where\n carrier : Type\nderiving Hashable",
            "structure Partial where\n value : Nat\nderiving Hashable, UnknownHandler",
            "inductive WrongTag where\n | first\n | second\nderiving Hashable\ntheorem bad : hash WrongTag.second = (0 : UInt64) := by rfl",
            "inductive Nested where\n | node (children : List Nested)\nderiving Hashable",
            "inductive FunctionRecursive where\n | node (children : Nat -> FunctionRecursive)\nderiving Hashable",
        ] {
            assert!(
                base.check_source_files(
                    &[source.as_bytes()],
                    &KVMap::new(),
                    SourceCheckLimits::new(admission()),
                )
                .is_err(),
                "must refuse without publishing an incomplete dictionary: {source}"
            );
            assert_eq!(base.logical_root(&KVMap::new()), before);
        }
        let recovered = checked(
            base,
            "inductive Recovery where\n | ok\nderiving Hashable\ntheorem recovered : hash Recovery.ok = (0 : UInt64) := by rfl",
        );
        assert_generated(
            &recovered,
            base,
            &["instHashableRecovery", "instHashableRecovery.hash"],
        );
    });
}
