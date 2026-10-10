//! Native derived equality crosses source elaboration, both judges and Golem.
//!
//! The ordinary constructor/recursive cases follow the retained pinned suite
//! `vendor/lean4-src/tests/elab/derivingBEq.lean`. The helper telescope follows
//! `Lean/Elab/Deriving/Util.lean`; these tests do not claim a new oracle run.
#![forbid(unsafe_code)]

use fln::source_check::modules::SourceModuleCheckLimits;
use fln::{
    Budget, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap, Name, SourceCheckLimits,
    SourceModuleInput, VmExit,
};
use fln_core::expr::{Expr, ExprNode};
use fln_env::constants::{ConstantInfo, DefinitionSafety};

fn name(text: &str) -> Name {
    Name::from_components(text.split('.'))
}

fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}

fn engine() -> Engine {
    Engine::with_source_seed(limits())
        .unwrap()
        .into_complete()
        .unwrap()
}

fn checked(base: &Engine, source: &str) -> Engine {
    base.check_source_files(
        &[source.as_bytes()],
        &KVMap::new(),
        SourceCheckLimits::new(limits()),
    )
    .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
    .into_complete()
    .expect("the generated helper and dictionary pass both checking engines")
    .engine
}

const RECURSIVE: &str = r#"
namespace Wire
inductive Chain (A : Type) where
  | nil
  | cons (head : A) (tail : Chain A)
deriving BEq
inductive Tree (A : Type) where
  | leaf (value : A)
  | branch (left right : Tree A)
deriving BEq
end Wire
def first : Wire.Chain Nat := .cons 7 (.cons 11 .nil)
def second : Wire.Chain Nat := .cons 7 (.cons 12 .nil)
def tree : Wire.Tree Nat := .branch (.leaf 7) (.branch (.leaf 11) (.leaf 12))
"#;

#[test]
fn enum_record_and_proof_fields_have_checked_boolean_equality() {
    let base = engine();
    let source = r#"
inductive Color where
  | red
  | green
  | blue
deriving BEq
structure Packet where
  number : Nat
  color : Color
  proof : number = number
deriving BEq
structure Marker : Type where
deriving BEq
theorem red_yes : (Color.red == Color.red) = true := by rfl
theorem red_no : (Color.red == Color.blue) = false := by rfl
theorem blue_yes : (Color.blue == Color.blue) = true := by rfl
theorem same : (Packet.mk 7 .red rfl == Packet.mk 7 .red rfl) = true := by rfl
theorem first_field : (Packet.mk 7 .red rfl == Packet.mk 8 .red rfl) = false := by rfl
theorem last_field : (Packet.mk 7 .red rfl == Packet.mk 7 .blue rfl) = false := by rfl
theorem marker_yes : (Marker.mk == Marker.mk) = true := by rfl
"#;
    let result = checked(&base, source);
    for generated in [
        "instBEqColor",
        "instBEqColor.beq",
        "instBEqPacket",
        "instBEqPacket.beq",
    ] {
        let Some(ConstantInfo::Defn(definition)) = result.environment().find(&name(generated))
        else {
            panic!("missing generated declaration {generated}");
        };
        assert_eq!(definition.safety, DefinitionSafety::Safe);
        assert!(!definition.value.has_expr_mvar());
        assert!(!definition.value.has_level_mvar());
        assert!(!definition.value.has_fvar());
        assert!(!definition.value.has_loose_bvars());
        assert!(!base.environment().contains(&name(generated)));
    }
    assert_eq!(
        result.logical_root(&KVMap::new()),
        checked(&base, source).logical_root(&KVMap::new())
    );
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
fn parameter_hypotheses_and_generated_names_follow_the_pinned_header() {
    let result = checked(
        &engine(),
        r#"
namespace Library
structure Box (A B : Type) where
  value : A
deriving BEq
def expected {A B : Type} [BEq A] [BEq B] : BEq (Box A B) := inferInstance
def expectedHelper {A B : Type} [BEq A] [BEq B] : Box A B -> Box A B -> Bool := instBEqBox.beq
def natural : Box Nat Nat := { value := 7 }
theorem same : (natural == natural) = true := by rfl
end Library
inductive Poly.{u} (A : Type u) where
  | value (a : A)
deriving BEq
def polyExpected.{u} {A : Type u} [BEq A] : BEq (Poly A) := inferInstance
"#,
    );
    for (generated, expected) in [
        ("Library.instBEqBox", "Library.expected"),
        ("Library.instBEqBox.beq", "Library.expectedHelper"),
        ("instBEqPoly", "polyExpected"),
    ] {
        let generated = result
            .environment()
            .find(&name(generated))
            .unwrap()
            .constant_val();
        let expected = result
            .environment()
            .find(&name(expected))
            .unwrap()
            .constant_val();
        assert_eq!(generated.level_params, expected.level_params);
        assert_eq!(alpha_type(&generated.type_), alpha_type(&expected.type_));
    }
}

#[test]
fn recursive_lists_and_multiple_recursive_fields_compute_and_execute() {
    let source = format!(
        r#"{RECURSIVE}
theorem same_chain : (first == first) = true := by rfl
theorem changed_tail : (first == second) = false := by rfl
theorem different_ctor : (first == Wire.Chain.nil) = false := by rfl
theorem nil_same : ((Wire.Chain.nil : Wire.Chain Nat) == (Wire.Chain.nil : Wire.Chain Nat)) = true := by rfl
theorem tree_same : (tree == tree) = true := by rfl
theorem left_diff : (Wire.Tree.branch (.leaf 7) (.leaf 9) == Wire.Tree.branch (.leaf 8) (.leaf 9)) = false := by rfl
theorem right_diff : (Wire.Tree.branch (.leaf 7) (.leaf 8) == Wire.Tree.branch (.leaf 7) (.leaf 9)) = false := by rfl
theorem different_shape : (Wire.Tree.branch (.leaf 7) (.leaf 7) == Wire.Tree.leaf 7) = false := by rfl
"#
    );
    let result = checked(&engine(), &source);
    let program = b"#eval if first == second then 0 else if tree == tree then 42 else 1";
    let run = || {
        result
            .execute_source_definitions(
                &[program],
                &KVMap::new(),
                EngineExecutionLimits::new(limits().kernel),
            )
            .unwrap()
            .into_complete()
            .unwrap()
    };
    let first = run();
    let VmExit::Returned(value) = &first.executions[0].exit else {
        panic!("derived recursive equality must return normally")
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
        Some("42")
    );
    assert_eq!(
        first.executions[0].flbc_artifact,
        run().executions[0].flbc_artifact
    );
}

#[test]
fn derived_equality_uses_field_dictionaries_instead_of_propositional_equality() {
    checked(
        &engine(),
        r#"
inductive Token where
  | left
  | right
instance : BEq Token where
  beq _ _ := true
structure Box where
  token : Token
deriving BEq
theorem custom : (Box.mk .left == Box.mk .right) = true := by rfl
structure PolyBox (A : Type) [BEq A] where
  value : A
deriving BEq
def expected {A : Type} {i : BEq A} [BEq A] : BEq (@PolyBox A i) := @instBEqPolyBox A i inferInstance
theorem dictionary : ((PolyBox.mk Token.left) == (PolyBox.mk Token.right)) = true := by rfl
"#,
    );
}

#[test]
fn generated_dictionaries_survive_module_replay_and_combined_deriving() {
    let library = name("Library");
    let main = name("Main");
    let modules = [
        SourceModuleInput {
            name: &library,
            source: b"namespace Data\ninductive Choice (A : Type) where\n | empty\n | value (a : A)\nderiving Inhabited, BEq\nend Data",
        },
        SourceModuleInput {
            name: &main,
            source: b"import Library\ndef chosen : Data.Choice Nat := default\ntheorem imported_equal : (chosen == Data.Choice.empty) = true := by rfl\ntheorem imported_different : (chosen == Data.Choice.value 7) = false := by rfl",
        },
    ];
    let result = engine()
        .check_source_modules(
            &modules,
            &main,
            &KVMap::new(),
            SourceModuleCheckLimits::new(SourceCheckLimits::new(limits())),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    for generated in [
        "Data.instBEqChoice",
        "Data.instBEqChoice.beq",
        "imported_equal",
        "imported_different",
    ] {
        assert!(
            result
                .checked
                .engine
                .environment()
                .contains(&name(generated)),
            "{generated}"
        );
    }
}

#[test]
fn false_equalities_missing_field_instances_and_incomplete_batches_are_rejected() {
    let base = engine();
    let before = base.logical_root(&KVMap::new());
    for source in [
        "inductive Color where\n | red\n | blue\nderiving BEq\ntheorem bad : (Color.red == Color.blue) = true := by rfl",
        "structure Box where\n value : Nat\nderiving BEq\ntheorem bad : (Box.mk 7 == Box.mk 8) = true := by rfl",
        "structure Missing where\n run : Nat -> Nat\nderiving BEq",
        "structure Dependent where\n carrier : Type\n value : carrier\nderiving BEq",
        "structure Point where\n value : Nat\nderiving BEq, DecidableEq",
    ] {
        assert!(
            base.check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits()),
            )
            .is_err(),
            "must refuse: {source}"
        );
        assert_eq!(base.logical_root(&KVMap::new()), before);
    }
    checked(
        &base,
        "inductive Retry where\n | ok\nderiving BEq\ntheorem recovered : (Retry.ok == Retry.ok) = true := by rfl",
    );
}
