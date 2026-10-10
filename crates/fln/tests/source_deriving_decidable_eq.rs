//! Derived decisions contain real equality/refutation proofs and execute natively.
//! Shapes follow the pinned Deriving/DecEq.lean and Deriving/Util.lean sources;
//! these tests do not claim a fresh run of the Reference executable.
#![forbid(unsafe_code)]
use fln::source_check::modules::SourceModuleCheckLimits;
use fln::{
    Budget, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap, Name, SourceCheckLimits,
    SourceModuleInput, VmExit, execute_flbc_artifact,
};
use fln_core::expr::{Expr, ExprNode};
use fln_env::constants::{ConstantInfo, DefinitionSafety};

fn n(text: &str) -> Name {
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
    .expect("the generated decision proofs pass both checking engines")
    .engine
}

const CHAIN: &str = "inductive Chain (A : Type) where\n\
    | nil\n\
    | cons (head : A) (tail : Chain A)\n\
    deriving DecidableEq\n";

#[test]
fn enums_and_empty_types_supply_decidable_propositions() {
    checked(
        &engine(),
        r#"
        inductive Color where
          | red | green | blue
        deriving DecidableEq
        theorem self : Color.red = Color.red := by decide
        theorem different : Not (Color.red = Color.blue) := by decide
        theorem computed_yes : decide (Color.green = Color.green) = true := by rfl
        theorem computed_no : decide (Color.green = Color.blue) = false := by rfl
        inductive NoValues where
        deriving DecidableEq
        def emptyDecision : DecidableEq NoValues := inferInstance
    "#,
    );
}

#[test]
fn records_prove_equalities_and_refute_each_unequal_field() {
    let base = engine();
    let result = checked(
        &base,
        r#"
        structure Point where
          x : Nat
          y : Nat
        deriving DecidableEq
        theorem self : Point.mk 7 9 = Point.mk 7 9 := by decide
        theorem first : Not (Point.mk 7 9 = Point.mk 8 9) := by decide
        theorem second : Not (Point.mk 7 9 = Point.mk 7 8) := by decide
        theorem boolean_bridge : (Point.mk 7 9 == Point.mk 7 8) = false := by rfl
        structure Marker : Type where
        deriving DecidableEq
        theorem singleton : Marker.mk = Marker.mk := by decide
    "#,
    );
    for generated in [
        "instDecidableEqPoint",
        "instDecidableEqPoint.decEq",
        "instDecidableEqMarker",
    ] {
        let Some(ConstantInfo::Defn(definition)) = result.environment().find(&n(generated)) else {
            panic!("missing checked generated declaration {generated}");
        };
        assert_eq!(definition.safety, DefinitionSafety::Safe);
        assert!(!definition.value.has_fvar());
        assert!(!definition.value.has_loose_bvars());
        assert!(!definition.value.has_expr_mvar());
        assert!(!definition.value.has_level_mvar());
        assert!(!base.environment().contains(&n(generated)));
    }
}

#[test]
fn proof_fields_and_dependent_remaining_telescopes_are_transported() {
    checked(
        &engine(),
        r#"
        structure Checked where
          count : Nat
          proof : count = count
        deriving DecidableEq
        theorem proofs (p q : 7 = 7) : Checked.mk 7 p = Checked.mk 7 q := by decide
        theorem unequal : Not (Checked.mk 7 (Eq.refl 7) = Checked.mk 8 (Eq.refl 8)) := by decide
        structure Sized (n : Nat) where
          value : Nat
        deriving DecidableEq
        structure Dependent where
          size : Nat
          value : Sized size
        deriving DecidableEq
        theorem dependent_same : Dependent.mk 2 (@Sized.mk 2 7) = Dependent.mk 2 (@Sized.mk 2 7) := by decide
        theorem dependent_value : Not (Dependent.mk 2 (@Sized.mk 2 7) = Dependent.mk 2 (@Sized.mk 2 8)) := by decide
        theorem dependent_index : Not (Dependent.mk 2 (@Sized.mk 2 7) = Dependent.mk 3 (@Sized.mk 3 7)) := by decide
    "#,
    );
}

#[test]
fn recursive_lists_use_real_child_decisions() {
    let source = format!(
        "{CHAIN}
        def first : Chain Nat := Chain.cons 7 (Chain.cons 9 Chain.nil)
        theorem self : first = first := by decide
        theorem payload : Not (Chain.cons 7 Chain.nil = Chain.cons 8 Chain.nil) := by decide
        theorem tail : Not (first = Chain.cons 7 (Chain.cons 8 Chain.nil)) := by decide
        theorem length : Not (first = Chain.cons 7 Chain.nil) := by decide
        theorem constructor : Not (first = Chain.nil) := by decide
        theorem opposite_constructor : Not (Chain.nil = first) := by decide
        theorem computed : decide (first = first) = true := by rfl"
    );
    let base = engine();
    let first = checked(&base, &source);
    let again = checked(&base, &source);
    assert_eq!(
        first.logical_root(&KVMap::new()),
        again.logical_root(&KVMap::new())
    );
}

#[test]
fn multiple_recursive_children_and_nested_parameter_instances_remain_distinct() {
    checked(
        &engine(),
        r#"
        inductive Tree (A : Type) where
          | leaf (value : A)
          | branch (left right : Tree A)
        deriving DecidableEq
        def tree : Tree Nat := Tree.branch (Tree.leaf 1) (Tree.branch (Tree.leaf 2) (Tree.leaf 3))
        theorem self : tree = tree := by decide
        theorem left : Not (tree = Tree.branch (Tree.leaf 9) (Tree.branch (Tree.leaf 2) (Tree.leaf 3))) := by decide
        theorem right : Not (tree = Tree.branch (Tree.leaf 1) (Tree.branch (Tree.leaf 2) (Tree.leaf 9))) := by decide
        theorem nested_parameter :
          (Tree.leaf (Tree.leaf 7) : Tree (Tree Nat)) = Tree.leaf (Tree.leaf 7) := by decide
    "#,
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
fn generic_instance_and_helper_statements_follow_the_pinned_header() {
    let result = checked(
        &engine(),
        r#"
        universe u v
        namespace Library
        structure Box (A : Type u) (B : Type v) where
          value : A
        deriving DecidableEq
        def expected {A : Type u} {B : Type v} [DecidableEq A] [DecidableEq B] : DecidableEq (Box A B) := inferInstance
        def expectedHelper {A : Type u} {B : Type v} [DecidableEq A] [DecidableEq B] (x y : Box A B) : Decidable (x = y) := instDecidableEqBox.decEq x y
        end Library
    "#,
    );
    for (generated, expected) in [
        ("Library.instDecidableEqBox", "Library.expected"),
        ("Library.instDecidableEqBox.decEq", "Library.expectedHelper"),
    ] {
        let generated = result
            .environment()
            .find(&n(generated))
            .unwrap()
            .constant_val();
        let expected = result
            .environment()
            .find(&n(expected))
            .unwrap()
            .constant_val();
        assert_eq!(generated.level_params, expected.level_params);
        assert_eq!(alpha_type(&generated.type_), alpha_type(&expected.type_));
    }
}

#[test]
fn combined_deriving_and_source_module_replay_publish_real_instances() {
    let main = n("Main");
    let library = n("Library");
    let modules = [
        SourceModuleInput {
            name: &library,
            source: b"namespace Data\ninductive Choice (A : Type) where\n | empty\n | value (a : A)\nderiving Inhabited, BEq, DecidableEq\nend Data",
        },
        SourceModuleInput {
            name: &main,
            source: b"import Library\ndef chosen : Data.Choice Nat := default\ntheorem imported : chosen = Data.Choice.empty := by decide\ntheorem unequal : Not (chosen = Data.Choice.value 7) := by decide",
        },
    ];
    let checked = engine()
        .check_source_modules(
            &modules,
            &main,
            &KVMap::new(),
            SourceModuleCheckLimits::new(SourceCheckLimits::new(limits())),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    for name in [
        "Data.instDecidableEqChoice",
        "Data.instDecidableEqChoice.decEq",
        "imported",
        "unequal",
    ] {
        assert!(
            checked.checked.engine.environment().contains(&n(name)),
            "{name}"
        );
    }
}

#[test]
fn unprovable_equalities_unsupported_fields_and_late_handlers_roll_back() {
    let base = engine();
    let root = base.logical_root(&KVMap::new());
    for suffix in [
        "structure Bad where\n run : Nat -> Nat\nderiving DecidableEq",
        "structure Bad where\n carrier : Type\n value : carrier\nderiving DecidableEq",
        "inductive Bad : Nat -> Type where\n | zero : Bad 0\nderiving DecidableEq",
        "inductive Bad where\n | node (children : List Bad)\nderiving DecidableEq",
        "structure Bad where\n n : Nat\nderiving Inhabited, BEq, DecidableEq, UnknownHandler",
        "structure Bad where\n n : Nat\nderiving DecidableEq\ntheorem bad : Bad.mk 1 = Bad.mk 2 := by decide",
    ] {
        let source = format!("def prefix : Nat := 7\n{suffix}");
        assert!(
            base.check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits()),
            )
            .is_err(),
            "{source}"
        );
        assert_eq!(base.logical_root(&KVMap::new()), root);
        for name in [
            "prefix",
            "Bad",
            "instDecidableEqBad",
            "instDecidableEqBad.decEq",
        ] {
            assert!(!base.environment().contains(&n(name)), "{name}");
        }
    }
    checked(
        &base,
        "structure Bad where\n n : Nat\nderiving DecidableEq\ntheorem recovered : Bad.mk 7 = Bad.mk 7 := by decide",
    );
}

#[test]
fn native_vm_executes_decidable_equality_and_replays_canonical_bytecode() {
    let base = checked(
        &engine(),
        &format!(
            "{CHAIN}
        def lhs : Chain Nat := Chain.cons 7 (Chain.cons 9 Chain.nil)
        def rhs : Chain Nat := Chain.cons 7 (Chain.cons 8 Chain.nil)"
        ),
    );
    let program = b"#eval if lhs = lhs then 42 else 0\n#eval if lhs = rhs then 0 else 42";
    let run = || {
        base.execute_source_definitions(
            &[program],
            &KVMap::new(),
            EngineExecutionLimits::new(limits().kernel),
        )
        .unwrap()
        .into_complete()
        .unwrap()
    };
    let first = run();
    let again = run();
    assert_eq!(first.executions.len(), 2);
    for (execution, recompiled) in first.executions.iter().zip(&again.executions) {
        let VmExit::Returned(value) = &execution.exit else {
            panic!("decision did not return: {:?}", execution.exit);
        };
        assert_eq!(
            fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
            Some("42")
        );
        assert_eq!(execution.flbc_artifact, recompiled.flbc_artifact);
        let replay =
            execute_flbc_artifact(&execution.flbc_artifact, &KVMap::new(), Default::default())
                .expect("the emitted canonical artifact decodes and validates")
                .into_complete()
                .expect("the saved equality decision executes without the source engine");
        let VmExit::Returned(value) = &replay else {
            panic!("replayed decision did not return: {replay:?}");
        };
        assert_eq!(
            fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
            Some("42")
        );
    }
}
