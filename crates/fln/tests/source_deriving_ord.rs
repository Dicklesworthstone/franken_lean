//! Native Ord deriving uses checked definitions and field dictionaries.
//!
//! The source fixture below declares the Ordering and Ord shapes from the
//! retained Init/Data/Ord/Basic.lean. The deriving behavior follows
//! Lean/Elab/Deriving/Ord.lean and Util.lean. These seed-only tests need no
//! installed Reference and do not claim an upstream executable comparison.
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

fn checked(base: &Engine, source: &str) -> Engine {
    base.check_source_files(
        &[source.as_bytes()],
        &KVMap::new(),
        SourceCheckLimits::new(limits()),
    )
    .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
    .into_complete()
    .expect("the generated comparison and instance pass both checkers")
    .engine
}

// The source seed deliberately does not include Ord or Ordering. Admit ordinary
// source declarations, including a structural Nat comparison, instead of
// injecting unchecked constants or requiring an installed upstream library.
const ORD_SOURCE: &str = r#"
inductive Ordering where
  | lt
  | eq
  | gt
class Ord.{u} (A : Type u) where
  compare : A -> A -> Ordering
def naturalCompare (left right : Nat) : Ordering :=
  match left with
  | .zero =>
    match right with
    | .zero => .eq
    | .succ n => .lt
  | .succ m =>
    match right with
    | .zero => .gt
    | .succ n => naturalCompare m n
instance nativeNatOrd : Ord Nat where
  compare := naturalCompare
def lexicographic (first next : Ordering) : Ordering :=
  match first with
  | .eq => next
  | other => other
def orderingCode (value : Ordering) : Nat :=
  match value with
  | .lt => 0
  | .eq => 1
  | .gt => 2
theorem fixture_less : Ord.compare 1 2 = Ordering.lt := by rfl
theorem fixture_equal : Ord.compare 2 2 = Ordering.eq := by rfl
theorem fixture_greater : Ord.compare 2 1 = Ordering.gt := by rfl
"#;

fn engine() -> Engine {
    let seed = Engine::with_source_seed(limits())
        .unwrap()
        .into_complete()
        .unwrap();
    checked(&seed, ORD_SOURCE)
}

fn execute_and_replay(
    base: &Engine,
    source: &str,
    expected: &[&str],
    execution_limits: EngineExecutionLimits,
) {
    let report = base
        .execute_source_definitions(&[source.as_bytes()], &KVMap::new(), execution_limits)
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .expect("bounded derived comparison execution completes");
    assert_eq!(report.executions.len(), expected.len());
    for (execution, expected) in report.executions.iter().zip(expected) {
        let VmExit::Returned(value) = &execution.exit else {
            panic!("derived comparison did not return: {source}")
        };
        assert_eq!(fln::nat_decimal(&value.value).as_deref(), Some(*expected));
        let replay =
            fln::execute_flbc_artifact(&execution.flbc_artifact, &KVMap::new(), Default::default())
                .unwrap()
                .into_complete()
                .expect("the serialized derived comparison executes");
        let VmExit::Returned(value) = replay else {
            panic!("derived comparison artifact replay did not return")
        };
        assert_eq!(fln::nat_decimal(&value.value).as_deref(), Some(*expected));
    }
}

#[test]
fn enums_records_empty_records_and_proof_fields_compare_and_execute() {
    let base = engine();
    let source = r#"
inductive Shade where
  | low
  | middle
  | high
deriving Ord
structure Packet where
  key : Nat
  shade : Shade
  proof : key = key
deriving Ord
structure Marker : Type where
deriving Ord
theorem ascending : Ord.compare Shade.low Shade.high = Ordering.lt := by rfl
theorem descending : Ord.compare Shade.high Shade.low = Ordering.gt := by rfl
theorem same : Ord.compare Shade.middle Shade.middle = Ordering.eq := by rfl
theorem first_field : Ord.compare (Packet.mk 1 .high rfl) (Packet.mk 2 .low rfl) = Ordering.lt := by rfl
theorem later_field : Ord.compare (Packet.mk 1 .low rfl) (Packet.mk 1 .high rfl) = Ordering.lt := by rfl
theorem proofs : Ord.compare (Packet.mk 1 .low rfl) (Packet.mk 1 .low (Eq.refl 1)) = Ordering.eq := by rfl
theorem marker : Ord.compare Marker.mk Marker.mk = Ordering.eq := by rfl
"#;
    let result = checked(&base, source);
    for generated in [
        "instOrdShade",
        "instOrdShade.ord",
        "instOrdPacket",
        "instOrdPacket.ord",
        "instOrdMarker",
        "instOrdMarker.ord",
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
    execute_and_replay(
        &result,
        r#"
#eval orderingCode (Ord.compare Shade.low Shade.high)
#eval orderingCode (Ord.compare Shade.high Shade.low)
#eval orderingCode (Ord.compare Shade.middle Shade.middle)
#eval orderingCode (Ord.compare (Packet.mk 1 .high rfl) (Packet.mk 2 .low rfl))
#eval orderingCode (Ord.compare (Packet.mk 1 .low rfl) (Packet.mk 1 .high rfl))
#eval orderingCode (Ord.compare Marker.mk Marker.mk)
"#,
        &["0", "2", "1", "0", "0", "1"],
        EngineExecutionLimits::new(limits().kernel),
    );
}

fn alpha_type(expression: &Expr) -> Expr {
    match expression.node() {
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
        _ => expression.clone(),
    }
}

#[test]
fn parameter_hypotheses_names_and_caller_dictionaries_are_preserved() {
    let result = checked(
        &engine(),
        r#"
namespace Library
structure Box (A B : Type) where
  value : A
deriving Ord
def expected {A B : Type} [Ord A] [Ord B] : Ord (Box A B) := inferInstance
def expectedHelper {A B : Type} [Ord A] [Ord B] : Box A B -> Box A B -> Ordering := instOrdBox.ord
end Library
inductive Poly.{u} (A : Type u) where
  | value (a : A)
deriving Ord
def polyExpected.{u} {A : Type u} [Ord A] : Ord (Poly A) := inferInstance
structure Generic (A : Type) where
  value : A
deriving Ord
def allGreater : Ord Nat := { compare := fun a b => Ordering.gt }
theorem supplied : @instOrdGeneric.ord Nat allGreater (Generic.mk 1) (Generic.mk 2) = Ordering.gt := by rfl
theorem supplied_instance : @Ord.compare (Generic Nat) (@instOrdGeneric Nat allGreater) (Generic.mk 1) (Generic.mk 2) = Ordering.gt := by rfl
theorem ordinary : Ord.compare (Generic.mk 1) (Generic.mk 2) = Ordering.lt := by rfl
theorem symbolic {A : Type} [Ord A] (left right : A) : Ord.compare (Generic.mk left) (Generic.mk right) = lexicographic (Ord.compare left right) Ordering.eq := by rfl
"#,
    );
    for (generated, expected) in [
        ("Library.instOrdBox", "Library.expected"),
        ("Library.instOrdBox.ord", "Library.expectedHelper"),
        ("instOrdPoly", "polyExpected"),
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
    execute_and_replay(
        &result,
        r#"
#eval orderingCode (@instOrdGeneric.ord Nat allGreater (Generic.mk 1) (Generic.mk 2))
#eval orderingCode (@Ord.compare (Generic Nat) (@instOrdGeneric Nat allGreater) (Generic.mk 1) (Generic.mk 2))
#eval orderingCode (Ord.compare (Generic.mk 1) (Generic.mk 2))
"#,
        &["2", "2", "0"],
        EngineExecutionLimits::new(limits().kernel),
    );
}

#[test]
fn enum_indices_use_the_selected_nat_dictionary_and_general_ctors_keep_their_order() {
    let result = checked(
        &engine(),
        r#"
section
local instance reversedNat : Ord Nat where
  compare left right := naturalCompare right left
inductive ReverseColor where
  | red
  | green
  | blue
deriving Ord
inductive Tagged where
  | empty
  | value (n : Nat)
deriving Ord
end
theorem reversed_enum : Ord.compare ReverseColor.red ReverseColor.blue = Ordering.gt := by rfl
theorem reversed_enum_back : Ord.compare ReverseColor.blue ReverseColor.red = Ordering.lt := by rfl
theorem same_enum : Ord.compare ReverseColor.green ReverseColor.green = Ordering.eq := by rfl
theorem different_ctors : Ord.compare Tagged.empty (Tagged.value 0) = Ordering.lt := by rfl
theorem reversed_field : Ord.compare (Tagged.value 0) (Tagged.value 1) = Ordering.gt := by rfl
theorem outside_scope : Ord.compare 0 1 = Ordering.lt := by rfl
"#,
    );
    execute_and_replay(
        &result,
        r#"
#eval orderingCode (Ord.compare ReverseColor.red ReverseColor.blue)
#eval orderingCode (Ord.compare ReverseColor.blue ReverseColor.red)
#eval orderingCode (Ord.compare Tagged.empty (Tagged.value 0))
#eval orderingCode (Ord.compare (Tagged.value 0) (Tagged.value 1))
#eval orderingCode (Ord.compare 0 1)
"#,
        &["2", "0", "0", "2", "0"],
        EngineExecutionLimits::new(limits().kernel),
    );
}

#[test]
fn suffix_standalone_and_combined_instances_survive_module_replay() {
    let library = name("Library");
    let main = name("Main");
    let modules = [
        SourceModuleInput {
            name: &library,
            source: b"namespace Data\ninductive Choice (A : Type) where\n | empty\n | value (a : A)\nderiving Inhabited, Ord\ninductive Direction where\n | south\n | north\nderiving instance Ord for Direction\nend Data",
        },
        SourceModuleInput {
            name: &main,
            source: b"import Library\ndef chosen : Data.Choice Nat := default\ntheorem imported_less : Ord.compare chosen (Data.Choice.value 7) = Ordering.lt := by rfl\ntheorem imported_equal : Ord.compare chosen Data.Choice.empty = Ordering.eq := by rfl\ntheorem standalone : Ord.compare Data.Direction.north Data.Direction.south = Ordering.gt := by rfl",
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
        "Data.instOrdChoice",
        "Data.instOrdChoice.ord",
        "Data.instOrdDirection",
        "Data.instOrdDirection.ord",
        "imported_less",
        "imported_equal",
        "standalone",
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
    execute_and_replay(
        &result.checked.engine,
        "#eval orderingCode (Ord.compare chosen (Data.Choice.value 7))\n#eval orderingCode (Ord.compare Data.Direction.north Data.Direction.south)",
        &["0", "2"],
        EngineExecutionLimits::new(limits().kernel),
    );
}

#[test]
fn false_results_missing_dictionaries_and_failed_batches_publish_nothing() {
    let base = engine();
    let before = base.logical_root(&KVMap::new());
    for source in [
        "inductive Color where\n | red\n | blue\nderiving Ord\ntheorem bad : Ord.compare Color.red Color.blue = Ordering.gt := by rfl",
        "structure Box where\n value : Nat\nderiving Ord\ntheorem bad : Ord.compare (Box.mk 1) (Box.mk 2) = Ordering.eq := by rfl",
        "structure Missing where\n run : Nat -> Nat\nderiving Ord",
        "structure Dependent where\n carrier : Type\n value : carrier\nderiving Ord",
        "structure Point where\n value : Nat\nderiving Ord, UnknownHandler",
        // The pin uses opaque partial helpers for recursive Ord. Until that
        // boundary is implemented, this slice must refuse rather than publish
        // a transparent structural helper with different proof behavior.
        "inductive Recursive where\n | leaf\n | node (child : Recursive)\nderiving Ord",
        // The pin uses casesOnSameCtor for large non-enum families. This
        // native slice leaves that distinct construction explicitly refused.
        "inductive Large where\n | a (n : Nat)\n | b\n | c\n | d\n | e\n | f\n | g\n | h\n | i\n | j\nderiving Ord",
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
    for generated in [
        "Color",
        "Box",
        "Missing",
        "Dependent",
        "Point",
        "Recursive",
        "Large",
        "instOrdPoint",
        "instOrdPoint.ord",
    ] {
        assert!(!base.environment().contains(&name(generated)));
    }
    checked(
        &base,
        "structure Point where\n value : Nat\nderiving Ord\ntheorem recovered : Ord.compare (Point.mk 1) (Point.mk 2) = Ordering.lt := by rfl",
    );
}

#[test]
fn an_early_non_equal_field_does_not_execute_later_comparisons() {
    let base = checked(
        &engine(),
        r#"
structure Slow where
  value : Nat
def spend (n : Nat) : Ordering := match n with | .zero => .eq | .succ k => spend k
instance slowOrd : Ord Slow where
  compare a b := spend (a.value + b.value)
structure Guarded where
  tag : Nat
  payload : Slow
deriving Ord
"#,
    );
    let mut execution_limits = EngineExecutionLimits::new(limits().kernel);
    execution_limits.vm.max_steps = 5000;
    execute_and_replay(
        &base,
        r#"
#eval orderingCode (Ord.compare (Guarded.mk 0 (Slow.mk 100000)) (Guarded.mk 1 (Slow.mk 100000)))
#eval orderingCode (Ord.compare (Guarded.mk 1 (Slow.mk 100000)) (Guarded.mk 0 (Slow.mk 100000)))
"#,
        &["0", "2"],
        execution_limits,
    );
    let would_run = base
        .execute_source_definitions(
            &[b"#eval orderingCode (Ord.compare (Guarded.mk 0 (Slow.mk 100000)) (Guarded.mk 0 (Slow.mk 100000)))"],
            &KVMap::new(),
            execution_limits,
        )
        .unwrap();
    let fln::Outcome::Inconclusive(reason) = would_run else {
        panic!("the late comparison must exceed this VM step budget")
    };
    let fln_core::outcome::InconclusiveCause::ResourceExhausted { usage } = reason.cause else {
        panic!("the late comparison must stop for its execution budget")
    };
    assert_eq!(usage.reason, fln_core::diag::ResourceReason::ExecutionSteps);
    assert_eq!(usage.allowed, execution_limits.vm.max_steps);
    assert!(usage.observed > usage.allowed);
}
