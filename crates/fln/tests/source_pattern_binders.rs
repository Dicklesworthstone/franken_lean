//! Mixed lambda telescopes and destructuring cross the ordinary admission seats.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, SourceCheckLimits};
use fln_core::{
    expr::{BinderInfo, ExprNode},
    name::Name,
};

fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}
fn engine() -> Engine {
    Engine::with_source_seed(limits())
        .unwrap()
        .into_complete()
        .unwrap()
}
fn check(source: &str) -> Engine {
    engine()
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        )
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .expect("both admission seats must complete")
        .engine
}
fn reject(source: &str) {
    let base = engine();
    let before = base.logical_root(&KVMap::new());
    let error = base
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        )
        .unwrap_err();
    assert!(!error.disposition().1, "{source}\n{error:?}");
    assert_eq!(base.logical_root(&KVMap::new()), before);
}
const PAIR: &str = "structure Pair where\n  first : Nat\n  second : Nat\n";

#[test]
fn explicit_groups_can_precede_follow_and_separate_pattern_binders() {
    check(&format!(
        "{PAIR}
      def combine : Nat -> Pair -> Nat -> Pair -> Nat :=
        fun (n : Nat) ⟨a, b⟩ (k : Nat) ⟨c, d⟩ => n + a + b + k + c + d
      theorem result : combine 1 ⟨2, 3⟩ 4 ⟨5, 6⟩ = 21 := rfl
      def grouped : Nat -> Nat -> Pair -> Nat := fun (n m : Nat) ⟨a, b⟩ => n + m + a + b
      theorem groupResult : grouped 1 2 ⟨3, 4⟩ = 10 := rfl"
    ));
}

#[test]
fn implicit_and_strict_lambda_parameters_keep_their_binder_styles() {
    for (binder, style) in [
        ("{A : Type}", BinderInfo::Implicit),
        ("⦃A : Type⦄", BinderInfo::StrictImplicit),
    ] {
        let result = check(&format!(
            "structure Box (A : Type) where\n  value : A\n
          def unpack : {binder} -> Nat -> Box A -> A := fun {binder} (_ : Nat) ⟨x⟩ => x
          theorem result : unpack 0 ⟨17⟩ = (17 : Nat) := rfl"
        ));
        let declaration = result
            .environment()
            .find(&Name::from_components(["unpack"]))
            .unwrap();
        let fln_env::constants::ConstantInfo::Defn(definition) = declaration else {
            panic!("unpack is a checked definition");
        };
        assert!(
            matches!(definition.value.node(), ExprNode::Lam { binder_info, .. } if *binder_info == style)
        );
    }
}

#[test]
fn pattern_lambdas_retain_instance_binders_and_expected_implicit_prefixes() {
    check(&format!(
        "{PAIR}
      class Item (A : Type) where\n  value : A
      instance itemNat : Item Nat := {{ value := 13 }}
      def select : {{A : Type}} -> [Item A] -> Pair -> A := fun {{A}} [Item A] ⟨_, _⟩ => Item.value
      theorem result : select ⟨2, 3⟩ = (13 : Nat) := rfl
      def keep : {{A : Type}} -> A -> Pair -> A := fun (x : _) ⟨_, _⟩ => x
      theorem insertedPrefix : keep 9 ⟨2, 3⟩ = (9 : Nat) := rfl"
    ));
}

#[test]
fn tuple_patterns_preserve_higher_order_expected_types() {
    check(
        "structure Prod (A B : Type) where\n  fst : A\n  snd : B\n\
 def apply (f : Nat -> Nat × Nat -> Nat) : Nat := f 1 (2, 3)
      def total : Nat := apply (fun (n : Nat) (a, b) => n + a + b)
      theorem result : total = 6 := rfl",
    );
}

#[test]
fn later_pattern_bindings_shadow_earlier_patterns_but_not_the_telescope() {
    check(&format!(
        "{PAIR}
      def sameName : Pair -> Nat -> Pair -> Nat := fun ⟨x, _⟩ (n : Nat) ⟨x, _⟩ => x + n
      theorem result : sameName ⟨1, 2⟩ 3 ⟨4, 5⟩ = 7 := rfl
      def outerType (A : Type) (value : A) : Pair -> A -> A := fun ⟨A, _⟩ (x : A) => x
      theorem scope : outerType Nat 1 ⟨2, 3⟩ 7 = 7 := rfl"
    ));
}

#[test]
fn mixed_patterns_cannot_erase_bad_domains_bodies_or_coverage() {
    for fragment in [
        "def bad : Bool -> Pair -> Nat := fun (n : Nat) ⟨a, b⟩ => a",
        "def bad : Nat -> Pair -> Nat := fun (n : 7) ⟨a, b⟩ => a",
        "def bad : Nat -> Pair -> Nat := fun (n : Nat) ⟨a, b⟩ => let unused := (1 : String); a",
        "def bad : Nat -> Pair -> Nat := fun (n : Nat) ⟨a, a⟩ => a",
        "def bad : Nat -> Pair -> Nat := fun (n : Nat) ⟨a, b⟩ => missing",
        "def bad : Nat -> Pair -> Nat := fun (n : Nat) ⟨a, b⟩ : Nat => a",
        "def bad : Nat -> Option Nat -> Nat := fun (n : Nat) (Option.some x) => x",
        "def bad : Pair -> Nat := fun ⟨a, b⟩ => _",
    ] {
        reject(&format!("{PAIR}{fragment}"));
    }
    reject(
        "structure Package where\n  carrier : Type\n  value : carrier\n
      def bad := fun ⟨A, x⟩ (y : A) => y",
    );
}

#[test]
fn mixed_pattern_functions_execute_through_the_source_command_api() {
    use fln::{EngineExecutionLimits, SourceCommandOutput, VmExit};
    let source = format!(
        "{PAIR}
      def total : Nat -> Pair -> Nat := fun (n : Nat) ⟨a, b⟩ => n + a + b
      #eval total 1 ⟨2, 3⟩
      #eval total 4 ⟨5, 6⟩"
    );
    let result = engine()
        .execute_source_commands_with_checks(
            source.as_bytes(),
            &KVMap::new(),
            EngineExecutionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024)),
        )
        .unwrap()
        .into_complete()
        .expect("checked VM result");
    assert_eq!(result.command_count, 4);
    assert_eq!(result.outputs.len(), 2);
    for (event, expected) in result.outputs.iter().zip(["6", "15"]) {
        let SourceCommandOutput::Evaluation {
            execution_index, ..
        } = event
        else {
            panic!("expected evaluation");
        };
        let VmExit::Returned(value) = &result.batch.executions[*execution_index].exit else {
            panic!("expected a returned value");
        };
        assert_eq!(
            fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
            Some(expected)
        );
    }
}
