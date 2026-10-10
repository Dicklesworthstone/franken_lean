//! Additional deriving decisions cover implicit fields, proof-bearing recursion,
//! dictionary selection, captured parameters and source-name hygiene.
//!
//! These cases follow the retained v4.32 derivingDecidableEq.lean fixture and
//! Deriving/DecEq.lean, including proof fields and structural recursive decisions.
//! The tests do not claim a fresh upstream executable run.
#![forbid(unsafe_code)]

use fln::{
    Budget, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap, Name, SourceCheckLimits,
    VmExit,
};
use fln_core::expr::{Expr, ExprNode};

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
    .expect("the generated proof-producing helper and dictionary pass both judges")
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
fn proof_instance_and_captured_parameters_keep_checked_headers() {
    let result = checked(
        &engine(),
        r#"
structure ProofBox (P : Prop) where
  proof : P
deriving DecidableEq
def proofExpected {P : Prop} [DecidableEq P] : DecidableEq (ProofBox P) := inferInstance
structure DictionaryBox (A : Type) [DecidableEq A] where
  value : A
deriving DecidableEq
def dictionaryExpected {A : Type} {i : DecidableEq A} [DecidableEq A] : DecidableEq (@DictionaryBox A i) := @instDecidableEqDictionaryBox A i inferInstance
theorem dictionary : DictionaryBox.mk 7 = DictionaryBox.mk 7 := by decide
section
variable {A : Type} [DecidableEq A]
inductive CapturedBox where
  | mk : A -> CapturedBox
deriving DecidableEq
end
def capturedExpected {A : Type} [DecidableEq A] : DecidableEq (@CapturedBox A) := inferInstance
theorem captured : CapturedBox.mk 7 = CapturedBox.mk 7 := by decide
"#,
    );
    for (generated, expected) in [
        ("instDecidableEqProofBox", "proofExpected"),
        ("instDecidableEqDictionaryBox", "dictionaryExpected"),
        ("instDecidableEqCapturedBox", "capturedExpected"),
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
fn recursive_proof_fields_compute_and_execute() {
    let source = r#"
namespace Wire
inductive Chain (A : Type) where
  | nil
  | cons (head : A) (tail : Chain A) (proof : head = head)
deriving DecidableEq
end Wire
def first : Wire.Chain Nat := .cons 7 (.cons 11 .nil rfl) rfl
def second : Wire.Chain Nat := .cons 7 (.cons 12 .nil rfl) rfl
theorem same_chain : first = first := by decide
theorem changed_tail : Not (first = second) := by decide
theorem different_ctor : Not (first = Wire.Chain.nil) := by decide
theorem nil_same : decide ((Wire.Chain.nil : Wire.Chain Nat) = Wire.Chain.nil) = true := by rfl
theorem arbitrary_proofs (p q : 7 = 7) : Wire.Chain.cons 7 Wire.Chain.nil p = Wire.Chain.cons 7 Wire.Chain.nil q := by decide
"#;
    let result = checked(&engine(), source);
    let program = b"#eval if first = second then 0 else if first = first then 42 else 1";
    let execution = result
        .execute_source_definitions(
            &[program],
            &KVMap::new(),
            EngineExecutionLimits::new(limits().kernel),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    let VmExit::Returned(value) = &execution.executions[0].exit else {
        panic!("derived recursive equality must return normally")
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
        Some("42")
    );
    let program = fln_comp::flbc::decode_canonical(
        &execution.executions[0].flbc_artifact,
        fln_comp::flbc::CodecLimits::default(),
    )
    .unwrap();
    let fln::Outcome::Complete(VmExit::Returned(value)) = fln_vm::interpreter::execute(
        &program,
        fln_vm::interpreter::ExecutionLimits::default(),
        None,
    ) else {
        panic!("the persisted recursive decision must replay normally")
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
        Some("42")
    );
}

#[test]
fn decisions_use_proofs_even_when_boolean_equality_lies() {
    checked(
        &engine(),
        r#"
inductive Token where
  | left
  | right
deriving DecidableEq
instance : BEq Token where
  beq _ _ := true
structure Box where
  token : Token
deriving BEq, DecidableEq
theorem boolean : (Box.mk .left == Box.mk .right) = true := by rfl
theorem propositional : Not (Box.mk .left = Box.mk .right) := by decide
theorem decision : decide (Box.mk .left = Box.mk .right) = false := by rfl
"#,
    );
}

#[test]
fn generated_binders_do_not_capture_user_names() {
    checked(
        &engine(),
        r#"
namespace Hidden
def left0 : Nat := 99
def same : Nat := 99
def recur : Nat := 99
structure Box (lhs rhs parameter0 : Type) where
  value : lhs
deriving DecidableEq
theorem same_value : (Box.mk (rhs := Nat) (parameter0 := Nat) 7) = Box.mk 7 := by decide
end Hidden
"#,
    );
}

#[test]
fn implicit_payloads_are_compared_and_implicit_proofs_are_irrelevant() {
    let base = checked(
        &engine(),
        r#"
inductive HiddenField where
  | mk {n : Nat} : HiddenField
deriving DecidableEq
inductive HiddenProof where
  | mk {n : Nat} {proof : n = n} : HiddenProof
deriving DecidableEq
theorem same : @HiddenField.mk 7 = @HiddenField.mk 7 := by decide
theorem unequal : Not (@HiddenField.mk 7 = @HiddenField.mk 8) := by decide
theorem proofs (p q : 7 = 7) : @HiddenProof.mk 7 p = @HiddenProof.mk 7 q := by decide
theorem different_payload : Not (@HiddenProof.mk 7 rfl = @HiddenProof.mk 8 rfl) := by decide
"#,
    );
    let before = base.logical_root(&KVMap::new());
    for source in [
        "theorem bad : @HiddenField.mk 7 = @HiddenField.mk 8 := by decide",
        "theorem bad : @HiddenProof.mk 7 rfl = @HiddenProof.mk 8 rfl := by decide",
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
}
