//! The public source command path constructs and dually checks actual ADTs.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, Name, Outcome, SourceCheckLimits};
fn limits() -> EngineAdmissionLimits { EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024)) }
fn engine() -> Engine { Engine::with_source_seed(limits()).unwrap().into_complete().unwrap() }
fn check(text: &str) -> fln::SourceFileCheck {
    engine().check_source_files(&[text.as_bytes()],&KVMap::new(),SourceCheckLimits::new(limits())).unwrap().into_complete().unwrap()
}
#[test]
fn source_enumerations_and_payload_variants_are_usable_by_later_commands() {
    let result=check("inductive Message where | stop | number (n : Nat) | text (s : String)\ndef message : Message := Message.number 13\ntheorem message_ok : message = Message.number 13 := by rfl");
    assert_eq!(result.commands,3); assert_eq!(result.theorems,1);
    assert!(result.engine.environment().contains(&Name::from_components(["Message","rec"])));
}
#[test]
fn source_uniform_parameters_and_result_annotations_are_preserved() {
    check("inductive Maybe (A : Type) where | none : Maybe A | some (x : A) : Maybe A\ndef zero : Maybe Nat := Maybe.none\ndef one : Maybe Nat := Maybe.some 1\ntheorem one_ok : one = Maybe.some 1 := by rfl");
    check("inductive Either (A B : Type) where | left : A -> Either A B | right : B -> Either A B\ndef leftValue : Either Nat Bool := Either.left 9\ndef rightValue : Either Nat Bool := Either.right true");
}
#[test]
fn source_direct_recursion_reaches_regenerated_induction_rules() {
    check("inductive Chain where | nil | cons (head : Nat) (tail : Chain)\ndef two : Chain := Chain.cons 2 (Chain.cons 1 Chain.nil)\ntheorem two_ok : two = Chain.cons 2 (Chain.cons 1 Chain.nil) := by rfl");
    check("inductive Unary where | zero : Unary | succ : Unary -> Unary\ndef one : Unary := Unary.succ Unary.zero");
}
#[test]
fn source_dependent_constructor_fields_infer_the_required_universe() {
    check("inductive Payload where | unit | package (A : Type) (x : A)\ndef wrapped : Payload := Payload.package Nat 19\ntheorem wrapped_ok : wrapped = Payload.package Nat 19 := by rfl");
}
#[test]
fn wrong_results_negative_recursion_and_unresolved_domains_do_not_publish() {
    let e=engine();let root=e.logical_root(&KVMap::new());
    for text in [
        "inductive Bad where | constructor : Nat",
        "inductive Bad where | constructor (f : Bad -> Nat)",
        "inductive Bad where | same | same",
        "inductive Bad : Type where | package (A : Type)",
        "inductive Bad where | constructor (x : Missing)",
        "inductive Bad where | constructor (x : _)",
        "inductive Bad : Prop where | constructor",
        "inductive Bad (A : Type) where | constructor : Bad Nat",
    ] {
        assert!(!matches!(e.check_source_files(&[text.as_bytes()],&KVMap::new(),SourceCheckLimits::new(limits())),Ok(Outcome::Complete(_))),"{text}");
        assert_eq!(e.logical_root(&KVMap::new()),root);
        assert!(!e.environment().contains(&Name::from_components(["Bad"])));
    }
}
#[test]
fn constructor_collision_and_late_failure_leave_the_base_snapshot_unchanged() {
    let e=engine();let root=e.logical_root(&KVMap::new());
    for text in ["def Item.mk : Nat := 7\ninductive Item where | mk", "inductive Valid where | ok\ntheorem false : 1 = 2 := by rfl"] {
        assert!(!matches!(e.check_source_files(&[text.as_bytes()],&KVMap::new(),SourceCheckLimits::new(limits())),Ok(Outcome::Complete(_))));
        assert_eq!(e.logical_root(&KVMap::new()),root);
    }
    check("inductive Valid where | ok\ntheorem good : Valid.ok = Valid.ok := by rfl");
}
