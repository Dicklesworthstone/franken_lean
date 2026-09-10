//! The public source command path constructs and dually checks actual ADTs.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, Name, Outcome, SourceCheckLimits};
fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}
fn engine() -> Engine {
    Engine::with_source_seed(limits())
        .unwrap()
        .into_complete()
        .unwrap()
}
fn check(text: &str) -> fln::SourceFileCheck {
    engine()
        .check_source_files(
            &[text.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        )
        .unwrap()
        .into_complete()
        .unwrap()
}
#[test]
fn source_enumerations_and_payload_variants_are_usable_by_later_commands() {
    let result = check(
        "inductive Message where | stop | number (n : Nat) | text (s : String)\ndef message : Message := Message.number 13\ntheorem message_ok : message = Message.number 13 := by rfl",
    );
    assert_eq!(result.commands, 3);
    assert_eq!(result.theorems, 1);
    assert!(
        result
            .engine
            .environment()
            .contains(&Name::from_components(["Message", "rec"]))
    );
}
#[test]
fn source_uniform_parameters_and_result_annotations_are_preserved() {
    check(
        "inductive Maybe (A : Type) where | none : Maybe A | some (x : A) : Maybe A\ndef zero : Maybe Nat := Maybe.none\ndef one : Maybe Nat := Maybe.some 1\ntheorem one_ok : one = Maybe.some 1 := by rfl",
    );
    check(
        "inductive Either (A B : Type) where | left : A -> Either A B | right : B -> Either A B\ndef leftValue : Either Nat Bool := Either.left 9\ndef rightValue : Either Nat Bool := Either.right true",
    );
}
#[test]
fn source_direct_recursion_reaches_regenerated_induction_rules() {
    check(
        "inductive Chain where | nil | cons (head : Nat) (tail : Chain)\ndef two : Chain := Chain.cons 2 (Chain.cons 1 Chain.nil)\ntheorem two_ok : two = Chain.cons 2 (Chain.cons 1 Chain.nil) := by rfl",
    );
    check(
        "inductive Unary where | zero : Unary | succ : Unary -> Unary\ndef one : Unary := Unary.succ Unary.zero",
    );
}
#[test]
fn source_dependent_constructor_fields_infer_the_required_universe() {
    check(
        "inductive Payload where | unit | package (A : Type) (x : A)\ndef wrapped : Payload := Payload.package Nat 19\ntheorem wrapped_ok : wrapped = Payload.package Nat 19 := by rfl",
    );
}
#[test]
fn wrong_results_negative_recursion_and_unresolved_domains_do_not_publish() {
    let e = engine();
    let root = e.logical_root(&KVMap::new());
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
        assert!(
            !matches!(
                e.check_source_files(
                    &[text.as_bytes()],
                    &KVMap::new(),
                    SourceCheckLimits::new(limits())
                ),
                Ok(Outcome::Complete(_))
            ),
            "{text}"
        );
        assert_eq!(e.logical_root(&KVMap::new()), root);
        assert!(!e.environment().contains(&Name::from_components(["Bad"])));
    }
}
#[test]
fn constructor_collision_and_late_failure_leave_the_base_snapshot_unchanged() {
    let e = engine();
    let root = e.logical_root(&KVMap::new());
    for text in [
        "def Item.mk : Nat := 7\ninductive Item where | mk",
        "inductive Valid where | ok\ntheorem false : 1 = 2 := by rfl",
    ] {
        assert!(!matches!(
            e.check_source_files(
                &[text.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits())
            ),
            Ok(Outcome::Complete(_))
        ));
        assert_eq!(e.logical_root(&KVMap::new()), root);
    }
    check("inductive Valid where | ok\ntheorem good : Valid.ok = Valid.ok := by rfl");
}

#[test]
fn source_recursors_compute_and_false_computation_does_not_publish() {
    let prefix = "inductive Chain where | nil | cons (head : Nat) (tail : Chain)\n";
    let term = "Chain.rec 0 (fun n tail ih => ih + 1) (Chain.cons 2 Chain.nil)";
    let good = format!("{prefix}theorem count : {term} = 1 := by rfl");
    let bad = format!("{prefix}theorem count : {term} = 2 := by rfl");
    let e = engine();
    let root = e.logical_root(&KVMap::new());
    let error = e
        .check_source_files(
            &[bad.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        )
        .unwrap_err();
    assert_eq!(error.disposition(), ("kernel-rejection", true, 1));
    assert_eq!(e.logical_root(&KVMap::new()), root);
    assert_eq!(check(&good).theorems, 1);
}

#[test]
fn zero_field_constructors_cannot_erase_unresolved_header_or_result_obligations() {
    let prefix = "def resultSort {A : Type} [Inhabited A] := Type\n\
                  def plainSort {A : Type} := Type\n\
                  def resultFamily (A : Type) {B : Type} [Inhabited B] : Type := A\n";
    let e = check(prefix).engine;
    let root = e.logical_root(&KVMap::new());
    for source in [
        "inductive Bad : resultSort where | mk",
        "inductive Bad : plainSort where | mk",
        "inductive Bad where | mk : resultFamily Bad",
        "inductive Bad : resultSort where",
    ] {
        let result = e.check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        );
        let Err(error) = result else {
            panic!("unresolved obligation accepted: {source}");
        };
        assert_eq!(
            error.disposition(),
            ("elaboration", false, 1),
            "{source}: {error}"
        );
        assert_eq!(e.logical_root(&KVMap::new()), root);
    }
    let complete = e
        .check_source_files(
            &[b"inductive Good where | mk\ntheorem good : Good.mk = Good.mk := by rfl"],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(complete.theorems, 1);
}

#[test]
fn discarded_type_assertions_are_checked_before_constructor_publication() {
    let e = engine();
    let root = e.logical_root(&KVMap::new());
    for source in [
        "inductive Bad : (Type : Nat) where | mk",
        "inductive Bad where | mk : (Bad : Nat)",
        "inductive Bad where | package (A : Type) : (Bad : Type)",
        "inductive Bad where | unit : (Bad : Type) | package (A : Type)",
        "inductive Bad (A : Type) where | mk (T : Type) : (Bad : Type -> Type) A",
    ] {
        let result = e.check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        );
        let Err(error) = result else {
            panic!("invalid type assertion accepted: {source}");
        };
        assert_eq!(
            error.disposition(),
            ("kernel-rejection", true, 1),
            "{error}"
        );
        assert_eq!(e.logical_root(&KVMap::new()), root);
    }
    check("inductive Good where | mk : (Good : Type)\ntheorem good : Good.mk = Good.mk := by rfl");
}

#[test]
fn constructor_results_keep_the_declared_family_head() {
    for source in [
        "def family (A : Type) : Type := A\ninductive Bad where | mk : family Bad",
        "inductive Bad where | mk : (fun T => T) Bad",
        "def family (A : Type) : Type := Nat -> A\ninductive Bad where | mk : family Bad",
        "inductive Bad where | mk : (fun T => Nat -> T) Bad",
    ] {
        let result = engine().check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        );
        let Err(error) = result else {
            panic!("indirect constructor result accepted: {source}");
        };
        assert_eq!(error.disposition(), ("elaboration", false, 1), "{error}");
    }
    check("inductive Good where | mk : Nat -> Good\ndef value : Good := Good.mk 4");
    check("inductive Good where | mk : (Nat -> Good : Type)\ndef value : Good := Good.mk 4");
    check(
        "inductive Box (A : Type) where | mk (x : A) : (Box : Type -> Type) A\ndef packed : Box Nat := Box.mk 3",
    );
}

#[test]
fn resolved_dictionary_obligations_and_empty_families_are_accepted() {
    check(
        "class Witness where\n value : Nat\n\
           def chosen [Witness] : Nat := 0\n\
           def erased (n : Nat) := Type\n\
           instance witness : Witness := { value := 1 }\n\
           inductive Good : erased chosen where | mk\n\
           theorem good : Good.mk = Good.mk := by rfl\n\
           inductive EmptyFamily where\n\
           theorem empty_elimination (x : EmptyFamily) : 1 = 2 := by exact EmptyFamily.rec (fun y => 1 = 2) x\n\
           inductive EmptyWithParameter (A : Type) where\n\
           theorem empty_parameter (x : EmptyWithParameter Nat) : 1 = 2 := by exact EmptyWithParameter.rec (fun y => 1 = 2) x",
    );
}

#[test]
fn constructor_generation_resource_stops_keep_their_wire_disposition() {
    let e = engine();
    let syntax = fln_parse::parse_definition(b"inductive Flag where | off | on").unwrap();
    let error = fln_elab::source::elaborate_inductive(
        syntax.syntax(),
        e.environment(),
        limits().kernel,
        fln_elab::records::RecordBudget {
            max_binders: 256,
            max_nodes: 0,
        },
    )
    .unwrap_err();
    assert!(matches!(
        error,
        fln_elab::NatDefinitionElabError::Inference(
            fln_elab::source::SourceInferenceError::Inductive(
                fln_elab::inductive::InductiveError::ResourceLimit
            )
        )
    ));
    let error = fln::SourceCheckError::Command {
        file: 0,
        command: 0,
        offset: 0,
        error: Box::new(fln::EngineExecutionError::Frontend(
            fln_elab::DefinitionFrontendError::Elaborate(error),
        )),
    };
    assert_eq!(error.disposition(), ("resource", false, 3));
    check("inductive Flag where | off | on\ndef selected : Flag := Flag.on");
}

#[test]
fn annotation_check_kernel_exhaustion_is_inconclusive_and_atomic() {
    let e = engine();
    let root = e.logical_root(&KVMap::new());
    let mut limited = limits();
    limited.kernel = limited.kernel.narrowed(0, limited.kernel.depth);
    let result = e.check_source_files(
        &[b"inductive Flag : Type where | off | on"],
        &KVMap::new(),
        SourceCheckLimits::new(limited),
    );
    let Err(error) = result else {
        panic!("expected bounded annotation-check stop");
    };
    assert_eq!(error.disposition(), ("inconclusive", false, 3), "{error}");
    assert_eq!(e.logical_root(&KVMap::new()), root);
    check("inductive Flag : Type where | off | on");
}
