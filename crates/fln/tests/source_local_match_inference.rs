//! Inferred local receivers remain open until later calls constrain delayed
//! field notation, including fields scrutinized by a constructor match.
#![forbid(unsafe_code)]

use fln::{
    Budget, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap, SourceCheckLimits, VmExit,
};
use std::sync::OnceLock;

fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}

fn seed() -> Engine {
    static SEED: OnceLock<Engine> = OnceLock::new();
    SEED.get_or_init(|| {
        Engine::with_source_seed(limits())
            .unwrap()
            .into_complete()
            .unwrap()
    })
    .clone()
}

fn checked(base: &Engine, source: &str) -> Engine {
    base.check_source_files(
        &[source.as_bytes()],
        &KVMap::new(),
        SourceCheckLimits::new(limits()),
    )
    .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
    .into_complete()
    .expect("both checkers completed")
    .engine
}

fn values(base: &Engine, source: &str) -> Vec<String> {
    let batch = base
        .execute_source_definitions(
            &[source.as_bytes()],
            &KVMap::new(),
            EngineExecutionLimits::new(limits().kernel),
        )
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .expect("native execution completed");
    batch
        .source_evaluation_indices
        .iter()
        .map(|&index| {
            let VmExit::Returned(value) = &batch.executions[index].exit else {
                panic!("expected a returned Nat: {:?}", batch.executions[index]);
            };
            fln_vm::interpreter::nat_decimal(&value.value).expect("Nat result")
        })
        .collect()
}

const DATA: &str = r#"
export Option (none some)
structure RefBox where
  start : Nat
  finish : Nat
def RefBox.getPos? (ref : RefBox) : Option Nat := some ref.start
def RefBox.getTailPos? (ref : RefBox) : Option Nat := some ref.finish
"#;

const SINGLE: &str = r#"
def first (ref : RefBox) : Nat :=
  let get ref :=
    match ref.getPos? with
    | some pos => pos
    | none => 0
  get ref
"#;

const MULTIPLE: &str = r#"
def combined (ref : RefBox) : Nat :=
  let get ref :=
    match ref.getPos?, ref.getTailPos? with
    | some pos, some tailPos => pos + tailPos
    | _, _ => 0
  get ref
"#;

#[test]
fn a_delayed_projection_resolves_its_local_receiver_from_the_call() {
    let base = checked(&seed(), DATA);
    let result = checked(
        &base,
        "def project (ref : RefBox) : Nat := let get ref := ref.start; get ref",
    );
    assert_eq!(values(&result, "#eval project ⟨17, 25⟩"), ["17"]);
}

#[test]
fn bare_anonymous_and_multiple_parameters_are_inferred_independently() {
    let base = checked(&seed(), DATA);
    let before = base.logical_root(&KVMap::new());
    let result = checked(
        &base,
        r#"
def dropped (box : RefBox) : Nat :=
  let keep _ value := value
  keep box (box.finish + 1)
def shifted (box : RefBox) (amount : Nat) : Nat :=
  let combine receiver amount := receiver.start + amount
  combine box amount
"#,
    );
    assert_eq!(
        values(&result, "#eval dropped ⟨17, 25⟩\n#eval shifted ⟨17, 25⟩ 25"),
        ["26", "42"]
    );
    assert!(
        base.check_source_files(
            &[b"def unresolved : Nat := let keep _ value := value; 0"],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        )
        .is_err(),
        "unused local parameters must still have resolved types"
    );
    assert_eq!(base.logical_root(&KVMap::new()), before);
}

#[test]
fn explicit_local_receiver_and_result_annotations_keep_constructor_matches() {
    let base = checked(&seed(), DATA);
    for (receiver, result_type) in [("(ref : RefBox)", ""), ("(ref : RefBox)", " : Nat")] {
        let source = format!(
            r#"
def combined (ref : RefBox) : Nat :=
  let get {receiver}{result_type} :=
    match ref.getPos?, ref.getTailPos? with
    | some pos, some tailPos => pos + tailPos
    | _, _ => 0
  get ref
"#
        );
        let result = checked(&base, &source);
        assert_eq!(values(&result, "#eval combined ⟨17, 25⟩"), ["42"]);
    }
}

#[test]
fn a_single_match_infers_the_local_field_receiver_from_its_later_call() {
    let base = checked(&seed(), DATA);
    let result = checked(&base, SINGLE);
    assert_eq!(
        values(&result, "#eval first ⟨17, 25⟩\n#eval first ⟨7, 35⟩"),
        ["17", "7"]
    );
}

#[test]
fn simultaneous_matches_infer_local_receivers_with_and_without_a_result_annotation() {
    let base = checked(&seed(), DATA);
    for source in [
        MULTIPLE.to_owned(),
        MULTIPLE.replace("let get ref :=", "let get ref : Nat :="),
    ] {
        let result = checked(&base, &source);
        assert_eq!(
            values(&result, "#eval combined ⟨17, 25⟩\n#eval combined ⟨3, 8⟩"),
            ["42", "11"]
        );
    }
}

const FROM_REF: &str = r#"
universe u
abbrev optParam (α : Sort u) (default : α) : Sort u := α
export Option (none some)
structure SpanRef where
  position : Option Nat
  tailPosition : Option Nat
  isCanonical : Bool
def SpanRef.getPos? (ref : SpanRef) (canonicalOnly := false) : Option Nat :=
  match canonicalOnly, ref.isCanonical with
  | true, false => none
  | _, _ => ref.position
def SpanRef.getTailPos? (ref : SpanRef) (canonicalOnly := false) : Option Nat :=
  match canonicalOnly, ref.isCanonical with
  | true, false => none
  | _, _ => ref.tailPosition
inductive ProbeInfo where
  | synthetic (first last : Nat) (canonical : Bool := false)
  | none
def fromRef (ref : SpanRef) (canonical := false) : ProbeInfo :=
  let noncanonical ref :=
    match ref.getPos?, ref.getTailPos? with
    | some pos, some tailPos => .synthetic pos tailPos
    | _, _ => .none
  match canonical with
  | true =>
    match ref.getPos? true, ref.getTailPos? true with
    | some pos, some tailPos => .synthetic pos tailPos true
    | _, _ => noncanonical ref
  | false => noncanonical ref
def ProbeInfo.code (info : ProbeInfo) : Nat :=
  match info with
  | .none => 0
  | .synthetic first last canonical =>
    if canonical then first + last + 1000 else first + last
"#;

#[test]
fn from_ref_shape_preserves_inferred_constructors_default_arguments_and_fallbacks() {
    let base = seed();
    let before = base.logical_root(&KVMap::new());
    let result = checked(&base, FROM_REF);
    assert_eq!(
        values(
            &result,
            r#"
#eval (fromRef ⟨some 17, some 25, true⟩).code
#eval (fromRef ⟨some 17, some 25, true⟩ true).code
#eval (fromRef ⟨some 17, some 25, false⟩).code
#eval (fromRef ⟨some 17, some 25, false⟩ true).code
#eval (fromRef ⟨some 17, none, true⟩ true).code
#eval (fromRef ⟨none, some 25, false⟩).code
#eval (fromRef ⟨none, none, true⟩ true).code
"#
        ),
        ["42", "1042", "42", "42", "0", "0", "0"]
    );
    assert_eq!(base.logical_root(&KVMap::new()), before);
}

const GENERIC_CAPTURE: &str = r#"
export Option (none some)
universe u
structure GenericBox (α : Type u) where
  value : Option α
def GenericBox.get? {α : Type u} (box : GenericBox α) : Option α := box.value
def pick {α : Type u} (box : GenericBox α) (fallback : α) : α :=
  let get ref :=
    match ref.get? with
    | some value => value
    | none => fallback
  get box
"#;

#[test]
fn inferred_family_parameters_capture_outer_types_and_fallback_values() {
    let result = checked(&seed(), GENERIC_CAPTURE);
    assert_eq!(
        result
            .environment()
            .find(&fln::Name::from_components(["pick"]))
            .unwrap()
            .constant_val()
            .level_params,
        [fln::Name::from_components(["u"])]
    );
    assert_eq!(
        values(
            &result,
            r#"
#eval pick (GenericBox.mk (some (17 + 25))) 7
#eval pick (GenericBox.mk (none : Option Nat)) 7
#eval String.length (pick (GenericBox.mk (some ("ab" ++ "c"))) "fallback")
#eval String.length (pick (GenericBox.mk (none : Option String)) ("fall" ++ "back"))
"#
        ),
        ["42", "7", "3", "8"]
    );
}

#[test]
fn recursive_local_and_lambda_receivers_reach_constructor_family_inference() {
    let result = checked(
        &seed(),
        r#"
structure RefBox where
  value : Option Nat
def recursiveLocal (box : RefBox) : Nat :=
  let rec get ref :=
    match ref.value with
    | Option.some n => n
    | Option.none => 0
  get box
def argumentLocal (box : RefBox) : Nat :=
  (fun ref =>
    match ref.value with
    | Option.some n => n
    | Option.none => 0) box

structure RecursiveRef where
  value : Option Nat
  tailValue : Option Nat
def RecursiveRef.getPos? (ref : RecursiveRef) : Option Nat := ref.value
def RecursiveRef.getTailPos? (ref : RecursiveRef) : Option Nat := ref.tailValue
def recursivePaired (box : RecursiveRef) : Nat :=
  let rec get ref :=
    match ref.getPos?, ref.getTailPos? with
    | Option.some start, Option.some stop => start + stop
    | _, _ => 0
  get box
"#,
    );
    assert_eq!(
        values(
            &result,
            r#"
#eval recursiveLocal (RefBox.mk (Option.some 42))
#eval recursiveLocal (RefBox.mk Option.none)
#eval argumentLocal (RefBox.mk (Option.some 17))
#eval argumentLocal (RefBox.mk Option.none)
#eval recursivePaired (RecursiveRef.mk (Option.some 17) (Option.some 25))
#eval recursivePaired (RecursiveRef.mk Option.none (Option.some 25))
#eval recursivePaired (RecursiveRef.mk (Option.some 17) Option.none)
"#,
        ),
        ["42", "0", "17", "0", "42", "0", "0"]
    );
    for helper in ["recursiveLocal.get", "recursivePaired.get"] {
        let helper = fln::Name::from_components(helper.split('.'));
        assert!(matches!(
            result.environment().find(&helper),
            Some(fln_env::constants::ConstantInfo::Defn(definition))
                if definition.safety == fln_env::constants::DefinitionSafety::Safe
        ));
        assert!(
            !result
                .environment()
                .contains(&fln::Name::str(helper, "_unsafe_rec"))
        );
    }
    let before = result.logical_root(&KVMap::new());
    for body in [
        "RefBox.mk ((get ref).value)",
        "let alias := get; RefBox.mk ((alias ref).value)",
    ] {
        // The explicit constructor makes this a deferred-receiver control,
        // independent of delayed expected-type constructor notation.
        let source = format!(
            r#"def sentinelPrefix : Nat := 99
def bad (box : RefBox) : RefBox :=
  let rec get ref := {body}
  get box
"#
        );
        assert!(
            result
                .check_source_files(
                    &[source.as_bytes()],
                    &KVMap::new(),
                    SourceCheckLimits::new(limits()),
                )
                .is_err(),
            "a recursive receiver must still prove decreasing calls: {source}"
        );
        assert_eq!(result.logical_root(&KVMap::new()), before);
        for absent in ["sentinelPrefix", "bad", "bad.get"] {
            assert!(
                !result
                    .environment()
                    .contains(&fln::Name::from_components(absent.split('.')))
            );
        }
    }
}

#[test]
fn delayed_constructor_results_respect_expected_families_and_lexical_scope() {
    let base = checked(
        &seed(),
        r#"
export Bool (false true)
inductive ResultBox where
  | payload (value : Nat)
  | empty
def atomicEmpty (n : Nat) : ResultBox :=
  let make _ := .empty
  make n
def choose (flag : Bool) (n : Nat) : ResultBox :=
  let make flag :=
    match flag with
    | true => .payload n
    | false => .empty
  make flag
inductive Wrapped where
  | mk (value : Nat)
def owner (n : Nat) : Wrapped :=
  let rec make (n : Nat) :=
    .mk (let rec inner (m : Nat) : Nat := m + 1; inner n)
  make n
"#,
    );
    for helper in ["owner.make", "owner.make.inner"] {
        assert!(
            base.environment()
                .contains(&fln::Name::from_components(helper.split('.'))),
            "delayed constructor arguments must retain lexical helper parent {helper}"
        );
    }
    assert!(
        !base
            .environment()
            .contains(&fln::Name::from_components(["owner", "inner"]))
    );
    let before = base.logical_root(&KVMap::new());
    assert_eq!(
        values(
            &base,
            r#"
#eval match atomicEmpty 42 with | .empty => 7 | .payload value => value
#eval match choose true 42 with | .empty => 7 | .payload value => value
#eval match choose false 42 with | .empty => 7 | .payload value => value
#eval match owner 41 with | .mk value => value
"#
        ),
        ["7", "42", "7", "42"]
    );
    for source in [
        "def bad : Nat := let make _ := .empty; make 0",
        "def bad : (α : Type) → α → Option α := let package value := .some value; fun α value => package value",
        "theorem bad : (0 : Nat) = 1 := let proof _ := .refl; proof 0",
        "def bad (n : Nat) : Wrapped := let rec make (n : Nat) := .mk (let alias := make; match alias n with | Wrapped.mk value => value); make n",
    ] {
        assert!(
            base.check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits()),
            )
            .is_err(),
            "accepted {source}"
        );
        assert_eq!(base.logical_root(&KVMap::new()), before);
        assert!(
            !base
                .environment()
                .contains(&fln::Name::from_components(["bad"]))
        );
        assert!(
            !base
                .environment()
                .contains(&fln::Name::from_components(["bad", "make"]))
        );
    }
}

#[test]
fn whole_helper_replay_preserves_nested_constructor_work_and_helper_identity() {
    let base = checked(
        &seed(),
        r#"
structure MixedRef where
  value : Option Nat
inductive MixedResult where
  | mk (value : Nat)
"#,
    );
    let before = base.logical_root(&KVMap::new());
    let source = r#"
def mixed (ref : MixedRef) : MixedResult :=
  let get input :=
    let rec make (n : Nat) :=
      .mk (let rec inner (m : Nat) : Nat := m + 1; inner n)
    match input.value with
    | .some value => make value
    | .none => .mk 0
  get ref
"#;
    let first = checked(&base, source);
    let repeated = checked(&base, source);
    assert_eq!(
        values(
            &first,
            r#"
#eval match mixed (MixedRef.mk (Option.some 41)) with | .mk value => value
#eval match mixed (MixedRef.mk Option.none) with | .mk value => value
"#,
        ),
        ["42", "0"]
    );
    for declaration in ["mixed", "mixed.make", "mixed.make.inner"] {
        let name = fln::Name::from_components(declaration.split('.'));
        let definition = first
            .environment()
            .find(&name)
            .unwrap_or_else(|| panic!("missing lexical declaration {declaration}"));
        assert_eq!(
            repeated.environment().find(&name),
            Some(definition),
            "whole-value replay must keep deterministic helper identities"
        );
    }
    let mut helpers: Vec<_> = first
        .environment()
        .constants()
        .map(|(name, _)| name.to_display_string())
        .filter(|name| name.starts_with("mixed.make"))
        .collect();
    helpers.sort();
    assert_eq!(helpers, ["mixed.make", "mixed.make.inner"]);
    assert!(
        !first
            .environment()
            .contains(&fln::Name::from_components(["mixed", "inner"]))
    );

    let invalid = r#"
def sentinelPrefix : Nat := 99
def bad (ref : MixedRef) : MixedResult :=
  let get input :=
    let rec make (n : Nat) :=
      .missing (let rec inner (m : Nat) : Nat := m + 1; inner n)
    match input.value with
    | .some value => make value
    | .none => .mk 0
  get ref
"#;
    assert!(
        base.check_source_files(
            &[invalid.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        )
        .is_err(),
        "selected delayed constructor errors cannot disappear during whole-helper replay"
    );
    assert_eq!(base.logical_root(&KVMap::new()), before);
    for absent in ["sentinelPrefix", "bad", "bad.make", "bad.make.inner"] {
        assert!(
            !base
                .environment()
                .contains(&fln::Name::from_components(absent.split('.')))
        );
    }
}

const INVALID: &[&str] = &[
    r#"
def sentinelPrefix : Nat := 99
def bad : Nat := let get A.x := 7; get 1
"#,
    r#"
def bad (ref : RefBox) : Nat :=
  let get ref :=
    match ref.noSuchPos? with
    | some pos => pos
    | none => 0
  get ref
"#,
    r#"
def bad : Nat :=
  let get ref :=
    match ref.getPos? with
    | some pos => pos
    | none => 0
  get true
"#,
    r#"
def bad (ref : RefBox) : Bool :=
  let get ref : Bool :=
    match ref.getPos? with
    | some pos => pos
    | none => false
  get ref
"#,
    r#"
def bad : Nat :=
  let get ref :=
    match ref.getPos? with
    | some pos => pos
    | none => 0
  0
"#,
    r#"
def bad (ref : RefBox) : Nat :=
  let get ref : Bool :=
    match ref.getPos? with
    | some pos => pos
    | none => false
  let ignored := get ref
  0
"#,
];

#[test]
fn invalid_fields_receivers_and_unused_bodies_remain_checked_and_atomic() {
    let base = checked(&seed(), DATA);
    let before = base.logical_root(&KVMap::new());
    for source in INVALID {
        assert!(
            base.check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits()),
            )
            .is_err(),
            "accepted {source}"
        );
        assert_eq!(base.logical_root(&KVMap::new()), before);
        assert!(
            !base
                .environment()
                .contains(&fln::Name::from_components(["sentinelPrefix"]))
        );
        assert!(
            !base
                .environment()
                .contains(&fln::Name::from_components(["bad"]))
        );
    }
    let usable = checked(&base, "def retained : Nat := (RefBox.mk 17 25).start");
    assert_eq!(values(&usable, "#eval retained"), ["17"]);
}
