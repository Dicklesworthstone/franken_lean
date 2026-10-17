//! Source-level higher-order inference through the ordinary dual-checker door.
#![forbid(unsafe_code)]

use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, Name, SourceCheckLimits};
use fln_env::constants::ConstantInfo;

fn limits() -> SourceCheckLimits {
    SourceCheckLimits::new(EngineAdmissionLimits::new(Budget::for_stack_bytes(
        2 * 1024 * 1024,
    )))
}
fn engine() -> Engine {
    Engine::with_source_seed(limits().admission)
        .unwrap()
        .into_complete()
        .unwrap()
}
fn checked(base: &Engine, text: &str, name: &str) -> Engine {
    let result = base
        .check_source_files(&[text.as_bytes()], &KVMap::new(), limits())
        .unwrap_or_else(|error| panic!("{text}\n{error:?}"))
        .into_complete()
        .expect("both checking engines must complete")
        .engine;
    assert!(matches!(
        result.environment().find(&Name::from_components([name])),
        Some(ConstantInfo::Defn(_))
    ));
    result
}
const ETA: &str = r#"
def etaArgument {F : Nat → Type} (wrap : (Nat → Nat) → Nat) (h : Nat → Nat)
    (x : F (wrap (fun n => h n))) : F (wrap (fun n => h n)) := x
def recoveredFamily (F : Nat → Type) (wrap : (Nat → Nat) → Nat) (h : Nat → Nat)
    (x : F (wrap h)) : F (wrap h) := etaArgument wrap h x
"#;
const PROOFS: &str = r#"
def proofArgument {F : Nat → Type} {P : Prop} (wrap : P → Nat) (p q : P)
    (x : F (wrap p)) : F (wrap p) := x
def recoveredProofFamily (F : Nat → Type) (P : Prop) (wrap : P → Nat) (p q : P)
    (x : F (wrap q)) : F (wrap q) := proofArgument wrap p q x
"#;

#[test]
fn source_infers_a_family_through_an_eta_equivalent_argument() {
    checked(&engine(), ETA, "recoveredFamily");
}

#[test]
fn source_infers_a_family_through_distinct_proof_arguments() {
    checked(&engine(), PROOFS, "recoveredProofFamily");
}

#[test]
fn source_refusal_does_not_publish_a_bad_family_or_break_recovery() {
    let base = engine();
    let source = format!(
        "{ETA}\ndef badFamily (F : Nat → Type) (wrap : (Nat → Nat) → Nat) \
         (h k : Nat → Nat) (x : F (wrap h)) : F (wrap k) := etaArgument wrap h x"
    );
    assert!(
        base.check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
            .is_err(),
        "unrelated functions cannot be made definitionally equal"
    );
    assert!(
        !base
            .environment()
            .contains(&Name::from_components(["badFamily"]))
    );
    checked(&base, ETA, "recoveredFamily");
}

const RECORD_SUFFIX: &str = r#"
structure PairN where
  left : Nat
  right : Nat
def consumeRecord {F : PairN → Type} (p : PairN)
    (x : F (PairN.mk p.left p.right)) : Nat := 7
def inferRecordFamily (F : PairN → Type) (p : PairN) (x : F p) : Nat :=
  consumeRecord p x
"#;

#[test]
fn source_infers_a_record_family_from_an_argument_without_a_result_type_hint() {
    checked(&engine(), RECORD_SUFFIX, "inferRecordFamily");
}

#[test]
fn source_infers_a_dependent_record_family_from_a_reconstruction() {
    checked(
        &engine(),
        r#"
structure Dependent where
  type : Type
  value : type
def consumeDependent {F : Dependent → Type} (p : Dependent)
    (x : F (Dependent.mk p.type p.value)) : Nat := 7
def inferDependentFamily (F : Dependent → Type) (p : Dependent) (x : F p) : Nat :=
  consumeDependent p x
"#,
        "inferDependentFamily",
    );
}

#[test]
fn source_record_suffix_refusal_is_atomic_and_does_not_guess_a_field() {
    let base = engine();
    let root = base.logical_root(&KVMap::new());
    let invalid = format!(
        r#"{RECORD_SUFFIX}
def badRecord (F : PairN → Type) (p q : PairN) (x : F q) : Nat :=
  consumeRecord (F := F) p x"#
    );
    assert!(
        base.check_source_files(&[invalid.as_bytes()], &KVMap::new(), limits())
            .is_err()
    );
    assert_eq!(base.logical_root(&KVMap::new()), root);
    assert!(
        !base
            .environment()
            .contains(&Name::from_components(["PairN"]))
    );
    checked(&base, RECORD_SUFFIX, "inferRecordFamily");
}
