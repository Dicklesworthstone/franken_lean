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
