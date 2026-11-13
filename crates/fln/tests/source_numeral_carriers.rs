//! Numeral carrier inference must preserve the type given to instance search.
//!
//! Pinned `Lean/Elab/BuiltinTerm.lean::mkFreshTypeMVarFor`/`elabNumLit`
//! retain the inferred carrier; `Lean/Meta/SynthInstance.lean::synthInstanceCore?`
//! then uses instances transparency. The two refusals are the pin observations
//! recorded in fln-5efd. A semireducible record value must not be unfolded merely
//! to assign the numeral's unknown type during operator elaboration.
#![forbid(unsafe_code)]

use fln::{
    Budget, Engine, EngineAdmissionLimits, EngineExecutionError, KVMap, NatDefinitionFrontendError,
    Outcome, SourceCheckError, SourceCheckLimits,
};
use fln_elab::NatDefinitionElabError;
use fln_elab::source::SourceInferenceError;

const PREFIX: &str = "structure Carrier where\n  carrier : Type\nstructure Value (A : Type) where\n  value : A\nstructure Both extends Carrier, Value carrier where\n  tag : Nat\ndef b : Both := { carrier := Nat, value := 31, tag := 37 }";

fn limits() -> SourceCheckLimits {
    SourceCheckLimits::new(EngineAdmissionLimits::new(Budget::for_stack_bytes(
        2 * 1024 * 1024,
    )))
}

fn engine() -> Engine {
    Engine::with_coercion_seed(limits().admission)
        .unwrap()
        .into_complete()
        .unwrap()
}

fn checked(base: &Engine, source: &str) -> Engine {
    base.check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .expect("both checkers must complete")
        .engine
}

const EXPECTED_FLN_5EFD_MESSAGE: &str = "\
failed to synthesize instance of type class
  OfNat b.carrier 31
numerals are polymorphic in Lean, but the numeral `31` cannot be used in a context where the expected type is
  b.carrier
due to the absence of the instance above

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.";

fn instance_refused(base: &Engine, source: &str) -> SourceCheckError {
    let before = base.logical_root(&KVMap::new());
    let result = base.check_source_files(&[source.as_bytes()], &KVMap::new(), limits());
    let error = match result {
        Err(error) => error,
        Ok(Outcome::Complete(_)) => panic!("pin-refused numeral was accepted: {source}"),
        Ok(_) => panic!("instance-search failure became a nonanswer: {source}"),
    };
    assert!(
        matches!(
            &error,
            SourceCheckError::Command { error, .. }
                if matches!(
                    error.as_ref(),
                    EngineExecutionError::Frontend(NatDefinitionFrontendError::Elaborate(
                        NatDefinitionElabError::Inference(
                            SourceInferenceError::InstanceSynthesisRequired(_)
                        )
                    ))
                )
        ),
        "expected instance-search refusal, not a different failure: {source}\n{error:?}"
    );
    assert_eq!(error.disposition(), ("elaboration", false, 1));
    assert_eq!(base.logical_root(&KVMap::new()), before);
    error
}

#[test]
fn dependent_result_preserves_its_carrier_for_numeral_instance_search() {
    let base = checked(&engine(), PREFIX);
    // Explicit parent projection isolates numeral inference from automatic
    // parent coercions (fln-azxg).
    let source = "def castV (b : Both) : Value b.carrier := b.toValue\ntheorem bad : (castV b).value = 31 := by rfl";
    let error = instance_refused(&base, source);
    let SourceCheckError::Command { offset, error, .. } = &error else {
        panic!("expected command refusal: {error:?}");
    };
    assert_eq!(*offset, source.rfind("31").unwrap());
    assert_eq!(
        error.lean_diagnostic(),
        Some(("error(lean.synthInstanceFailed)", EXPECTED_FLN_5EFD_MESSAGE))
    );
}

#[test]
fn ascribed_projection_retains_its_actual_carrier_for_numeral_instance_search() {
    let base = checked(&engine(), PREFIX);
    // An ascription checks convertibility; it does not replace inferType's
    // result for the projected value with Nat.
    let source = "theorem bad : (b.toValue.value : Nat) = 31 := by rfl";
    let error = instance_refused(&base, source);
    let SourceCheckError::Command { offset, error, .. } = &error else {
        panic!("expected command refusal: {error:?}");
    };
    assert_eq!(*offset, source.rfind("31").unwrap());
    assert_eq!(
        error.lean_diagnostic(),
        Some(("error(lean.synthInstanceFailed)", EXPECTED_FLN_5EFD_MESSAGE))
    );
}

#[test]
fn explicitly_typed_numerals_still_convert_to_a_dependent_carrier() {
    let base = checked(&engine(), PREFIX);
    checked(
        &base,
        "def castV (b : Both) : Value b.carrier := b.toValue\ntheorem via_function : (castV b).value = (31 : Nat) := by rfl\ntheorem via_projection : (b.toValue.value : Nat) = (31 : Nat) := by rfl",
    );
}

#[test]
fn explicitly_typed_numerals_still_convert_to_semireducible_type_aliases() {
    checked(
        &engine(),
        "def MyNat := Nat\ndef z : MyNat := (31 : Nat)\ntheorem correct : z = (31 : Nat) := by rfl",
    );
}

#[test]
fn concrete_numeric_aliases_cannot_fall_back_to_default_instances() {
    let base = checked(&engine(), "def NumericAlias (A : Type) : Type := A");
    // The pin reports a failed concrete search before trying defaults. These
    // also cover the old default-conversion fixture's incorrect acceptances.
    for source in [
        "def bad : NumericAlias Nat := 7",
        "def bad : NumericAlias Float := 1.25",
    ] {
        let _ = instance_refused(&base, source);
    }
    checked(
        &base,
        "def natural : NumericAlias Nat := (7 : Nat)\ndef scientific : NumericAlias Float := (1.25 : Float)",
    );
}

#[test]
fn stuck_numeric_carriers_still_receive_defaults() {
    checked(
        &engine(),
        "def inferred := 31\ndef scientific := 1.25\ntheorem inferred_ok : inferred = (31 : Nat) := rfl",
    );
}
