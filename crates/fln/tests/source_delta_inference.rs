//! Deferred ordinary source typing may unfold safe definitions; selection
//! queries and the final dual-checker admission retain their own policies.
#![forbid(unsafe_code)]
use fln::{Engine, EngineAdmissionLimits, SourceCheckLimits};
use fln_core::{name::Name, options::KVMap, outcome::Outcome};
use fln_kernel::verdict::Budget;

fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}
fn engine() -> Engine {
    Engine::with_source_seed(limits())
        .unwrap()
        .into_complete()
        .unwrap()
}
fn check(base: &Engine, source: &str) -> fln::SourceFileCheck {
    base.check_source_files(
        &[source.as_bytes()],
        &KVMap::new(),
        SourceCheckLimits::new(limits()),
    )
    .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
    .into_complete()
    .expect("both checkers must answer")
}
const WRAP: &str = "def wrap (n : Nat) : Nat := n\n";

#[test]
fn ordinary_rfl_infers_shared_arguments_through_safe_delta_conversion() {
    let base = check(&engine(), WRAP).engine;
    for source in [
        "theorem left (n : Nat) : wrap n = n := rfl",
        "theorem right (n : Nat) : n = wrap n := rfl",
        "theorem nested (n : Nat) : wrap (wrap n) = n := rfl",
        "theorem beta (n : Nat) : wrap ((fun x => x) n) = n := rfl",
        "theorem proofLambda : forall n : Nat, wrap n = n := fun n => rfl",
    ] {
        check(&base, source);
    }
}

#[test]
fn ordinary_implicit_calls_not_only_rfl_use_the_delta_retry() {
    check(
        &engine(),
        "def wrap (n : Nat) : Nat := n\ndef reflAlias {n : Nat} : wrap n = n := by rfl\ntheorem use (n : Nat) : n = n := reflAlias\ndef takeProof (n : Nat) (h : wrap n = n) : Nat := n\ndef answer : Nat := takeProof 7 rfl\ntheorem result : answer = 7 := by rfl",
    );
}

#[test]
fn polymorphic_definitions_are_instantiated_before_delta_matching() {
    check(
        &engine(),
        "def identity {A : Sort u} (x : A) : A := x\ntheorem term {A : Sort u} (x : A) : identity x = x := rfl\ntheorem type (A : Type) : identity A = A := rfl\ntheorem prop (P : Prop) : identity P = P := rfl",
    );
}

#[test]
fn failed_speculative_conversion_falls_back_without_publishing_assignments() {
    let base = check(&engine(), WRAP).engine;
    check(
        &base,
        "theorem fallback (x y : Nat) (h : x = y) : wrap x = y := by first | exact rfl | exact h",
    );
    check(
        &base,
        "theorem direct (x : Nat) : wrap x = x := by first | exact rfl | fail",
    );
    for source in [
        "theorem bad (n : Nat) : wrap n = Nat.succ n := rfl",
        "theorem bad : wrap 0 = 1 := by first | exact rfl | rfl",
        "theorem bad (rfl : Nat) (n : Nat) : wrap n = n := rfl",
    ] {
        let root = base.logical_root(&KVMap::new());
        assert!(
            base.check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits())
            )
            .is_err(),
            "{source}"
        );
        assert_eq!(base.logical_root(&KVMap::new()), root);
        assert!(!base.environment().contains(&Name::from_components(["bad"])));
    }
}

#[test]
fn resource_nonanswers_do_not_trigger_conversion_success() {
    let base = check(&engine(), WRAP).engine;
    let root = base.logical_root(&KVMap::new());
    let mut low = SourceCheckLimits::new(limits());
    low.admission.kernel = low.admission.kernel.narrowed(0, 32);
    let result = base.check_source_files(
        &[b"theorem low (n : Nat) : wrap n = n := rfl"],
        &KVMap::new(),
        low,
    );
    match result {
        Ok(Outcome::Inconclusive(_)) => {}
        Err(error) => assert!(
            matches!(error.disposition(), ("resource" | "inconclusive", false, 3)),
            "{error:?}"
        ),
        other => panic!("resource stop changed into a verdict: {other:?}"),
    }
    assert_eq!(base.logical_root(&KVMap::new()), root);
    assert!(!base.environment().contains(&Name::from_components(["low"])));
}
