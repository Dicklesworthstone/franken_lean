//! Nat's compiled logical body is observable on open terms, even when closed
//! arithmetic can use the native literal evaluator. These exact source programs
//! were checked against pinned Reference 4.32.0 (8c9756b): all positive programs
//! accept, while the six negative proofs fail at definitional equality.
#![forbid(unsafe_code)]

use fln::{Budget, ConstantInfo, Engine, EngineAdmissionLimits, KVMap, Name, SourceCheckLimits};

const ADD_MODEL: &str = "def addModel (a b : Nat) : Nat := Nat.rec (motive := fun _ => Nat) a (fun _ ih => Nat.succ ih) b";

fn limits() -> SourceCheckLimits {
    SourceCheckLimits::new(EngineAdmissionLimits::new(Budget::for_stack_bytes(
        2 * 1024 * 1024,
    )))
}

fn engine() -> Engine {
    Engine::with_source_seed(limits().admission)
        .unwrap()
        .into_complete()
        .expect("source seed must pass both checkers")
}

fn checked(base: &Engine, source: &str) -> Engine {
    base.check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .expect("both checkers must complete")
        .engine
}

fn refused_conversion(base: &Engine, source: &str) {
    let before = base.logical_root(&KVMap::new());
    let error = base
        .check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
        .expect_err("the pin refuses this reflexivity proof");
    assert_eq!(
        error.disposition(),
        ("elaboration", false, 1),
        "a conversion refusal is required, not unsupported syntax or resource exhaustion: {source}\n{error:?}",
    );
    assert_eq!(base.logical_root(&KVMap::new()), before);
}

#[test]
fn closed_and_symbolic_addition_equations_follow_the_pin() {
    checked(
        &engine(),
        "theorem closed : Nat.add 17 25 = 42 := rfl\n\
         theorem nestedClosed : Nat.add (Nat.add 2 3) (Nat.add 4 5) = 14 := rfl\n\
         theorem zeroRight (n : Nat) : Nat.add n 0 = n := rfl\n\
         theorem literalSuccessor (n : Nat) : Nat.add n 2 = Nat.succ (Nat.succ n) := rfl\n\
         theorem symbolicSuccessor (a b : Nat) : Nat.add a (Nat.succ b) = Nat.succ (Nat.add a b) := rfl\n\
         theorem nestedOffset (n : Nat) : Nat.add (Nat.add n 2) 3 = Nat.add n 5 := rfl",
    );
}

#[test]
fn invalid_symbolic_offsets_refuse_without_publishing() {
    let base = engine();
    for source in [
        "theorem badOffset (n : Nat) : Nat.add n 2 = 1 := rfl",
        "theorem badOffsetReverse (n : Nat) : 1 = Nat.add n 2 := rfl",
        "theorem badDifference (n : Nat) : Nat.add n 2 = Nat.add n 3 := rfl",
        "theorem badBases (a b : Nat) : Nat.add a 3 = Nat.add b 3 := rfl",
    ] {
        refused_conversion(&base, source);
    }
    checked(&base, "theorem recovery : Nat.add 3 4 = 7 := rfl");
}

#[test]
fn course_of_values_addition_is_not_replaced_by_a_direct_fold() {
    let base = engine();
    // Check the model declaration independently. A Nat.rec parser or motive
    // inference refusal cannot masquerade as the intended compatibility result.
    let model = checked(&base, ADD_MODEL);
    assert!(matches!(
        model
            .environment()
            .find(&Name::from_components(["addModel"])),
        Some(ConstantInfo::Defn(_)),
    ));
    checked(
        &model,
        "theorem modelClosed : addModel 17 25 = Nat.add 17 25 := rfl\n\
         theorem modelZero (n : Nat) : addModel n 0 = n := rfl",
    );
    // The pin's compiled Nat.add uses Nat.brecOn and a product-valued history.
    // With an unknown second argument it is not definitionally equal to this
    // mathematically equivalent direct Nat.rec implementation.
    for source in [
        "theorem badModel (a b : Nat) : addModel a b = Nat.add a b := rfl",
        "theorem badModelReverse (a b : Nat) : Nat.add a b = addModel a b := rfl",
    ] {
        refused_conversion(&model, source);
    }
}
