//! Pinned generator/consumer selection order, exercised through source admission.
#![forbid(unsafe_code)]

use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, SourceCheckLimits};

fn limits() -> SourceCheckLimits {
    SourceCheckLimits::new(EngineAdmissionLimits::new(Budget::for_stack_bytes(
        2 * 1024 * 1024,
    )))
}

fn checked(base: &Engine, source: &str) -> Engine {
    base.check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
        .unwrap_or_else(|error| panic!("source checking failed: {error:?}\n{source}"))
        .into_complete()
        .expect("complete source admission")
        .engine
}

fn source(source: &str) -> Engine {
    let base = Engine::with_source_seed(limits().admission)
        .unwrap()
        .into_complete()
        .unwrap();
    checked(&base, source)
}

fn refuses(engine: &Engine, source: &str) {
    let before = engine.logical_root(&KVMap::new());
    let error = engine
        .check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
        .expect_err("the conflicting selected-instance value must be refused");
    assert_eq!(error.disposition(), ("elaboration", false, 1));
    assert_eq!(engine.logical_root(&KVMap::new()), before);
}

/// Only the outer synthesis request preprocesses output parameters. The pin's
/// `SynthInstance.tryResolve` matches a prerequisite's repeated unknown before
/// `consume` can run the candidate's prerequisites. Erasing the two occurrences
/// independently lets the impossible `duoBad` warm `Side` with `sideLow`; the
/// later `sideHigh` has the same answer type and cannot replace that value.
#[test]
fn repeated_prerequisite_outputs_reject_an_impossible_candidate_before_its_subgoals() {
    let engine = source(
        r#"class Duo (a : outParam Nat) (b : outParam Nat) where
  value : Nat
class Side where
  value : Nat
instance duoGood : Duo 0 0 := Duo.mk 0
instance sideLow : Side := Side.mk 1
instance sideHigh {n : Nat} [d : Duo n n] : Side := Side.mk 3
instance duoBad [s : Side] : Duo 0 1 := Duo.mk 99
class Root where
  value : Nat
instance root {n : Nat} [d : Duo n n] [s : Side] : Root := Root.mk s.value
def result : Root := inferInstance
theorem selectedValue : result.value = 3 := by rfl"#,
    );
    refuses(
        &engine,
        "theorem warmedByImpossibleCandidate : result.value = 1 := by rfl",
    );
}

/// `SynthInstance.mkAnswer` infers the dictionary value's type, and
/// `isNewAnswer` compares that type structurally. The query `D (Box ?A)` becomes
/// `D (Box Nat)` for both candidates, but the actual types `D NatBox` and
/// `D (Box Nat)` are distinct table answers. The first cannot satisfy `Accept`,
/// so the second must remain available to the suspended consumer.
#[test]
fn distinct_dictionary_type_aliases_remain_distinct_completed_answers() {
    let engine = source(
        r#"structure Box (A : Type) where
  value : A
abbrev NatBox := Box Nat
class D (A : semiOutParam Type) where
  value : Nat
instance low : D (Box Nat) := D.mk 7
instance high : D NatBox := D.mk 99
class Accept (A : Type) [d : D A] where
  value : Nat
instance accept : @Accept (Box Nat) low := @Accept.mk (Box Nat) low 7
class Root where
  value : Nat
instance root {A : Type} [d : D (Box A)] [ok : @Accept (Box A) d] : Root := Root.mk ok.value
def result : Root := inferInstance
theorem selectedValue : result.value = 7 := by rfl"#,
    );
    refuses(
        &engine,
        "theorem discardedAlternative : result.value = 99 := by rfl",
    );
}

/// The pin's `mkTableKey` renames both expression and universe variables.
/// Once `Allowed Type` fails, the new Nat answer wakes both Carrier consumers;
/// their resumptions run before the fresh `Allowed Nat` generator. That
/// generator therefore completes the newer both-Nat branch first. Explicit
/// priority makes the initial Type choice independent of index tie ordering.
#[test]
fn polymorphic_consumers_share_answers_before_a_later_generator_runs() {
    let engine = source(
        r#"class Carrier.{u} (A : outParam (Type u)) where
  value : Nat
instance low : Carrier Nat := Carrier.mk 7
instance (priority := 1100) high : Carrier Type := Carrier.mk 99
class Allowed.{u} (A : Type u) where
  value : Nat
instance allowed : Allowed Nat := Allowed.mk 7
class Root where
  first : Nat
  second : Nat
instance root.{u,v} {A : Type u} {B : Type v} [first : Carrier A] [second : Carrier B] [valid : Allowed B] : Root := Root.mk first.value second.value
def result : Root := inferInstance
theorem firstValue : result.first = 7 := by rfl
theorem secondValue : result.second = 7 := by rfl"#,
    );
    refuses(
        &engine,
        "theorem staleFirstChoice : result.first = 99 := by rfl",
    );
}
