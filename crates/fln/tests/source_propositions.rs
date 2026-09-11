//! Real source proofs exercise candidate generation and both admission engines.
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
fn check(source: &str) -> fln::SourceFileCheck {
    engine()
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        )
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .unwrap()
}
fn refuses(source: &str) {
    let base = engine();
    let root = base.logical_root(&KVMap::new());
    let result = base.check_source_files(
        &[source.as_bytes()],
        &KVMap::new(),
        SourceCheckLimits::new(limits()),
    );
    assert!(!matches!(result, Ok(Outcome::Complete(_))), "{source}");
    assert_eq!(base.logical_root(&KVMap::new()), root);
}
const EITHER: &str =
    "inductive EitherProof (P Q : Prop) : Prop where | left (h : P) | right (h : Q)\n";
const BOTH: &str = "inductive Both (P Q : Prop) : Prop where | intro (hp : P) (hq : Q)\n";
const EXISTS: &str =
    "inductive HasWitness (A : Type) (P : A -> Prop) : Prop where | intro (a : A) (h : P a)\n";
const LE: &str = "inductive Below (a : Nat) : Nat -> Prop where | refl : Below a a | step (n : Nat) (h : Below a n) : Below a (Nat.succ n)\n";

#[test]
fn source_empty_and_unit_predicates_have_checked_large_eliminators() {
    check(
        "inductive Absurd : Prop where\ninductive Truth : Prop where | intro\ntheorem truth : Truth := Truth.intro\ndef eliminate (A : Type) (h : Absurd) : A := by cases h\ndef constant (h : Truth) : Nat := match h with | .intro => 7\ntheorem computes : constant Truth.intro = 7 := by rfl",
    );
}
#[test]
fn conjunction_and_disjunction_can_be_constructed_and_eliminated() {
    check(&format!(
        "{BOTH}{EITHER}theorem leftProjection (P Q : Prop) (h : Both P Q) : P := by cases h with | intro hp hq => exact hp\ntheorem swap (P Q : Prop) (h : EitherProof P Q) : EitherProof Q P := by cases h with | left hp => exact EitherProof.right hp | right hq => exact EitherProof.left hq"
    ));
}
#[test]
fn small_elimination_is_available_to_ordinary_matches() {
    check(&format!(
        "{EITHER}theorem collapse (P : Prop) (h : EitherProof P P) : P := match h with | .left hp => hp | .right hp => hp"
    ));
}
#[test]
fn proof_fields_permit_singleton_large_elimination() {
    check(&format!(
        "{BOTH}def constant (P Q : Prop) (h : Both P Q) : Nat := match h with | .intro hp hq => 3\ntheorem constant_ok (P Q : Prop) (hp : P) (hq : Q) : constant P Q (Both.intro hp hq) = 3 := by rfl"
    ));
}
#[test]
fn witnesses_in_prop_can_live_in_arbitrarily_large_sorts() {
    check(
        "inductive HasType : Prop where | intro (A : Type) (value : A)\ntheorem wrapped : HasType := HasType.intro Nat 7\ninductive LargeData where | pack (A : Type)\ninductive LargeWitness : Prop where | intro (value : LargeData)\ntheorem big : LargeWitness := LargeWitness.intro (LargeData.pack Nat)",
    );
}
#[test]
fn existential_elimination_retains_the_logical_premise() {
    check(&format!(
        "{EXISTS}theorem transport (A : Type) (P Q : A -> Prop) (f : forall a : A, P a -> Q a) (h : HasWitness A P) : HasWitness A Q := by cases h with | intro a hp => exact HasWitness.intro a (f a hp)"
    ));
}
#[test]
fn disjunction_and_existentials_cannot_be_eliminated_into_data() {
    refuses(&format!(
        "{EITHER}def distinguish (P Q : Prop) (h : EitherProof P Q) : Nat := match h with | .left hp => 0 | .right hq => 1"
    ));
    refuses(&format!(
        "{EXISTS}def witness (A : Type) (P : A -> Prop) (h : HasWitness A P) : A := by cases h with | intro a hp => exact a"
    ));
    refuses(&format!(
        "{EXISTS}def witness (A : Type) (P : A -> Prop) (h : HasWitness A P) : A := match h with | .intro a hp => a"
    ));
}
#[test]
fn indexed_recursive_relations_support_actual_induction() {
    check(&format!(
        "{LE}theorem sample : Below 2 4 := Below.step 3 (Below.step 2 Below.refl)\ntheorem transitive (a b : Nat) (hab : Below a b) (c : Nat) (hbc : Below b c) : Below a c := by induction hbc with | refl => exact hab | step n h ih => exact Below.step n ih"
    ));
}
#[test]
fn singleton_data_fields_must_be_recoverable_as_exact_indices() {
    check(
        "inductive At (A : Type) : A -> Prop where | intro (a : A) : At A a\ndef recover (A : Type) (a : A) (h : At A a) : A := by cases h with | intro value => exact value\ntheorem recovered : recover Nat 7 (At.intro 7) = 7 := by rfl",
    );
    refuses(
        "inductive Hidden : Nat -> Prop where | intro (n : Nat) : Hidden (Nat.succ n)\ndef extract (n : Nat) (h : Hidden n) : Nat := by cases h with | intro value => exact value",
    );
}
#[test]
fn false_propositional_proofs_and_negative_occurrences_never_publish() {
    refuses(&format!(
        "{LE}theorem falseRelation : Below 3 0 := Below.refl"
    ));
    refuses("inductive Bad : Prop where | intro (f : Bad -> Nat)");
    refuses(&format!(
        "{BOTH}theorem falseProof : Both (1 = 2) (0 = 0) := Both.intro rfl rfl"
    ));
    let good = check(&format!(
        "{BOTH}theorem recover : Both (1 = 1) (0 = 0) := Both.intro rfl rfl"
    ));
    assert!(
        good.engine
            .environment()
            .contains(&Name::from_components(["recover"]))
    );
}
