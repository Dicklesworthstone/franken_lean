//! Constructor reasoning must produce real proof terms for both checking seats.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, SourceCheckLimits};
fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}
fn engine() -> Engine {
    Engine::with_source_seed(limits())
        .unwrap()
        .into_complete()
        .unwrap()
}
fn check(source: &str) {
    engine()
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        )
        .unwrap_or_else(|e| panic!("{source}\n{e:?}"))
        .into_complete()
        .unwrap();
}
fn refuse(source: &str) {
    let base = engine();
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
    assert_eq!(root, base.logical_root(&KVMap::new()));
}
#[test]
fn successor_injection_and_disjointness_are_checked() {
    check(
        "theorem inject (x y : Nat) (h : Nat.succ x = Nat.succ y) : x = y := by injection h with hx; exact hx",
    );
    check("theorem clash (x : Nat) (h : Nat.succ x = 0) : 7 = 9 := by injection h");
    check("def clash (x : Nat) (h : 0 = Nat.succ x) : String := by injection h");
}
#[test]
fn record_fields_and_recursive_fields_produce_equalities_in_order() {
    check(
        "structure Pair (A : Type) where\n  fst : A\n  snd : A\n theorem inj (A : Type) (a b c d : A) (h : Pair.mk a b = Pair.mk c d) : b = d := by injection h with ha hb; exact hb",
    );
    check(
        "inductive Seq (A : Type) where\n  | nil\n  | cons (head : A) (tail : Seq A)\n theorem tails (A : Type) (a b : A) (xs ys : Seq A) (h : Seq.cons a xs = Seq.cons b ys) : xs = ys := by injection h with hh ht; exact ht",
    );
}
#[test]
fn indexed_payload_selector_generalizes_indices_instead_of_guessing_them() {
    check(
        "inductive Vec (A : Type) : Nat -> Type where\n  | nil : Vec A 0\n  | cons (n : Nat) (head : A) (tail : Vec A n) : Vec A (Nat.succ n)\n theorem heads (A : Type) (n : Nat) (a b : A) (xs ys : Vec A n) (h : Vec.cons n a xs = Vec.cons n b ys) : a = b := by injection h with hn hab; exact hab",
    );
}
#[test]
fn different_constructors_can_eliminate_into_dependent_data() {
    check(
        "inductive Choice (A : Type) where\n  | left (a : A)\n  | right (a : A)\n def impossible (A : Type) (a b : A) (h : Choice.left a = Choice.right b) (P : A -> Type) : P a := by injection h",
    );
    check("theorem impossible (h : true = false) : 0 = 1 := by injection h");
}
#[test]
fn introduced_and_branch_local_equalities_keep_their_scopes() {
    check(
        "theorem introEq (x y : Nat) : Nat.succ x = Nat.succ y -> x = y := by intro h; injection h with eq; exact eq",
    );
    check(
        "theorem nested (b : Bool) (x y : Nat) (h : Nat.succ x = Nat.succ y) : x = y := by\n  cases b with\n  | false =>\n    injection h with eq\n    exact eq\n  | true =>\n    injection h\n    assumption",
    );
}
#[test]
fn malformed_or_false_injections_never_publish_proofs() {
    for source in [
        "theorem bad (x y : Nat) (h : Nat.succ x = Nat.succ y) : 0 = 1 := by injection h with eq; rfl",
        "theorem bad (x y : Nat) (h : x = y) : x = y := by injection h; assumption",
        "theorem bad (h : 0 = 0) : 0 = 1 := by injection h",
        "theorem bad (x y : Nat) (h : Nat.succ x = Nat.succ y) : x = y := by injection h with eq extra; assumption",
        "theorem bad (x y : Nat) (h : Nat.succ x = Nat.succ y) : x = y := by injection h with eq; exact (fun ignored => eq) (1 : String)",
    ] {
        refuse(source);
    }
}
#[test]
fn proof_constructor_equalities_do_not_expose_existential_data() {
    refuse(
        "inductive Witness (A : Type) : Prop where\n  | intro (a : A)\n theorem invalid (a b : Nat) (h : Witness.intro a = Witness.intro b) : a = b := by injection h with eq; exact eq",
    );
    refuse(
        "inductive Either (P Q : Prop) : Prop where\n  | left (p : P)\n  | right (q : Q)\n theorem invalid (P Q : Prop) (p : P) (q : Q) (h : Either.left p = Either.right q) : 0 = 1 := by injection h",
    );
}
