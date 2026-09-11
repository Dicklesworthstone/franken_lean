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

#[test]
fn contradiction_descends_nested_constructor_equalities() {
    check(
        "theorem impossible (h : Nat.succ (Nat.succ 0) = Nat.succ 0) : 7 = 9 := by contradiction",
    );
    check(
        "inductive Tree where\n  | leaf (n : Nat)\n  | branch (a b : Tree)\n theorem impossible (t : Tree) (h : Tree.branch t (Tree.leaf 7) = Tree.branch t (Tree.branch t t)) : 1 = 0 := by contradiction",
    );
}
#[test]
fn contradictory_huge_literals_use_compact_computation() {
    check(
        "theorem impossible (h : 340282366920938463463374607431768211456 = 340282366920938463463374607431768211455) : 0 = 1 := by contradiction",
    );
    check(
        "def impossible (h : 340282366920938463463374607431768211455 = 340282366920938463463374607431768211456) : Nat := by contradiction",
    );
}
#[test]
fn contradiction_uses_empty_evidence_and_negated_assumptions() {
    check("inductive Void : Prop where\n def impossible (h : Void) : Nat := by contradiction");
    check(
        "inductive Void : Prop where\n theorem impossible (P : Prop) (p : P) (np : P -> Void) : 1 = 0 := by contradiction",
    );
    check(
        "inductive Void : Prop where\n theorem impossible (n : Nat) (h : (n = n) -> Void) : 1 = 0 := by contradiction",
    );
}
#[test]
fn contradiction_can_use_an_injected_equality_against_a_negation() {
    check(
        "inductive Void : Prop where\n theorem impossible (x y : Nat) (h : Nat.succ x = Nat.succ y) (ne : (x = y) -> Void) : 1 = 0 := by contradiction",
    );
}
#[test]
fn consistent_or_proof_irrelevant_contexts_are_not_contradictions() {
    for source in [
        "theorem bad (h : 7 = 7) : 0 = 1 := by contradiction",
        "theorem bad (x y : Nat) (h : Nat.succ x = Nat.succ y) : 0 = 1 := by contradiction",
        "inductive Witness (A : Type) : Prop where\n  | intro (a : A)\n theorem bad (h : Witness.intro 0 = Witness.intro 1) : 0 = 1 := by contradiction",
        "inductive Or (P Q : Prop) : Prop where\n  | left (p : P)\n  | right (q : Q)\n theorem bad (P Q : Prop) (p : P) (q : Q) (h : Or.left p = Or.right q) : 0 = 1 := by contradiction",
    ] {
        refuse(source);
    }
}
#[test]
fn contradiction_keeps_lexical_scopes_and_all_source_obligations() {
    check(
        "theorem contradictionInBranch (b : Bool) (h : true = false) : 0 = 1 := by\n  cases b with\n  | false => contradiction\n  | true => contradiction",
    );
    refuse(
        "theorem bad (h : true = false) : 0 = 1 := let ignored : Nat := (1 : String); by contradiction",
    );
}

#[test]
fn injected_equalities_feed_dependent_substitution() {
    check(
        "theorem transported (A : Type) (P : A -> Prop) (x y : A) (hx : P x) (h : Inhabited.mk x = Inhabited.mk y) : P y := by injection h with same; subst same; exact hx",
    );
}

#[test]
fn dependent_record_payloads_are_injected_through_checked_type_transport() {
    check(
        "structure Package where\n  carrier : Type\n  value : carrier\n theorem values (A : Type) (x y : A) (h : Package.mk A x = Package.mk A y) : x = y := by injection h with types values; exact values",
    );
}
#[test]
fn indexed_recursive_payloads_retain_their_dependent_field_domains() {
    check(
        "inductive Vec (A : Type) : Nat -> Type where\n  | nil : Vec A 0\n  | cons (n : Nat) (head : A) (tail : Vec A n) : Vec A (Nat.succ n)\n theorem tails (A : Type) (n : Nat) (a b : A) (xs ys : Vec A n) (h : Vec.cons n a xs = Vec.cons n b ys) : xs = ys := by injection h with lengths heads tails; exact tails",
    );
}
#[test]
fn dependent_fields_support_other_constructor_fallbacks() {
    check(
        "inductive Package where\n  | none\n  | pack (carrier : Type) (value : carrier)\n theorem values (A : Type) (x y : A) (h : Package.pack A x = Package.pack A y) : x = y := by injection h with types values; exact values",
    );
}

#[test]
fn dependent_payload_equalities_survive_substitution_of_their_type_equation() {
    check(
        "structure Package where\n  carrier : Type\n  value : carrier\n theorem transport (P : forall A : Type, A -> Prop) (A B : Type) (x : A) (y : B) (hx : P A x) (h : Package.mk A x = Package.mk B y) : P B y := by injection h with sameType sameValue; subst sameType; subst sameValue; exact hx",
    );
}
#[test]
fn dependent_field_casts_cannot_equate_unrelated_values_or_erase_obligations() {
    for source in [
        "structure Package where\n  carrier : Type\n  value : carrier\n theorem bad (A : Type) (x y : A) (h : Package.mk A x = Package.mk A y) : 0 = 1 := by injection h with types values; rfl",
        "structure Package where\n  carrier : Type\n  value : carrier\n theorem bad (A : Type) (x y : A) (h : Package.mk A x = Package.mk A y) : x = y := by injection h with types values; exact (fun ignored => values) (0 : String)",
        "structure Package where\n  carrier : Type\n  value : carrier\n theorem bad (h : Package.mk Nat 0 = Package.mk Nat 0) : 0 = 1 := by contradiction",
    ] {
        refuse(source);
    }
}
#[test]
fn contradiction_can_reach_a_dependent_payload_after_checked_cast_reduction() {
    check(
        "structure Package where\n  carrier : Type\n  value : carrier\n theorem impossible (h : Package.mk Nat 0 = Package.mk Nat 1) : 7 = 9 := by contradiction",
    );
}
#[test]
fn proof_fields_of_data_records_remain_typed_during_injection() {
    check(
        "structure Evidence (A : Type) (P : A -> Prop) where\n  value : A\n  witness : P value\n theorem values (A : Type) (P : A -> Prop) (x y : A) (px : P x) (py : P y) (h : Evidence.mk x px = Evidence.mk y py) : x = y := by injection h with same; exact same",
    );
}
