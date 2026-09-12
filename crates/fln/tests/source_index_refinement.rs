//! Fixed index elimination builds actual equality transports and contradictions.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, SourceCheckLimits};
fn check(source: &str) {
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let engine = Engine::with_source_seed(limits)
        .unwrap()
        .into_complete()
        .unwrap();
    engine
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits),
        )
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .unwrap();
}
const VEC: &str = "inductive Vec (A : Type) : Nat -> Type where | nil : Vec A 0 | cons (n : Nat) (head : A) (tail : Vec A n) : Vec A (Nat.succ n)\n";
#[test]
fn nonempty_vector_head_omits_only_the_impossible_branch() {
    check(&format!(
        "{VEC}\
    def head {{A : Type}} (n : Nat) (xs : Vec A (Nat.succ n)) : A := by\n  cases xs with\n  | cons k x tail => exact x\n\
    theorem head_ok : head 0 (Vec.cons 0 9 Vec.nil) = 9 := by rfl"
    ));
}
#[test]
fn nonempty_vector_tail_refines_its_dependent_result() {
    check(&format!(
        "{VEC}\
    def tail {{A : Type}} (n : Nat) (xs : Vec A (Nat.succ n)) : Vec A n := by\n  cases xs with\n  | cons k x rest => exact rest\n\
    theorem tail_ok : tail 0 (Vec.cons 0 9 Vec.nil) = Vec.nil := by rfl"
    ));
}
#[test]
fn repeated_indices_remain_connected() {
    check(
        "inductive Same : Nat -> Nat -> Type where | mk (k : Nat) : Same k k\n\
    def selected (n : Nat) (x : Same n n) : Nat := by\n  cases x with\n  | mk k => exact k\n\
    theorem selected_ok : selected 7 (Same.mk 7) = 7 := by rfl",
    );
}

#[test]
fn repeated_constructor_fields_keep_their_source_names_after_refinement() {
    check(
        "inductive PairAt : Nat -> Nat -> Type where | mk (a b : Nat) : PairAt a b\n\
    theorem equal_fields (n : Nat) (x : PairAt n n) : n = n := by\n  cases x with\n  | mk a b => exact (rfl : a = b)\n\
    def field_sum (n : Nat) (x : PairAt n n) : Nat := by\n  cases x with\n  | mk a b => exact a + b\n\
    theorem sum_ok : field_sum 7 (PairAt.mk 7 7) = 14 := by rfl",
    );
}

#[test]
fn shared_parameter_index_is_not_generalized_out_of_the_parameter() {
    check(
        "inductive Tagged (tag : Nat) : Nat -> Type where | mk : Tagged tag tag\n\
    def selected (n : Nat) (x : Tagged n n) : Nat := by\n  cases x with\n  | mk => exact n\n\
    theorem selected_ok : selected 7 Tagged.mk = 7 := by rfl",
    );
}

#[test]
fn fixed_dependent_indices_transport_values_and_proof_dependent_hypotheses() {
    check(
        "inductive Witness (A : Type) (P : A -> Type) : forall a : A, P a -> Type where | intro (a : A) (v : P a) : Witness A P a v\n\
    def extract (w : Witness Nat (fun x => Bool) 7 true) : Bool := by\n  cases w with\n  | intro a v => exact v\n\
    theorem extract_ok : extract (Witness.intro 7 true) = true := by rfl\n\
    theorem retain (w : Witness Nat (fun x => Bool) 7 true) (h : w = w) (P : w = w -> Prop) (hp : P h) : P h := by\n  cases w with\n  | intro a v => exact hp",
    );
}

#[test]
fn nested_fixed_cases_refine_the_correct_original_discriminant() {
    check(&format!(
        "{VEC}\
    def second (xs : Vec Nat 2) : Nat := by\n  cases xs with\n  | cons k x rest =>\n    cases rest with\n    | cons j y tail => exact y\n\
    theorem second_ok : second (Vec.cons 1 5 (Vec.cons 0 9 Vec.nil)) = 9 := by rfl"
    ));
}

#[test]
fn dependent_original_values_remain_usable_through_aliases() {
    check(&format!(
        "{VEC}\
    theorem reconstruct {{A : Type}} (n : Nat) (xs : Vec A (Nat.succ n)) : xs = xs := by\n  cases xs with\n  | cons k x tail => exact (rfl : xs = Vec.cons k x tail)\n\
    def from_let (xs : Vec Nat 1) : Nat := let saved := xs; by\n  cases xs with\n  | cons k x rest => exact x\n\
    theorem from_let_ok : from_let (Vec.cons 0 5 Vec.nil) = 5 := by rfl"
    ));
}

#[test]
fn contradictory_repeated_indices_and_bool_tags_need_no_source_branch() {
    check(
        "inductive Diagonal : Nat -> Nat -> Type where | mk (n : Nat) : Diagonal n n\n\
    def impossible (x : Diagonal 0 1) : Nat := by cases x\n\
    inductive TruthTag : Bool -> Type where | tagged : TruthTag true\n\
    def impossible_bool (x : TruthTag false) : Nat := by cases x\n\
    inductive Open : Nat -> Type where\n\
    def impossible_empty (x : Open 7) : Nat := by cases x",
    );
}

#[test]
fn let_indices_and_huge_literals_are_not_unrolled_into_unary_data() {
    check(&format!(
        "{VEC}\
    def let_input : Nat := let n := 1; let xs : Vec Nat n := Vec.cons 0 7 Vec.nil; by\n  cases xs with\n  | cons k x tail => exact x\n\
    theorem let_ok : let_input = 7 := by rfl\n\
    inductive Tag : Nat -> Type where | point : Tag 340282366920938463463374607431768211456\n\
    def huge (x : Tag 340282366920938463463374607431768211457) : Nat := by cases x"
    ));
}

#[test]
fn proof_families_keep_small_elimination_policy() {
    check(
        "inductive Even : Nat -> Prop where | zero : Even 0 | step (n : Nat) (h : Even n) : Even (Nat.succ (Nat.succ n))\n\
    theorem impossible (h : Even 1) : 0 = 1 := by cases h",
    );
}

fn reject(source: &str) {
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let engine = Engine::with_source_seed(limits)
        .unwrap()
        .into_complete()
        .unwrap();
    let root = engine.logical_root(&KVMap::new());
    assert!(
        engine
            .check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits)
            )
            .is_err(),
        "unexpected acceptance:\n{source}"
    );
    assert_eq!(root, engine.logical_root(&KVMap::new()));
}

#[test]
fn incomplete_or_unreachable_supplied_branches_are_not_silently_erased() {
    for suffix in [
        "def wrong (x : Vec Nat 1) : Nat := by cases x with | nil => exact 0",
        "def wrong (x : Vec Nat 1) : Nat := by cases x with | nil => exact (true : Nat) | cons k a tail => exact a",
        "def wrong (x : Vec Nat 1) : Nat := by cases x with | cons k a tail => exact (true : Nat)",
        "def wrong (x : Vec Nat 1) : Nat := by cases x with | cons k a tail => exact missing",
        "theorem wrong (x : Vec Nat 1) : 0 = 1 := by cases x with | cons k a tail => rfl",
    ] {
        reject(&format!("{VEC}{suffix}"));
    }
}

#[test]
fn unknown_equations_do_not_justify_pruning_a_branch() {
    reject(
        "inductive Tag : Nat -> Type where | zero : Tag 0 | one : Tag 1\n\
    def wrong (f : Nat -> Nat) (x : Tag (f 7)) : Nat := by cases x with | zero => exact 0",
    );
    reject(
        "inductive Diagonal : Nat -> Nat -> Type where | mk (n : Nat) : Diagonal n n\n\
    theorem wrong (n : Nat) (x : Diagonal n n) : n = 0 := by cases x with | mk k => rfl",
    );
}

#[test]
fn dependent_fixed_cases_do_not_expose_hidden_induction_hypotheses_or_prop_data() {
    reject(&format!(
        "{VEC}\
    theorem wrong (x : Vec Nat 1) : x = Vec.cons 0 0 Vec.nil := by cases x with | cons k a tail => assumption"
    ));
    reject(
        "inductive EitherAt (A : Type) : Nat -> Prop where | left (a : A) : EitherAt A 0 | right (a : A) : EitherAt A 1\n\
    def extract {A : Type} (h : EitherAt A 0) : A := by cases h with | left a => exact a",
    );
}

#[test]
fn constructor_binders_shadow_reintroduced_original_hypotheses() {
    check(&format!(
        "{VEC}\
    def shadow (xs : Vec Nat 1) (x : xs = xs) : Nat := by\n  cases xs with\n  | cons k x tail => exact x\n\
    theorem shadow_ok : shadow (Vec.cons 0 7 Vec.nil) rfl = 7 := by rfl\n\
    def major_shadow (xs : Vec Nat 1) : Nat := by\n  cases xs with\n  | cons k xs tail => exact xs\n\
    theorem major_ok : major_shadow (Vec.cons 0 9 Vec.nil) = 9 := by rfl"
    ));
}

#[test]
fn failed_refinement_never_publishes_a_file_prefix() {
    use fln::Outcome;
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let engine = Engine::with_source_seed(limits)
        .unwrap()
        .into_complete()
        .unwrap();
    let root = engine.logical_root(&KVMap::new());
    let prefix = format!(
        "{VEC}\
    def head (xs : Vec Nat 1) : Nat := by cases xs with | cons k x tail => exact x"
    );
    let bad =
        "theorem impossible (xs : Vec Nat 1) : 0 = 1 := by cases xs with | cons k x tail => rfl";
    let good = "theorem correct : head (Vec.cons 0 9 Vec.nil) = 9 := by rfl";
    for source in [bad, good, bad, good] {
        let result = engine.check_source_files(
            &[prefix.as_bytes(), source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits),
        );
        assert_eq!(
            matches!(result, Ok(Outcome::Complete(_))),
            source == good,
            "{result:?}"
        );
        assert_eq!(engine.logical_root(&KVMap::new()), root);
    }
}

#[test]
fn unused_invalid_discriminants_remain_checked_obligations() {
    reject(&format!(
        "{VEC}\
    def wrong : Nat := let xs : Vec Nat 1 := (Vec.nil : Vec Nat 1); by\n  cases xs with\n  | cons k x tail => exact 0"
    ));
}
