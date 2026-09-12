//! Equation bodies lower through the actual source compiler and both checkers.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, SourceCheckLimits};
fn run(source: &str) -> Result<(), String> {
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
        .map_err(|e| format!("{e:?}"))?
        .into_complete()
        .map(|_| ())
        .map_err(|e| format!("{e:?}"))
}
fn check(source: &str) {
    run(source).unwrap_or_else(|e| panic!("{source}\n{e}"));
}
fn reject(source: &str) {
    assert!(run(source).is_err(), "accepted: {source}");
}
const SEQ: &str = "inductive Seq (A : Type) where | nil | cons (value : A) (tail : Seq A)\n";
const VEC: &str = "inductive Vec (A : Type) : Nat -> Type where | nil : Vec A 0 | cons (n : Nat) (head : A) (tail : Vec A n) : Vec A (Nat.succ n)\n";
#[test]
fn scalar_equations_retain_order_and_simultaneous_bindings() {
    check(
        "def priority : Bool -> Bool -> Nat\n | true, _ => 1\n | _, true => 2\n | _, _ => 3\n\
      theorem a : priority true true = 1 := by rfl\n\
      theorem b : priority false true = 2 := by rfl\n\
      theorem c : priority false false = 3 := by rfl\n\
      def swap : Nat -> Nat -> Nat | y, x => x\n theorem d : swap 3 7 = 7 := by rfl",
    );
}
#[test]
fn recursive_list_equations_compute_and_support_induction() {
    check(&format!("{SEQ}
      def append {{A : Type}} : Seq A -> Seq A -> Seq A
        | .nil, ys => ys
        | .cons x xs, ys => Seq.cons x (append xs ys)
      theorem computed : append (Seq.cons 2 Seq.nil) (Seq.cons 3 Seq.nil) = Seq.cons 2 (Seq.cons 3 Seq.nil) := by rfl
      theorem identity {{A : Type}} (xs : Seq A) : append xs Seq.nil = xs := by
        induction xs with
        | nil => rfl
        | cons x xs ih => simp only [append, ih]"));
}
#[test]
fn dependent_telescope_domains_follow_preceding_arguments() {
    check(
        "def identity : forall A : Type, A -> A | T, value => value\n\
       theorem a : identity Nat 7 = 7 := by rfl\n theorem b : identity Bool true = true := by rfl",
    );
}
#[test]
fn header_parameters_remain_in_scope_and_may_be_shadowed() {
    check(
        "def addTo (n : Nat) : Nat -> Nat | value => n + value\n\
       def shadow (x : Nat) : Nat -> Nat | x => x\n\
       theorem a : addTo 4 5 = 9 := by rfl\n theorem b : shadow 4 5 = 5 := by rfl",
    );
}
#[test]
fn fewer_columns_can_return_functions_and_definition_aliases_unfold() {
    check(
        "def signature : Type := Bool -> Nat\n\
      def choice : signature | true => 4 | false => 8\n\
      def first : Nat -> Nat -> Nat | x => fun y => x\n\
      theorem a : choice false = 8 := by rfl\n theorem b : first 3 9 = 3 := by rfl",
    );
}
#[test]
fn recursive_equations_generalize_accumulators() {
    check(
        "def sum : Nat -> Nat -> Nat\n | .zero, acc => acc\n | .succ k, acc => sum k (acc + k)\n\
      theorem computed : sum 4 7 = 13 := by rfl",
    );
}
#[test]
fn fixed_index_equations_omit_only_provably_impossible_rows() {
    check(&format!(
        "{VEC}
      def tail {{A : Type}} (n : Nat) : Vec A (Nat.succ n) -> Vec A n
        | .cons k x rest => rest
      theorem a : tail 0 (Vec.cons 0 9 Vec.nil) = Vec.nil := by rfl"
    ));
}
#[test]
fn indexed_recursion_rebinds_header_indices() {
    check(&format!(
        "{VEC}
      def copy {{A : Type}} (n : Nat) : Vec A n -> Vec A n
        | .nil => Vec.nil
        | .cons k x rest => Vec.cons k x (copy k rest)
      theorem a : copy 1 (Vec.cons 0 9 Vec.nil) = Vec.cons 0 9 Vec.nil := by rfl"
    ));
}
#[test]
fn nested_equations_and_rhs_matches_preserve_payloads() {
    check(
        "inductive Maybe (A : Type) where | none | some (value : A)\n\
      def flatten : Maybe (Maybe Nat) -> Nat
        | .none => 0
        | .some .none => 1
        | .some (.some value) => match true with
          | true => value
          | false => 0
      theorem a : flatten (Maybe.some (Maybe.some 9)) = 9 := by rfl",
    );
}
#[test]
fn equation_theorems_keep_their_dependent_expected_propositions() {
    check(
        "theorem self : forall b : Bool, b = b\n | true => by rfl\n | false => by\n   have same : false = false := rfl\n   exact same",
    );
}
#[test]
fn equation_return_types_can_depend_on_the_discriminant() {
    check(
        "structure Package where\n carrier : Type\n value : carrier\n\
      def unpack : forall p : Package, p.carrier | .mk A value => value\n\
      def package : Package := { carrier := Nat, value := 8 }\n theorem a : unpack package = 8 := by rfl",
    );
}
#[test]
fn equation_instances_are_registered_only_after_checking() {
    check(
        "class Mark (b : Bool) where\n value : Nat\n instance selected : forall b : Bool, Mark b | true => { value := 7 } | false => { value := 9 }\n\
      def f (b : Bool) : Nat := (selected b).value\n theorem a : f true = 7 := by rfl",
    );
}
#[test]
fn malformed_equations_and_unsolved_headers_are_not_guessed() {
    for source in [
        "def bad | true => 0 | false => 1",
        "def bad : Nat | n => n",
        "def bad : Bool -> Nat | true, false => 0",
        "def bad : Bool -> Bool -> Nat | true, true => 0 | false => 1",
        "def bad : Bool -> Nat | true => 0",
        "def bad : Bool -> Nat | _ => 0 | false => 1",
        "def bad : Nat -> Nat | x => _",
        "def bad : _ | true => 0 | false => 1",
    ] {
        reject(source);
    }
}
#[test]
fn invalid_branch_obligations_and_recursive_calls_cannot_be_erased() {
    for source in [
        "def bad : Bool -> Nat | true => 0 | false => let unused : String := 1; 0",
        "theorem bad : forall b : Bool, 0 = 1 | true => rfl | false => rfl",
        "def bad : Nat -> Nat | .zero => 0 | .succ k => bad (Nat.succ k)",
        "def bad : Nat -> Nat | .zero => 0 | .succ k => let unused := bad (Nat.succ k); 0",
        "def bad : Nat -> Nat | .zero => 0 | .succ k => bad",
    ] {
        reject(source);
    }
}
#[test]
fn no_pattern_names_escape_their_alternative() {
    reject("def bad : Bool -> Nat | true => let secret := 3; secret | false => secret");
    reject("def bad (T : Type) : T -> Nat | x => 0\n def later : Nat := x");
}

#[test]
fn resource_stops_leave_equation_prefixes_unpublished_and_reusable() {
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let engine = Engine::with_source_seed(limits)
        .unwrap()
        .into_complete()
        .unwrap();
    let root = engine.logical_root(&KVMap::new());
    let source = b"def choose : Bool -> Nat | true => 7 | false => 3";
    let mut low = SourceCheckLimits::new(limits);
    low.admission.kernel = low.admission.kernel.narrowed(0, 32);
    match engine.check_source_files(&[source], &KVMap::new(), low) {
        Ok(fln::Outcome::Inconclusive(_)) => {}
        Err(error) => assert!(
            matches!(error.disposition(), ("resource" | "inconclusive", false, 3)),
            "{error:?}"
        ),
        other => panic!("expected resource nonanswer: {other:?}"),
    }
    assert_eq!(engine.logical_root(&KVMap::new()), root);
    engine
        .check_source_files(&[source], &KVMap::new(), SourceCheckLimits::new(limits))
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(engine.logical_root(&KVMap::new()), root);
}

#[test]
fn an_unused_bad_annotation_reaches_the_ordinary_kernel() {
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let engine = Engine::with_source_seed(limits)
        .unwrap()
        .into_complete()
        .unwrap();
    let error = engine
        .check_source_files(
            &[b"def bad : Bool -> Nat | true => 0 | false => let unused : String := 1; 0"],
            &KVMap::new(),
            SourceCheckLimits::new(limits),
        )
        .expect_err("the complete candidate must retain its annotation");
    assert!(
        error.disposition().1,
        "expected authoritative kernel rejection: {error:?}"
    );
}

#[test]
fn catch_all_equations_bind_abstract_values_without_an_inductive_recursion_rule() {
    check(
        "def identity {A : Type} : A -> A | value => value\n\
      def constant {A : Type} : A -> Nat | _ => 7\n\
      theorem a : identity true = true := by rfl\n\
      def natId (n : Nat) : Nat := n\n theorem b : constant natId = 7 := by rfl\n\
      theorem abstract {A : Type} (a : A) : identity a = a := by rfl",
    );
    check(
        "def direct (A : Type) (a : A) : A := match a with | x => x\n\
      theorem kept (A : Type) (a : A) : direct A a = a := by rfl",
    );
    reject("def bad {A : Type} : A -> Nat | x => 0 | y => let unused : String := 1; 0");
}
