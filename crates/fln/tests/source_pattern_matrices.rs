//! Real source pattern matrices must produce fully checked recursor terms.
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
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .unwrap();
}
fn reject(source: &str) {
    let engine = engine();
    let before = engine.logical_root(&KVMap::new());
    let result = engine.check_source_files(
        &[source.as_bytes()],
        &KVMap::new(),
        SourceCheckLimits::new(limits()),
    );
    assert!(result.is_err(), "invalid matrix accepted: {source}");
    assert_eq!(engine.logical_root(&KVMap::new()), before);
}
const MAYBE: &str = "inductive Maybe (A : Type) where | none | some (value : A)\n";
#[test]
fn two_discriminants_have_exhaustive_constructor_coverage() {
    check(
        "def code (a b : Bool) : Nat := match a, b with
      | true, true => 11
      | true, false => 12
      | false, true => 21
      | false, false => 22
    theorem tt : code true true = 11 := by rfl
    theorem tf : code true false = 12 := by rfl
    theorem ft : code false true = 21 := by rfl
    theorem ff : code false false = 22 := by rfl",
    );
}
#[test]
fn nested_constructor_rows_share_the_outer_discriminant() {
    check(&format!(
        "{MAYBE}
      def flatten (m : Maybe (Maybe Nat)) : Nat := match m with
      | .none => 1
      | .some .none => 2
      | .some (.some x) => x
      theorem outer : flatten Maybe.none = 1 := by rfl
      theorem inner : flatten (Maybe.some Maybe.none) = 2 := by rfl
      theorem value : flatten (Maybe.some (Maybe.some 37)) = 37 := by rfl"
    ));
}
#[test]
fn overlapping_wildcards_follow_source_priority() {
    check(
        "def code (a b : Bool) : Nat := match a, b with
      | true, _ => 1
      | _, true => 2
      | _, _ => 3
    theorem tt : code true true = 1 := by rfl
    theorem ft : code false true = 2 := by rfl
    theorem ff : code false false = 3 := by rfl",
    );
}
#[test]
fn variable_columns_bind_values_without_erasing_discriminants() {
    check(
        "def copy (n : Nat) (b : Bool) : Nat := match n, b with
      | x, true => x
      | y, false => y + 1
    theorem yes : copy 7 true = 7 := by rfl
    theorem no : copy 7 false = 8 := by rfl",
    );
    reject("def bad : Nat := match (1 : String), true with | _, _ => 7");
    reject("def bad : Nat := match true, (1 : String) with | _, _ => 7");
}
#[test]
fn redundancy_and_missing_cases_do_not_hide_invalid_rows() {
    reject("def bad (a b : Bool) : Nat := match a, b with | true, true => 1 | false, _ => 2");
    reject(
        "def bad (a b : Bool) : Nat := match a, b with | _, _ => 1 | true, false => (1 : String)",
    );
    reject(
        "def bad (a b : Bool) : Nat := match a, b with | true, _ => 1 | false, _ => 2 | _, _ => (1 : String)",
    );
    reject("def bad (a b : Bool) : Nat := match a, b with | x, x => 1");
}

#[test]
fn row_bindings_are_simultaneous_even_when_names_swap() {
    check(
        "def pick (x y : Nat) : Nat := match x, y with | y, x => x
        theorem swapped : pick 3 7 = 7 := by rfl
        def mix (x y : Nat) (b : Bool) : Nat := match x, y, b with
        | y, x, true => x * 10 + y
        | y, x, false => y * 10 + x
        theorem yes : mix 3 7 true = 73 := by rfl
        theorem no : mix 3 7 false = 37 := by rfl",
    );
}

const VEC: &str = "inductive Vec (A : Type) : Nat -> Type where | nil : Vec A 0 | cons (n : Nat) (head : A) (tail : Vec A n) : Vec A (Nat.succ n)\n";
#[test]
fn nested_fixed_index_patterns_prune_only_proved_impossible_branches() {
    check(&format!(
        "{VEC}
      def second (xs : Vec Nat 2) : Nat := match xs with
      | .cons k x (.cons j y rest) => y
      theorem value : second (Vec.cons 1 7 (Vec.cons 0 9 Vec.nil)) = 9 := by rfl"
    ));
}
#[test]
fn dependent_discriminants_refine_each_others_types() {
    check(&format!(
        "{VEC}
      def sumHeads (n : Nat) (xs ys : Vec Nat n) : Nat := match xs, ys with
      | .nil, .nil => 0
      | .cons k x xt, .cons j y yt => x + y
      theorem nils : sumHeads 0 Vec.nil Vec.nil = 0 := by rfl
      theorem heads : sumHeads 1 (Vec.cons 0 7 Vec.nil) (Vec.cons 0 9 Vec.nil) = 16 := by rfl"
    ));
}
#[test]
fn a_prior_scalar_column_refines_a_later_indexed_column() {
    check(&format!(
        "{VEC}
      def first (n : Nat) (xs : Vec Nat n) : Nat := match n, xs with
      | .zero, .nil => 0
      | .succ k, .cons j x tail => x
      theorem empty : first 0 Vec.nil = 0 := by rfl
      theorem value : first 1 (Vec.cons 0 7 Vec.nil) = 7 := by rfl"
    ));
}
#[test]
fn nested_nonlocal_discriminants_and_function_results_are_checked() {
    check(&format!(
        "{MAYBE}
      def add (m : Maybe Nat) (b : Bool) : Nat -> Nat := match (Maybe.some m), b with
      | .some .none, _ => fun n => n
      | .some (.some x), true => fun n => n + x
      | .some (.some x), false => fun n => x
      | .none, _ => fun n => 0
      theorem yes : add (Maybe.some 7) true 3 = 10 := by rfl
      theorem no : add (Maybe.some 7) false 3 = 7 := by rfl
      theorem none : add Maybe.none true 3 = 3 := by rfl"
    ));
}
#[test]
fn matrix_matches_preserve_local_proofs_and_branch_isolation() {
    check(
        "theorem reflexive (a b : Bool) : a = a := match a, b with
      | true, _ => by
        have h : true = true := rfl
        exact h
      | false, _ => rfl",
    );
    reject(
        "theorem bad (a b : Bool) : 0 = 1 := match a, b with | true, _ => rfl | false, _ => rfl",
    );
    reject(
        "def bad (a b : Bool) : Nat := match a, b with | true, _ => let secret := 7; secret | false, _ => secret",
    );
    reject(
        "def bad (a b : Bool) : Nat := match a, b with | true, _ => let unused := (1 : String); 0 | false, _ => 1",
    );
}
#[test]
fn recursive_instantiations_are_payloads_not_extra_induction_hypotheses() {
    check(&format!(
        "{MAYBE}
      def nested (m : Maybe (Maybe Nat)) : Nat := match m with
      | .none => 0
      | .some inside => match inside with | .none => 1 | .some n => n
      theorem nested_ok : nested (Maybe.some (Maybe.some 8)) = 8 := by rfl
      theorem cases_ok (m : Maybe (Maybe Nat)) : m = m := by
        cases m with | none => rfl | some inside => rfl"
    ));
    check("inductive Seq (A : Type) where | nil | cons (head : A) (tail : Seq A)
      def count (xs : Seq (Seq Nat)) : Nat := match xs with
      | .nil => 0
      | .cons head tail => Nat.succ (count tail)
      theorem count_ok : count (Seq.cons Seq.nil (Seq.cons (Seq.cons 7 Seq.nil) Seq.nil)) = 2 := by rfl
      theorem same (xs : Seq (Seq Nat)) : xs = xs := by
        induction xs with | nil => rfl | cons head tail ih => rfl");
}
#[test]
fn unselected_nested_branches_cannot_hide_bad_source() {
    reject(&format!(
        "{MAYBE} def bad : Nat := match Maybe.some (Maybe.some 7), true with
       | .some (.some x), _ => x
       | .some .none, _ => (1 : String)
       | .none, _ => 0"
    ));
    reject(&format!(
        "{VEC} def bad (xs : Vec Nat 2) : Nat := match xs with
       | .cons k x (.cons j y rest) => y
       | .nil => (1 : String)"
    ));
}
#[test]
fn proof_family_restrictions_survive_matrix_compilation() {
    reject(
        "inductive Exists (A : Type) (P : A -> Prop) : Prop where | intro (x : A) (h : P x)
      def leak (A : Type) (P : A -> Prop) (h : Exists A P) (b : Bool) : A := match h, b with
      | .intro x evidence, true => x
      | .intro x evidence, false => x",
    );
}

#[test]
fn qualified_and_relative_heads_merge_without_hiding_foreign_families() {
    check(&format!(
        "{MAYBE}
      def code (m : Maybe Bool) (b : Bool) : Nat := match m, b with
      | .none, _ => 0
      | .some true, _ => 1
      | Maybe.some false, _ => 2
      theorem yes : code (Maybe.some true) false = 1 := by rfl
      theorem no : code (Maybe.some false) true = 2 := by rfl"
    ));
    reject(&format!(
        "{MAYBE} inductive Other where | some (b : Bool)
      def bad (m : Maybe Bool) (b : Bool) : Nat := match m, b with
      | .none, _ => 0
      | .some true, _ => 1
      | Other.some false, _ => 2"
    ));
}

#[test]
fn compiled_matrices_retain_each_actual_recursor() {
    use fln::{ConstantInfo, Name};
    use fln_core::expr::ExprNode;
    let checked = engine().check_source_files(&[b"def code (a b : Bool) : Nat := match a, b with | true, _ => 1 | _, true => 2 | _, _ => 3"], &KVMap::new(), SourceCheckLimits::new(limits())).unwrap().into_complete().unwrap();
    let Some(ConstantInfo::Defn(definition)) = checked
        .engine
        .environment()
        .find(&Name::from_components(["code"]))
    else {
        panic!("checked definition");
    };
    let mut pending = vec![&definition.value];
    let mut visited = std::collections::HashSet::new();
    let mut recursors = 0;
    while let Some(expr) = pending.pop() {
        if !visited.insert(expr.allocation_identity()) {
            continue;
        }
        match expr.node() {
            ExprNode::Const { name, .. } if name == &Name::from_components(["Bool", "rec"]) => {
                recursors += 1
            }
            ExprNode::App { f, a } => {
                pending.push(f);
                pending.push(a);
            }
            ExprNode::Lam {
                binder_type, body, ..
            }
            | ExprNode::ForallE {
                binder_type, body, ..
            } => {
                pending.push(binder_type);
                pending.push(body);
            }
            ExprNode::LetE {
                type_, value, body, ..
            } => {
                pending.push(type_);
                pending.push(value);
                pending.push(body);
            }
            ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => pending.push(expr),
            _ => {}
        }
    }
    assert!(
        recursors > 0,
        "the matrix is compiled to real elimination, not evaluated during elaboration"
    );
}
#[test]
fn row_budget_exhaustion_and_failed_files_leave_no_partial_environment() {
    use fln::Outcome;
    let engine = engine();
    let root = engine.logical_root(&KVMap::new());
    let oversized = format!(
        "def bad (a b : Bool) : Nat := match a, b with {}",
        "| _, _ => 0 ".repeat(257)
    );
    let stopped = engine.check_source_files(
        &[oversized.as_bytes()],
        &KVMap::new(),
        SourceCheckLimits::new(limits()),
    );
    assert!(
        matches!(stopped, Err(ref error) if matches!(error.disposition(), ("resource" | "inconclusive", false, 3))),
        "{stopped:?}"
    );
    let prefix = b"def table (a b : Bool) : Nat := match a, b with | true, _ => 1 | _, _ => 2";
    let bad = b"theorem invalid : table false true = 7 := by rfl";
    for valid in [true, false, true] {
        let sources = if valid {
            vec![prefix.as_slice()]
        } else {
            vec![prefix.as_slice(), bad.as_slice()]
        };
        let result =
            engine.check_source_files(&sources, &KVMap::new(), SourceCheckLimits::new(limits()));
        assert_eq!(
            matches!(result, Ok(Outcome::Complete(_))),
            valid,
            "{result:?}"
        );
        assert_eq!(engine.logical_root(&KVMap::new()), root);
    }
}
#[test]
fn supplied_impossible_nested_rows_and_wrong_arity_are_rejected() {
    reject(&format!(
        "{VEC} def bad (xs : Vec Nat 1) (b : Bool) : Nat := match xs, b with
        | .nil, _ => 0
        | .cons k x tail, _ => x"
    ));
    reject(&format!(
        "{MAYBE} def bad (x : Maybe Nat) (b : Bool) : Nat := match x, b with
        | .none, _ => 0 | .some a c, _ => a"
    ));
    reject(&format!(
        "{MAYBE} def bad (x : Maybe Nat) (b : Bool) : Nat := match x, b with
        | .none, _ => 0 | .some (.none), _ => 1"
    ));
}

#[test]
fn global_discriminants_are_retained_once_even_when_named() {
    use fln::{ConstantInfo, Name};
    use fln_core::expr::ExprNode;
    let result = engine().check_source_files(&[b"def flag : Bool := true\ndef table : Nat := match flag, false with | true, _ => 7 | false, _ => 9\ntheorem value : table = 7 := by rfl"], &KVMap::new(), SourceCheckLimits::new(limits())).unwrap().into_complete().unwrap();
    let Some(ConstantInfo::Defn(definition)) = result
        .engine
        .environment()
        .find(&Name::from_components(["table"]))
    else {
        panic!("checked definition");
    };
    let mut nodes = vec![&definition.value];
    let mut uses = 0;
    while let Some(expr) = nodes.pop() {
        match expr.node() {
            ExprNode::Const { name, .. } if name == &Name::from_components(["flag"]) => uses += 1,
            ExprNode::App { f, a } => {
                nodes.push(f);
                nodes.push(a);
            }
            ExprNode::Lam {
                binder_type, body, ..
            }
            | ExprNode::ForallE {
                binder_type, body, ..
            } => {
                nodes.push(binder_type);
                nodes.push(body);
            }
            ExprNode::LetE {
                type_, value, body, ..
            } => {
                nodes.push(type_);
                nodes.push(value);
                nodes.push(body);
            }
            ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => nodes.push(expr),
            _ => {}
        }
    }
    assert_eq!(
        uses, 1,
        "a named nonlocal discriminant must not be duplicated"
    );
}
