//! Local structural recursion goes through ordinary source and dual admission.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, Name, SourceCheckLimits};

fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}
fn engine() -> Engine {
    Engine::with_source_seed(limits())
        .unwrap()
        .into_complete()
        .unwrap()
}
fn checked(base: &Engine, source: &str) -> Engine {
    base.check_source_files(
        &[source.as_bytes()],
        &KVMap::new(),
        SourceCheckLimits::new(limits()),
    )
    .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
    .into_complete()
    .unwrap()
    .engine
}

#[test]
fn local_recursors_capture_outer_values_and_compute_without_global_helpers() {
    let base = engine();
    let result = checked(
        &base,
        "def repeat (base n : Nat) : Nat := let rec loop (k : Nat) : Nat := match k with | .zero => base | .succ j => loop j + 1; loop n\ntheorem computes : repeat 10 5 = 15 := by rfl",
    );
    assert!(
        !result
            .environment()
            .contains(&Name::from_components(["loop"]))
    );
    assert!(
        !result
            .environment()
            .contains(&Name::from_components(["repeat", "loop"]))
    );
    assert!(
        !base
            .environment()
            .contains(&Name::from_components(["repeat"]))
    );
}

#[test]
fn local_recursive_accumulators_vary_and_completed_functions_can_escape() {
    checked(
        &engine(),
        "def mk (base : Nat) : Nat -> Nat := let rec loop (k acc : Nat) : Nat := match k with | .zero => acc | .succ j => loop j (acc + 1); fun n => loop n base\ntheorem computes : mk 30 12 = 42 := by rfl",
    );
}

#[test]
fn local_recursive_names_shadow_outer_locals_and_globals_only_in_the_value() {
    checked(
        &engine(),
        "def f (n : Nat) : Nat := 99\ndef outer (f : Nat -> Nat) : Nat := let rec f (n : Nat) : Nat := match n with | .zero => 0 | .succ k => f k + 1; f 3\ntheorem computes : outer f = 3 := by rfl\ntheorem restored : f 3 = 99 := by rfl",
    );
}

#[test]
fn captured_functions_and_implicit_local_parameters_preserve_scope() {
    checked(
        &engine(),
        "def repeat {A : Type} (step : A -> A) (seed : A) (n : Nat) : A := let rec loop {B : Type} (f : B -> B) (zero : B) (k : Nat) : B := match k with | .zero => zero | .succ j => f (loop f zero j); loop step seed n\ntheorem computes : repeat (fun n : Nat => n + 2) 1 3 = 7 := by rfl",
    );
}

#[test]
fn nested_local_recursors_restore_the_enclosing_recursion_state() {
    checked(
        &engine(),
        "def outer (n : Nat) : Nat := let rec loop (k : Nat) : Nat := match k with | .zero => 0 | .succ j => let rec inner (m : Nat) : Nat := match m with | .zero => 1 | .succ q => inner q + 1; loop j + inner 2; loop n\ntheorem computes : outer 4 = 12 := by rfl",
    );
}

#[test]
fn ordinary_let_helpers_and_header_shadowing_do_not_become_recursive() {
    checked(
        &engine(),
        "def outer : Nat := let rec id (id : Nat) : Nat := id; let helper (n : Nat) : Nat := id n; helper 7\ntheorem computes : outer = 7 := by rfl",
    );
}

#[test]
fn local_recursion_can_produce_types_and_proofs() {
    checked(
        &engine(),
        "def ty (n : Nat) : Type := let rec loop (k : Nat) : Type := match k with | .zero => Nat | .succ j => loop j; loop n\ndef value : ty 3 := 7\ntheorem result : value = 7 := by rfl\ntheorem reflexive (n : Nat) : n = n := let rec proof (k : Nat) : k = k := match k with | .zero => by rfl | .succ j => by rfl; proof n",
    );
}

#[test]
fn invalid_recursive_values_are_not_erased_even_when_the_binding_is_unused() {
    let base = engine();
    let root = base.logical_root(&KVMap::new());
    for source in [
        "def bad : Nat := let rec f (n : Nat) : Nat := match n with | .zero => 0 | .succ k => f n; 7",
        "def bad : Nat := let rec f (n : Nat) : Nat := f n; 7",
        "def bad : Nat := let rec f (n : Nat) : Nat := match n with | .zero => true | .succ k => f k; 7",
        "def bad : Nat := let rec f (n : Nat) : Nat := match n with | .zero => 0 | .succ k => let ignore : Nat := f n; f k; 7",
        "theorem bad : 0 = 1 := let rec f (n : Nat) : 0 = 1 := match n with | .zero => by rfl | .succ k => f k; f 1",
    ] {
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
    }
    checked(
        &base,
        "def recovery : Nat := let rec f (n : Nat) : Nat := match n with | .zero => 0 | .succ k => f k + 1; f 3",
    );
}

#[test]
fn structural_selection_retries_the_second_match_column() {
    checked(
        &engine(),
        "def add (x y : Nat) : Nat := let rec go (a b : Nat) : Nat := match a, b with | _, .zero => a | _, .succ k => go a k + 1; go x y\ntheorem computes : add 10 5 = 15 := by rfl",
    );
}

#[test]
fn later_structural_candidates_can_change_earlier_accumulators() {
    checked(
        &engine(),
        "def add (x y : Nat) : Nat := let rec go (a b : Nat) : Nat := match a, b with | _, .zero => a | _, .succ k => go (a + 1) k; go x y\ntheorem computes : add 10 5 = 15 := by rfl",
    );
}

#[test]
fn nonrecursive_local_rec_matches_need_no_decreasing_parameter() {
    checked(
        &engine(),
        "def outer (n : Nat) : Nat := let rec choose (x : Nat) : Nat := match n with | .zero => x | .succ k => x + k; choose 10\ntheorem computes : outer 6 = 15 := by rfl",
    );
}

#[test]
fn nested_candidate_stacks_restore_outer_candidates() {
    checked(
        &engine(),
        "def outer (n : Nat) : Nat := let rec go (a b : Nat) : Nat := match a, b with | _, .zero => a | _, .succ k => let rec inner (x y : Nat) : Nat := match x, y with | _, .zero => x | _, .succ j => inner (x + 1) j; go (inner a 2) k; go 0 n\ntheorem computes : outer 3 = 6 := by rfl",
    );
}

#[test]
fn proof_alternatives_recover_from_failed_recursive_helpers() {
    checked(
        &engine(),
        "def chosen : Nat := by first | exact (let rec loop (n : Nat) : Nat := match n with | .zero => 0 | .succ k => loop n; loop 2) | exact 9\ntheorem computes : chosen = 9 := by rfl",
    );
    checked(
        &engine(),
        "def chosen : Nat := let rec loop (n : Nat) : Nat := match n with\n | .zero => by\n     first | exact missing | exact 0\n | .succ k => loop k + 1; loop 3\ntheorem computes : chosen = 3 := by rfl",
    );
}

#[test]
fn parenthesized_recursive_matrices_keep_candidate_information() {
    checked(
        &engine(),
        "def add (x y : Nat) : Nat := (let rec go (a b : Nat) : Nat := ((match a, b with | _, .zero => a | _, .succ k => go (a + 1) k)); go x y)\ntheorem computes : add 10 5 = 15 := by rfl",
    );
}

#[test]
fn all_failed_candidates_and_failed_continuations_preserve_the_input() {
    let base = engine();
    let root = base.logical_root(&KVMap::new());
    for source in [
        "def bad : Nat := let rec go (a b : Nat) : Nat := match a, b with | .zero, _ => 0 | .succ x, .zero => 0 | .succ x, .succ y => go a b; 0",
        "def bad : Nat := let rec go (a b : Nat) : Nat := match a, b with | _, .zero => a | _, .succ k => let unused : Nat := go a b; go a k; 0",
        "def bad : Nat := let rec go (a b : Nat) : Nat := match a, b with | _, .zero => a | _, .succ k => go a k; missing",
        "def bad : Nat := let rec go (a b : Nat) : Nat := match a, b with | _, .zero => true | _, .succ k => go a k; 0",
    ] {
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
    }
    checked(
        &base,
        "def recovery : Nat := let rec go (a b : Nat) : Nat := match a, b with | _, .zero => a | _, .succ k => go (a + 1) k; go 20 22",
    );
}

#[test]
fn local_candidate_resource_stops_are_not_tactic_success() {
    let base = engine();
    let root = base.logical_root(&KVMap::new());
    let source = "def result : Nat := by first | exact (let rec go (a b : Nat) : Nat := match a, b with | _, .zero => a | _, .succ k => go (a + 1) k; go 20 22) | exact 0";
    let mut low = SourceCheckLimits::new(limits());
    low.admission.kernel = low.admission.kernel.narrowed(0, 32);
    match base.check_source_files(&[source.as_bytes()], &KVMap::new(), low) {
        Ok(fln::Outcome::Inconclusive(_)) => {}
        Err(error) => assert!(
            matches!(error.disposition(), ("resource" | "inconclusive", false, 3)),
            "{error:?}"
        ),
        result => panic!("resource stop swallowed: {result:?}"),
    }
    assert_eq!(base.logical_root(&KVMap::new()), root);
    checked(&base, source);
}

#[test]
fn newline_layout_separates_recursive_values_and_continuations() {
    checked(
        &engine(),
        "def sum (n : Nat) : Nat :=\n  let rec go (acc k : Nat) : Nat :=\n    match acc, k with\n    | _, .zero => acc\n    | _, .succ j => go (acc + 1) j\n  go 10 n\ntheorem computes : sum 5 = 15 := by rfl",
    );
}

#[test]
fn newline_layout_keeps_nested_local_definitions_and_branch_scopes() {
    checked(
        &engine(),
        "def result (n : Nat) : Nat :=\n  let rec go (k : Nat) : Nat :=\n    match k with\n    | .zero => 0\n    | .succ j =>\n      let rec inner (q : Nat) : Nat :=\n        match q with\n        | .zero => 1\n        | .succ r => inner r + 1\n      let amount : Nat := inner 2\n      go j + amount\n  let final : Nat := go n\n  final\ntheorem computes : result 4 = 12 := by rfl",
    );
}

#[test]
fn newline_continuations_preserve_parentheses_and_ordinary_let_scopes() {
    checked(
        &engine(),
        "def result : Nat := (\n  let rec id (n : Nat) : Nat := n\n  let plus (n : Nat) : Nat := n + 2\n  plus (id 40))\ntheorem computes : result = 42 := by rfl",
    );
}

fn execute(source: &str, expected: &str) {
    let result = engine()
        .execute_source_definitions(
            &[source.as_bytes()],
            &KVMap::new(),
            fln::EngineExecutionLimits::new(limits().kernel),
        )
        .unwrap_or_else(|error| panic!("{source}: {error:?}"))
        .into_complete()
        .unwrap();
    let fln::VmExit::Returned(result) = &result.executions.last().unwrap().exit else {
        panic!("recursive program did not return")
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&result.value).as_deref(),
        Some(expected)
    );
}

#[test]
fn recursive_local_programs_execute_on_the_native_vm() {
    execute(
        "def count (base n : Nat) : Nat :=\n  let rec go (acc k : Nat) : Nat :=\n    match acc, k with\n    | _, .zero => acc\n    | _, .succ j => go (acc + 1) j\n  go base n\n#eval count 10 32",
        "42",
    );
    execute(
        "#eval let rec go (k : Nat) : Nat := match k with | .zero => 0 | .succ j => go j + 1; go 42",
        "42",
    );
}

#[test]
fn recursive_local_programs_capture_owned_strings_and_functions() {
    execute(
        "def repeat (suffix : String) (n : Nat) : Nat :=\n  let rec go (k : Nat) : String :=\n    match k with\n    | .zero => suffix\n    | .succ j => go j ++ suffix\n  String.length (go n)\n#eval repeat \"abc\" 3",
        "12",
    );
    execute(
        "def repeat (step : Nat -> Nat) (seed n : Nat) : Nat := let rec go (k : Nat) : Nat := match k with | .zero => seed | .succ j => step (go j); go n\n#eval repeat (fun n : Nat => n + 2) 2 20",
        "42",
    );
}

#[test]
fn local_recursion_eliminates_user_defined_data_with_captured_parameters() {
    checked(
        &engine(),
        "inductive Chain (A : Type) where | nil | cons (head : A) (tail : Chain A)\ndef size {A : Type} (xs : Chain A) : Nat :=\n  let rec go (ys : Chain A) : Nat :=\n    match ys with\n    | .nil => 0\n    | .cons x tail => go tail + 1\n  go xs\ntheorem computes : size (Chain.cons 1 (Chain.cons 2 Chain.nil)) = 2 := by rfl",
    );
}

#[test]
fn local_recursion_retains_access_to_its_enclosing_recursive_definition() {
    checked(
        &engine(),
        "def outside (n : Nat) : Nat := match n with\n| .zero => 0\n| .succ k =>\n  let rec inside (m : Nat) : Nat := match m with\n    | .zero => outside k\n    | .succ j => inside j + 1\n  inside 2\ntheorem computes : outside 3 = 6 := by rfl",
    );
}

#[test]
fn recursive_definition_captures_survive_multiple_local_levels() {
    checked(
        &engine(),
        "def outside (n : Nat) : Nat := match n with | .zero => 0 | .succ k => let rec middle (x : Nat) : Nat := match x with | .zero => outside k | .succ j => let rec inner (y : Nat) : Nat := match y with | .zero => outside k | .succ q => inner q + 1; middle j + inner 1; middle 1\ntheorem computes : outside 3 = 7 := by rfl",
    );
}

#[test]
fn enclosing_recursive_names_keep_namespace_and_lexical_shadowing() {
    checked(
        &engine(),
        "namespace Area\ndef outside (n : Nat) : Nat := match n with | .zero => 0 | .succ k => let rec inside (m : Nat) : Nat := match m with | .zero => Area.outside k | .succ j => inside j + 1; inside 2\ntheorem computes : outside 3 = 6 := by rfl\ndef shadow (n : Nat) : Nat := match n with | .zero => 0 | .succ k => let prior : Nat := shadow k; let rec inside (shadow : Nat -> Nat) (m : Nat) : Nat := match m with | .zero => shadow prior | .succ j => inside shadow j + 1; inside (fun x : Nat => x + 1) 1\ntheorem shadowed : shadow 3 = 6 := by rfl\nend Area",
    );
}

#[test]
fn enclosing_recursive_calls_still_require_structural_descent_inside_helpers() {
    let base = engine();
    let root = base.logical_root(&KVMap::new());
    for source in [
        "def outside (n : Nat) : Nat := match n with | .zero => 0 | .succ k => let rec inside (m : Nat) : Nat := match m with | .zero => outside n | .succ j => inside j + 1; inside 2",
        "def outside (n : Nat) : Nat := match n with | .zero => 0 | .succ k => let rec inside (m : Nat) : Nat := match m with | .zero => let unused : Nat := outside n; outside k | .succ j => inside j + 1; 0",
        "def outside (n : Nat) : Nat := match n with | .zero => 0 | .succ k => let rec inside (m : Nat) : Nat := match m with | .zero => outside | .succ j => inside j; 0",
    ] {
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
    }
    checked(
        &base,
        "def recovery (n : Nat) : Nat := match n with | .zero => 0 | .succ k => let rec inside (m : Nat) : Nat := match m with | .zero => recovery k | .succ j => inside j + 1; inside 2\ntheorem computes : recovery 3 = 6 := by rfl",
    );
}
