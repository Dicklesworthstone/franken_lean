//! Explicit structural measures select the actual native recursion parameter.
//! The pinned `TerminationMeasure.elab` treats the measure as a parameter, and
//! its aliases bind only the function's arguments after the declaration colon.
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

fn check(base: &Engine, source: &str) -> Engine {
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
fn pinned_structural_recursion_fixture_computes() {
    // The definition is the positive case in the vendored pinned Reference's
    // tests/elab/terminationByStructurally.lean. The concrete theorem also
    // exercises admission of the generated recursor through both kernels.
    check(
        &engine(),
        "def foo (n : Nat) : Nat := match n with\n\
         | 0 => 0\n| n+1 => foo n\n\
         termination_by structural n\n\
         theorem computes : foo 32 = 0 := by rfl",
    );
}

#[test]
fn hinted_header_parameters_generalize_changing_earlier_arguments() {
    check(
        &engine(),
        "def tally (base n : Nat) : Nat := match n with\n\
         | .zero => base\n| .succ k => tally (base + 1) k\n\
         termination_by structural n\n\
         theorem computes : tally 10 32 = 42 := by rfl",
    );
}

#[test]
fn hint_selects_the_later_matrix_column() {
    check(
        &engine(),
        "def walk (a b : Nat) : Nat := match a, b with\n\
         | _, .zero => a\n| _, .succ k => walk (a + 1) k\n\
         termination_by structural b\n\
         theorem computes : walk 10 32 = 42 := by rfl",
    );
}

#[test]
fn equation_and_lambda_arguments_use_termination_aliases() {
    check(
        &engine(),
        "def fromEquations : Nat -> Nat\n\
         | .zero => 0\n| .succ n => fromEquations n + 1\n\
         termination_by structural n => n\n\
         def fromLambda : Nat -> Nat := fun n => match n with\n\
         | .zero => 0\n| .succ k => fromLambda k + 1\n\
         termination_by structural size => (size : Nat)\n\
         theorem equationsCompute : fromEquations 12 = 12 := by rfl\n\
         theorem lambdaComputes : fromLambda 15 = 15 := by rfl",
    );
}

#[test]
fn aliases_skip_unused_extra_parameters_and_preserve_header_scope() {
    check(
        &engine(),
        "def count (step : Nat) : Nat -> Nat -> Nat := fun acc n => match n with\n\
         | .zero => acc\n| .succ k => count step (acc + step) k\n\
         termination_by structural _ remaining => remaining\n\
         theorem computes : count 2 10 16 = 42 := by rfl",
    );
    check(
        &engine(),
        "def count (n : Nat) : Nat -> Nat := fun acc => match n with\n\
         | .zero => acc\n| .succ k => count k (acc + 1)\n\
         termination_by structural n\n\
         theorem computes : count 32 10 = 42 := by rfl",
    );
}

#[test]
fn local_hints_select_recursion_and_preserve_outer_captures() {
    check(
        &engine(),
        "def localCount (offset n : Nat) : Nat :=\n\
         \x20 let rec go (a k : Nat) : Nat := match a, k with\n\
         \x20   | _, .zero => a\n\
         \x20   | _, .succ j => go (a + 1) j\n\
         \x20 termination_by structural k\n\
         \x20 go offset n\n\
         theorem computes : localCount 10 32 = 42 := by rfl",
    );
    check(
        &engine(),
        "def localLambda (offset n : Nat) : Nat :=\n\
         \x20 let rec go : Nat -> Nat := fun k => match k with\n\
         \x20   | .zero => offset\n\
         \x20   | .succ j => go j + 1\n\
         \x20 termination_by structural size => size\n\
         \x20 go n\n\
         theorem computes : localLambda 10 32 = 42 := by rfl",
    );
}

#[test]
fn where_helpers_use_the_same_structural_hint_path() {
    check(
        &engine(),
        "def fromWhere (offset n : Nat) : Nat := go n where\n\
         \x20 go (k : Nat) : Nat := match k with\n\
         \x20   | .zero => offset\n\
         \x20   | .succ j => go j + 1\n\
         \x20 termination_by structural k\n\
         theorem computes : fromWhere 10 32 = 42 := by rfl",
    );
}

#[test]
fn hints_cannot_succeed_by_selecting_a_different_decreasing_parameter() {
    let base = engine();
    let root = base.logical_root(&KVMap::new());
    for source in [
        "def bad (a b : Nat) : Nat := match a, b with\n| _, .zero => a\n| _, .succ k => bad (a + 1) k\ntermination_by structural a",
        "def bad (a b : Nat) : Nat := match b with\n| .zero => a\n| .succ k => bad a k\ntermination_by structural a",
        "def bad (n : Nat) : Nat := match n with\n| .zero => 0\n| .succ k => bad n\ntermination_by structural n",
        "def bad : Nat :=\n  let rec go (a b : Nat) : Nat := match a, b with\n    | _, .zero => a\n    | _, .succ k => go (a + 1) k\n  termination_by structural a\n  go 10 32",
        "def bad : Nat :=\n  let rec go (n : Nat) : Nat := match n with\n    | .zero => 0\n    | .succ k => go n\n  termination_by structural n\n  42",
    ] {
        assert!(
            base.check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits()),
            )
            .is_err(),
            "{source}"
        );
        assert_eq!(base.logical_root(&KVMap::new()), root);
    }
    check(&base, "def recovered : Nat := 42");
}

#[test]
fn measures_are_checked_terms_in_the_declared_alias_scope() {
    let base = engine();
    let root = base.logical_root(&KVMap::new());
    for measure in ["missing", "n + 0", "(n : Bool)", "let k := n; k", "n => n"] {
        let source = format!(
            "def bad (n : Nat) : Nat := match n with\n| .zero => 0\n| .succ k => bad k + 1\ntermination_by structural {measure}"
        );
        assert!(
            base.check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits()),
            )
            .is_err(),
            "{source}"
        );
        assert_eq!(base.logical_root(&KVMap::new()), root);
    }
    for measure in ["n", "x y => y", "x => n", "(by assumption : Nat)"] {
        let source = format!(
            "def bad : Nat -> Nat := fun n => match n with\n| .zero => 0\n| .succ k => bad k + 1\ntermination_by structural {measure}"
        );
        assert!(
            base.check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits()),
            )
            .is_err(),
            "{source}"
        );
        assert_eq!(base.logical_root(&KVMap::new()), root);
    }
    // An underscore alias is still a local parameter: assumption can pick it
    // out. An unaliased lambda parameter, tested above, is not in that scope.
    check(
        &base,
        "def anonymousAlias : Nat -> Nat := fun n => match n with\n\
         | .zero => 0\n| .succ k => anonymousAlias k + 1\n\
         termination_by structural _ => (by assumption : Nat)",
    );
}

#[test]
fn well_founded_and_decreasing_clauses_are_not_discarded() {
    let base = engine();
    for suffix in [
        "termination_by n",
        "decreasing_by exact Nat.lt_succ_self _",
        "termination_by structural n\ndecreasing_by exact Nat.lt_succ_self _",
    ] {
        let source = format!(
            "def bad (n : Nat) : Nat := match n with\n| .zero => 0\n| .succ k => bad k + 1\n{suffix}"
        );
        assert!(
            base.check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits()),
            )
            .is_err(),
            "{source}"
        );
    }
}

#[test]
fn hinted_global_and_local_recursion_execute_on_the_native_vm() {
    let source = "def count (offset n : Nat) : Nat :=\n\
                  \x20 let rec go (acc k : Nat) : Nat := match acc, k with\n\
                  \x20   | _, .zero => acc\n\
                  \x20   | _, .succ j => go (acc + 1) j\n\
                  \x20 termination_by structural k\n\
                  \x20 go offset n\n\
                  def twice (n : Nat) : Nat := match n with\n\
                  | .zero => 0\n| .succ k => twice k + 2\n\
                  termination_by structural n\n\
                  #eval count (twice 5) 32";
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
        panic!("hinted recursive program did not return")
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&result.value).as_deref(),
        Some("42")
    );
}
