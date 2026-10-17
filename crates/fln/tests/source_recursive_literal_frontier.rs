//! Ordered literal matrices must remain covered during structural recursion.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, SourceCheckLimits};

fn check(source: &str) {
    let admission = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let engine = Engine::with_source_seed(admission)
        .unwrap()
        .into_complete()
        .unwrap();
    engine
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(admission),
        )
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .unwrap();
}

#[test]
fn recursive_last_column_retains_earlier_literal_fallbacks() {
    check(
        "def foo : Nat -> Nat -> Nat -> Nat\n | _, _, 0 => 1\n | 0, _, _ => 2\n | n, d, k+1 => foo n d k\ntheorem zero : foo 0 9 0 = 1 := by rfl\ntheorem left : foo 0 9 3 = 2 := by rfl\ntheorem right : foo 4 9 3 = 1 := by rfl",
    );
}
#[test]
fn nonrecursive_literal_matrix_control() {
    check(
        "def h : Nat -> Nat -> Nat\n | 0, _ => 0\n | _, 0 => 0\n | a+1, b+1 => a + b\ntheorem right : h 4 5 = 7 := by rfl",
    );
}
#[test]
fn relative_constructor_columns_do_not_invent_unreachable_fallbacks() {
    check(include_str!(
        "../../fln-parse/tests/fixtures/relative_matrix_coverage.lean"
    ));
}

#[test]
fn relative_recursive_splits_keep_literal_priority() {
    check(
        "def pick : Nat -> Nat -> Nat -> Nat\n | _, _, .zero => 1\n | .zero, _, _ => 2\n | n, d, .succ k => pick n d k\ntheorem overlap : pick 0 9 0 = 1 := by rfl\ntheorem fallback : pick 0 9 4 = 2 := by rfl\ntheorem recursion : pick 3 9 4 = 1 := by rfl",
    );
}

#[test]
fn relative_field_patterns_work_below_written_lambdas() {
    check(
        "inductive Tag where | one (n : Nat) | two (n : Nat)\ndef code : Tag -> Nat -> Nat := fun t n => match t, n with\n | _, 0 => 10\n | .one a, .succ k => a + k\n | .two b, .succ k => b + k + 20\ntheorem first : code (Tag.one 8) 0 = 10 := by rfl\ntheorem one : code (Tag.one 8) 3 = 10 := by rfl\ntheorem two : code (Tag.two 8) 3 = 30 := by rfl",
    );
}

#[test]
fn nested_relative_columns_preserve_their_own_family_and_bindings() {
    check(
        "inductive Tag where | left | right\ninductive Box where | pack (tag : Tag) | empty\ndef code (b : Box) (n : Nat) : Nat := match b, n with\n | _, 0 => 10\n | .empty, .succ k => k + 20\n | .pack .left, .succ k => k + 30\n | .pack .right, .succ k => k + 40\ntheorem empty : code Box.empty 4 = 23 := by rfl\ntheorem left : code (Box.pack Tag.left) 4 = 33 := by rfl\ntheorem right : code (Box.pack Tag.right) 4 = 43 := by rfl\ntheorem zero : code (Box.pack Tag.right) 0 = 10 := by rfl",
    );
}

#[test]
fn relative_coverage_uses_the_typed_subject_not_namespace_spelling() {
    check(
        "inductive Tag where | left | right\nnamespace Shadow\ninductive Tag where | left | right | other\ndef code (t : _root_.Tag) (n : Nat) : Nat := match t, n with\n | _, 0 => 10\n | .left, .succ k => k + 20\n | .right, .succ k => k + 30\ntheorem right : code _root_.Tag.right 4 = 33 := by rfl\nend Shadow",
    );
}

fn reject(source: &str) {
    let admission = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let base = Engine::with_source_seed(admission)
        .unwrap()
        .into_complete()
        .unwrap();
    let options = KVMap::new();
    let before = base.logical_root(&options);
    let error = base
        .check_source_files(
            &[source.as_bytes()],
            &options,
            SourceCheckLimits::new(admission),
        )
        .unwrap_err();
    assert!(
        !format!("{error:?}").contains("Frontend(Parse("),
        "negative control did not parse: {source}\n{error:?}"
    );
    assert_eq!(
        error.disposition().2,
        1,
        "missing coverage must refuse, not exhaust: {error:?}"
    );
    assert_eq!(base.logical_root(&options), before);
    base.check_source_files(
        &[b"theorem recovery (n : Nat) : n = n := by rfl"],
        &options,
        SourceCheckLimits::new(admission),
    )
    .unwrap()
    .into_complete()
    .unwrap();
}

#[test]
fn reachable_literal_misses_still_refuse_even_for_closed_inputs() {
    for source in [
        "def bad (n : Nat) : Nat := match n with | 0 => 1",
        "def bad : Nat := match 0 with | 0 => 1",
        "inductive Tag where | left | right | other\ndef bad (t : Tag) (n : Nat) : Nat := match t, n with | _, 0 => 10 | .left, .succ k => k | .right, .succ k => k",
        "inductive Tag where | left | right\ndef bad (t : Tag) (n : Nat) : Nat := match t, n with | .left, 0 => 10 | .right, _ => 20",
    ] {
        reject(source);
    }
}

#[test]
fn deferred_coverage_does_not_hide_bad_types_foreign_heads_or_redundant_rows() {
    for source in [
        "inductive Tag where | left | right\ndef bad (t : Tag) (n : Nat) : Nat := match t, n with | _, 0 => let discarded := (1 : String); 10 | .left, .succ k => k | .right, .succ k => k",
        "inductive Tag where | left | right\ndef bad (t : Tag) (n : Nat) : Nat := match t, n with | .left, _ => 10 | .right, _ => 20 | _, 0 => 30",
        "inductive Tag where | left | right\ninductive Other where | left | right\ndef bad (t : Tag) (n : Nat) : Nat := match t, n with | _, 0 => 10 | .left, .succ k => k | Other.right, .succ k => k",
        "inductive Tag where | left | right\ndef bad (t : Tag) (n : Nat) : Nat := match t, n with | _, 0 => 10 | .left, .succ k => (k : String) | .right, .succ k => k",
        "def bad : Nat -> Nat -> Nat -> Nat | _, _, .zero => 1 | .zero, _, _ => 2 | n, d, .succ k => bad n d (.succ k)",
    ] {
        reject(source);
    }
}

#[test]
fn relative_matrix_results_execute_after_both_checkers_admit() {
    use fln::{EngineExecutionLimits, SourceCommandOutput, VmExit};
    let limits = EngineExecutionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let base = Engine::with_source_seed(limits.admission())
        .unwrap()
        .into_complete()
        .unwrap();
    let source = "inductive Tag where | left | right\ndef code (t : Tag) (n : Nat) : Nat := match t, n with | _, 0 => 10 | .left, .succ k => k + 20 | .right, .succ k => k + 30\n#eval code Tag.left 0\n#eval code Tag.left 4\n#eval code Tag.right 4";
    let result = base
        .execute_source_commands_with_checks(source.as_bytes(), &KVMap::new(), limits)
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(result.outputs.len(), 3);
    for (event, expected) in result.outputs.iter().zip(["10", "23", "33"]) {
        let SourceCommandOutput::Evaluation {
            execution_index, ..
        } = event
        else {
            panic!("expected #eval output")
        };
        let VmExit::Returned(value) = &result.batch.executions[*execution_index].exit else {
            panic!("expected returned value")
        };
        assert_eq!(
            fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
            Some(expected)
        );
    }
}

#[test]
fn missing_literal_cases_fail_inside_their_tactic_alternative() {
    // Coverage is a failure of this candidate, not of an unrelated alternative.
    // Even n = 0 cannot make a non-exhaustive candidate acceptable.
    check(
        "def chosen (n : Nat) : Nat := by first | exact (match n with | 0 => 1) | exact 7\ntheorem zero : chosen 0 = 7 := by rfl\ntheorem other : chosen 5 = 7 := by rfl",
    );
    check(
        "def chosen (n : Nat) : Nat := by first | exact 7 | exact (match n with | 0 => 1)\ntheorem zero : chosen 0 = 7 := by rfl",
    );
}

#[test]
fn a_failed_relative_matrix_alternative_cannot_publish_a_partial_result() {
    check(
        "inductive Tag where | left | right | third\ndef chosen (t : Tag) (n : Nat) : Nat := by\n first\n | exact (match t, n with | _, 0 => 10 | .left, .succ k => k + 20 | .right, .succ k => k + 30)\n | exact 99\ntheorem result : chosen Tag.left 0 = 99 := by rfl\ntheorem other : chosen Tag.third 4 = 99 := by rfl",
    );
}
