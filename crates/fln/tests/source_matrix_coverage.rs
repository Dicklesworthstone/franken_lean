//! Exhaustive matrix branches retain source order and checked recursion.
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

#[test]
fn literal_catchalls_remain_covered_after_selecting_the_structural_column() {
    // The overlap in the pin's tests/elab/29.lean: choosing the third column
    // must not separately compile the unreachable catchall-only matrix [_, 0].
    // Nat results isolate matrix compilation from imported List support.
    check(
        "def foo : Nat -> Nat -> Nat -> Nat
          | _, _, 0 => 1
          | 0, _, _ => 2
          | n, d, k+1 => foo n d k
        theorem overlap : foo 0 7 0 = 1 := by rfl
        theorem fallback : foo 0 7 4 = 2 := by rfl
        theorem base : foo 3 7 0 = 1 := by rfl
        theorem recursiveResult : foo 3 7 4 = 1 := by rfl",
    );
}

#[test]
fn exhaustive_recursive_heads_preserve_rows_at_each_structural_column() {
    check(
        "def firstColumn : Nat -> Nat -> Nat -> Nat
          | 0, _, _ => 1
          | _, 0, d => d
          | k+1, n, d => firstColumn k n d
        def middleColumn : Nat -> Nat -> Nat -> Nat
          | _, 0, _ => 1
          | 0, _, d => d
          | n, k+1, d => middleColumn n k d
        def lastColumn : Nat -> Nat -> Nat -> Nat
          | _, _, 0 => 1
          | 0, d, _ => d
          | n, d, k+1 => lastColumn n d k
        theorem firstOverlap : firstColumn 0 0 9 = 1 := by rfl
        theorem firstFallback : firstColumn 4 0 9 = 9 := by rfl
        theorem firstRecursive : firstColumn 4 3 9 = 1 := by rfl
        theorem middleOverlap : middleColumn 0 0 9 = 1 := by rfl
        theorem middleFallback : middleColumn 0 4 9 = 9 := by rfl
        theorem middleRecursive : middleColumn 3 4 9 = 1 := by rfl
        theorem lastOverlap : lastColumn 0 9 0 = 1 := by rfl
        theorem lastFallback : lastColumn 0 9 4 = 9 := by rfl
        theorem lastRecursive : lastColumn 3 9 4 = 1 := by rfl",
    );
}

#[test]
fn earlier_catchall_rows_keep_priority_in_a_complete_recursive_split() {
    check(
        "def rowPriority : Nat -> Nat -> Nat -> Nat
          | 0, d, _ => d
          | _, _, 0 => 1
          | n, d, k+1 => rowPriority n d k
        theorem overlap : rowPriority 0 9 0 = 9 := by rfl
        theorem fallback : rowPriority 0 9 4 = 9 := by rfl
        theorem recursiveResult : rowPriority 3 9 4 = 1 := by rfl",
    );
}

#[test]
fn complete_recursive_splits_keep_coverage_typing_and_termination_obligations() {
    for source in [
        // A complete outer Nat split does not cover missing inner cases.
        "def bad : Nat -> Nat -> Nat -> Nat | _, _, 0 => 1 | 0, d, k+1 => bad 0 d k",
        // The partial catchall row is live, so its unused terms stay checked.
        "def bad : Nat -> Nat -> Nat -> Nat | _, _, 0 => 1 | 0, _, _ => let unused := (1 : String); 2 | n, d, k+1 => bad n d k",
        // Pruning a dead fallback cannot justify a nondecreasing recursive call.
        "def bad : Nat -> Nat -> Nat -> Nat | _, _, 0 => 1 | 0, _, _ => 2 | n, d, k+1 => bad n d (Nat.succ k)",
        "def bad : Nat -> Nat -> Nat -> Nat | _, _, 0 => 1 | 0, _, _ => 2 | n, d, k+1 => let unused := bad n d (Nat.succ k); 3",
    ] {
        reject(source);
    }
}

#[test]
fn complete_constructor_splits_do_not_compile_unreachable_literal_fallbacks() {
    check(
        "def code (b : Bool) (n : Nat) : Nat := match b, n with
          | Bool.true, 0 => 11
          | Bool.false, _ => 22
          | _, Nat.succ k => k + 33
        theorem trueZero : code true 0 = 11 := by rfl
        theorem trueSucc : code true 4 = 36 := by rfl
        theorem falseZero : code false 0 = 22 := by rfl
        theorem falseSucc : code false 4 = 22 := by rfl",
    );
    check(
        "inductive Tag where | left | right
        def code (t : Tag) (n : Nat) : Nat := match t, n with
          | _, 0 => 10
          | Tag.left, Nat.succ k => k + 20
          | Tag.right, Nat.succ k => k + 30
        theorem leftZero : code Tag.left 0 = 10 := by rfl
        theorem rightZero : code Tag.right 0 = 10 := by rfl
        theorem leftSucc : code Tag.left 4 = 23 := by rfl
        theorem rightSucc : code Tag.right 4 = 33 := by rfl",
    );
}

#[test]
fn constructor_completeness_never_erases_live_missing_or_foreign_cases() {
    for source in [
        "def bad (b : Bool) (n : Nat) : Nat := match b, n with | Bool.true, 0 => 1 | Bool.false, _ => 2",
        // A third constructor keeps the default reachable, including at n = 0.
        "inductive Tag where | left | right | other\ndef bad (t : Tag) (n : Nat) : Nat := match t, n with | Tag.left, _ => 1 | Tag.right, _ => 2 | _, Nat.succ k => k",
        // Equal constructor counts from different families prove nothing.
        "inductive Other where | left | right\ndef bad (b : Bool) (n : Nat) : Nat := match b, n with | Bool.true, 0 => 1 | Other.right, _ => 2 | _, Nat.succ k => k",
        // Even a complete family must be checked against the discriminant.
        "def bad (n : Nat) (m : Nat) : Nat := match n, m with | Bool.true, 0 => 1 | Bool.false, _ => 2 | _, Nat.succ k => k",
        // A source row made redundant by explicit branches keeps its witness.
        "def bad (b : Bool) (n : Nat) : Nat := match b, n with | Bool.true, _ => 1 | Bool.false, _ => 2 | _, 0 => let unused := (1 : String); 3",
    ] {
        reject(source);
    }
}

#[test]
fn recursive_literal_splits_share_coverage_with_relative_successor_patterns() {
    check(
        "def foo : Nat -> Nat -> Nat -> Nat
          | _, _, 0 => 1
          | 0, _, _ => 2
          | n, d, .succ k => foo n d k
        theorem overlap : foo 0 7 0 = 1 := by rfl
        theorem fallback : foo 0 7 4 = 2 := by rfl
        theorem recursiveResult : foo 3 7 4 = 1 := by rfl",
    );
}

#[test]
fn recursive_literal_matrices_execute_after_checked_admission() {
    use fln::{EngineExecutionLimits, VmExit};
    let limits = EngineExecutionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let engine = Engine::with_source_seed(limits.admission())
        .unwrap()
        .into_complete()
        .unwrap();
    let source = "def foo : Nat -> Nat -> Nat -> Nat
        | _, _, 0 => 1
        | 0, d, _ => d
        | n, d, k+1 => foo n d k
      #eval foo 0 9 0
      #eval foo 0 9 4
      #eval foo 3 9 4";
    let output = engine
        .execute_source_commands_with_checks(source.as_bytes(), &KVMap::new(), limits)
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .expect("matrix admission and native execution must complete");
    assert_eq!(output.command_count, 4);
    assert_eq!(output.outputs.len(), 3);
    for (index, (event, expected)) in output.outputs.iter().zip(["1", "9", "1"]).enumerate() {
        let fln::SourceCommandOutput::Evaluation {
            command_index,
            execution_index,
        } = event
        else {
            panic!("every output must come from a written #eval");
        };
        assert_eq!(*command_index, index + 1);
        let execution = &output.batch.executions[*execution_index];
        let VmExit::Returned(value) = &execution.exit else {
            panic!("recursive matrix execution must return");
        };
        assert_eq!(
            fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
            Some(expected)
        );
    }
}

#[test]
fn relative_constructor_siblings_use_an_explicit_family_anchor_in_either_order() {
    for (yes, no) in [("Bool.true", ".false"), (".true", "Bool.false")] {
        check(&format!(
            "def code (b : Bool) (n : Nat) : Nat := match b, n with
              | _, 0 => 10
              | {yes}, Nat.succ k => k + 20
              | {no}, Nat.succ k => k + 30
            theorem trueZero : code true 0 = 10 := by rfl
            theorem falseZero : code false 0 = 10 := by rfl
            theorem trueSucc : code true 4 = 23 := by rfl
            theorem falseSucc : code false 4 = 33 := by rfl"
        ));
    }
}

#[test]
fn relative_coverage_anchors_do_not_capture_namespace_shadowing() {
    check(
        "namespace Shadow
        inductive Bool where | true | false | extra
        def code (b : _root_.Bool) (n : Nat) : Nat := match b, n with
          | _, 0 => 10
          | _root_.Bool.true, Nat.succ k => k + 20
          | .false, Nat.succ k => k + 30
        theorem trueZero : code _root_.Bool.true 0 = 10 := by rfl
        theorem falseZero : code _root_.Bool.false 0 = 10 := by rfl
        theorem trueSucc : code _root_.Bool.true 4 = 23 := by rfl
        theorem falseSucc : code _root_.Bool.false 4 = 33 := by rfl
        end Shadow",
    );
}

#[test]
fn relative_constructor_coverage_does_not_supply_a_discriminant_type() {
    for source in [
        "inductive Other where | true | false\ndef bad (b : Other) (n : Nat) : Nat := match b, n with | _, 0 => 1 | Bool.true, Nat.succ k => 2 | .false, Nat.succ k => 3",
        "inductive Tag where | left | right | other\ndef bad (t : Tag) (n : Nat) : Nat := match t, n with | Tag.left, _ => 1 | .right, _ => 2 | _, Nat.succ k => k",
        "inductive Tag where | left | right | other\ndef bad (t : Tag) (n : Nat) : Nat := match t, n with | .left, _ => 1 | .right, _ => 2 | _, Nat.succ k => k",
        "def bad (b : Bool) (n : Nat) : Nat := match b, n with | _, 0 => 1 | Bool.true, Nat.succ k => 2 | .missing, Nat.succ k => 3",
    ] {
        reject(source);
    }
}
