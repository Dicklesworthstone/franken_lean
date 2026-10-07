//! Later argument types unblock earlier higher-order source applications.
#![forbid(unsafe_code)]

use fln::{Budget, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap, SourceCheckLimits};

fn limits() -> SourceCheckLimits {
    SourceCheckLimits::new(EngineAdmissionLimits::new(Budget::for_stack_bytes(
        2 * 1024 * 1024,
    )))
}

fn engine() -> Engine {
    Engine::with_coercion_seed(limits().admission)
        .unwrap()
        .into_complete()
        .unwrap()
}

fn check(base: &Engine, source: &str) -> Engine {
    base.check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .unwrap()
        .engine
}

fn evaluate(source: &str, expected: &str) {
    let result = engine()
        .execute_source_definitions(
            &[source.as_bytes()],
            &KVMap::new(),
            EngineExecutionLimits::new(limits().admission.kernel),
        )
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .unwrap();
    let fln::VmExit::Returned(result) = &result.executions.last().unwrap().exit else {
        panic!("postponed application did not return")
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&result.value).as_deref(),
        Some(expected),
        "{source}"
    );
}

const USE: &str = "def use {A : Type} (run : A -> Nat) (value : A) : Nat := run value";

#[test]
fn later_values_determine_unannotated_callable_parameters() {
    for declaration in [
        "def result : Nat := use (fun f => f 20) (fun n => n + 22)",
        "def result : Nat := use (fun f => f (n := 20)) (fun (n : Nat) => n + 22)",
        "def first {A B : Type} (x : A) (y : B) : A := x\n\
         def result : Nat := use (fun f => first (f 20) true) (fun n => n + 22)",
    ] {
        let source = format!("{USE}\n{declaration}");
        check(
            &engine(),
            &format!("{source}\ntheorem computes : result = 42 := by rfl"),
        );
        evaluate(&format!("{source}\n#eval result"), "42");
    }
}

#[test]
fn successive_arguments_resolve_distinct_blockers() {
    let source = "def use2 {A B : Type} (run : A -> B -> Nat) (a : A) (b : B) : Nat := run a b
      def result : Nat := use2 (fun f g => f 20 + g 21) (fun n => n + 1) (fun n => n)";
    check(
        &engine(),
        &format!("{source}\ntheorem computes : result = 42 := by rfl"),
    );
    evaluate(&format!("{source}\n#eval result"), "42");
}

#[test]
fn nested_arguments_resume_their_containing_lambda() {
    for declaration in [
        "def result : Nat := use (fun f => use (fun g => g 0) f) (fun n => n + 42)",
        "def result : Nat := use (fun f => use (fun g => use (fun h => h 0) g) f) (fun n => n + 42)",
        "def captured (offset : Nat) : Nat :=\n  let saved := offset\n  use (fun f => let added := 2; use (fun g => g saved + added) f) (fun n => n)\ndef result : Nat := captured 40",
    ] {
        let source = format!("{USE}\n{declaration}");
        check(
            &engine(),
            &format!("{source}\ntheorem computes : result = 42 := by rfl"),
        );
        evaluate(&format!("{source}\n#eval result"), "42");
    }
}

#[test]
fn nested_arguments_keep_coercions_and_structural_calls() {
    let source = format!(
        "{USE}
         structure Callable where
           run : Nat -> Nat
         instance callable : CoeFun Callable (fun _ => Nat -> Nat) := CoeFun.mk (fun c => c.run)
         def result : Nat := use (fun f => use (fun g => g 39) f) (Callable.mk (fun n => n + 3))"
    );
    check(
        &engine(),
        &format!("{source}\ntheorem computes : result = 42 := by rfl"),
    );
    evaluate(&format!("{source}\n#eval result"), "42");
    for (body, expected) in [
        ("use (fun f => f (count k)) (fun x => x + 1)", "3"),
        (
            "use (fun f => use (fun g => g (count k)) f) (fun x => x + 1)",
            "3",
        ),
        (
            "by first | exact use (fun f => use (fun g => g (count k)) f) (fun x => x + 1) | exact 0",
            "3",
        ),
        (
            "by first | (exact use (fun f => use (fun g => g (count k)) f) (fun x => x + 1); fail) | exact 7",
            "7",
        ),
    ] {
        let source = format!(
            "{USE}\ndef count (n : Nat) : Nat := match n with
             | 0 => 0
             | Nat.succ k => {body}"
        );
        check(
            &engine(),
            &format!("{source}\ntheorem computes : count 3 = {expected} := by rfl"),
        );
        evaluate(&format!("{source}\n#eval count 3"), expected);
    }
}

#[test]
fn nested_recursion_preserves_candidate_retry_and_explicit_failure() {
    for (declaration, expected) in [
        (
            "def count (n : Nat) : Nat := match n with\n  | 0 => 4\n  | Nat.succ k => by\n      first\n      | (exact use (fun f => use (fun g => g (count n)) f) (fun x => x + 1); fail)\n      | exact count k + 1\ndef result : Nat := count 3",
            "7",
        ),
        (
            "def count (acc n : Nat) : Nat := match n with\n  | 0 => acc\n  | Nat.succ k => use (fun f => use (fun g => g (count (acc + 1) k)) f) (fun x => x)\ndef result : Nat := count 39 3",
            "42",
        ),
        (
            "def result : Nat :=\n  let rec loop (acc n : Nat) : Nat := match n with\n    | 0 => acc\n    | Nat.succ k => use (fun f => use (fun g => g (loop (acc + 1) k)) f) (fun x => x)\n  loop 39 3",
            "42",
        ),
    ] {
        let source = format!("{USE}\n{declaration}");
        check(
            &engine(),
            &format!("{source}\ntheorem computes : result = {expected} := by rfl"),
        );
        evaluate(&format!("{source}\n#eval result"), expected);
    }
}

#[test]
fn nested_suspension_preserves_tactic_choice() {
    for declaration in [
        "def result : Nat := use (fun f => by first | exact use (fun g => g 0) f | exact 0) (fun n => n + 42)",
        "def result : Nat := by first\n\
         | (exact use (fun f => use (fun g => g 0) f) (42 : Nat); fail)\n\
         | exact use (fun f => use (fun g => g 40) f) (fun n => n + 2)",
    ] {
        let source = format!("{USE}\n{declaration}");
        check(
            &engine(),
            &format!("{source}\ntheorem computes : result = 42 := by rfl"),
        );
        evaluate(&format!("{source}\n#eval result"), "42");
    }
    for callback in ["fun f => f result", "fun f => use (fun g => g result) f"] {
        let source = format!(
            "{USE}\ndef result : Nat := by first
             | (exact use ({callback}) (fun (n : Nat) => n); fail)
             | exact 42"
        );
        check(
            &engine(),
            &format!("{source}\ntheorem computes : result = 42 := by rfl"),
        );
        evaluate(&format!("{source}\n#eval result"), "42");
    }
}

#[test]
fn hidden_callback_lists_supply_their_types_after_the_fold_function() {
    let source = "structure Handlers where
      carrier : Type
      value : carrier
      values : List (carrier -> Nat)
    def total (p : Handlers) : Nat :=
      p.values.foldl (fun n f => n + f p.value) 0
    def make (offset : Nat) : Handlers :=
      { carrier := Nat, value := 20, values := [fun n => n + offset, fun n => n] }";
    check(
        &engine(),
        &format!("{source}\ntheorem computes : total (make 2) = 42 := by rfl"),
    );
    evaluate(&format!("{source}\n#eval total (make 2)"), "42");
}

#[test]
fn a_later_bundled_type_selects_its_actual_function_coercion() {
    let source = format!(
        "{USE}
         structure Callable where
           run : Nat -> Nat
         instance callable : CoeFun Callable (fun _ => Nat -> Nat) := CoeFun.mk (fun c => c.run)
         def result : Nat := use (fun f => f 39) (Callable.mk (fun n => n + 3))"
    );
    check(
        &engine(),
        &format!("{source}\ntheorem computes : result = 42 := by rfl"),
    );
    evaluate(&format!("{source}\n#eval result"), "42");
}

#[test]
fn postponed_arguments_preserve_dependent_results_and_captures() {
    check(
        &engine(),
        "def applyProof {A : Sort u} (run : A -> 0 = 0) (value : A) : 0 = 0 := run value
         theorem proof : 0 = 0 := applyProof (fun f => f 0) (fun (n : Nat) => (rfl : n = n))",
    );
    for body in [
        "use (fun f => f offset) (fun n => n + 2)",
        "let captured := offset; use (fun f => f captured) (fun n => n + 2)",
    ] {
        let source = format!("{USE}\ndef result (offset : Nat) : Nat := {body}");
        check(
            &engine(),
            &format!("{source}\ntheorem computes : result 40 = 42 := by rfl"),
        );
        evaluate(&format!("{source}\n#eval result 40"), "42");
    }
    let source = format!(
        "{USE}
         structure Box where
           value : Nat
         instance boxZero : OfNat Box 0 := OfNat.mk (Box.mk 7)
         def result : Nat :=
           let captured := 0
           use (fun f => f captured) (fun (n : Box) => n.value + 35)"
    );
    check(
        &engine(),
        &format!("{source}\ntheorem computes : result = 42 := by rfl"),
    );
    evaluate(&format!("{source}\n#eval result"), "42");
}

#[test]
fn failed_postponed_arguments_restore_the_tactic_alternative() {
    for first_value in ["(fun n => n + 1)", "(42 : Nat)"] {
        let source = format!(
            "{USE}\ndef result : Nat := by first
             | (exact use (fun f => f 0) {first_value}; fail)
             | exact use (fun f => f 40) (fun n => n + 2)"
        );
        check(
            &engine(),
            &format!("{source}\ntheorem computes : result = 42 := by rfl"),
        );
        evaluate(&format!("{source}\n#eval result"), "42");
    }
}

#[test]
fn postponed_work_cannot_turn_resource_stops_into_tactic_success() {
    let base = check(&engine(), USE);
    let root = base.logical_root(&KVMap::new());
    let mut stopped = 0;
    for body in [
        "let captured := 40; use (fun f => f captured) (fun n => n + 2)",
        "let captured := 40; use (fun f => use (fun g => g captured) f) (fun n => n + 2)",
    ] {
        let source = format!(
            "def result : Nat := by first | exact ({body}) | exact 0\n\
             theorem computes : result = 42 := by rfl"
        );
        for steps in [100, 1_000] {
            let mut low = limits();
            low.admission.kernel = low.admission.kernel.narrowed(steps, 256);
            match base.check_source_files(&[source.as_bytes()], &KVMap::new(), low) {
                Ok(fln::Outcome::Inconclusive(_)) => stopped += 1,
                Err(error) => {
                    assert!(
                        matches!(error.disposition(), ("resource" | "inconclusive", false, 3)),
                        "steps={steps}: {error:?}"
                    );
                    stopped += 1;
                }
                Ok(fln::Outcome::Complete(_)) => {}
                result => panic!("resource stop swallowed: {result:?}"),
            }
            assert_eq!(base.logical_root(&KVMap::new()), root);
        }
        check(&base, &source);
    }
    assert!(stopped > 0, "the bounded controls must exhaust work");
}

#[test]
fn unresolved_and_nonfunction_callees_still_refuse_atomically() {
    let base = check(&engine(), USE);
    let root = base.logical_root(&KVMap::new());
    for source in [
        "def bad : Nat := use (fun f => f 0) _",
        "def bad : Nat := use (fun f => f 0) (42 : Nat)",
        "def bad : Nat := use (fun f => f true) (fun (n : Nat) => n)",
        "def bad : Nat := let ignored := use (fun f => f 0) (42 : Nat); 42",
        "def bad : Nat := by first | exact use (fun f => f 0) (42 : Nat) | exact 42",
        "def bad : Nat := use (fun f => use (fun g => g 0) f) _",
        "def bad : Nat := by first | exact use (fun f => use (fun g => g 0) f) (42 : Nat) | exact 42",
        "def bad : Nat := by first | exact use (fun f => use (fun g => g missing) f) (fun (x : Nat) => x) | exact 42",
        "def bad (n : Nat) : Nat := match n with | 0 => 0 | Nat.succ k => use (fun f => use (fun g => g (bad n)) f) (fun x => x + 1)",
        "def bad (n : Nat) : Nat := match n with\n  | 0 => 0\n  | Nat.succ k => by\n      first\n      | exact use (fun f => use (fun g => g (bad n)) f) (fun x => x + 1)\n      | exact 0",
        "def bad : Nat :=\n  let rec loop (n : Nat) : Nat := match n with\n    | 0 => 0\n    | Nat.succ k => by\n        first\n        | exact use (fun f => use (fun g => g (loop n)) f) (fun x => x + 1)\n        | exact 0\n  loop 3",
    ] {
        let error = base
            .check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
            .expect_err(source);
        assert!(
            !format!("{error:?}").contains("Frontend(Parse("),
            "{source}\n{error:?}"
        );
        if source.contains("bad n") || source.contains("loop n") {
            assert!(
                format!("{error:?}").contains("NotDecreasing"),
                "recursive calls must reach their structural check: {source}\n{error:?}"
            );
        }
        assert_eq!(base.logical_root(&KVMap::new()), root);
    }
    check(&base, "def recovered : Nat := 42");
}
