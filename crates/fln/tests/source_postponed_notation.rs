//! Expected-type notation waits for information from later source arguments.
//! The resulting terms pass both checkers and execute through the ordinary VM.
#![forbid(unsafe_code)]

use fln::{Budget, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap, SourceCheckLimits};

const DECLARATIONS: &str = "structure Point where
  x : Nat
  y : Nat
def consume {A : Type} (value : A) (run : A -> Nat) : Nat := run value
def build {A : Type} (make : Nat -> A) (run : A -> Nat) : Nat := run (make 40)
def keep {A : Type} (value witness : A) : A := value
def ignore {A : Type} (value witness : A) : Nat := 42
def get (value : Option Nat) : Nat := match value with
  | .none => 0
  | .some n => n";

fn limits() -> SourceCheckLimits {
    SourceCheckLimits::new(EngineAdmissionLimits::new(Budget::for_stack_bytes(
        2 * 1024 * 1024,
    )))
}

fn engine() -> Engine {
    Engine::with_source_seed(limits().admission)
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

fn evaluates(declaration: &str, expected: &str) {
    let source = format!("{DECLARATIONS}\n{declaration}");
    check(
        &engine(),
        &format!("{source}\ntheorem computes : result = {expected} := by rfl"),
    );
    let source = format!("{source}\n#eval result");
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
        panic!("postponed notation did not return")
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&result.value).as_deref(),
        Some(expected),
        "{source}"
    );
}

#[test]
fn later_arguments_determine_anonymous_constructors_and_dotted_heads() {
    for (declaration, expected) in [
        (
            "def result : Nat := consume ⟨20, 22⟩ (fun (p : Point) => p.x + p.y)",
            "42",
        ),
        ("def result : Nat := consume (.some 42) get", "42"),
        ("def result : Nat := consume .none get", "0"),
        // The result of the expected function type determines `.some`'s namespace.
        ("def result : Nat := build .some get", "40"),
    ] {
        evaluates(declaration, expected);
    }
}

#[test]
fn nested_notation_replays_its_containing_lambda_with_captured_locals() {
    for declaration in [
        "def result : Nat := build (fun n => ⟨n, 2⟩) (fun (p : Point) => p.x + p.y)",
        "def result : Nat := build (fun n => keep ⟨n, 2⟩ ⟨0, 0⟩) (fun (p : Point) => p.x + p.y)",
        "def captured (offset : Nat) : Nat :=\n  let saved := offset\n  build (fun n => let added := 2; keep ⟨n, saved + added⟩ ⟨0, 0⟩) (fun (p : Point) => p.x + p.y)\ndef result : Nat := captured 0",
        "def result : Nat := build (fun n => keep (.some (n + 2)) .none) get",
    ] {
        evaluates(declaration, "42");
    }
}

#[test]
fn suspension_waits_before_selecting_a_tactic_alternative() {
    for (declaration, expected) in [
        (
            "def result : Nat := consume (by first | exact ⟨20, 22⟩ | exact (0 : Nat)) (fun (p : Point) => p.x + p.y)",
            "42",
        ),
        (
            "def result : Nat := build (fun n => by first | exact ⟨n, 2⟩ | exact (0 : Nat)) (fun (p : Point) => p.x + p.y)",
            "42",
        ),
        // Once the argument is replayed with A = Nat, the first branch is an
        // ordinary notation error and `first` can select its second branch.
        (
            "def result : Nat := consume (by first | exact ⟨20, 22⟩ | exact (0 : Nat)) (fun (n : Nat) => n)",
            "0",
        ),
    ] {
        evaluates(declaration, expected);
    }
}

#[test]
fn deferred_errors_keep_the_notations_original_diagnostic() {
    let base = check(&engine(), DECLARATIONS);
    let root = base.logical_root(&KVMap::new());
    for (source, message) in [
        (
            "def bad : Nat := ignore ⟨20, 22⟩ _",
            "The expected type of this term could not be determined",
        ),
        (
            "def bad : Nat := ignore .none _",
            "The expected type of `.none` could not be determined",
        ),
        (
            "def bad : Nat := ignore ⟨20, 22⟩ (0 : Nat)",
            "The expected type has more than one constructor",
        ),
        (
            "def bad : Nat := ignore .some (0 : Nat)",
            "Unknown constant `Nat.some`",
        ),
        (
            "def bad : Nat := build (fun n => keep ⟨n, 2⟩ ⟨0, 0⟩) (fun _ => 0)",
            "The expected type of this term could not be determined",
        ),
    ] {
        let error = base
            .check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
            .expect_err(source);
        assert_eq!(error.disposition().0, "elaboration", "{source}: {error}");
        assert!(error.to_string().contains(message), "{source}: {error}");
        assert_eq!(base.logical_root(&KVMap::new()), root);
    }
    check(&base, "def recovered : Nat := 42");
}

#[test]
fn later_information_cannot_guess_an_unrelated_carrier_or_erase_a_bad_term() {
    let base = check(&engine(), DECLARATIONS);
    let root = base.logical_root(&KVMap::new());
    for source in [
        "def first {A B : Type} (x : A) (y : B) : A := x\ndef bad : Nat := consume (first ⟨20, 22⟩ (Point.mk 0 0)) (fun (n : Nat) => n)",
        "def bad : Nat := consume ⟨true, 22⟩ (fun (p : Point) => p.x + p.y)",
        "def bad : Nat := let discarded := ignore ⟨20, 22⟩ (0 : Nat); 42",
        "def bad : Nat := by first | exact ignore ⟨20, 22⟩ (0 : Nat) | exact 42",
        "def bad : Nat := by first | exact ignore .some (0 : Nat) | exact 42",
    ] {
        let error = base
            .check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
            .expect_err(source);
        assert!(
            !format!("{error:?}").contains("Frontend(Parse("),
            "{source}: {error:?}"
        );
        assert_eq!(base.logical_root(&KVMap::new()), root);
    }
}

#[test]
fn explicit_failure_rolls_back_its_pending_notation_and_diagnostics() {
    for failed in [
        "ignore ⟨1, 2⟩ (0 : Nat)",
        "ignore .some (0 : Nat)",
        "consume ⟨1, 2⟩ (fun (p : Point) => p.x + p.y)",
    ] {
        evaluates(
            &format!(
                "def result : Nat := by first\n | (exact {failed}; fail)\n | exact consume ⟨20, 22⟩ (fun (p : Point) => p.x + p.y)"
            ),
            "42",
        );
    }
}

#[test]
fn postponed_notation_cannot_turn_resource_stops_into_tactic_success() {
    let base = check(&engine(), DECLARATIONS);
    let root = base.logical_root(&KVMap::new());
    let mut stopped = 0;
    for body in [
        "consume ⟨20, 22⟩ (fun (p : Point) => p.x + p.y)",
        "build (fun n => keep (.some (n + 2)) .none) get",
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
