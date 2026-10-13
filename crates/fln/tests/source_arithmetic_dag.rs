//! Arithmetic DAGs must finish in the real source and dual-checker path.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, Name, SourceCheckLimits};
use fln_env::constants::ConstantInfo;

fn limits() -> SourceCheckLimits {
    let mut admission = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    // Much tighter than the unchanged product default. No wall-clock assertion.
    admission.checker.admission.conversion.nat.max_steps = 20_000;
    admission.checker.admission.conversion.nat.max_work_items = 20_000;
    SourceCheckLimits::new(admission)
}
fn base() -> Engine {
    Engine::with_source_seed(limits().admission)
        .unwrap()
        .into_complete()
        .unwrap()
}
fn source(depth: usize, parameter: bool, expected: &str) -> String {
    let mut text = if parameter {
        String::from("def answer (input : Nat) : Nat :=\n  let n0 : Nat := input\n")
    } else {
        String::from("def answer : Nat :=\n  let n0 : Nat := 1\n")
    };
    for n in 1..=depth {
        text.push_str(&format!(
            "  let n{n} : Nat := Nat.add n{} n{}\n",
            n - 1,
            n - 1
        ));
    }
    let applied = if parameter { "answer 3" } else { "answer" };
    text.push_str(&format!(
        "  n{depth}\ntheorem computes : {applied} = {expected} := by rfl\n"
    ));
    text
}
fn checked(base: &Engine, source: &str) {
    let result = base
        .check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
        .unwrap_or_else(|error| panic!("{error:?}"))
        .into_complete()
        .expect("both checkers must complete");
    assert!(matches!(
        result
            .engine
            .environment()
            .find(&Name::from_components(["computes"])),
        Some(ConstantInfo::Thm(_))
    ));
}

#[test]
fn source_doubling_32_finishes_both_checkers_under_tight_arithmetic_budget() {
    checked(&base(), &source(32, false, "4294967296"));
}

#[test]
fn substituted_function_arguments_preserve_shared_arithmetic() {
    checked(&base(), &source(32, true, "12884901888"));
}

#[test]
fn source_doubling_preserves_arbitrary_precision_results() {
    checked(&base(), &source(96, false, "79228162514264337593543950336"));
}

#[test]
fn wrong_arithmetic_is_rejected_without_publication_and_a_fresh_request_recovers() {
    let base = base();
    let options = KVMap::new();
    let original = base.logical_root(&options);
    let wrong = source(32, false, "4294967297");
    let error = base
        .check_source_files(&[wrong.as_bytes()], &options, limits())
        .unwrap_err();
    assert_eq!(
        error.disposition().2,
        1,
        "wrong result is a rejection, not exhaustion: {error:?}"
    );
    assert_eq!(base.logical_root(&options), original);
    assert!(
        !base
            .environment()
            .contains(&Name::from_components(["answer"]))
    );
    checked(&base, &source(32, false, "4294967296"));
    assert_eq!(base.logical_root(&options), original);
}

fn constants_source(depth: usize, expected: &str) -> String {
    let mut text = String::from("def n0 : Nat := 1\n");
    for n in 1..=depth {
        text.push_str(&format!(
            "def n{n} : Nat := Nat.add n{} n{}\n",
            n - 1,
            n - 1
        ));
    }
    text.push_str(&format!(
        "theorem computes : n{depth} = {expected} := by rfl\n"
    ));
    text
}

#[test]
fn shared_source_definition_graphs_finish_both_checkers() {
    let input = include_str!("../../fln-parse/tests/fixtures/shared_definition_graph.lean");
    assert_eq!(input, constants_source(32, "4294967296"));
    checked(&base(), input);
}

#[test]
fn shared_definitions_still_reject_wrong_results_without_a_successor() {
    let base = base();
    let options = KVMap::new();
    let original = base.logical_root(&options);
    let error = base
        .check_source_files(
            &[constants_source(24, "16777217").as_bytes()],
            &options,
            limits(),
        )
        .unwrap_err();
    assert_eq!(error.disposition().2, 1, "{error:?}");
    assert_eq!(base.logical_root(&options), original);
    assert!(!base.environment().contains(&Name::from_components(["n0"])));
    checked(&base, &constants_source(24, "16777216"));
}
