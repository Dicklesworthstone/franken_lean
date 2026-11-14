//! The shared fixture observes progress and exact residual goals, not merely definitional
//! equality at final admission. Run identical bytes against the pinned Lean when available.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, Name, SourceCheckLimits};
use std::path::PathBuf;
use std::process::Command;

fn limits() -> SourceCheckLimits {
    SourceCheckLimits::new(EngineAdmissionLimits::new(Budget::for_stack_bytes(
        2 * 1024 * 1024,
    )))
}

fn reference() -> Option<PathBuf> {
    let path = std::env::var_os("FLN_REFERENCE_BIN")
        .or_else(|| std::env::var_os("FLN_REFERENCE_LEAN"))
        .map(PathBuf::from)
        .or_else(|| {
            let lib = PathBuf::from(std::env::var_os("FLN_REFERENCE_LIB")?);
            Some(lib.parent()?.parent()?.join("bin/lean"))
        })
        .filter(|path| path.is_file());
    assert!(
        path.is_some() || std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
        "the pinned Reference is required"
    );
    if let Some(path) = &path {
        let result = Command::new(path).arg("--version").output().unwrap();
        let version = String::from_utf8(result.stdout).unwrap();
        let pin = include_str!("../../../SUITE.lock")
            .lines()
            .find(|line| line.starts_with("reference leanprover/lean4 "))
            .unwrap();
        let field = |prefix: &str| {
            pin.split_whitespace()
                .find_map(|word| word.strip_prefix(prefix))
                .unwrap()
        };
        assert!(
            result.status.success()
                && version.contains(field("tag=").trim_start_matches('v'))
                && version.contains(field("commit=")),
            "wrong Reference: {version}"
        );
    }
    path
}

fn semantic_rejection(error: &fln::SourceCheckError) -> bool {
    use fln::{EngineExecutionError, NatDefinitionFrontendError, SourceCheckError};
    use fln_elab::NatDefinitionElabError;
    use fln_elab::source::{SourceInferenceError, TacticError};
    if !matches!(error.disposition().0, "elaboration" | "kernel-rejection") {
        return false;
    }
    let SourceCheckError::Command { error, .. } = error else {
        return false;
    };
    let mut error = error.as_ref();
    while let EngineExecutionError::BatchCommand { error: inner, .. } = error {
        error = inner;
    }
    matches!(
        error,
        EngineExecutionError::KernelRejected { .. }
            | EngineExecutionError::Frontend(NatDefinitionFrontendError::Elaborate(
                NatDefinitionElabError::Inference(SourceInferenceError::Tactic(
                    TacticError::SimplificationNoProgress
                        | TacticError::NoMatchingAssumption
                        | TacticError::UnsolvedGoals { .. }
                        | TacticError::FailIfSuccessSucceeded
                ))
            ))
    )
}

#[test]
fn automatic_unfolding_matches_the_pin_without_guessing_discriminants() {
    let base = Engine::with_source_seed(limits().admission)
        .unwrap()
        .into_complete()
        .unwrap();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    let reference = reference();
    let directory = std::env::temp_dir().join(format!("fln-simp-auto-{}", std::process::id()));
    if reference.is_some() {
        std::fs::create_dir_all(&directory).unwrap();
    }
    let mut pieces = include_str!("source_simp_auto_unfold.lean").split("-- CASE ");
    let preamble = pieces.next().unwrap();
    let mut failures = Vec::new();
    let mut count = 0;
    for piece in pieces {
        let (header, body) = piece.split_once('\n').unwrap();
        let (name, verdict) = header.split_once(' ').unwrap();
        assert!(matches!(verdict, "accept" | "reject"));
        let source = format!("{preamble}\n{body}");
        let expected = verdict == "accept";
        if let Some(reference) = &reference {
            let path = directory.join(format!("{name}.lean"));
            std::fs::write(&path, &source).unwrap();
            let output = Command::new(reference).arg(path).output().unwrap();
            assert_eq!(
                output.status.code(),
                Some(if expected { 0 } else { 1 }),
                "Reference {name}: {}{}",
                String::from_utf8_lossy(&output.stdout),
                String::from_utf8_lossy(&output.stderr)
            );
        }
        match base.check_source_files(&[source.as_bytes()], &options, limits()) {
            Ok(result) if expected => match result.into_complete() {
                Ok(result) => assert!(
                    result
                        .engine
                        .environment()
                        .contains(&Name::from_components(["t"])),
                    "{name}"
                ),
                Err(outcome) => {
                    failures.push(format!("{name}: inconclusive admission: {outcome:?}"))
                }
            },
            Err(error) if !expected && semantic_rejection(&error) => {}
            Err(error) => failures.push(format!("{name}: {error:?}")),
            Ok(_) => failures.push(format!("{name}: unexpectedly admitted")),
        }
        assert_eq!(
            base.logical_root(&options),
            root,
            "{name}: changed input engine"
        );
        count += 1;
    }
    assert_eq!(count, 35, "shared fixture inventory");
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

/// A match-like helper name is not imported matcher metadata. These user-authored lookalikes
/// deliberately exercise that ambiguous boundary; this is a capability test, not a claimed
/// Reference rejection. None of the ordinary backtracking controls may convert it to success.
#[test]
fn missing_matcher_metadata_remains_a_capability_through_backtracking() {
    use fln::{EngineExecutionError, NatDefinitionFrontendError, SourceCheckError};
    use fln_elab::NatDefinitionElabError;
    use fln_elab::source::{SourceInferenceError, TacticError};

    const DEFINITIONS: &str = "\
def candidate.match_1 (b : Bool) (x y : Nat) : Nat :=
  match b with
  | true => x
  | false => y
def candidate (b : Bool) (x y : Nat) : Nat := candidate.match_1 b x y
";
    let base = Engine::with_source_seed(limits().admission)
        .unwrap()
        .into_complete()
        .unwrap();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    for body in [
        "dsimp! only []",
        "fail_if_success dsimp! only []\n  exact h",
        "first | dsimp! only [] | exact h",
        "try dsimp! only []\n  exact h",
    ] {
        let source = format!(
            "{DEFINITIONS}theorem t (P : Nat → Prop) (x y : Nat) \
             (h : P (candidate true x y)) : P (candidate true x y) := by\n  {body}\n"
        );
        let error = base
            .check_source_files(&[source.as_bytes()], &options, limits())
            .expect_err("missing matcher metadata must not become tactic success");
        assert_eq!(
            error.disposition(),
            ("capability", false, 5),
            "{body}: {error:?}"
        );
        assert!(
            !semantic_rejection(&error),
            "{body}: capability is not a verdict"
        );
        let SourceCheckError::Command { error, .. } = &error else {
            panic!("{body}: {error:?}");
        };
        let mut cause = error.as_ref();
        while let EngineExecutionError::BatchCommand { error, .. } = cause {
            cause = error;
        }
        assert!(
            matches!(
                cause,
                EngineExecutionError::Frontend(NatDefinitionFrontendError::Elaborate(
                    NatDefinitionElabError::Inference(SourceInferenceError::Tactic(
                        TacticError::SimprocUnsupported(
                            "automatic unfolding without imported matcher metadata"
                        )
                    ))
                ))
            ),
            "{body}: {cause:?}"
        );
        assert_eq!(
            base.logical_root(&options),
            root,
            "{body}: changed input engine"
        );
    }

    // A partial application cannot select a match at the pin and needs no matcher metadata.
    let body = "fail_if_success dsimp! only []\n  exact h";
    let source = format!(
        "{DEFINITIONS}theorem t (P : (Nat → Nat) → Prop) (x : Nat) \
         (h : P (candidate true x)) : P (candidate true x) := by\n  {body}\n"
    );
    let admitted = base
        .check_source_files(&[source.as_bytes()], &options, limits())
        .unwrap()
        .into_complete()
        .unwrap();
    assert!(
        admitted
            .engine
            .environment()
            .contains(&Name::from_components(["t"]))
    );
    assert_eq!(base.logical_root(&options), root);
}
