//! Ground indexed-history proofs must complete at the ordinary source budget.
//! The pinned compiler is an oracle only, never an implementation fallback.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, Name, SourceCheckLimits};
use std::{
    path::PathBuf,
    process::Command,
    sync::atomic::{AtomicUsize, Ordering},
};

const SOURCE: &str = r#"
inductive CoursePair : Nat -> Nat -> Type where
 | leaf (a b : Nat) : CoursePair a b
 | step (a b : Nat) : CoursePair a b -> CoursePair (Nat.succ a) (Nat.succ b)
def weight (b a : Nat) (xs : CoursePair a b) : Nat := match xs with
 | .leaf x _ => x
 | .step _ _ (.leaf x _) => x
 | .step _ _ (.step x y tail) => weight y x tail
termination_by structural xs
"#;

fn limits() -> SourceCheckLimits {
    SourceCheckLimits::new(EngineAdmissionLimits::new(Budget::for_stack_bytes(
        8 * 1024 * 1024,
    )))
}

fn base() -> Engine {
    Engine::with_source_seed(limits().admission)
        .unwrap()
        .into_complete()
        .unwrap()
        .check_source_files(
            &[b"structure Prod (A : Type u) (B : Type v) where\n fst : A\n snd : B\n"],
            &KVMap::new(),
            limits(),
        )
        .unwrap()
        .into_complete()
        .unwrap()
        .engine
}

fn reference(source: &str, accepted: bool) {
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    let row = include_str!("../../../SUITE.lock")
        .lines()
        .find(|line| line.starts_with("reference leanprover/lean4 "))
        .unwrap();
    let field = |key: &str| {
        row.split_whitespace()
            .find_map(|s| s.strip_prefix(key))
            .unwrap()
    };
    let lib = std::env::var_os("FLN_REFERENCE_LIB")
        .map(PathBuf::from)
        .or_else(|| {
            std::env::var_os("HOME").map(|home| {
                PathBuf::from(home)
                    .join(".elan/toolchains")
                    .join(format!("leanprover--lean4---{}", field("tag=")))
                    .join("lib/lean")
            })
        });
    let pin = lib
        .and_then(|p| Some(p.parent()?.parent()?.join("bin/lean")))
        .filter(|p| p.is_file());
    let Some(pin) = pin else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "pinned Reference required"
        );
        eprintln!("SKIP: pinned Reference compiler is absent");
        return;
    };
    let version = Command::new(&pin).arg("--version").output().unwrap();
    let text = String::from_utf8(version.stdout).unwrap();
    assert!(
        version.status.success()
            && text.contains(field("tag=").trim_start_matches('v'))
            && text.contains(field("commit=")),
        "{text}"
    );
    let directory =
        std::env::temp_dir().join(format!("fln-indexed-conversion-{}", std::process::id()));
    std::fs::create_dir_all(&directory).unwrap();
    let path = directory.join(format!("{}.lean", NEXT.fetch_add(1, Ordering::Relaxed)));
    std::fs::write(&path, source).unwrap();
    let output = Command::new(pin).arg(path).output().unwrap();
    assert_eq!(
        output.status.success(),
        accepted,
        "{source}\n{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

fn checked_source(source: &str) {
    reference(source, true);
    let base = base();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    let first = base
        .check_source_files(&[source.as_bytes()], &options, limits())
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .expect("the actual source proof must finish under unchanged limits");
    assert!(first.theorems > 0);
    let second = base
        .check_source_files(&[source.as_bytes()], &options, limits())
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(first.result_logical_root, second.result_logical_root);
    assert_eq!(base.logical_root(&options), root);
}

#[test]
fn two_index_ground_rfl_finishes_under_the_unchanged_source_budget() {
    checked_source(&format!(
        "{SOURCE}theorem weight_ground : weight 9 5 (.step 4 8 (.step 3 7 (.leaf 3 7))) = 3 := rfl\n"
    ));
}

#[test]
fn incorrect_two_index_result_never_publishes_the_checked_prefix() {
    let base = base();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    let source = format!(
        "{SOURCE}theorem wrong_index : weight 9 5 (.step 4 8 (.step 3 7 (.leaf 3 7))) = 7 := rfl\n"
    );
    reference(&source, false);
    match base.check_source_files(&[source.as_bytes()], &options, limits()) {
        Err(error) => assert!(
            matches!(
                error.disposition().0,
                "elaboration" | "kernel-rejection" | "resource" | "inconclusive"
            ),
            "an internal fault cannot satisfy the negative control: {error:?}"
        ),
        Ok(fln::Outcome::Inconclusive(_)) => {}
        other => panic!("a false result cannot be a published theorem: {other:?}"),
    }
    assert!(
        !base
            .environment()
            .contains(&Name::from_components(["weight"]))
    );
    assert!(
        !base
            .environment()
            .contains(&Name::from_components(["wrong_index"]))
    );
    assert_eq!(base.logical_root(&options), root);
}

#[test]
fn two_index_arithmetic_ground_history_proof_uses_ordinary_source_checking() {
    checked_source(
        r#"
inductive CoursePair : Nat -> Nat -> Type where
 | leaf (a b : Nat) : CoursePair a b
 | step (a b : Nat) : CoursePair a b -> CoursePair (Nat.succ a) (Nat.succ b)
def total (b a : Nat) (xs : CoursePair a b) : Nat := match xs with
 | .leaf x y => x + y
 | .step _ _ (.leaf x y) => x + y + 1
 | .step _ _ (.step x y tail) => total y x tail + 2
termination_by structural xs
theorem total_ground : total 9 5 (.step 4 8 (.step 3 7 (.leaf 3 7))) = 12 := rfl
"#,
    );
}

#[test]
fn stopped_ground_proofs_leave_the_environment_unchanged_and_can_retry() {
    let base = base();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    let source = format!(
        "{SOURCE}theorem weight_ground : weight 9 5 (.step 4 8 (.step 3 7 (.leaf 3 7))) = 3 := rfl\n"
    );
    for allowance in [0, 1, 32] {
        let mut low = limits();
        low.admission.kernel = low.admission.kernel.narrowed(allowance, 32);
        match base.check_source_files(&[source.as_bytes()], &options, low) {
            Ok(fln::Outcome::Inconclusive(_)) => {}
            Err(error) => assert!(
                matches!(error.disposition(), ("resource" | "inconclusive", false, 3)),
                "{error:?}"
            ),
            other => panic!("expected a resource nonanswer: {other:?}"),
        }
        assert_eq!(base.logical_root(&options), root);
    }
    checked_source(&source);
}

#[test]
fn generic_two_index_equations_complete_under_the_ordinary_budget() {
    checked_source(&format!(
        r#"{SOURCE}
theorem weight_step (b a : Nat) (tail : CoursePair a b) :
 weight (Nat.succ (Nat.succ b)) (Nat.succ (Nat.succ a)) (.step (Nat.succ a) (Nat.succ b) (.step a b tail)) = weight b a tail := rfl
"#
    ));
}

#[test]
fn generic_two_index_arithmetic_equations_remain_definitional() {
    checked_source(
        r#"
inductive CoursePair : Nat -> Nat -> Type where
 | leaf (a b : Nat) : CoursePair a b
 | step (a b : Nat) : CoursePair a b -> CoursePair (Nat.succ a) (Nat.succ b)
def total (b a : Nat) (xs : CoursePair a b) : Nat := match xs with
 | .leaf x y => x + y
 | .step _ _ (.leaf x y) => x + y + 1
 | .step _ _ (.step x y tail) => total y x tail + 2
termination_by structural xs
theorem total_step (b a : Nat) (tail : CoursePair a b) :
 total (b+2) (a+2) (.step (a+1) (b+1) (.step a b tail)) = total b a tail + 2 := rfl
"#,
    );
}

#[test]
fn false_generic_equations_cannot_publish_a_valid_definition_prefix() {
    let base = base();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    let text = format!(
        r#"{SOURCE}
theorem wrong_step (b a : Nat) (tail : CoursePair a b) :
 weight (b+2) (a+2) (.step (a+1) (b+1) (.step a b tail)) = weight b a tail + 1 := rfl
"#
    );
    reference(&text, false);
    match base.check_source_files(&[text.as_bytes()], &options, limits()) {
        Err(error) => assert!(
            matches!(
                error.disposition().0,
                "elaboration" | "kernel-rejection" | "resource" | "inconclusive"
            ),
            "{error:?}"
        ),
        Ok(fln::Outcome::Inconclusive(_)) => {}
        other => panic!("false generic proof cannot be admitted: {other:?}"),
    }
    assert_eq!(base.logical_root(&options), root);
    assert!(
        !base
            .environment()
            .contains(&Name::from_components(["weight"]))
    );
    assert!(
        !base
            .environment()
            .contains(&Name::from_components(["wrong_step"]))
    );
}

#[test]
fn generic_proofs_stopped_by_admission_limits_retry_without_publishing() {
    let base = base();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    let source = format!(
        r#"{SOURCE}
theorem weight_step (b a : Nat) (tail : CoursePair a b) :
 weight (b+2) (a+2) (.step (a+1) (b+1) (.step a b tail)) = weight b a tail := rfl
"#
    );
    for allowance in [0, 1, 32] {
        let mut low = limits();
        low.admission.kernel = low.admission.kernel.narrowed(allowance, 32);
        match base.check_source_files(&[source.as_bytes()], &options, low) {
            Ok(fln::Outcome::Inconclusive(_)) => {}
            Err(error) => assert!(
                matches!(error.disposition(), ("resource" | "inconclusive", false, 3)),
                "{error:?}"
            ),
            other => panic!("expected typed resource stop: {other:?}"),
        }
        assert_eq!(base.logical_root(&options), root);
    }
    checked_source(&source);
}
