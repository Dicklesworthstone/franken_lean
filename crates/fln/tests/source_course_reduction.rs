//! Rebuilt reduction demands must retain ordinary checked proof computation.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, SourceCheckLimits};
use std::{
    path::PathBuf,
    process::Command,
    sync::{
        OnceLock,
        atomic::{AtomicUsize, Ordering},
    },
};

const FIB: &str = "def fib : Nat -> Nat\n | 0 => 0\n | 1 => 1\n | n+2 => fib n + fib (n+1)\ntermination_by structural n => n\n";
fn limits() -> SourceCheckLimits {
    SourceCheckLimits::new(EngineAdmissionLimits::new(Budget::for_stack_bytes(
        8 * 1024 * 1024,
    )))
}
fn engine() -> Engine {
    static BASE: OnceLock<Engine> = OnceLock::new();
    BASE.get_or_init(|| {
        Engine::with_source_seed(limits().admission)
            .unwrap()
            .into_complete()
            .unwrap()
    })
    .clone()
}
fn checked(source: &str) -> fln::SourceFileCheck {
    let base = engine();
    let root = base.logical_root(&KVMap::new());
    let result = base
        .check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .unwrap();
    assert!(result.theorems > 0);
    assert_eq!(base.logical_root(&KVMap::new()), root);
    reference(source, true);
    result
}
fn reference(source: &str, accepted: bool) {
    static PIN: OnceLock<Option<PathBuf>> = OnceLock::new();
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    let pin = PIN.get_or_init(|| {
        let row = include_str!("../../../SUITE.lock")
            .lines()
            .find(|line| line.starts_with("reference leanprover/lean4 "))
            .unwrap();
        let field = |key: &str| {
            row.split_whitespace()
                .find_map(|value| value.strip_prefix(key))
                .unwrap()
        };
        let library = std::env::var_os("FLN_REFERENCE_LIB")
            .map(PathBuf::from)
            .or_else(|| {
                std::env::var_os("HOME").map(|home| {
                    PathBuf::from(home)
                        .join(".elan/toolchains")
                        .join(format!("leanprover--lean4---{}", field("tag=")))
                        .join("lib/lean")
                })
            });
        let pin = library
            .and_then(|path| Some(path.parent()?.parent()?.join("bin/lean")))
            .filter(|path| path.is_file());
        if let Some(pin) = &pin {
            let result = Command::new(pin).arg("--version").output().unwrap();
            let version = String::from_utf8(result.stdout).unwrap();
            assert!(
                result.status.success()
                    && version.contains(field("tag=").trim_start_matches('v'))
                    && version.contains(field("commit=")),
                "{version}"
            );
        } else {
            assert!(
                std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
                "pinned Reference required"
            );
            eprintln!("SKIP: proof reduction differential requires the pinned Lean compiler");
        }
        pin
    });
    let Some(pin) = pin else {
        return;
    };
    let directory =
        std::env::temp_dir().join(format!("fln-rebuilt-demands-{}", std::process::id()));
    std::fs::create_dir_all(&directory).unwrap();
    let path = directory.join(format!("{}.lean", NEXT.fetch_add(1, Ordering::Relaxed)));
    std::fs::write(&path, source).unwrap();
    let result = Command::new(pin).arg(path).output().unwrap();
    assert_eq!(
        result.status.success(),
        accepted,
        "{source}\n{}{}",
        String::from_utf8_lossy(&result.stdout),
        String::from_utf8_lossy(&result.stderr)
    );
}

#[test]
fn ordinary_fibonacci_proofs_fit_the_existing_source_budget() {
    checked(&format!("{FIB}theorem ground : fib 10 = 55 := rfl\n"));
}

#[test]
fn fibonacci_decide_proofs_and_unhinted_recursion_remain_computational() {
    checked(&format!(
        "{FIB}theorem ground : fib 12 = 144 := by decide\n"
    ));
    checked(&format!(
        "{}theorem ground : fib 10 = 55 := rfl\n",
        FIB.replace("termination_by structural n => n\n", "")
    ));
}

#[test]
fn generic_equations_and_ground_arithmetic_keep_their_original_meaning() {
    checked(&format!(
        "{FIB}theorem step (n : Nat) : fib (n+2) = fib n + fib (n+1) := rfl\ntheorem repeated : fib 10 + fib 10 = 110 := rfl\ndef half : Nat -> Nat\n | 0 => 0\n | 1 => 0\n | n+2 => half n + 1\ntheorem half_step (n : Nat) : half (n+2) = half n + 1 := rfl\ntheorem half_ground : half 20 = 10 := by decide\n"
    ));
}

#[test]
fn false_ground_proofs_refuse_without_publishing_a_checked_prefix() {
    let base = engine();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    for proof in ["rfl", "by decide"] {
        let source = format!(
            "{FIB}theorem good : fib 10 = 55 := rfl\ntheorem wrong : fib 5 = 6 := {proof}\n"
        );
        let error = base
            .check_source_files(&[source.as_bytes()], &options, limits())
            .unwrap_err();
        assert_eq!(error.disposition(), ("elaboration", false, 1), "{error:?}");
        assert_eq!(base.logical_root(&options), root);
        reference(&source, false);
    }
    let good = format!("{FIB}theorem good : fib 10 = 55 := rfl\n");
    let first = checked(&good);
    let second = checked(&good);
    assert_eq!(first.result_logical_root, second.result_logical_root);
}

#[test]
fn resource_stops_remain_nonanswers_and_clean_retries_are_deterministic() {
    let base = engine();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    let source = format!("{FIB}theorem good : fib 10 = 55 := rfl\n");
    for allowance in [0, 1, 32] {
        let mut low = limits();
        low.admission.kernel = low.admission.kernel.narrowed(allowance, 32);
        match base.check_source_files(&[source.as_bytes()], &options, low) {
            Ok(fln::Outcome::Inconclusive(_)) => {}
            Err(error) => assert!(
                matches!(error.disposition(), ("resource" | "inconclusive", false, 3)),
                "{error:?}"
            ),
            other => panic!("expected resource nonanswer, got {other:?}"),
        }
        assert_eq!(base.logical_root(&options), root);
    }
    let first = checked(&source);
    let second = checked(&source);
    assert_eq!(first.result_logical_root, second.result_logical_root);
    assert_eq!(base.logical_root(&options), root);
}

#[test]
fn the_remaining_large_false_comparison_is_never_a_published_proof() {
    let base = engine();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    let source =
        format!("{FIB}theorem good : fib 10 = 55 := rfl\ntheorem wrong : fib 10 = 56 := rfl\n");
    // The larger failed comparison still exceeds the current work limit.
    // Keep that capability boundary explicit, separate from the semantic
    // rejection controls above. Neither outcome may publish the good prefix.
    match base.check_source_files(&[source.as_bytes()], &options, limits()) {
        Ok(fln::Outcome::Inconclusive(_)) => {}
        Err(error) => assert!(
            matches!(
                error.disposition(),
                ("elaboration", false, 1) | ("resource" | "inconclusive", false, 3)
            ),
            "{error:?}"
        ),
        other => panic!("a false equality must not be admitted: {other:?}"),
    }
    assert_eq!(base.logical_root(&options), root);
    reference(&source, false);
}

#[test]
fn convertible_equality_transport_indices_keep_kernel_checked_rfl_proofs() {
    checked(
        r#"
theorem converted (p : 4 = Nat.succ 3) :
 @Eq.rec Nat 4 (fun _ _ => Nat) 23 (Nat.succ 3) p = 23 := rfl
theorem betaConverted (f : Nat -> Nat) (p : f ((fun x : Nat => x) 7) = f 7) :
 @Eq.rec Nat (f ((fun x : Nat => x) 7)) (fun _ _ => Nat) 23 (f 7) p = 23 := rfl
"#,
    );
}

#[test]
fn false_equality_transport_results_cannot_publish_a_valid_prefix() {
    let base = engine();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    let source = r#"
theorem converted (p : 4 = Nat.succ 3) :
 @Eq.rec Nat 4 (fun _ _ => Nat) 23 (Nat.succ 3) p = 23 := rfl
theorem wrong (p : 4 = Nat.succ 3) :
 @Eq.rec Nat 4 (fun _ _ => Nat) 23 (Nat.succ 3) p = 24 := rfl
"#;
    reference(source, false);
    let error = base
        .check_source_files(&[source.as_bytes()], &options, limits())
        .unwrap_err();
    assert_eq!(error.disposition(), ("elaboration", false, 1), "{error:?}");
    assert_eq!(root, base.logical_root(&options));
}
