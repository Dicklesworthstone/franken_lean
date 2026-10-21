//! Source structural recursion through the admitted course-of-values dictionary.
//! Every accepted program retains checked proofs, rather than just a declared body.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, SourceCheckLimits};
use fln_core::name::Name;
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
        // The bounded seed has PUnit/PProd but not Prod. The native generator,
        // like the pin, waits for Prod before emitting a new family's below.
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
    })
    .clone()
}
fn check(source: &str) -> fln::SourceFileCheck {
    let base = engine();
    let root = base.logical_root(&KVMap::new());
    let checked = base
        .check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .unwrap();
    assert!(checked.theorems > 0, "the fixture must check actual proofs");
    assert_eq!(base.logical_root(&KVMap::new()), root);
    reference(source, true);
    checked
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
                .find_map(|s| s.strip_prefix(key))
                .unwrap()
        };
        let lib = std::env::var_os("FLN_REFERENCE_LIB")
            .map(PathBuf::from)
            .or_else(|| {
                std::env::var_os("HOME").map(|h| {
                    PathBuf::from(h)
                        .join(".elan/toolchains")
                        .join(format!("leanprover--lean4---{}", field("tag=")))
                        .join("lib/lean")
                })
            });
        let pin = lib
            .and_then(|p| Some(p.parent()?.parent()?.join("bin/lean")))
            .filter(|p| p.is_file());
        if let Some(pin) = &pin {
            let out = Command::new(pin).arg("--version").output().unwrap();
            let version = String::from_utf8(out.stdout).unwrap();
            assert!(
                out.status.success()
                    && version.contains(field("tag=").trim_start_matches('v'))
                    && version.contains(field("commit=")),
                "{version}"
            );
        } else {
            assert!(
                std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
                "pinned Reference required"
            );
            eprintln!("SKIP: course-of-values differential requires the pinned Lean compiler");
        }
        pin
    });
    let Some(pin) = pin else {
        return;
    };
    let dir = std::env::temp_dir().join(format!("fln-course-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join(format!("{}.lean", NEXT.fetch_add(1, Ordering::Relaxed)));
    std::fs::write(&path, source).unwrap();
    let out = Command::new(pin).arg(path).output().unwrap();
    assert_eq!(
        out.status.success(),
        accepted,
        "{source}\n{}{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
}

#[test]
fn fibonacci_keeps_definitional_equations_and_checked_ground_values() {
    let checked = check(&format!(
        "{FIB}example : fib 5 = 5 := rfl\ntheorem fib_step (n : Nat) : fib (n+2) = fib n + fib (n+1) := rfl\n"
    ));
    let info = checked
        .engine
        .environment()
        .find(&Name::from_components(["fib"]))
        .unwrap();
    let fln_env::constants::ConstantInfo::Defn(value) = info else {
        panic!("actual definition");
    };
    assert!(!value.value.has_fvar());
    assert_eq!(value.safety, fln_env::constants::DefinitionSafety::Safe);
}

#[test]
fn automatic_two_step_recursion_remains_definitional_without_well_founded_fallback() {
    check(
        "def half : Nat -> Nat\n | 0 => 0\n | 1 => 0\n | n+2 => half n + 1\nexample : half 8 = 4 := rfl\ntheorem half_step (n : Nat) : half (n+2) = half n + 1 := rfl\n",
    );
}

#[test]
fn deeper_list_tails_and_transparent_aliases_use_the_actual_dictionary() {
    check(
        "inductive CourseList (A : Type u) where\n | nil : CourseList A\n | cons : A -> CourseList A -> CourseList A\ndef count {A : Type u} : CourseList A -> Nat\n | .nil => 0\n | .cons _ .nil => 1\n | .cons _ (.cons _ tail) => let rest := tail; count rest + 2\ntermination_by structural xs => xs\nexample : count (.cons 1 (.cons 2 (.cons 3 .nil))) = 3 := rfl\ntheorem count_step (A : Type u) (a b : A) (tail : CourseList A) : count (.cons a (.cons b tail)) = count tail + 2 := rfl\n",
    );
}

#[test]
fn changing_accumulators_remain_arguments_of_the_previous_result() {
    check(
        "def jump (n acc : Nat) : Nat := match n with\n | 0 => acc\n | 1 => acc\n | k+2 => jump k (acc+2)\ntermination_by structural n\nexample : jump 6 3 = 9 := rfl\ntheorem jump_step (n acc : Nat) : jump (n+2) acc = jump n (acc+2) := rfl\n",
    );
}

#[test]
fn earlier_changed_parameters_are_generalized_after_the_failed_direct_trial() {
    check(
        "def jump (acc n : Nat) : Nat := match n with\n | 0 => acc\n | 1 => acc\n | k+2 => jump (acc+2) k\ntermination_by structural n\nexample : jump 3 6 = 9 := rfl\ntheorem jump_step (n acc : Nat) : jump acc (n+2) = jump (acc+2) n := rfl\n",
    );
}

#[test]
fn multiple_recursive_fields_select_distinct_deeper_subtrees() {
    check(
        "inductive Tree where\n | leaf : Nat -> Tree\n | node : Tree -> Tree -> Tree\ndef total : Tree -> Nat\n | .leaf n => n\n | .node (.leaf n) right => n + total right\n | .node (.node left middle) right => total left + total middle + total right\ntermination_by structural tree => tree\ntheorem total_ground : total (.node (.node (.leaf 7) (.leaf 11)) (.leaf 24)) = 42 := rfl\n",
    );
}

#[test]
fn invalid_self_calls_and_original_typing_are_not_hidden_by_dictionary_search() {
    let base = engine();
    let root = base.logical_root(&KVMap::new());
    for body in [
        "loop (n+2)",
        "let unused := loop (n+2); loop n",
        "let invalid : Bool := n; loop n",
    ] {
        let source = format!(
            "def loop : Nat -> Nat\n | 0 => 0\n | 1 => 0\n | n+2 => {body}\ntermination_by structural n => n\n"
        );
        assert!(
            base.check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
                .is_err(),
            "{source}"
        );
        assert_eq!(base.logical_root(&KVMap::new()), root);
        reference(&source, false);
    }
    let source = format!("{FIB}example : fib 5 = 6 := rfl\n");
    assert!(
        base.check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
            .is_err()
    );
    assert_eq!(base.logical_root(&KVMap::new()), root);
    reference(&source, false);
}

#[test]
fn resource_stops_and_late_failures_preserve_the_original_environment() {
    let base = engine();
    let options = KVMap::new();
    let before = base.logical_root(&options);
    let source = format!("{FIB}theorem step (n : Nat) : fib (n+2) = fib n + fib (n+1) := rfl\n");
    for allowance in [0, 1, 32] {
        let mut low = limits();
        low.admission.kernel = low.admission.kernel.narrowed(allowance, 32);
        match base.check_source_files(&[source.as_bytes()], &options, low) {
            Ok(fln::Outcome::Inconclusive(_)) => {}
            Err(error) => assert!(
                matches!(error.disposition(), ("resource" | "inconclusive", false, 3)),
                "{error:?}"
            ),
            other => panic!("expected a resource stop: {other:?}"),
        }
        assert_eq!(base.logical_root(&options), before);
    }
    let late = format!("{source}theorem false_value : fib 3 = 8 := rfl\n");
    assert!(
        base.check_source_files(&[late.as_bytes()], &options, limits())
            .is_err()
    );
    assert_eq!(base.logical_root(&options), before);
    let one = base
        .check_source_files(&[source.as_bytes()], &options, limits())
        .unwrap()
        .into_complete()
        .unwrap();
    let two = base
        .check_source_files(&[source.as_bytes()], &options, limits())
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(one.result_logical_root, two.result_logical_root);
    assert_eq!(base.logical_root(&options), before);
    reference(&source, true);
    reference(&late, false);
}

#[test]
fn nested_matrix_entries_match_conversion_without_assuming_arbitrary_descent() {
    check(
        "def same (n : Nat) (b : Bool) : Nat := match n, b with | .zero, _ => 0 | .succ k, _ => same (k + 0) b\ntermination_by structural n\ntheorem same_step (n : Nat) (b : Bool) : same (n+1) b = same n b := rfl\n",
    );
    check(
        "def skip (n : Nat) (b : Bool) : Nat := match n, b with | .zero, _ => 0 | .succ (.succ k), _ => skip k b | .succ .zero, _ => 0\ntermination_by structural n\ntheorem skip_step (n : Nat) (b : Bool) : skip (n+2) b = skip n b := rfl\n",
    );
    let bad = "def bad (n : Nat) (b : Bool) : Nat := match n, b with | .zero, _ => 0 | .succ k, _ => bad 0 b\ntermination_by structural n";
    assert!(
        engine()
            .check_source_files(&[bad.as_bytes()], &KVMap::new(), limits())
            .is_err()
    );
    reference(bad, false);
}

#[test]
fn partial_child_applications_preserve_the_varying_argument_telescope() {
    check(
        "def walk (n a b : Nat) : Nat := match n with\n | 0 => a+b\n | 1 => a+b\n | k+2 => let next := walk k; next (a+1) (b+2)\ntermination_by structural n\ntheorem walk_step (n a b : Nat) : walk (n+2) a b = walk n (a+1) (b+2) := rfl\nexample : walk 4 1 2 = 9 := rfl\n",
    );
}
