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

/// An auto-bound `α : Sort ?u` keeps its universe hole until the declaration generalizes it.
/// Dictionary entries and a `termination_by structural` measure are still compared, with each
/// open universe as a rigid parameter; before that, the first fell back to well-founded
/// recursion and the second was refused for unresolved universes.
#[test]
fn auto_bound_universes_still_select_dictionary_entries() {
    check(
        "inductive CourseList (A : Type u) where\n | nil : CourseList A\n | cons : A -> CourseList A -> CourseList A\ndef countAuto : CourseList α -> Nat\n | .nil => 0\n | .cons _ .nil => 1\n | .cons _ (.cons _ tail) => countAuto tail + 2\nexample : countAuto (.cons 1 (.cons 2 (.cons 3 .nil))) = 3 := rfl\ndef countHint (xs : CourseList α) : Nat := match xs with\n | .nil => 0\n | .cons _ .nil => 1\n | .cons _ (.cons _ tail) => countHint tail + 2\ntermination_by structural xs\ntheorem countHint_step (a b : α) (tail : CourseList α) : countHint (.cons a (.cons b tail)) = countHint tail + 2 := rfl\n",
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

#[test]
fn deeper_indexed_vector_tails_keep_their_actual_length_indices() {
    check(
        r#"
inductive CourseVec (A : Type u) : Nat -> Type u where
 | nil : CourseVec A 0
 | cons (n : Nat) : A -> CourseVec A n -> CourseVec A (Nat.succ n)
def countVec {A : Type u} (n : Nat) (xs : CourseVec A n) : Nat := match xs with
 | .nil => 0
 | .cons _ _ .nil => 1
 | .cons _ _ (.cons k _ tail) => countVec k tail + 2
termination_by structural xs
example : countVec 3 (.cons 2 11 (.cons 1 22 (.cons 0 33 .nil))) = 3 := rfl
theorem countVec_step {A : Type u} (n : Nat) (a b : A) (tail : CourseVec A n) :
 countVec (n+2) (.cons (n+1) a (.cons n b tail)) = countVec n tail + 2 := rfl
"#,
    );
}

const INDEXED_VEC: &str = "inductive CourseVec (A : Type u) : Nat -> Type u where\n | nil : CourseVec A 0\n | cons (n : Nat) : A -> CourseVec A n -> CourseVec A (Nat.succ n)\n";

#[test]
fn indexed_course_infers_implicit_indices_without_a_termination_hint() {
    check(&format!(
        r#"{INDEXED_VEC}
def countImplicit {{A : Type u}} {{n : Nat}} (xs : CourseVec A n) : Nat := match xs with
 | .nil => 0
 | .cons _ _ .nil => 1
 | .cons _ _ (.cons _ _ tail) => countImplicit tail + 2
example : countImplicit (.cons 2 11 (.cons 1 22 (.cons 0 33 .nil))) = 3 := rfl
theorem countImplicit_step {{A : Type u}} (n : Nat) (a b : A) (tail : CourseVec A n) :
 countImplicit (.cons (n+1) a (.cons n b tail)) = countImplicit tail + 2 := rfl
"#
    ));
}

#[test]
fn indexed_course_preserves_a_result_family_depending_on_the_length() {
    check(&format!(
        r#"{INDEXED_VEC}
def copyTwo {{A : Type u}} (n : Nat) (xs : CourseVec A n) : CourseVec A n := match xs with
 | .nil => .nil
 | .cons _ a .nil => .cons 0 a .nil
 | .cons _ a (.cons k b tail) => .cons (k+1) a (.cons k b (copyTwo k tail))
termination_by structural xs
theorem copyTwo_step {{A : Type u}} (n : Nat) (a b : A) (tail : CourseVec A n) :
 copyTwo (n+2) (.cons (n+1) a (.cons n b tail)) = CourseVec.cons (n+1) a (.cons n b (copyTwo n tail)) := rfl
example : copyTwo 2 (.cons 1 17 (.cons 0 23 .nil)) = CourseVec.cons 1 17 (.cons 0 23 .nil) := rfl
"#
    ));
}

#[test]
fn indexed_course_uses_family_index_order_not_function_header_order() {
    use fln_core::expr::{Expr, Literal, NatLit};
    use fln_core::level::Level;
    use fln_env::constants::{ConstantVal, TheoremVal};
    let source = r#"
inductive CoursePair : Nat -> Nat -> Type where
 | leaf (a b : Nat) : CoursePair a b
 | step (a b : Nat) : CoursePair a b -> CoursePair (Nat.succ a) (Nat.succ b)
def weight (b a : Nat) (xs : CoursePair a b) : Nat := match xs with
 | .leaf x _ => x
 | .step _ _ (.leaf x _) => x
 | .step _ _ (.step x y tail) => weight y x tail
termination_by structural xs
"#;
    let base = engine();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    let checked = base
        .check_source_files(&[source.as_bytes()], &options, limits())
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(base.logical_root(&options), root);
    let theorem_source = format!(
        "{source}theorem weight_ground : weight 9 5 (.step 4 8 (.step 3 7 (.leaf 3 7))) = 3 := rfl\n"
    );
    reference(&theorem_source, true);
    // The ordinary source unifier still exhausts its fixed work budget on
    // this larger two-index conversion. Prove the lowering's actual result
    // through BOTH existing admission seats without changing that budget.
    let name = |s: &str| Name::from_components(s.split('.'));
    let constant = |s| Expr::const_(name(s), vec![]);
    let numeral = |n| Expr::lit(Literal::Nat(NatLit::from_u64(n)));
    let apply = |f, args: Vec<_>| args.into_iter().fold(f, Expr::app);
    let leaf = apply(constant("CoursePair.leaf"), vec![numeral(3), numeral(7)]);
    let child = apply(
        constant("CoursePair.step"),
        vec![numeral(3), numeral(7), leaf],
    );
    let major = apply(
        constant("CoursePair.step"),
        vec![numeral(4), numeral(8), child],
    );
    let call = apply(constant("weight"), vec![numeral(9), numeral(5), major]);
    let theorem = |expected| {
        fln::Declaration::Thm(TheoremVal {
            base: ConstantVal {
                name: name("checkedWeight"),
                level_params: vec![],
                type_: apply(
                    Expr::const_(name("Eq"), vec![Level::one()]),
                    vec![constant("Nat"), call.clone(), numeral(expected)],
                ),
            },
            value: apply(
                Expr::const_(name("Eq.refl"), vec![Level::one()]),
                vec![constant("Nat"), numeral(expected)],
            ),
            all: vec![name("checkedWeight")],
        })
    };
    checked
        .engine
        .admit_declaration(theorem(3), &options, limits().admission)
        .unwrap()
        .into_complete()
        .unwrap();
    assert!(
        checked
            .engine
            .admit_declaration(theorem(7), &options, limits().admission)
            .is_err(),
        "reversing the indices must not produce the other leaf index"
    );
    let before = checked.engine.logical_root(&options);
    match checked.engine.check_source_files(
        &[b"theorem weight_ground : weight 9 5 (.step 4 8 (.step 3 7 (.leaf 3 7))) = 3 := rfl"],
        &options,
        limits(),
    ) {
        Ok(fln::Outcome::Complete(_)) | Ok(fln::Outcome::Inconclusive(_)) => {}
        Err(error) => assert!(
            matches!(error.disposition(), ("resource" | "inconclusive", false, 3)),
            "valid conversion must not become a semantic rejection: {error:?}"
        ),
        other => panic!("unexpected checked conversion outcome: {other:?}"),
    }
    assert_eq!(checked.engine.logical_root(&options), before);
}

#[test]
fn indexed_course_generalizes_changed_accumulators_on_either_side_of_the_major() {
    check(&format!(
        r#"{INDEXED_VEC}
def walkAfter (n : Nat) (xs : CourseVec Nat n) (acc : Nat) : Nat := match xs with
 | .nil => acc
 | .cons _ a .nil => acc+a
 | .cons _ a (.cons k b tail) => walkAfter k tail (acc+a+b)
termination_by structural xs
def walkBefore (acc n : Nat) (xs : CourseVec Nat n) : Nat := match xs with
 | .nil => acc
 | .cons _ a .nil => acc+a
 | .cons _ a (.cons k b tail) => walkBefore (acc+a+b) k tail
termination_by structural xs
example : walkAfter 3 (.cons 2 1 (.cons 1 2 (.cons 0 3 .nil))) 36 = 42 := rfl
example : walkBefore 36 3 (.cons 2 1 (.cons 1 2 (.cons 0 3 .nil))) = 42 := rfl
theorem walkAfter_step (n acc a b : Nat) (tail : CourseVec Nat n) :
 walkAfter (n+2) (.cons (n+1) a (.cons n b tail)) acc = walkAfter n tail (acc+a+b) := rfl
"#
    ));
}

#[test]
fn indexed_course_rejects_wrong_indices_nondecreasing_calls_and_invalid_branch_types() {
    let base = engine();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    for body in [
        "bad n tail",
        "bad n xs",
        "let unused := bad (k+1) tail; bad k tail",
        "let invalid : Bool := k; bad k tail",
    ] {
        let source = format!(
            "{INDEXED_VEC}def bad {{A : Type u}} (n : Nat) (xs : CourseVec A n) : Nat := match xs with\n | .nil => 0\n | .cons _ _ .nil => 1\n | .cons _ _ (.cons k _ tail) => {body}\ntermination_by structural xs\n"
        );
        reference(&source, false);
        assert!(
            base.check_source_files(&[source.as_bytes()], &options, limits())
                .is_err(),
            "{source}"
        );
        assert_eq!(base.logical_root(&options), root);
        assert!(!base.environment().contains(&Name::from_components(["bad"])));
    }
}

#[test]
fn indexed_course_resource_stops_are_atomic_and_retry_keeps_the_checked_root() {
    let base = engine();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    let source = format!(
        r#"{INDEXED_VEC}
def recover (n : Nat) (xs : CourseVec Nat n) : Nat := match xs with
 | .nil => 0
 | .cons _ _ .nil => 1
 | .cons _ _ (.cons k _ tail) => recover k tail + 2
termination_by structural xs
theorem recovery : recover 2 (.cons 1 3 (.cons 0 5 .nil)) = 2 := rfl
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
            other => panic!("expected bounded nonanswer: {other:?}"),
        }
        assert_eq!(base.logical_root(&options), root);
    }
    let first = check(&source);
    let second = check(&source);
    assert_eq!(first.result_logical_root, second.result_logical_root);
    assert_eq!(base.logical_root(&options), root);
}

#[test]
fn indexed_course_preserves_dependent_index_telescope_domains() {
    check(
        r#"
inductive DepHistory : (A : Type u) -> A -> Type (u+1) where
 | leaf (A : Type u) (a : A) : DepHistory A a
 | step (A : Type u) (a : A) : DepHistory A a -> DepHistory A a
def depthDep (A : Type u) (a : A) (xs : DepHistory A a) : Nat := match xs with
 | .leaf _ _ => 0
 | .step _ _ (.leaf _ _) => 1
 | .step _ _ (.step _ _ tail) => Nat.succ (Nat.succ (depthDep A a tail))
termination_by structural xs
theorem depthDep_step (A : Type u) (a : A) (tail : DepHistory A a) :
 depthDep A a (.step A a (.step A a tail)) = Nat.succ (Nat.succ (depthDep A a tail)) := rfl
example : depthDep Nat 17 (.step Nat 17 (.step Nat 17 (.leaf Nat 17))) = 2 := rfl
"#,
    );
}

#[test]
fn indexed_course_partial_calls_keep_remaining_function_arguments() {
    check(&format!(
        r#"{INDEXED_VEC}
def deferred (n : Nat) (xs : CourseVec Nat n) (acc : Nat) : Nat := match xs with
 | .nil => acc
 | .cons _ a .nil => acc+a
 | .cons _ a (.cons k b tail) => let resume := deferred k tail; resume (acc+a+b)
termination_by structural xs
theorem deferred_step (n acc a b : Nat) (tail : CourseVec Nat n) :
 deferred (n+2) (.cons (n+1) a (.cons n b tail)) acc = deferred n tail (acc+a+b) := rfl
example : deferred 2 (.cons 1 17 (.cons 0 23 .nil)) 2 = 42 := rfl
"#
    ));
}
