//! Dependent index telescopes remain typed through matches and recursive calls.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, Name, Outcome, SourceCheckLimits};

fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}
fn engine() -> Engine {
    Engine::with_source_seed(limits())
        .unwrap()
        .into_complete()
        .unwrap()
}
fn check(text: &str) -> fln::SourceFileCheck {
    engine()
        .check_source_files(
            &[text.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        )
        .unwrap_or_else(|error| panic!("{text}\n{error:?}"))
        .into_complete()
        .unwrap()
}
const TRACE: &str = "inductive Trace (A : Type) (P : A -> Type) : forall a : A, P a -> Type where\n\
  | stop (a : A) (v : P a) : Trace A P a v\n\
  | step (a b : A) (v : P a) (w : P b) (child : Trace A P a v) : Trace A P b w\n\
def trace : Trace Nat (fun a => Bool) 2 false := Trace.step 1 2 true false (Trace.stop 1 true)\n";

#[test]
fn dependent_index_matches_refine_result_domains_without_casts() {
    check(&format!("{TRACE}
        def extract {{A : Type}} {{P : A -> Type}} (a : A) (v : P a) (t : Trace A P a v) : P a := match t with
          | .stop x vx => vx
          | .step x y vx vy child => vy
        def rebuild {{A : Type}} {{P : A -> Type}} (a : A) (v : P a) (t : Trace A P a v) : Trace A P a v := match t with
          | .stop x vx => Trace.stop x vx
          | .step x y vx vy child => Trace.step x y vx vy child
        theorem extracted : extract 2 false trace = false := by rfl
        theorem rebuilt : rebuild 2 false trace = trace := by rfl"));
}

#[test]
fn recursive_dependent_indices_and_inferred_fixed_families_are_preserved() {
    check(&format!("{TRACE}
        def copyTrace {{A : Type}} {{P : A -> Type}} (a : A) (v : P a) (t : Trace A P a v) : Trace A P a v := match t with
          | .stop x vx => Trace.stop x vx
          | .step x y vx vy child => Trace.step x y vx vy (copyTrace x vx child)
        theorem compute : copyTrace 2 false trace = trace := by rfl
        theorem identity {{A : Type}} {{P : A -> Type}} (a : A) (v : P a) (t : Trace A P a v) : copyTrace a v t = t := by
          induction t with
          | stop x vx => rfl
          | step x y vx vy child ih => simp only [copyTrace, ih]; rfl"));
}

#[test]
fn dependent_original_index_names_follow_the_current_constructor() {
    check(&format!("{TRACE}
        def current {{A : Type}} {{P : A -> Type}} (a : A) (v : P a) (t : Trace A P a v) : P a := match t with
          | .stop x vx => v
          | .step x y vx vy child => let prior := current x vx child; v
        def sumIndices (a : Nat) (v : Bool) (t : Trace Nat (fun a => Bool) a v) : Nat := match t with
          | .stop x vx => a
          | .step x y vx vy child => sumIndices x vx child + a
        theorem value : current 2 false trace = false := by rfl
        theorem indices : sumIndices 2 false trace = 3 := by rfl"));
}

#[test]
fn dependent_prefix_arguments_and_trailing_values_are_generalized_together() {
    check(&format!("{TRACE}
        def count {{A : Type}} {{P : A -> Type}} (a : A) (v : P a) (h : v = v) (t : Trace A P a v) (acc : Nat) : Nat := match t with
          | .stop x vx => acc
          | .step x y vx vy child => count x vx rfl child (acc + 1)
        def other {{A : Type}} {{P : A -> Type}} (a : A) (v : P a) (spare : Trace A P a v) (t : Trace A P a v) : Nat := match t with
          | .stop x vx => 0
          | .step x y vx vy child => other x vx child child + 1
        theorem count_ok : count 2 false rfl trace 9 = 10 := by rfl
        theorem other_ok : other 2 false trace trace = 1 := by rfl"));
}

#[test]
fn three_dependent_indices_and_higher_order_parameters_keep_telescope_order() {
    check("inductive Deep (A : Type) (P : A -> Type) (Q : forall a : A, P a -> Type) : forall a : A, forall p : P a, Q a p -> Type where
          | stop (a : A) (p : P a) (q : Q a p) : Deep A P Q a p q
          | step (a b : A) (p : P a) (r : P b) (q : Q a p) (s : Q b r) (child : Deep A P Q a p q) : Deep A P Q b r s
        def input : Deep Nat (fun a => Bool) (fun a p => Nat) 2 false 8 := Deep.step 1 2 true false 7 8 (Deep.stop 1 true 7)
        def depth (A : Type) (P : A -> Type) (Q : forall a : A, P a -> Type) (a : A) (p : P a) (q : Q a p) (t : Deep A P Q a p q) : Nat := match t with
          | .stop x px qx => 0
          | .step x y px py qx qy child => depth A P Q x px qx child + 1
        theorem computed : depth Nat (fun a => Bool) (fun a p => Nat) 2 false 8 input = 1 := by rfl");
}

#[test]
fn exact_eta_expansions_of_fixed_functions_are_safe_but_not_general_conversion() {
    check(
        "def unary (f : Nat -> Nat) (n : Nat) : Nat := match n with
          | .zero => f 0
          | .succ k => unary (fun x => f x) k
        def binary (f : Nat -> Nat -> Nat) (n : Nat) : Nat := match n with
          | .zero => f 1 2
          | .succ k => binary (fun x y => f x y) k
        theorem one : unary (fun x => x + 7) 3 = 7 := by rfl
        theorem two : binary (fun x y => x + y) 3 = 3 := by rfl",
    );
    let base = engine();
    let root = base.logical_root(&KVMap::new());
    for argument in [
        "fun x => f 0",
        "fun x => f (f x)",
        "fun x => let bad : String := 0; f x",
        "fun x => (f x : String)",
        "fun x => let hidden := bad f n; f x",
    ] {
        let source = format!(
            "def bad (f : Nat -> Nat) (n : Nat) : Nat := match n with | .zero => 0 | .succ k => bad ({argument}) k"
        );
        assert!(
            base.check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits())
            )
            .is_err(),
            "{source}"
        );
        assert_eq!(base.logical_root(&KVMap::new()), root);
    }
}

#[test]
fn dependent_index_failures_never_discard_a_branch_or_publish_a_prefix() {
    let base = engine();
    let root = base.logical_root(&KVMap::new());
    for source in [
        "def bad {A : Type} {P : A -> Type} (a : A) (v : P a) (t : Trace A P a v) : P a := match t with | .stop x vx => vx | .step x y vx vy child => vx",
        "def bad {A : Type} {P : A -> Type} (a : A) (v : P a) (t : Trace A P a v) : Trace A P a v := match t with | .stop x vx => t | .step x y vx vy child => t",
        "def bad {A : Type} {P : A -> Type} (a : A) (v : P a) (t : Trace A P a v) : Nat := match t with | .stop x vx => 0 | .step x y vx vy child => bad y vy child",
        "def bad {A : Type} {P : A -> Type} (a : A) (v : P a) (t : Trace A P a v) : Nat := match t with | .stop x vx => 0 | .step x y vx vy child => let unused := bad a v t; 0",
        "theorem bad {A : Type} {P : A -> Type} (a : A) (v : P a) (t : Trace A P a v) : 0 = 0 := match t with | .stop x vx => rfl | .step x y vx vy child => by assumption",
        "def bad {A : Type} {P : A -> Type} (a : A) (v : P a) (t : Trace A P a v) : Nat := match t with | .stop x vx => (0 : String) | .step x y vx vy child => bad x vx child",
    ] {
        let result = base.check_source_files(
            &[TRACE.as_bytes(), source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        );
        assert!(result.is_err(), "{source}\n{result:?}");
        assert_eq!(base.logical_root(&KVMap::new()), root);
        assert!(
            !base
                .environment()
                .contains(&Name::from_components(["Trace"]))
        );
    }
    assert!(
        base.check_source_files(
            &[TRACE.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits())
        )
        .is_ok()
    );
}

#[test]
fn dependent_recursion_exhaustion_remains_a_recoverable_nonanswer() {
    let prepared = check(TRACE).engine;
    let root = prepared.logical_root(&KVMap::new());
    let source = b"def depth {A : Type} {P : A -> Type} (a : A) (v : P a) (t : Trace A P a v) : Nat := match t with | .stop x vx => 0 | .step x y vx vy child => depth x vx child + 1";
    let mut bound = limits();
    bound.kernel.steps = 1;
    match prepared.check_source_files(&[source], &KVMap::new(), SourceCheckLimits::new(bound)) {
        Ok(Outcome::Inconclusive(_)) => {}
        Err(error) => assert!(
            matches!(error.disposition(), ("resource" | "inconclusive", false, 3)),
            "{error:?}"
        ),
        other => panic!("expected a typed nonanswer: {other:?}"),
    }
    assert_eq!(prepared.logical_root(&KVMap::new()), root);
    assert!(
        prepared
            .check_source_files(&[source], &KVMap::new(), SourceCheckLimits::new(limits()))
            .unwrap()
            .into_complete()
            .is_ok()
    );
}
