//! Leading source lambdas use the same structural recursion and council path
//! as header binders. The corresponding programs were run with Lean v4.32.0;
//! the positives compute the values below and the negatives are refused.
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

fn check(base: &Engine, source: &str) -> Engine {
    base.check_source_files(
        &[source.as_bytes()],
        &KVMap::new(),
        SourceCheckLimits::new(limits()),
    )
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
            fln::EngineExecutionLimits::new(limits().kernel),
        )
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .unwrap();
    let fln::VmExit::Returned(result) = &result.executions.last().unwrap().exit else {
        panic!("recursive program did not return")
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&result.value).as_deref(),
        Some(expected),
        "{source}"
    );
}

#[test]
fn leading_lambda_parameters_are_structural_inputs() {
    let source = "def loop : Nat -> Nat := fun n => match n with
        | .zero => 0
        | .succ k => loop k + 1";
    check(
        &engine(),
        &format!("{source}\ntheorem computes : loop 12 = 12 := by rfl"),
    );
    evaluate(&format!("{source}\n#eval loop 12"), "12");
}

#[test]
fn nested_lambdas_and_header_arguments_share_generalization() {
    for source in [
        "def loop (acc : Nat) : Nat -> Nat := fun n => match n with
          | .zero => acc | .succ k => loop (acc + 1) k",
        "def loop : Nat -> Nat -> Nat := fun acc => fun n => match n with
          | .zero => acc | .succ k => loop (acc + 1) k",
        "def loop : Nat -> Nat -> Nat := (fun acc n => (match n with
          | .zero => acc | .succ k => loop (acc + 1) k))",
    ] {
        check(
            &engine(),
            &format!("{source}\ntheorem computes : loop 10 32 = 42 := by rfl"),
        );
        evaluate(&format!("{source}\n#eval loop 10 32"), "42");
    }
}

#[test]
fn inferred_implicit_prefix_and_written_domains_keep_their_types() {
    let source = "def keep : {A : Type} -> A -> Nat -> A := fun value n => match n with
        | .zero => value | .succ k => keep value k";
    check(
        &engine(),
        &format!("{source}\ntheorem computes : keep (A := Nat) 42 3 = 42 := by rfl"),
    );
    evaluate(&format!("{source}\n#eval keep 42 3"), "42");
    evaluate(
        "def keep : {A : Type} -> A -> Nat -> A := fun {A} (value : A) (n : Nat) =>
           match n with | .zero => value | .succ k => keep value k
         #eval String.length (keep \"retained\" 3)",
        "8",
    );
}

#[test]
fn lambda_recursion_can_return_dependent_proofs() {
    check(
        &engine(),
        "theorem succCongr {a b : Nat} (h : a = b) : Nat.succ a = Nat.succ b := Eq.rec rfl h
         theorem reflLoop : (n : Nat) -> n = n := fun n => match n with
          | .zero => rfl | .succ k => succCongr (reflLoop k)
         theorem usesProof : 3 = 3 := reflLoop 3",
    );
}

#[test]
fn indexed_lambda_parameters_retain_the_actual_child_indices() {
    check(
        &engine(),
        "inductive LambdaVec (A : Type) : Nat -> Type where
           | nil : LambdaVec A 0
           | cons (n : Nat) (value : A) (tail : LambdaVec A n) : LambdaVec A (Nat.succ n)
         def copy {A : Type} : (n : Nat) -> LambdaVec A n -> LambdaVec A n := fun n xs =>
           match xs with
           | .nil => LambdaVec.nil
           | .cons k x rest => LambdaVec.cons k x (copy k rest)
         theorem copied : copy 1 (LambdaVec.cons 0 42 LambdaVec.nil) = LambdaVec.cons 0 42 LambdaVec.nil := by rfl",
    );
}

#[test]
fn indexed_lambdas_check_the_original_body_before_refining_the_major() {
    let base = engine();
    let root = base.logical_root(&KVMap::new());
    let family = "inductive LambdaVec (A : Type) : Nat -> Type where
      | nil : LambdaVec A 0
      | cons (n : Nat) (value : A) (tail : LambdaVec A n) : LambdaVec A (Nat.succ n)";
    for declaration in [
        "def retain {A : Type} : (n : Nat) -> LambdaVec A n -> LambdaVec A n :=
           fun n xs => match xs with
           | .nil => LambdaVec.nil
           | .cons k x rest => let used := retain k rest; xs",
        "def bad : Nat :=
           let rec retain : (n : Nat) -> LambdaVec Nat n -> LambdaVec Nat n :=
             fun n xs => match xs with
             | .nil => LambdaVec.nil
             | .cons k x rest => let used := retain k rest; xs
           42",
    ] {
        let source = format!("{family}\n{declaration}");
        let error = base
            .check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits()),
            )
            .expect_err(&source);
        assert!(
            !format!("{error:?}").contains("Frontend(Parse("),
            "{source}\n{error:?}"
        );
        assert_eq!(base.logical_root(&KVMap::new()), root);
    }
}

#[test]
fn local_recursive_lambdas_capture_and_generalize_without_global_helpers() {
    for source in [
        "def value : Nat := let rec go : Nat -> Nat := fun n => match n with
           | .zero => 10 | .succ k => go k + 1; go 32",
        "def value : Nat := let rec go (acc : Nat) : Nat -> Nat := fun n => match n with
           | .zero => acc | .succ k => go (acc + 1) k; go 10 32",
        "def value : Nat := let rec go : Nat -> Nat -> Nat := fun acc => fun n => match n with
           | .zero => acc | .succ k => go (acc + 1) k; go 10 32",
        "def value : Nat := let base := 10; let rec go : Nat -> Nat := fun n => match n with
           | .zero => base | .succ k => go k + 1; go 32",
    ] {
        let checked = check(
            &engine(),
            &format!("{source}\ntheorem computes : value = 42 := by rfl"),
        );
        assert!(
            !checked
                .environment()
                .contains(&fln::Name::from_components(["go"]))
        );
        evaluate(&format!("{source}\n#eval value"), "42");
    }
}

#[test]
fn local_lambda_matrices_keep_their_structural_hypotheses() {
    let source = "def value : Nat := let rec go : Nat -> Bool -> Nat := fun n b =>
        match n, b with
        | .zero, _ => 0
        | .succ k, true => go k false + 1
        | .succ k, false => go k true + 2; go 3 true";
    check(
        &engine(),
        &format!("{source}\ntheorem computes : value = 4 := by rfl"),
    );
    evaluate(&format!("{source}\n#eval value"), "4");
}

#[test]
fn nested_local_lambdas_restore_the_outer_recursive_owner() {
    let source = "def outer (n : Nat) : Nat := match n with
        | .zero => 0
        | .succ k => let rec go : Nat -> Nat := fun n => match n with
          | .zero => outer k + 1 | .succ j => go j; go 1";
    check(
        &engine(),
        &format!("{source}\ntheorem computes : outer 5 = 5 := by rfl"),
    );
    evaluate(&format!("{source}\n#eval outer 5"), "5");
    evaluate(
        "def value : Nat := let rec go : Nat -> Nat := fun go => go; go 42\n#eval value",
        "42",
    );
}

#[test]
fn local_pattern_functions_keep_their_ordinary_lambda_path() {
    evaluate(
        "def value : Nat := let rec choose : Bool -> Nat :=
           fun | true => 42 | false => 0; choose true
         #eval value",
        "42",
    );
}

#[test]
fn invalid_calls_and_lambda_annotations_never_publish_a_prefix() {
    let base = engine();
    let root = base.logical_root(&KVMap::new());
    for source in [
        "def bad : Nat -> Nat := fun n => match n with | .zero => 0 | .succ k => bad n",
        "def bad : Nat -> Nat := fun n => match n with | .zero => 0 | .succ k => let ignored := bad n; bad k",
        "def bad : Nat -> Nat := fun (n : Bool) => match n with | true => 0 | false => bad 0",
        "def bad : Nat := let rec go : Nat -> Nat := fun n => match n with | .zero => 0 | .succ k => go n; 42",
        "def bad : Nat := let rec go : Nat := fun n => n; 42",
        "def go (input : Nat) : Type := Nat\ndef bad : Nat := let rec go : Nat -> Nat := fun (n : go 0) => n; go 0",
        "theorem bad : (n : Nat) -> 0 = 1 := fun n => match n with | .zero => by rfl | .succ k => bad k",
    ] {
        let error = base
            .check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits()),
            )
            .expect_err(source);
        assert!(
            !format!("{error:?}").contains("Frontend(Parse("),
            "{source}\n{error:?}"
        );
        assert_eq!(base.logical_root(&KVMap::new()), root);
    }
    check(&base, "def recovered : Nat := 42");
}
