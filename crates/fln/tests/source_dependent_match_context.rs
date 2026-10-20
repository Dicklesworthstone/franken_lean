//! Ordinary constructor matches specialize their dependent local telescope.
#![forbid(unsafe_code)]
use fln::{
    Budget, ClosedVmValue, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap,
    closed_vm_value,
};

fn returns(source: &str, expected: usize) {
    reference(source, true, Some(expected));
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let engine = Engine::with_source_seed(limits)
        .unwrap()
        .into_complete()
        .unwrap();
    let result = engine
        .execute_source_definitions(
            &[source.as_bytes()],
            &KVMap::new(),
            EngineExecutionLimits::new(limits.kernel),
        )
        .unwrap_or_else(|e| panic!("{source}\n{e:?}"))
        .into_complete()
        .unwrap();
    assert_eq!(
        closed_vm_value(&result.executions.last().unwrap().exit).unwrap(),
        Some(ClosedVmValue::Scalar(expected))
    );
}

#[test]
fn match_rebinds_a_data_local_depending_on_its_major() {
    returns(
        r#"structure Token (n : Nat) where
  value : Nat
def preserve (n : Nat) (token : Token n) : Token n :=
  match n with
  | .zero => token
  | .succ k => token
#eval (preserve 7 (Token.mk 42)).value"#,
        42,
    );
}

#[test]
fn match_specializes_dependent_inputs_even_with_a_constant_result_type() {
    returns(
        r#"structure Token (n : Nat) where
  value : Nat
def zeroToken (t : Token 0) : Nat := t.value
def succToken (n : Nat) (t : Token (Nat.succ n)) : Nat := t.value
def read (n : Nat) (token : Token n) : Nat :=
  match n with
  | .zero => zeroToken token
  | .succ k => succToken k token
#eval read 7 (Token.mk 42)"#,
        42,
    );
}

#[test]
fn nested_matches_specialize_a_dependent_callback_and_value_together() {
    returns(
        r#"structure Token (n : Nat) where
  value : Nat
def zeroToken (t : Token 0) : Nat := t.value
def oneToken (t : Token 1) : Nat := t.value
def laterToken (n : Nat) (t : Token (Nat.succ (Nat.succ n))) : Nat := t.value
def read (n : Nat) (token : Token n) : Nat :=
  match n with
  | .zero => zeroToken token
  | .succ k => match k with
    | .zero => oneToken token
    | .succ j => laterToken j token
#eval read 7 (Token.mk 42)"#,
        42,
    );
}

#[test]
fn dependent_callbacks_are_specialized_in_declaration_order() {
    returns(
        r#"structure Token (n : Nat) where
  value : Nat
def read (n : Nat) (token : Token n) (measure : Token n -> Nat) : Nat :=
  match n with
  | .zero => measure token
  | .succ k => measure token
def token : Token 7 := { value := 40 }
#eval read 7 token (fun t => t.value + 2)"#,
        42,
    );
}

#[test]
fn boolean_discriminants_specialize_dependent_data() {
    returns(
        r#"structure Flagged (b : Bool) where
  value : Nat
def yes (t : Flagged true) : Nat := t.value
def no (t : Flagged false) : Nat := t.value
def read (b : Bool) (token : Flagged b) : Nat :=
  match b with
  | .false => no token
  | .true => yes token
#eval read true (Flagged.mk 42)"#,
        42,
    );
}

#[test]
fn dependent_proof_parameters_remain_checked_after_generalization() {
    returns(
        r#"structure Token (n : Nat) where
  value : Nat
def preserve (n : Nat) (token : Token n) (h : token.value = 42) : token.value = 42 :=
  match n with
  | .zero => h
  | .succ k => h
def token : Token 7 := { value := 42 }
theorem verified : token.value = 42 := preserve 7 token rfl
#eval token.value"#,
        42,
    );
}

#[test]
fn dependent_function_domains_preserve_captured_values_and_shadowing() {
    returns(
        r#"structure Token (n : Nat) where
  value : Nat
def read (n : Nat) (token : Token n) (f : Token n -> Nat) : Nat :=
  let captured : Nat := 2
  match n with
  | .zero => captured + f token
  | .succ n => captured + f token
#eval read 7 (Token.mk 40) (fun t => t.value)"#,
        42,
    );
}

#[test]
fn explicit_course_history_can_be_specialized_by_nested_matches() {
    use fln::SourceCheckLimits;
    let source = r#"noncomputable def courseFib (n : Nat) : Nat := Nat.brecOn n (fun k previous =>
  match k with
  | .zero => 0
  | .succ k => match k with
    | .zero => 1
    | .succ k => match previous with
      | .mk first rest => match rest with
        | .mk second history => first + second)
theorem courseFib_six : courseFib 6 = 8 := by rfl"#;
    reference(source, true, None);
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let engine = Engine::with_source_seed(limits)
        .unwrap()
        .into_complete()
        .unwrap();
    engine
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits),
        )
        .unwrap_or_else(|e| panic!("{e:?}"))
        .into_complete()
        .expect("both checking engines finish");
}

fn rejects(source: &str) {
    use fln::source_check::SourceCheckError;
    use fln::{DefinitionFrontendError, EngineExecutionError, SourceCheckLimits};
    use fln_elab::{NatDefinitionElabError, source::SourceInferenceError};
    use fln_kernel::verdict::{RejectClass, Verdict};
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let engine = Engine::with_source_seed(limits)
        .unwrap()
        .into_complete()
        .unwrap();
    let root = engine.logical_root(&KVMap::new());
    let error = engine
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits),
        )
        .expect_err("an ill-typed branch must remain rejected");
    let SourceCheckError::Command { error, .. } = error else {
        panic!("not a completed type refusal: {error:?}");
    };
    let EngineExecutionError::Frontend(DefinitionFrontendError::Elaborate(
        NatDefinitionElabError::Inference(reason),
    )) = *error
    else {
        panic!("not a typing refusal: {error:?}");
    };
    match reason {
        SourceInferenceError::ConversionRefused(verdict) => assert!(matches!(
            verdict.as_ref(),
            Verdict::Rejected {
                class: RejectClass::NotDefEq,
                ..
            }
        )),
        SourceInferenceError::TypeMismatch { .. } => {}
        other => panic!("a resource stop or other failure is not a negative control: {other:?}"),
    }
    assert_eq!(engine.logical_root(&KVMap::new()), root);
    reference(source, false, None);
}

#[test]
fn generalization_does_not_make_incompatible_branch_results_equal() {
    rejects(
        r#"structure Token (n : Nat) where
  value : Nat
def wrong (n : Nat) (token : Token n) : Token 0 :=
  match n with
  | .zero => token
  | .succ k => token"#,
    );
    rejects(
        r#"theorem wrong (n : Nat) (h : n = n) : n = 0 :=
  match n with
  | .zero => h
  | .succ k => h"#,
    );
}

#[test]
fn unused_let_initializers_still_have_their_original_typing_obligations() {
    rejects(
        r#"structure Token (n : Nat) where
  value : Nat
def wrong (n : Nat) (token : Token n) : Nat :=
  let unused : Nat := "bad"
  match n with
  | .zero => token.value
  | .succ k => token.value"#,
    );
}

fn reference(source: &str, accepted: bool, expected: Option<usize>) {
    use std::path::PathBuf;
    use std::process::Command;
    use std::sync::OnceLock;
    static REFERENCE: OnceLock<Option<PathBuf>> = OnceLock::new();
    let binary = REFERENCE.get_or_init(|| {
        let pin = include_str!("../../../SUITE.lock")
            .lines()
            .find(|s| s.starts_with("reference leanprover/lean4 "))
            .unwrap();
        let field = |key: &str| {
            pin.split_whitespace()
                .find_map(|word| word.strip_prefix(key))
                .unwrap()
        };
        let tag = field("tag=");
        let commit = field("commit=");
        let lib = std::env::var_os("FLN_REFERENCE_LIB")
            .map(PathBuf::from)
            .or_else(|| {
                std::env::var_os("HOME").map(|p| {
                    PathBuf::from(p)
                        .join(".elan/toolchains")
                        .join(format!("leanprover--lean4---{tag}"))
                        .join("lib/lean")
                })
            });
        let binary = lib
            .filter(|p| p.join("Init.olean").is_file())
            .and_then(|p| p.parent()?.parent().map(|p| p.join("bin/lean")))
            .filter(|p| p.is_file());
        let Some(binary) = binary else {
            assert!(
                std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
                "pinned Reference required"
            );
            eprintln!("SKIP: dependent-match differential requires the pinned Reference");
            return None;
        };
        let result = Command::new(&binary).arg("--version").output().unwrap();
        let version = String::from_utf8(result.stdout).unwrap();
        assert!(
            result.status.success()
                && version.contains(tag.trim_start_matches('v'))
                && version.contains(commit),
            "{version}"
        );
        Some(binary)
    });
    let Some(binary) = binary else {
        return;
    };
    let root = std::env::temp_dir().join(format!(
        "fln-dependent-match-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos()
    ));
    std::fs::create_dir(&root).unwrap();
    let path = root.join("case.lean");
    std::fs::write(&path, source).unwrap();
    let result = Command::new(binary).arg(&path).output().unwrap();
    let stdout = String::from_utf8(result.stdout).unwrap();
    assert_eq!(
        result.status.code(),
        Some(if accepted { 0 } else { 1 }),
        "{source}\n{stdout}{}",
        String::from_utf8_lossy(&result.stderr)
    );
    if let Some(expected) = expected {
        assert_eq!(
            stdout.lines().last(),
            Some(expected.to_string().as_str()),
            "{source}\n{stdout}"
        );
    }
}
