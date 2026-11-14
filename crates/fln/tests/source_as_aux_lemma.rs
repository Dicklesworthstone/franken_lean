//! Auxiliary proofs are checked theorems with ordered, atomic admissions.
#![forbid(unsafe_code)]
use fln::source_check::modules::SourceModuleCheckLimits;
use fln::{
    Budget, Engine, EngineAdmissionLimits, KVMap, Name, SourceCheckLimits, SourceModuleInput,
};
use fln_env::constants::{ConstantInfo, TheoremVal};

fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}

fn engine() -> Engine {
    Engine::with_source_seed(limits())
        .unwrap()
        .into_complete()
        .unwrap()
}

fn reference(label: &str, source: &str, accepted: bool) {
    let reference = std::env::var_os("FLN_REFERENCE_LEAN")
        .or_else(|| std::env::var_os("FLN_REFERENCE_BIN"))
        .map(std::path::PathBuf::from)
        .filter(|path| path.is_file());
    let Some(reference) = reference else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "as_aux_lemma source differential requires the pinned executable"
        );
        return;
    };
    let path = std::env::temp_dir().join(format!(
        "fln-as-aux-lemma-{}-{label}.lean",
        std::process::id()
    ));
    std::fs::write(&path, source).unwrap();
    let output = std::process::Command::new(reference)
        .arg("-j1")
        .arg(path)
        .output()
        .unwrap();
    assert_eq!(
        output.status.code(),
        Some(if accepted { 0 } else { 1 }),
        "pin {label}: {}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

fn checked(base: &Engine, label: &str, source: &str) -> Engine {
    reference(label, source, true);
    let options = KVMap::new();
    let root = base.logical_root(&options);
    let result = base
        .check_source_files(
            &[source.as_bytes()],
            &options,
            SourceCheckLimits::new(limits()),
        )
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .unwrap();
    assert_eq!(base.logical_root(&options), root);
    result.engine
}

fn auxiliaries<'a>(engine: &'a Engine, owner: &str) -> Vec<&'a TheoremVal> {
    let owner = Name::from_components(owner.split('.'));
    engine
        .environment()
        .constants()
        .filter(|(name, _)| {
            name.parent() == owner
                && matches!(name.leaf_view(), fln_core::name::LeafView::Str(part)
                    if part.starts_with("_proof_"))
        })
        .map(|(_, info)| {
            let ConstantInfo::Thm(theorem) = info else {
                panic!("an auxiliary proof must be a checked theorem: {info:?}");
            };
            theorem
        })
        .collect()
}

#[test]
fn auxiliary_theorems_close_transitive_hypotheses_and_universes() {
    let source = r#"
universe u
theorem generic (A : Sort u) (P : A → Prop) (x : A) (h : P x) : P x := by
  as_aux_lemma => exact h
theorem introduced (P : Prop) : P → P := by
  intro h
  as_aux_lemma => exact h
theorem nested (P : Prop) (h : P) : P := by
  as_aux_lemma =>
    as_aux_lemma => exact h
theorem explicit_implicit_binder : True := by
  have h : {P : Prop} → P → P := by
    as_aux_lemma => exact fun {P} h => h
  trivial
theorem strict_implicit_binder : True := by
  have h : ⦃P : Prop⦄ → P → P := by
    as_aux_lemma => exact fun ⦃P⦄ h => h
  trivial
"#;
    let checked = checked(&engine(), "closures", source);
    let generic = auxiliaries(&checked, "generic");
    assert_eq!(generic.len(), 1);
    assert_eq!(
        generic[0].base.level_params,
        [Name::from_components(["u_1"])]
    );
    for owner in ["generic", "introduced", "nested"] {
        let lemmas = auxiliaries(&checked, owner);
        assert_eq!(lemmas.len(), 1, "{owner}");
        assert!(!lemmas[0].value.has_fvar());
        assert!(!lemmas[0].value.has_expr_mvar());
        assert!(!lemmas[0].base.type_.has_fvar());
    }
}

#[test]
fn sibling_goals_remain_isolated_and_identical_closures_reuse_a_theorem() {
    let source = r#"
theorem siblings (P Q : Prop) (h : P) (j : Q) : P ∧ Q := by
  constructor
  as_aux_lemma => exact h
  exact j
theorem cached (P : Prop) (h : P) : P ∧ P := by
  constructor
  as_aux_lemma => exact h
  as_aux_lemma => exact h
theorem tagged (P Q : Prop) (h : P) (j : Q) : P ∧ Q := by
  constructor
  as_aux_lemma =>
    case left => exact h
  case right => exact j
"#;
    let checked = checked(&engine(), "siblings", source);
    assert_eq!(auxiliaries(&checked, "siblings").len(), 1);
    assert_eq!(auxiliaries(&checked, "cached").len(), 1);
    assert_eq!(auxiliaries(&checked, "tagged").len(), 1);
}

#[test]
fn failed_and_unsolved_inner_scripts_roll_back_auxiliary_effects() {
    let source = r#"
theorem failed (P : Prop) (h : P) : P := by
  first
  | (as_aux_lemma => exact h); fail
  | exact h
theorem unsolved (P : Prop) (h : P) : P := by
  first
  | as_aux_lemma => skip
  | exact h
"#;
    let checked = checked(&engine(), "rollback", source);
    assert!(auxiliaries(&checked, "failed").is_empty());
    assert!(auxiliaries(&checked, "unsolved").is_empty());
}

#[test]
fn invalid_auxiliary_proofs_never_publish_a_partial_command() {
    let base = engine();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    for (label, source) in [
        (
            "false",
            "theorem invalid : True ∧ False := by\n  constructor\n  as_aux_lemma => trivial\n  as_aux_lemma => trivial",
        ),
        (
            "open_goals",
            "theorem invalid (P : Prop) (h : P) : P := by\n  as_aux_lemma => skip\n  exact h",
        ),
        (
            "sibling_leak",
            "theorem invalid (P : Prop) (h : P) : P ∧ P := by\n  constructor\n  as_aux_lemma =>\n    have secret : P := h\n    exact secret\n  exact secret",
        ),
        (
            "cached_bad_body",
            "theorem invalid (n : Nat) : n = n ∧ n = n := by\n  constructor\n  as_aux_lemma => rfl\n  as_aux_lemma => exact @Eq.refl Nat (n + 1)",
        ),
        (
            "cached_open_goals",
            "theorem invalid (n : Nat) : n = n ∧ n = n := by\n  constructor\n  as_aux_lemma => rfl\n  as_aux_lemma => exact ?_",
        ),
        (
            "implicit_binder_type",
            "theorem invalid : True := by\n  have h : {P : Prop} → P → P := by\n    as_aux_lemma => exact fun {P} h => P\n  trivial",
        ),
    ] {
        reference(label, source, false);
        let error = base
            .check_source_files(
                &[source.as_bytes()],
                &options,
                SourceCheckLimits::new(limits()),
            )
            .expect_err("the complete invalid command must be refused");
        assert_eq!(error.disposition().2, 1, "{label}: {error}");
        assert!(
            matches!(error.disposition().0, "elaboration" | "kernel-rejection"),
            "{label} must reach proof checking: {error}"
        );
        if label == "cached_open_goals" {
            let fln::SourceCheckError::Command { error: cause, .. } = &error else {
                panic!("the auxiliary child must report its open goal: {error}");
            };
            let mut cause = cause.as_ref();
            while let fln::EngineExecutionError::BatchCommand { error, .. } = cause {
                cause = error;
            }
            assert!(
                matches!(
                    cause,
                    fln::EngineExecutionError::Frontend(
                        fln_elab::NatDefinitionFrontendError::Elaborate(
                            fln_elab::NatDefinitionElabError::Inference(
                                fln_elab::source::SourceInferenceError::Tactic(
                                    fln_elab::source::TacticError::UnsolvedGoals { .. }
                                )
                            )
                        )
                    )
                ),
                "a cached theorem cannot discharge an open child goal: {error}"
            );
        }
        assert_eq!(base.logical_root(&options), root);
        assert!(auxiliaries(&base, "invalid").is_empty());
    }
}

#[test]
fn unsupported_closures_are_capability_outcomes_that_alternatives_cannot_hide() {
    let base = engine();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    for (label, tactic) in [
        ("captured_let", "as_aux_lemma => rfl"),
        ("captured_let_try", "try (as_aux_lemma => rfl)"),
        ("captured_let_first", "first | (as_aux_lemma => rfl) | rfl"),
    ] {
        let source = format!(
            "theorem unsupported : True := by\n  let n : Nat := 3\n  have h : n = n := by\n    {tactic}\n  trivial"
        );
        // The pin can abstract this independent let as an ordinary parameter.
        // The native boundary must not report its valid proof as false.
        reference(label, &source, true);
        let error = base
            .check_source_files(
                &[source.as_bytes()],
                &options,
                SourceCheckLimits::new(limits()),
            )
            .expect_err("dependent let closure is a typed unsupported boundary");
        assert_eq!(error.disposition(), ("capability", false, 5), "{error}");
        assert_eq!(base.logical_root(&options), root);
    }
}

#[test]
fn checked_auxiliaries_survive_native_module_import_and_resume() {
    let base = engine();
    let library_name = Name::from_components(["AuxLibrary"]);
    let main_name = Name::from_components(["AuxMain"]);
    let library = b"namespace AuxLibrary\ntheorem identity (P : Prop) (h : P) : P := by as_aux_lemma => exact h\nend AuxLibrary\n";
    let main = b"import AuxLibrary\ntheorem consumer (P : Prop) (h : P) : P := by\n  as_aux_lemma => exact AuxLibrary.identity P h\n";
    let checked = base
        .check_source_modules(
            &[
                SourceModuleInput {
                    name: &library_name,
                    source: library,
                },
                SourceModuleInput {
                    name: &main_name,
                    source: main,
                },
            ],
            &main_name,
            &KVMap::new(),
            SourceModuleCheckLimits::new(SourceCheckLimits::new(limits())),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(
        auxiliaries(&checked.checked.engine, "AuxLibrary.identity").len(),
        1
    );
    assert_eq!(auxiliaries(&checked.checked.engine, "consumer").len(), 1);
    let resumed = Engine::from_environment(checked.checked.engine.environment().clone());
    let source = "theorem resumed (P : Prop) (h : P) : P := by as_aux_lemma => exact consumer P h";
    let after = resumed
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(auxiliaries(&after.engine, "resumed").len(), 1);
}
