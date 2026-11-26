//! Inline simp attributes use the admitted identity of named and anonymous instances.
#![forbid(unsafe_code)]

use fln::source_check::SourceCheckError;
use fln::{
    Budget, ConstantInfo, DefinitionFrontendError, Engine, EngineAdmissionLimits,
    EngineExecutionError, KVMap, Name, SourceCheckLimits, SourceFileCheck,
};
use fln_elab::source::{SourceInferenceError, TacticError, scope::simp};
use fln_elab::{NatDefinitionElabError, instances::InstanceRegistry};
use std::io::Write;
use std::path::PathBuf;
use std::process::{Command, Stdio};
use std::sync::OnceLock;

fn n(text: &str) -> Name {
    Name::from_components(text.split('.'))
}

fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}

fn base() -> Engine {
    Engine::with_source_seed(limits())
        .unwrap()
        .into_complete()
        .unwrap()
}

fn checked(source: &str) -> SourceFileCheck {
    let checked = base()
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        )
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .unwrap();
    reference_verdict(source, true);
    checked
}

fn owner(checked: &SourceFileCheck, class: &str, explicit: bool) -> Name {
    let registry = InstanceRegistry::read(checked.engine.environment()).unwrap();
    let [entry] = registry.candidates(&n(class)) else {
        panic!("the command must register exactly its checked instance");
    };
    assert_eq!(entry.priority, 610);
    assert_eq!(entry.declaration.parent(), n("Rules"));
    if explicit {
        assert_eq!(entry.declaration, n("Rules.supplied"));
    }
    let rules = simp::read(checked.engine.environment()).unwrap();
    let selected: Vec<_> = rules
        .iter()
        .filter(|rule| rule.declaration == entry.declaration)
        .collect();
    assert_eq!(selected.len(), 1);
    assert_eq!(selected[0].priority, 710);
    assert!(!selected[0].reverse);
    entry.declaration.clone()
}

#[test]
fn named_and_anonymous_proof_instances_supply_simp_theorems() {
    for explicit in [true, false] {
        let written_name = if explicit { "supplied " } else { "" };
        let source = format!(
            "class SimpProof : Prop where\n  proof : True\n\
             namespace Rules\n\
             @[simp 710] instance (priority := 610) {written_name}: SimpProof := {{ proof := True.intro }}\n\
             end Rules\n\
             theorem automatic : SimpProof := by simp\n"
        );
        let checked = checked(&source);
        let name = owner(&checked, "SimpProof", explicit);
        assert!(matches!(
            checked.engine.environment().find(&name),
            Some(ConstantInfo::Thm(_))
        ));
    }
}

#[test]
fn named_and_anonymous_data_instances_supply_unfolding_rules() {
    for explicit in [true, false] {
        let written_name = if explicit { "supplied " } else { "" };
        // Default simp skips instance-implicit arguments of class projections.
        // Compare the dictionary itself so its registered unfolding is needed.
        let source = format!(
            "class SimpData : Type where\n  marker : Nat\n\
             namespace Rules\n\
             @[simp 710] instance (priority := 610) {written_name}: SimpData := {{ marker := 7 }}\n\
             end Rules\n\
             theorem automatic : (inferInstance : SimpData) = SimpData.mk 7 := by simp\n"
        );
        let checked = checked(&source);
        let name = owner(&checked, "SimpData", explicit);
        assert!(matches!(
            checked.engine.environment().find(&name),
            Some(ConstantInfo::Defn(_))
        ));
        // Instance synthesis still succeeds without the attribute, but simp's
        // default transparency must not unfold the resulting dictionary.
        let unregistered = source.replacen("@[simp 710] ", "", 1);
        let error = base()
            .check_source_files(
                &[unregistered.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits()),
            )
            .expect_err("the data instance must need its registered simp rule");
        let SourceCheckError::Command { error, .. } = error else {
            panic!("the unregistered dictionary must reach simplification");
        };
        assert!(
            matches!(
                error.as_ref(),
                EngineExecutionError::Frontend(DefinitionFrontendError::Elaborate(
                    NatDefinitionElabError::Inference(SourceInferenceError::Tactic(
                        TacticError::SimplificationNoProgress | TacticError::UnsolvedGoals { .. }
                    ))
                ))
            ),
            "{unregistered}\n{error:?}"
        );
        reference_verdict(&unregistered, false);
    }
}

#[test]
fn reversed_data_instance_rules_are_refused_without_publishing_metadata() {
    let source = "class SimpData : Type where\n  marker : Nat\n\
                  @[simp ←] instance supplied : SimpData := { marker := 7 }\n";
    let base = base();
    let options = KVMap::new();
    let before = base.logical_root(&options);
    let error = base
        .check_source_files(
            &[source.as_bytes()],
            &options,
            SourceCheckLimits::new(limits()),
        )
        .unwrap_err();
    let SourceCheckError::Command { error, .. } = error else {
        panic!("the admitted data instance must reach simp's direction validation");
    };
    assert!(matches!(
        *error,
        EngineExecutionError::Frontend(DefinitionFrontendError::Elaborate(
            NatDefinitionElabError::Inference(SourceInferenceError::SimpSet(
                simp::SimpSetError::UnsupportedDeclaration(ref name)
            ))
        )) if name == &n("supplied")
    ));
    assert_eq!(base.logical_root(&options), before);
    assert!(!base.environment().contains(&n("supplied")));
    reference_verdict(source, false);
}

fn reference_verdict(source: &str, accepted: bool) {
    static REFERENCE: OnceLock<Option<PathBuf>> = OnceLock::new();
    let reference = REFERENCE.get_or_init(|| {
        let executable = std::env::var_os("FLN_REFERENCE_LEAN")
            .or_else(|| std::env::var_os("FLN_REFERENCE_BIN"))
            .map(PathBuf::from)
            .or_else(|| {
                std::env::var_os("FLN_REFERENCE_LIB").and_then(|lib| {
                    PathBuf::from(lib)
                        .parent()?
                        .parent()
                        .map(|root| root.join("bin/lean"))
                })
            })
            .or_else(|| {
                std::env::var_os("HOME").map(|home| {
                    PathBuf::from(home)
                        .join(".elan/toolchains")
                        .join(format!("leanprover--lean4---{}", fln::OLEAN_PIN_TAG))
                        .join("bin/lean")
                })
            })
            .filter(|path| path.is_file());
        let Some(executable) = executable else {
            assert!(
                std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
                "the pinned Reference executable is required"
            );
            eprintln!("SKIP: simp-instance differential requires the pinned Reference");
            return None;
        };
        let identity = Command::new(&executable).arg("--githash").output().unwrap();
        assert!(identity.status.success());
        assert_eq!(
            String::from_utf8_lossy(&identity.stdout).trim(),
            fln_olean::format::PIN_COMMIT
        );
        Some(executable)
    });
    let Some(reference) = reference else {
        return;
    };
    let mut child = Command::new(reference)
        .arg("--stdin")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    child
        .stdin
        .take()
        .unwrap()
        .write_all(source.as_bytes())
        .unwrap();
    let result = child.wait_with_output().unwrap();
    assert_eq!(
        result.status.success(),
        accepted,
        "{source}\n{}{}",
        String::from_utf8_lossy(&result.stdout),
        String::from_utf8_lossy(&result.stderr)
    );
}
