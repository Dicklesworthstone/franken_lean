//! Native proof tactics in public modules evaluate with checked implementations
//! while source lookup and exported auxiliary signatures keep their public world.
#![forbid(unsafe_code)]

use fln::source_check::modules::{
    SourceModuleCheckError, SourceModuleCheckLimits,
    execution::{SourceProgramExecution, SourceProgramLimits},
    imported::{SourceOleanImport, SourceOleanImportLimits},
};
use fln::{
    Budget, ConstantInfo, Declaration, Engine, EngineAdmissionLimits, EngineExecutionLimits,
    Environment, KVMap, Name, OleanCheckLimits, OleanModuleInput, Outcome, SourceCheckLimits,
    SourceModuleInput,
};
use std::path::{Path, PathBuf};

const STACK: usize = 256 * 1024 * 1024;

fn n(text: &str) -> Name {
    Name::from_components(text.split('.'))
}

fn private(module: &str, declaration: &str) -> Name {
    Name::num(n(&format!("_private.{module}")), 0).append_core(&n(declaration))
}

fn execute(
    imported: &SourceOleanImport,
    files: &[(&str, &str)],
    stack: usize,
) -> Result<Outcome<SourceProgramExecution>, SourceModuleCheckError> {
    let names: Vec<_> = files.iter().map(|(name, _)| n(name)).collect();
    let inputs: Vec<_> = files
        .iter()
        .zip(&names)
        .map(|((_, source), name)| SourceModuleInput {
            name,
            source: source.as_bytes(),
        })
        .collect();
    imported.execute_source_modules(
        &inputs,
        &names[0],
        &KVMap::new(),
        SourceProgramLimits::new(EngineExecutionLimits::for_stack_bytes(stack)),
        None,
    )
}

fn native_axioms(engine: &Engine, owner: &Name) -> Vec<Name> {
    let prefix = owner.append_core(&n("_native"));
    engine
        .environment()
        .constants()
        .filter(|(name, info)| {
            name.parent().parent() == prefix && matches!(info, ConstantInfo::Axiom(_))
        })
        .map(|(name, _)| name.clone())
        .collect()
}

fn source_inference(
    error: &SourceModuleCheckError,
) -> Option<&fln_elab::source::SourceInferenceError> {
    let SourceModuleCheckError::Source {
        error: fln::SourceCheckError::Command { error, .. },
        ..
    } = error
    else {
        return None;
    };
    match error.as_ref() {
        fln::EngineExecutionError::Frontend(fln::DefinitionFrontendError::Elaborate(
            fln_elab::NatDefinitionElabError::Inference(error),
        )) => Some(error),
        _ => None,
    }
}

#[test]
fn public_native_decide_requires_its_syntax_import() {
    // An execution provider does not install syntax. This source-only module
    // must retain the ordinary missing-Init.Tactics boundary even when its
    // declaration has an otherwise valid direct proof.
    const BASE: &str = "prelude
inductive False : Prop
inductive Truth : Prop where
| make
class inductive Decidable (P : Prop) : Type where
| isFalse (proof : P -> False)
| isTrue (proof : P)
class Law : Prop where
  proof : Truth
";
    const PREFIX: &str = "module
prelude
public import Base
private noncomputable instance secret : Decidable Truth := Decidable.isTrue Truth.make
";
    let options = KVMap::new();
    let imported = SourceOleanImport::empty(&options);
    let before = imported.engine.logical_root(&options);
    let good = format!("{PREFIX}@[expose] public instance publicLaw : Law := Law.mk Truth.make");
    let control = execute(
        &imported,
        &[("Api", &good), ("Base", BASE)],
        2 * 1024 * 1024,
    );
    assert!(
        matches!(control, Ok(Outcome::Complete(_))),
        "the same public declaration with a direct proof must check: {control:?}"
    );
    let bad =
        format!("{PREFIX}@[expose] public instance publicLaw : Law := Law.mk (by native_decide)");
    let error = execute(&imported, &[("Api", &bad), ("Base", BASE)], 2 * 1024 * 1024).unwrap_err();
    assert!(
        matches!(source_inference(&error),
            Some(fln_elab::source::SourceInferenceError::UnknownConstant(name))
                if name == &n("Lean.Parser.Tactic.nativeDecide")),
        "{error:?}"
    );
    assert_eq!(imported.engine.logical_root(&options), before);
    assert!(imported.engine.environment().is_empty());
}

fn pinned_lib() -> Option<PathBuf> {
    let lib = std::env::var_os("FLN_REFERENCE_LIB")
        .map(PathBuf::from)
        .or_else(|| {
            std::env::var_os("HOME").map(|home| {
                PathBuf::from(home)
                    .join(".elan/toolchains")
                    .join(format!("leanprover--lean4---{}", fln::OLEAN_PIN_TAG))
                    .join("lib/lean")
            })
        })
        .filter(|lib| lib.join("Init/Tactics.olean").is_file());
    assert!(
        lib.is_some() || std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
        "FLN_REQUIRE_REFERENCE is set but the pinned Reference library is absent"
    );
    if lib.is_none() {
        eprintln!("SKIP: pinned Reference lib/lean absent (set FLN_REQUIRE_REFERENCE=1 to fail)");
    }
    lib
}

fn import_pinned(lib: &Path) -> SourceOleanImport {
    let names: Vec<_> = ["Init.Prelude", "Init.Coe", "Init.Notation", "Init.Tactics"]
        .into_iter()
        .map(n)
        .collect();
    let parts: Vec<[Vec<u8>; 3]> = names
        .iter()
        .map(|name| {
            let base = name
                .to_display_string()
                .split('.')
                .fold(lib.to_path_buf(), |path, part| path.join(part))
                .with_extension("olean");
            [
                std::fs::read(&base).expect("pinned public artifact"),
                std::fs::read(base.with_extension("olean.server")).expect("pinned server artifact"),
                std::fs::read(base.with_extension("olean.private"))
                    .expect("pinned private artifact"),
            ]
        })
        .collect();
    let inputs: Vec<_> = names
        .iter()
        .zip(&parts)
        .map(|(name, [public, server, private])| OleanModuleInput {
            name,
            artifact: public,
            server_artifact: Some(server),
            private_artifact: Some(private),
        })
        .collect();
    Engine::from_environment(Environment::new())
        .import_olean_modules_for_source(
            &inputs,
            &[n("Init.Tactics")],
            &KVMap::new(),
            SourceOleanImportLimits::new(OleanCheckLimits::new(
                256 * 1024 * 1024,
                Budget::for_stack_bytes(STACK),
            )),
        )
        .unwrap()
        .into_complete()
        .unwrap()
}

#[test]
fn native_module_auxiliaries_execute_checked_bodies_and_export_only_permitted_axioms() {
    let Some(lib) = pinned_lib() else {
        return;
    };
    std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(move || {
            let imported = import_pinned(&lib);
            let options = KVMap::new();
            let before = imported.engine.logical_root(&options);
            const HEADER: &str = "module\nprelude\npublic import Init.Tactics\n";
            let api = format!(
                "{HEADER}public def publicValue : Nat := 41
private def privateValue : Nat := 41
public theorem hidden : publicValue = 41 := by native_decide
public theorem viaDecide : 2 + 2 = 4 := by decide +native
public def hiddenData : Fin 42 := by
  have saved : privateValue = 41 := by native_decide
  exact ⟨41, by native_decide⟩
@[expose] public def exposedData : Fin 42 := ⟨41, by native_decide⟩
public class Witness : Prop where
  proof : publicValue = 41
@[expose] public instance witness : Witness := ⟨by native_decide⟩
public instance finInhabited : Inhabited (Fin 42) := ⟨⟨41, by native_decide⟩⟩
"
            );
            let main = "module
prelude
public import Api
public theorem useHidden : publicValue = 41 := hidden
public theorem useWitness : publicValue = 41 := @Witness.proof witness
public theorem useExposedData : exposedData.val = 41 := by rfl
";
            let result = execute(&imported, &[("Main", main), ("Api", &api)], STACK)
                .unwrap()
                .into_complete()
                .unwrap();
            let local = &result
                .modules
                .iter()
                .find(|module| module.module == n("Api"))
                .unwrap()
                .commands
                .batch;
            let client = &result.modules.last().unwrap().commands.batch.engine;
            assert!(matches!(
                local.engine.environment().find(&n("publicValue")),
                Some(ConstantInfo::Defn(_))
            ));
            assert!(matches!(
                client.environment().find(&n("publicValue")),
                Some(ConstantInfo::Axiom(_))
            ));
            assert!(!client.environment().contains(&private("Api", "privateValue")));

            for (owner, hidden, expected) in [
                ("hidden", true, 1),
                ("viaDecide", true, 1),
                ("hiddenData", true, 2),
                ("exposedData", false, 1),
                ("witness", false, 1),
                ("finInhabited", false, 1),
            ] {
                let prefix = if hidden {
                    private("Api", owner)
                } else {
                    n(owner)
                };
                let axioms = native_axioms(&local.engine, &prefix);
                assert_eq!(axioms.len(), expected, "{owner}: {axioms:?}");
                for axiom in axioms {
                    let Some(ConstantInfo::Axiom(accepted)) =
                        local.engine.environment().find(&axiom)
                    else {
                        panic!("native proof support must retain explicit axiom evidence");
                    };
                    let receipts: Vec<_> = local
                        .source_admissions
                        .iter()
                        .flat_map(|command| &command.admission.admissions)
                        .filter(|row| {
                            matches!(&row.declaration, Declaration::Axiom(value)
                                if value.base.name == axiom)
                        })
                        .collect();
                    assert_eq!(receipts.len(), 1, "{axiom:?}");
                    assert_eq!(receipts[0].declaration, Declaration::Axiom(accepted.clone()));
                    if hidden {
                        assert!(!client.environment().contains(&axiom), "{axiom:?}");
                    } else {
                        assert_eq!(
                            client.environment().find(&axiom),
                            Some(&ConstantInfo::Axiom(accepted.clone()))
                        );
                    }
                }
                let native = prefix.append_core(&n("_native"));
                assert!(
                    !local.engine.environment().constants().any(|(name, _)| {
                        name.parent().parent() == native
                            && matches!(name.leaf_view(), fln_core::name::LeafView::Str(part)
                                if part.starts_with("decl_"))
                    }),
                    "the compiled Bool scratch definition must not be published"
                );
            }

            for (source, reason) in [
                (
                    format!("{HEADER}public theorem falseProof : 2 + 2 = 5 := by native_decide"),
                    "NativeDecideFalse",
                ),
                (
                    format!("{HEADER}private def secret : Nat := 41\n@[expose] public def invalid : Fin 42 := by\n  have leaked : secret = 41 := by native_decide\n  exact ⟨41, by native_decide⟩"),
                    "Unknown identifier `secret`",
                ),
            ] {
                let error = execute(&imported, &[("Api", &source)], STACK).unwrap_err();
                let rendered = format!("{error:?} {error}");
                assert!(rendered.contains(reason), "{rendered}");
                assert!(!rendered.contains("Unavailable"), "{rendered}");
                assert_eq!(imported.engine.logical_root(&options), before);
            }

            // The native provider can execute private implementations, but an
            // exposed body's instance search still uses only public entries.
            let dictionary_prefix = format!(
                "{HEADER}public inductive NativeTruth : Prop where
| make
public class NativeLaw : Prop where
  proof : NativeTruth
private instance secretDecision : Decidable NativeTruth := Decidable.isTrue NativeTruth.make
"
            );
            let direct = format!(
                "{dictionary_prefix}@[expose] public instance publicLaw : NativeLaw := NativeLaw.mk NativeTruth.make"
            );
            let control = execute(&imported, &[("Api", &direct)], STACK);
            assert!(matches!(control, Ok(Outcome::Complete(_))), "{control:?}");
            let private_dictionary = format!(
                "{dictionary_prefix}@[expose] public instance publicLaw : NativeLaw := NativeLaw.mk (by native_decide)"
            );
            let error = execute(&imported, &[("Api", &private_dictionary)], STACK).unwrap_err();
            assert!(
                matches!(source_inference(&error),
                    Some(fln_elab::source::SourceInferenceError::InstanceSynthesisRequired(_))),
                "{error:?}"
            );
            assert_eq!(imported.engine.logical_root(&options), before);

            // Real syntax and dictionaries do not grant a checking-only API
            // the capability to execute a native proof.
            let module = n("Api");
            let checked_only = format!(
                "{HEADER}public theorem checkedOnly : 2 + 2 = 4 := by native_decide"
            );
            let error = imported
                .check_source_modules(
                    &[SourceModuleInput {
                        name: &module,
                        source: checked_only.as_bytes(),
                    }],
                    &module,
                    &options,
                    SourceModuleCheckLimits::new(SourceCheckLimits::new(
                        EngineAdmissionLimits::new(Budget::for_stack_bytes(STACK)),
                    )),
                    None,
                )
                .unwrap_err();
            assert_eq!(error.disposition(), ("capability", false, 5));
            assert!(
                matches!(source_inference(&error),
                    Some(fln_elab::source::SourceInferenceError::NativeEvaluation(
                        fln_elab::native::NativeEvaluationError::Unavailable
                    ))),
                "{error:?}"
            );
            assert_eq!(imported.engine.logical_root(&options), before);
        })
        .expect("spawn the checking thread")
        .join()
        .expect("the checking thread completes");
}
