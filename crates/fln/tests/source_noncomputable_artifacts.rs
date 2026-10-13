//! Noncomputable restrictions survive actual pinned-format module artifacts.
#![forbid(unsafe_code)]
use fln::{
    Budget, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap, Name, SourceCheckLimits,
};
use std::collections::BTreeSet;
fn n(text: &str) -> Name {
    Name::from_components(text.split('.'))
}
fn admission() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 << 20))
}
fn tags(engine: &Engine) -> BTreeSet<Name> {
    fln_elab::noncomputable::read(engine.environment()).unwrap()
}

#[test]
fn partial_compiler_effects_survive_checked_module_export_and_reimport() {
    use fln::source_check::modules::{SourceModuleCheckLimits, imported::SourceOleanImportLimits};
    use fln::{OleanCheckLimits, OleanModuleInput, OleanWriteBudget, SourceModuleInput};
    // Every exported declaration needs real module provenance, not an ambient
    // source seed. Define the witness interface and data constructors in Lib.
    let base = Engine::builder().build_empty();
    let lib = n("Lib");
    let main = n("Main");
    let library = r#"prelude
universe u
class Inhabited (A : Sort u) where
  default : A
def default {A : Sort u} [inst : Inhabited A] : A := Inhabited.default
inductive Flag where | stop | again
noncomputable def secret : Flag := Flag.again
noncomputable section
partial def recur (flag : Flag) : Flag := match flag with
  | Flag.stop => secret
  | Flag.again => recur Flag.stop
end
"#;
    let consumer =
        b"prelude\nimport Lib\nnoncomputable section\ndef blocked : Flag := recur Flag.stop\nend\n";
    let built = base
        .compile_source_modules(
            &[
                SourceModuleInput {
                    name: &lib,
                    source: library.as_bytes(),
                },
                SourceModuleInput {
                    name: &main,
                    source: consumer,
                },
            ],
            &main,
            &KVMap::new(),
            SourceModuleCheckLimits::new(SourceCheckLimits::new(admission())),
            OleanWriteBudget::default(),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    let inputs: Vec<_> = built
        .artifacts
        .iter()
        .map(|artifact| OleanModuleInput {
            name: &artifact.name,
            artifact: &artifact.bytes,
            server_artifact: None,
            private_artifact: None,
        })
        .collect();
    let imported = base
        .import_olean_modules_for_source(
            &inputs,
            &[main],
            &KVMap::new(),
            SourceOleanImportLimits::new(OleanCheckLimits::new(4 << 20, admission().kernel)),
        )
        .unwrap()
        .into_complete()
        .unwrap()
        .engine;
    assert_eq!(
        tags(&imported),
        BTreeSet::from([n("secret"), n("recur._unsafe_rec"), n("blocked")])
    );
    assert_eq!(tags(&imported), tags(&built.checked.checked.engine));
    for call in ["recur Flag.stop", "blocked"] {
        let error = imported
            .check_source_files(
                &[format!("def leak : Flag := {call}\n").as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(admission()),
            )
            .unwrap_err();
        assert!(error.to_string().contains("noncomputable"), "{error:?}");
    }
    let result = imported
        .execute_source_commands_with_checks(
            b"#eval Flag.again\n",
            &KVMap::new(),
            EngineExecutionLimits::new(admission().kernel),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    let fln::VmExit::Returned(returned) = &result.batch.executions[0].exit else {
        panic!("returned constructor")
    };
    assert_eq!(
        fln::vm_value_kind(&returned.value),
        fln_vm::interpreter::ValueKind::Ctor(1)
    );
}

fn encoded(constants: &[fln::ConstantInfo], tags: Vec<Name>) -> Vec<u8> {
    fln_olean::write::source::encode_module_with_source_metadata(
        fln::OleanModuleWriteInput {
            is_module: false,
            imports: &[],
            constants,
            extra_const_names: &[],
        },
        &fln_olean::write::source::SourceMetadata {
            noncomputable: tags,
            ..Default::default()
        },
        fln::OleanWriteHeader {
            version: fln::OLEAN_ACCEPTED_VERSIONS[0],
            flags: 1,
            lean_version: fln::OLEAN_PIN_TAG.strip_prefix('v').unwrap(),
            githash: fln::OLEAN_PIN_COMMIT,
            base_addr: fln::OLEAN_REGION_ALIGN as u64 * 2,
        },
        fln::OleanWriteBudget::default(),
    )
    .unwrap()
    .bytes
}
fn seed() -> Engine {
    Engine::with_source_seed(admission())
        .unwrap()
        .into_complete()
        .unwrap()
}
fn constant(value: fln::Expr) -> fln::ConstantInfo {
    fln::ConstantInfo::Defn(fln::DefinitionVal {
        base: fln::ConstantVal {
            name: n("owned"),
            level_params: vec![],
            type_: fln::Expr::const_(n("Nat"), vec![]),
        },
        value,
        hints: fln::ReducibilityHints::Regular(1),
        safety: fln::DefinitionSafety::Safe,
        all: vec![n("owned")],
    })
}
fn import_limits() -> fln::source_check::modules::imported::SourceOleanImportLimits {
    fln::source_check::modules::imported::SourceOleanImportLimits::new(fln::OleanCheckLimits::new(
        4 << 20,
        admission().kernel,
    ))
}
fn import(
    base: &Engine,
    bytes: &[u8],
    limits: fln::source_check::modules::imported::SourceOleanImportLimits,
) -> Result<
    fln::Outcome<fln::source_check::modules::imported::SourceOleanImport>,
    fln::source_check::modules::imported::SourceOleanImportError,
> {
    let name = n("Library");
    base.import_olean_modules_for_source(
        &[fln::OleanModuleInput {
            name: &name,
            artifact: bytes,
            server_artifact: None,
            private_artifact: None,
        }],
        std::slice::from_ref(&name),
        &KVMap::new(),
        limits,
    )
}

#[test]
fn owning_module_tags_activate_only_after_the_constant_passes_both_checkers() {
    let base = seed();
    let good = constant(fln::Expr::lit(fln::Literal::Nat(fln::NatLit::from_u64(41))));
    let bytes = encoded(&[good], vec![n("owned")]);
    let imported = import(&base, &bytes, import_limits())
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(imported.modules[0].noncomputable, 1);
    assert!(
        !imported.modules[0]
            .uninterpreted
            .contains(&n("Lean.noncomputableExt"))
    );
    assert_eq!(tags(&imported.engine), BTreeSet::from([n("owned")]));
    let checked = imported
        .engine
        .check_source_files(
            &[b"theorem logical : owned = 41 := by rfl\n"],
            &KVMap::new(),
            SourceCheckLimits::new(admission()),
        )
        .unwrap()
        .into_complete()
        .unwrap()
        .engine;
    assert!(checked.environment().contains(&n("logical")));
    assert!(
        checked
            .execute_source_commands_with_checks(
                b"#eval owned\n",
                &KVMap::new(),
                EngineExecutionLimits::new(admission().kernel)
            )
            .is_err()
    );
    assert!(tags(&base).is_empty() && !base.environment().contains(&n("owned")));
    let wrong = encoded(
        &[constant(fln::Expr::const_(n("Bool.true"), vec![]))],
        vec![n("owned")],
    );
    assert!(
        import(&base, &wrong, import_limits()).is_err(),
        "metadata must not bypass a false constant type"
    );
    assert!(tags(&base).is_empty() && !base.environment().contains(&n("owned")));
}

#[test]
fn tags_cannot_reclassify_an_ambient_or_missing_declaration() {
    let base = seed();
    let before = base.logical_root(&KVMap::new());
    for name in [n("Nat"), n("absent")] {
        let bytes = encoded(&[], vec![name]);
        let error = import(&base, &bytes, import_limits()).unwrap_err();
        assert!(
            matches!(
                error,
                fln::source_check::modules::imported::SourceOleanImportError::Metadata { .. }
            ),
            "{error:?}"
        );
        assert_eq!(base.logical_root(&KVMap::new()), before);
        assert!(tags(&base).is_empty());
    }
}

#[test]
fn exhausted_tag_decode_publishes_nothing_and_a_fresh_retry_succeeds() {
    let base = seed();
    let bytes = encoded(
        &[constant(fln::Expr::lit(fln::Literal::Nat(
            fln::NatLit::from_u64(41),
        )))],
        vec![n("owned")],
    );
    let before = base.logical_root(&KVMap::new());
    let mut limits = import_limits();
    limits.metadata.max_entries = 0;
    assert!(matches!(
        import(&base, &bytes, limits),
        Err(fln::source_check::modules::imported::SourceOleanImportError::Limit(_))
    ));
    assert_eq!(base.logical_root(&KVMap::new()), before);
    assert!(tags(&base).is_empty());
    assert_eq!(
        tags(
            &import(&base, &bytes, import_limits())
                .unwrap()
                .into_complete()
                .unwrap()
                .engine
        ),
        BTreeSet::from([n("owned")])
    );
}

#[test]
fn diamond_imports_export_each_modules_own_tags_once() {
    use fln::source_check::modules::SourceModuleCheckLimits;
    let base = Engine::builder().build_empty();
    let names = ["Core", "Left", "Right", "Main"].map(n);
    let sources: [&[u8]; 4] = [
        b"prelude\ninductive Flag where | stop | again\nnoncomputable def secret : Flag := Flag.again\n",
        b"prelude\nimport Core\nnoncomputable section\ndef left : Flag := secret\nend\n",
        b"prelude\nimport Core\nnoncomputable section\ndef right : Flag := secret\nend\n",
        b"prelude\nimport Left\nimport Right\nnoncomputable section\ndef selected : Flag := left\nend\n",
    ];
    let inputs: Vec<_> = names
        .iter()
        .zip(sources)
        .map(|(name, source)| fln::SourceModuleInput { name, source })
        .collect();
    let build = base
        .compile_source_modules(
            &inputs,
            &names[3],
            &KVMap::new(),
            SourceModuleCheckLimits::new(SourceCheckLimits::new(admission())),
            fln::OleanWriteBudget::default(),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(build.artifacts.len(), 4);
    for artifact in &build.artifacts {
        let blocks = fln_olean::region::OleanView::parse(&artifact.bytes)
            .unwrap()
            .extension_payloads(fln::OleanWalkBudget::default(), 4 << 20)
            .unwrap();
        let decoded = fln_olean::source_extensions::decode(
            &blocks,
            fln_olean::source_extensions::DecodeLimits::default(),
        )
        .unwrap();
        assert_eq!(
            decoded.noncomputable.len(),
            1,
            "{}",
            artifact.name.to_display_string()
        );
    }
    let artifacts: Vec<_> = build
        .artifacts
        .iter()
        .map(|artifact| fln::OleanModuleInput {
            name: &artifact.name,
            artifact: &artifact.bytes,
            server_artifact: None,
            private_artifact: None,
        })
        .collect();
    let imported = base
        .import_olean_modules_for_source(&artifacts, &names[3..], &KVMap::new(), import_limits())
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(
        imported
            .modules
            .iter()
            .map(|report| report.noncomputable)
            .sum::<usize>(),
        4
    );
    assert_eq!(
        tags(&imported.engine),
        ["secret", "left", "right", "selected"]
            .map(n)
            .into_iter()
            .collect()
    );
    assert!(base.environment().is_empty());
}
