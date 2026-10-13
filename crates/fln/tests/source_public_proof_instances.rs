//! Public proof instances retain checked theorems privately and export only
//! their checked interfaces, while ordinary data dictionaries remain exposed.
#![forbid(unsafe_code)]

use fln::source_check::inspect::{ObservationKind, SourceObservation};
use fln::source_check::modules::{
    SourceModuleCacheLimits, SourceModuleCheck, SourceModuleCheckError, SourceModuleCheckLimits,
    SourceModuleSession, execution::SourceProgramLimits,
};
use fln::{
    Budget, ConstantInfo, DefinitionSafety, Engine, EngineAdmissionLimits, EngineExecutionLimits,
    Expr, ExprNode, KVMap, Name, Outcome, SourceCheckLimits, SourceModuleInput,
};
use fln_elab::instances::InstanceRegistry;
use fln_elab::reducibility::{Reducibility, ReducibilityTable};

fn n(value: &str) -> Name {
    Name::from_components(value.split('.'))
}

fn private(module: &str, declaration: &str) -> Name {
    Name::num(n(&format!("_private.{module}")), 0).append_core(&n(declaration))
}

fn limits() -> SourceModuleCheckLimits {
    SourceModuleCheckLimits::new(SourceCheckLimits::new(EngineAdmissionLimits::new(
        Budget::for_stack_bytes(2 * 1024 * 1024),
    )))
}

fn session() -> SourceModuleSession {
    SourceModuleSession::new(
        Engine::builder().build_empty(),
        KVMap::new(),
        limits(),
        SourceModuleCacheLimits::default(),
    )
}

fn check(files: &[(&str, &str)]) -> Result<Outcome<SourceModuleCheck>, SourceModuleCheckError> {
    let names: Vec<_> = files.iter().map(|(name, _)| n(name)).collect();
    let modules: Vec<_> = files
        .iter()
        .zip(&names)
        .map(|((_, source), name)| SourceModuleInput {
            name,
            source: source.as_bytes(),
        })
        .collect();
    Engine::builder().build_empty().check_source_modules(
        &modules,
        &names[0],
        &KVMap::new(),
        limits(),
    )
}

fn checked(files: &[(&str, &str)]) -> SourceModuleCheck {
    check(files)
        .unwrap_or_else(|error| panic!("{files:?}: {error:?}"))
        .into_complete()
        .unwrap()
}

fn references(expr: &Expr, target: &Name) -> bool {
    let mut pending = vec![expr];
    while let Some(expr) = pending.pop() {
        match expr.node() {
            ExprNode::Const { name, .. } if name == target => return true,
            ExprNode::App { f, a } => pending.extend([f, a]),
            ExprNode::Lam {
                binder_type, body, ..
            }
            | ExprNode::ForallE {
                binder_type, body, ..
            } => pending.extend([binder_type, body]),
            ExprNode::LetE {
                type_, value, body, ..
            } => pending.extend([type_, value, body]),
            ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => pending.push(expr),
            _ => {}
        }
    }
    false
}

const BASE: &str = "prelude\ninductive Truth : Prop where\n| make\nclass Law (P : Prop) : Prop where\n  proof : P\ndef chosenLaw (P : Prop) [law : Law P] : Law P := law\ninductive Token where\n| left\n| right\nclass Pick where\n  value : Token\ndef chosen [p : Pick] : Token := p.value";
const HEADER: &str = "module\nprelude\npublic import Base\n";
const SECRET: &str = "prelude\nimport Base\ndef hiddenProof : Truth := Truth.make\ndef Hidden (P : Prop) : Prop := P\ninductive Secret : Prop where\n| make";
const API: &str = "module\nprelude\npublic import Base\nimport Secret\nnamespace API\ndef localProof : Truth := hiddenProof\npublic instance witness : Law Truth := Law.mk localProof\nend API";
const MAIN: &str =
    "prelude\nimport Api\ntheorem client : Truth := @Law.proof Truth (chosenLaw Truth)";

#[test]
fn private_checked_theorems_export_safe_proof_interfaces_and_instance_metadata() {
    let local = checked(&[("Api", API), ("Secret", SECRET), ("Base", BASE)]);
    let local_env = local.checked.engine.environment();
    let Some(ConstantInfo::Thm(proof)) = local_env.find(&n("API.witness")) else {
        panic!("the defining module must retain the checked proof theorem");
    };
    assert!(references(&proof.value, &private("Api", "API.localProof")));
    assert_eq!(
        ReducibilityTable::effective(local_env)
            .unwrap()
            .status(&n("API.witness")),
        Reducibility::Semireducible
    );

    let imported = checked(&[
        ("Main", MAIN),
        ("Api", API),
        ("Secret", SECRET),
        ("Base", BASE),
    ]);
    let env = imported.checked.engine.environment();
    let Some(ConstantInfo::Axiom(interface)) = env.find(&n("API.witness")) else {
        panic!("the importer must receive only the checked proof interface");
    };
    assert!(!interface.is_unsafe);
    assert_eq!(interface.base, proof.base);
    assert!(matches!(env.find(&n("client")), Some(ConstantInfo::Thm(_))));
    assert!(matches!(
        env.find(&n("Law.proof")),
        Some(ConstantInfo::Thm(_))
    ));
    assert!(!env.contains(&n("hiddenProof")));
    assert!(!env.contains(&private("Api", "API.localProof")));
    let registry = InstanceRegistry::read(env).unwrap();
    let [instance] = registry.candidates(&n("Law")) else {
        panic!("exactly the published proof instance must be registered");
    };
    assert_eq!(instance.declaration, n("API.witness"));
    assert_eq!(instance.priority, 1000);
    assert_eq!(
        ReducibilityTable::effective(env)
            .unwrap()
            .status(&instance.declaration),
        Reducibility::Semireducible
    );
}

#[test]
fn literal_infer_instance_consumes_an_imported_proof_interface() {
    let base = Engine::with_source_seed(limits().source.admission)
        .unwrap()
        .into_complete()
        .unwrap();
    let names = [n("Main"), n("Api")];
    let sources = [
        "prelude\nimport Api\ntheorem proof : True := @Law.proof True (inferInstance : Law True)",
        "module\nprelude\npublic class Law (P : Prop) : Prop where\n  proof : P\nprivate theorem hidden : True := True.intro\npublic instance lawful : Law True := Law.mk hidden",
    ];
    let inputs: Vec<_> = names
        .iter()
        .zip(sources)
        .map(|(name, source)| SourceModuleInput {
            name,
            source: source.as_bytes(),
        })
        .collect();
    let result = base
        .check_source_modules(&inputs, &names[0], &KVMap::new(), limits())
        .unwrap()
        .into_complete()
        .unwrap();
    assert!(matches!(
        result.checked.engine.environment().find(&n("lawful")),
        Some(ConstantInfo::Axiom(_))
    ));
    assert!(matches!(
        result.checked.engine.environment().find(&n("proof")),
        Some(ConstantInfo::Thm(_))
    ));
}

#[test]
fn executable_module_route_retains_checked_proofs_and_replays_only_interfaces() {
    let names = [n("Main"), n("Api"), n("Secret"), n("Base")];
    let modules: Vec<_> = names
        .iter()
        .zip([MAIN, API, SECRET, BASE])
        .map(|(name, source)| SourceModuleInput {
            name,
            source: source.as_bytes(),
        })
        .collect();
    let options = KVMap::new();
    let executed = fln::source_check::modules::imported::SourceOleanImport::empty(&options)
        .execute_source_modules(
            &modules,
            &names[0],
            &options,
            SourceProgramLimits::new(EngineExecutionLimits::new(limits().source.admission.kernel)),
            None,
        )
        .unwrap()
        .into_complete()
        .unwrap();
    let api = executed
        .modules
        .iter()
        .find(|module| module.module == n("Api"))
        .unwrap();
    let Some(ConstantInfo::Thm(proof)) = api
        .commands
        .batch
        .engine
        .environment()
        .find(&n("API.witness"))
    else {
        panic!("the executable route must retain the checked proof theorem");
    };
    let receipts: Vec<_> = api.commands.batch.source_admissions.iter()
        .flat_map(|command| &command.admission.admissions)
        .filter(|row| matches!(&row.declaration, fln::Declaration::Thm(theorem) if theorem.base.name == n("API.witness")))
        .collect();
    let [receipt] = receipts.as_slice() else {
        panic!("the private theorem must have exactly one dual-check receipt");
    };
    assert_eq!(&receipt.declaration, &fln::Declaration::Thm(proof.clone()));
    assert!(api.commands.batch.executions.is_empty());

    let secret = executed
        .modules
        .iter()
        .find(|module| module.module == n("Secret"))
        .unwrap();
    let Some(ConstantInfo::Defn(helper)) = secret
        .commands
        .batch
        .engine
        .environment()
        .find(&n("hiddenProof"))
    else {
        panic!("an authored proof-valued def must preserve its declaration kind");
    };
    assert_eq!(helper.safety, DefinitionSafety::Safe);
    assert!(references(&helper.value, &n("Truth.make")));
    let receipts: Vec<_> = secret.commands.batch.source_admissions.iter()
        .flat_map(|command| &command.admission.admissions)
        .filter(|row| matches!(&row.declaration, fln::Declaration::Defn(definition) if definition.base.name == n("hiddenProof")))
        .collect();
    let [receipt] = receipts.as_slice() else {
        panic!("the ordinary proof def must have exactly one dual-check receipt");
    };
    assert_eq!(
        &receipt.declaration,
        &fln::Declaration::Defn(helper.clone())
    );
    assert!(
        secret.commands.batch.executions.is_empty(),
        "proof-valued source definitions must not enter the VM"
    );
    let client = executed.modules.last().unwrap();
    assert!(matches!(
        client.commands.batch.engine.environment().find(&n("API.witness")),
        Some(ConstantInfo::Axiom(interface)) if !interface.is_unsafe && interface.base == proof.base
    ));
    assert_eq!(
        InstanceRegistry::read(client.commands.batch.engine.environment())
            .unwrap()
            .candidates(&n("Law"))
            .len(),
        1
    );
    let checked = checked(&[
        ("Main", MAIN),
        ("Api", API),
        ("Secret", SECRET),
        ("Base", BASE),
    ]);
    assert_eq!(
        client.commands.batch.engine.logical_root(&options),
        checked.checked.result_logical_root
    );
}

#[test]
fn named_anonymous_and_private_priorities_keep_distinct_checked_histories() {
    let api = format!(
        "{HEADER}namespace API\npublic instance (priority := 1800) first : Law Truth := Law.mk Truth.make\nprivate instance (priority := 2000) hidden : Law Truth := Law.mk Truth.make\npublic instance (priority := 1800) : Law Truth := Law.mk Truth.make\npublic instance (priority := 500) lower : Law Truth := Law.mk Truth.make\ndef selected : Law Truth := chosenLaw Truth\nend API"
    );
    let local = checked(&[("Api", &api), ("Base", BASE)]);
    let local_env = local.checked.engine.environment();
    let Some(ConstantInfo::Defn(selected)) = local_env.find(&private("Api", "API.selected")) else {
        panic!("missing private choice");
    };
    assert!(references(&selected.value, &private("Api", "API.hidden")));
    let main = "prelude\nimport Api\ndef selected : Law Truth := chosenLaw Truth\ntheorem evidence : Truth := @Law.proof Truth selected";
    let imported = checked(&[("Main", main), ("Api", &api), ("Base", BASE)]);
    let env = imported.checked.engine.environment();
    let registry = InstanceRegistry::read(env).unwrap();
    let rows = registry.candidates(&n("Law"));
    assert_eq!(rows.len(), 3);
    assert_eq!(rows[0].priority, 1800);
    assert_eq!(rows[1].declaration, n("API.first"));
    assert_eq!(rows[2].declaration, n("API.lower"));
    assert_ne!(rows[0].declaration, rows[1].declaration);
    assert!(rows[0].order > rows[1].order);
    assert_eq!(rows[0].declaration.parent(), n("API"));
    assert!(
        rows[0]
            .declaration
            .to_display_string()
            .contains("instLawTruth")
    );
    let Some(ConstantInfo::Defn(selected)) = env.find(&n("selected")) else {
        panic!("missing imported choice");
    };
    assert!(references(&selected.value, &rows[0].declaration));
    assert!(!references(&selected.value, &private("Api", "API.hidden")));
    for row in rows {
        assert!(matches!(
            env.find(&row.declaration),
            Some(ConstantInfo::Axiom(_))
        ));
        assert_eq!(
            ReducibilityTable::effective(env)
                .unwrap()
                .status(&row.declaration),
            Reducibility::Semireducible
        );
    }
}

#[test]
fn anonymous_public_proof_names_avoid_private_and_public_predecessors() {
    let api = format!(
        "{HEADER}namespace API\ninstance : Law Truth := Law.mk Truth.make\npublic instance : Law Truth := Law.mk Truth.make\npublic instance : Law Truth := Law.mk Truth.make\nend API"
    );
    let local = checked(&[("Api", &api), ("Base", BASE)]);
    let local_env = local.checked.engine.environment();
    let hidden = private("Api", "API.instLawTruth");
    let exported = [n("API.instLawTruth_1"), n("API.instLawTruth_2")];
    let local_statuses = ReducibilityTable::effective(local_env).unwrap();
    for name in std::iter::once(&hidden).chain(&exported) {
        assert!(
            matches!(local_env.find(name), Some(ConstantInfo::Thm(_))),
            "{name:?}"
        );
        assert_eq!(local_statuses.status(name), Reducibility::Semireducible);
    }
    let main = "prelude\nimport Api\ndef selected : Law Truth := chosenLaw Truth\ntheorem evidence : Truth := @Law.proof Truth selected";
    let imported = checked(&[("Main", main), ("Api", &api), ("Base", BASE)]);
    let env = imported.checked.engine.environment();
    assert!(!env.contains(&hidden));
    assert!(!env.contains(&n("API.instLawTruth")));
    let registry = InstanceRegistry::read(env).unwrap();
    let rows = registry.candidates(&n("Law"));
    assert_eq!(rows.len(), 2);
    assert_eq!(rows[0].declaration, exported[1]);
    assert_eq!(rows[1].declaration, exported[0]);
    assert!(rows[0].order > rows[1].order);
    let imported_statuses = ReducibilityTable::effective(env).unwrap();
    for name in &exported {
        let Some(ConstantInfo::Axiom(interface)) = env.find(name) else {
            panic!("an anonymous proof instance must export only its checked interface");
        };
        assert!(!interface.is_unsafe);
        assert_eq!(
            &interface.base,
            local_env.find(name).unwrap().constant_val()
        );
        assert_eq!(imported_statuses.status(name), Reducibility::Semireducible);
    }
    let Some(ConstantInfo::Defn(selected)) = env.find(&n("selected")) else {
        panic!("missing imported instance choice");
    };
    assert!(references(&selected.value, &exported[1]));
    assert!(!references(&selected.value, &hidden));
}

#[test]
fn proof_exposure_attributes_and_section_defaults_choose_the_correct_body_world() {
    for declaration in [
        "public instance hidden : Law Truth := Law.mk hiddenProof",
        "@[no_expose] public instance hidden : Law Truth := Law.mk hiddenProof",
        "@[expose, no_expose] public instance hidden : Law Truth := Law.mk hiddenProof",
        "@[expose] public section\ninstance hidden : Law Truth := Law.mk hiddenProof\nend",
    ] {
        let api = format!("{HEADER}import Secret\n{declaration}");
        let result = checked(&[
            ("Main", "prelude\nimport Api"),
            ("Api", &api),
            ("Secret", SECRET),
            ("Base", BASE),
        ]);
        assert!(matches!(
            result.checked.engine.environment().find(&n("hidden")),
            Some(ConstantInfo::Axiom(_))
        ));
    }
    let api = format!(
        "{HEADER}@[expose] public instance exposed : Law Truth := Law.mk Truth.make\npublic instance data : Pick := Pick.mk Token.left\npublic section\ninstance inherited : Law Truth := Law.mk Truth.make\nend\ninstance restored : Law Truth := Law.mk Truth.make"
    );
    let result = checked(&[
        ("Main", "prelude\nimport Api\ndef value : Token := chosen"),
        ("Api", &api),
        ("Base", BASE),
    ]);
    let env = result.checked.engine.environment();
    assert!(matches!(
        env.find(&n("exposed")),
        Some(ConstantInfo::Axiom(interface)) if !interface.is_unsafe
    ));
    assert!(matches!(
        env.find(&n("data")),
        Some(ConstantInfo::Defn(definition)) if definition.safety == DefinitionSafety::Safe
    ));
    let local = checked(&[("Api", &api), ("Base", BASE)]);
    assert!(matches!(
        local.checked.engine.environment().find(&n("exposed")),
        Some(ConstantInfo::Thm(_))
    ));
    assert!(matches!(
        env.find(&n("inherited")),
        Some(ConstantInfo::Axiom(_))
    ));
    assert!(!env.contains(&private("Api", "restored")));
    let statuses = ReducibilityTable::effective(env).unwrap();
    assert_eq!(statuses.status(&n("exposed")), Reducibility::Semireducible);
    assert_eq!(statuses.status(&n("data")), Reducibility::ImplicitReducible);
}

#[test]
fn hidden_header_dependencies_bad_proofs_and_exposed_private_bodies_are_refused() {
    for declaration in [
        "public instance leak : Law Secret := Law.mk Secret.make",
        "public instance leak : Law (Hidden Truth) := Law.mk hiddenProof",
        "public instance invalid (P Q : Prop) (h : P) : Law Q := Law.mk h",
        "@[expose] public instance leak : Law Truth := Law.mk hiddenProof",
        "@[no_expose] public instance data : Pick := Pick.mk Token.left",
        "private instance repeated : Law Truth := Law.mk Truth.make\npublic instance repeated : Law Truth := Law.mk Truth.make",
        "public instance repeated : Law Truth := Law.mk Truth.make\nprivate instance repeated : Law Truth := Law.mk Truth.make",
    ] {
        let api = format!("{HEADER}import Secret\n{declaration}");
        assert!(
            matches!(
                check(&[("Main", "prelude\nimport Api"), ("Api", &api), ("Secret", SECRET), ("Base", BASE)]),
                Err(SourceModuleCheckError::Source { module, .. }) if module == n("Api")
            ),
            "{declaration}"
        );
    }
}

#[test]
fn proof_instances_preserve_body_used_section_variables_and_rigid_header_universes() {
    let declaration = "section\nvariable (P : Prop) (proof : P)\npublic instance fromBody : Law P := Law.mk proof\nend\npublic instance polymorphic (A : Type _) : Law Truth := Law.mk Truth.make";
    let api = format!("{HEADER}{declaration}");
    let local = checked(&[("Api", &api), ("Base", BASE)]);
    let imported = checked(&[
        (
            "Main",
            "prelude\nimport Api\ntheorem used (P : Prop) (proof : P) : P := @Law.proof P (fromBody P proof)",
        ),
        ("Api", &api),
        ("Base", BASE),
    ]);
    for name in ["fromBody", "polymorphic"] {
        assert_eq!(
            local
                .checked
                .engine
                .environment()
                .find(&n(name))
                .unwrap()
                .constant_val(),
            imported
                .checked
                .engine
                .environment()
                .find(&n(name))
                .unwrap()
                .constant_val()
        );
    }
    assert_eq!(
        imported
            .checked
            .engine
            .environment()
            .find(&n("polymorphic"))
            .unwrap()
            .constant_val()
            .level_params
            .len(),
        1
    );
    let private_control = format!(
        "{HEADER}{}",
        declaration.replace("public instance", "instance")
    );
    let control = checked(&[("Api", &private_control), ("Base", BASE)]);
    assert_eq!(
        local
            .checked
            .engine
            .environment()
            .find(&n("fromBody"))
            .unwrap()
            .constant_val()
            .type_,
        control
            .checked
            .engine
            .environment()
            .find(&private("Api", "fromBody"))
            .unwrap()
            .constant_val()
            .type_
    );
    for declaration in [
        "public instance restricted (A : Type _) : Law Truth := by\n  have fixed : Type := A\n  exact Law.mk Truth.make",
        "@[expose] public instance restricted (A : Type _) : Law Truth := by\n  have fixed : Type := A\n  exact Law.mk Truth.make",
        "section\nvariable (secret : Secret)\npublic instance fromPrivate : Law Truth := let unused := secret; Law.mk Truth.make\nend",
    ] {
        let source = format!("{HEADER}import Secret\n{declaration}");
        assert!(matches!(
            check(&[("Api", &source), ("Secret", SECRET), ("Base", BASE)]),
            Err(SourceModuleCheckError::Source { module, .. }) if module == n("Api")
        ));
    }
}

#[test]
fn failed_public_proof_edits_do_not_publish_cached_interfaces_or_instance_rows() {
    let mut session = session();
    let names = [n("Main"), n("Api"), n("Secret"), n("Base")];
    let files = [MAIN, API, SECRET, BASE];
    let inputs: Vec<_> = names
        .iter()
        .zip(files)
        .map(|(name, source)| SourceModuleInput {
            name,
            source: source.as_bytes(),
        })
        .collect();
    let cold = session
        .check(&inputs, &names[0])
        .unwrap()
        .into_complete()
        .unwrap();
    let warm = session
        .check(&inputs, &names[0])
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!((cold.elaborated_modules, warm.reused_modules), (4, 4));
    let retained = session.retained_modules();
    let expected_registry =
        InstanceRegistry::read(cold.checked.checked.engine.environment()).unwrap();
    for changed in [
        API.replace("public instance witness", "private instance witness"),
        format!("{API}\npublic instance broken (P Q : Prop) (h : P) : Law Q := Law.mk h"),
        API.replace("Law.mk localProof", "Law.mk absentProof"),
    ] {
        let mut changed_inputs = inputs.clone();
        changed_inputs[1].source = changed.as_bytes();
        assert!(matches!(
            session.check(&changed_inputs, &names[0]),
            Err(SourceModuleCheckError::Source { .. })
        ));
        assert_eq!(session.retained_modules(), retained);
        let recovered = session
            .check(&inputs, &names[0])
            .unwrap()
            .into_complete()
            .unwrap();
        assert_eq!(recovered.reused_modules, 4);
        assert_eq!(
            recovered.checked.checked.result_logical_root,
            cold.checked.checked.result_logical_root
        );
        assert_eq!(
            InstanceRegistry::read(recovered.checked.checked.engine.environment()).unwrap(),
            expected_registry
        );
        assert!(
            !recovered
                .checked
                .checked
                .engine
                .environment()
                .contains(&n("broken"))
        );
    }
}

#[test]
fn editor_proof_observations_use_private_bodies_without_publishing_pending_instances() {
    let mut session = session();
    let names = [n("Api"), n("Secret"), n("Base")];
    let prefix =
        format!("{HEADER}import Secret\nprivate theorem hiddenLocal : Truth := hiddenProof\n");
    let source =
        format!("{prefix}public instance pending : Law Truth := by\n  exact Law.mk hiddenLocal");
    let inputs = [
        SourceModuleInput {
            name: &names[0],
            source: source.as_bytes(),
        },
        SourceModuleInput {
            name: &names[1],
            source: SECRET.as_bytes(),
        },
        SourceModuleInput {
            name: &names[2],
            source: BASE.as_bytes(),
        },
    ];
    for _ in 0..2 {
        let observed = session
            .inspect(&inputs, &names[0], source.len(), ObservationKind::Goals)
            .unwrap()
            .into_complete()
            .unwrap();
        assert!(
            matches!(observed.observation, Some(SourceObservation::Goals { goals, .. }) if goals.is_empty())
        );
        let env = observed.prefix.checked.checked.engine.environment();
        assert!(!env.contains(&n("pending")));
        assert!(
            InstanceRegistry::read(env)
                .unwrap()
                .candidates(&n("Law"))
                .is_empty()
        );
    }
    let observed = session
        .inspect(
            &inputs,
            &names[0],
            source.rfind("hiddenLocal").unwrap() + 2,
            ObservationKind::Term,
        )
        .unwrap()
        .into_complete()
        .unwrap();
    let Some(SourceObservation::Term { expression, .. }) = observed.observation else {
        panic!("expected the actual private proof helper");
    };
    assert!(references(&expression, &private("Api", "hiddenLocal")));
    for source in [
        format!(
            "{prefix}public instance pending : Law (Hidden Truth) := by exact Law.mk hiddenLocal"
        ),
        format!(
            "{prefix}@[expose] public instance pending : Law Truth := by exact Law.mk hiddenLocal"
        ),
    ] {
        let mut changed = inputs;
        changed[0].source = source.as_bytes();
        assert!(
            session
                .inspect(&changed, &names[0], source.len(), ObservationKind::Goals)
                .is_err()
        );
    }
}

#[test]
fn completion_classifies_the_header_before_revealing_private_proof_helpers() {
    let mut session = session();
    let names = [n("Api"), n("Secret"), n("Base")];
    let prefix = format!(
        "{HEADER}import Secret\nnamespace Proofs\npublic class OpenLaw (P : Prop) : Prop where\n  proof : P\nend Proofs\nprivate theorem hiddenLocal : Truth := hiddenProof\n"
    );
    for (declaration, hidden) in [
        ("public instance pending : Law hid", false),
        ("public instance pending : Law Truth := Law.mk hid", true),
        (
            "@[no_expose] public instance pending : Law Truth := Law.mk hid",
            true,
        ),
        (
            "@[expose] public instance pending : Law Truth := Law.mk hid",
            false,
        ),
        (
            "@[expose] public section\ninstance pending : Law Truth := Law.mk hid",
            true,
        ),
        ("public instance pending : Pick := hid", false),
        ("private instance pending : Law hid", true),
        (
            "set_option maxRecDepth 2048 in open Proofs in public instance pending : OpenLaw Truth := OpenLaw.mk hid",
            true,
        ),
        (
            "set_option maxRecDepth 2048 in open Proofs in @[no_expose] public instance pending : OpenLaw Truth := OpenLaw.mk hid",
            true,
        ),
        (
            "set_option maxRecDepth 2048 in open Proofs in @[expose] public instance pending : OpenLaw Truth := OpenLaw.mk hid",
            false,
        ),
        (
            "set_option maxRecDepth 2048 in open Proofs in public instance pending : OpenLaw hid",
            false,
        ),
    ] {
        let source = format!("{prefix}{declaration}");
        let inputs = [
            SourceModuleInput {
                name: &names[0],
                source: source.as_bytes(),
            },
            SourceModuleInput {
                name: &names[1],
                source: SECRET.as_bytes(),
            },
            SourceModuleInput {
                name: &names[2],
                source: BASE.as_bytes(),
            },
        ];
        let result = session
            .complete(&inputs, &names[0], source.len())
            .unwrap_or_else(|error| panic!("{declaration}: {error:?}"))
            .into_complete()
            .unwrap()
            .unwrap();
        for label in ["hiddenProof", "hiddenLocal"] {
            assert_eq!(
                result.items.iter().any(|item| item.label == label),
                hidden,
                "{declaration}: {result:?}"
            );
        }
        if hidden {
            assert!(result.items.iter().any(
                |item| item.label == "hiddenLocal" && item.replacement == "_root_.hiddenLocal"
            ));
        }
    }
}
