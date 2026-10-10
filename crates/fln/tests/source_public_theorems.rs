//! Public theorem statements and private proofs travel through separate, checked
//! module worlds. Exporting a signature never stands in for checking its proof.
#![forbid(unsafe_code)]

use fln::source_check::modules::{
    SourceModuleCacheLimits, SourceModuleCheck, SourceModuleCheckError, SourceModuleCheckLimits,
    SourceModuleSession, execution::SourceProgramLimits,
};
use fln::{
    Budget, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap, Name, Outcome,
    SourceCheckLimits, SourceModuleInput,
};
use fln_env::constants::ConstantInfo;

fn n(text: &str) -> Name {
    Name::from_components(text.split('.'))
}

fn private(module: &str, declaration: &str) -> Name {
    Name::num(n(&format!("_private.{module}")), 0).append_core(&n(declaration))
}

fn limits() -> SourceModuleCheckLimits {
    SourceModuleCheckLimits::new(SourceCheckLimits::new(EngineAdmissionLimits::new(
        Budget::for_stack_bytes(2 * 1024 * 1024),
    )))
}

fn check(
    base: &Engine,
    files: &[(&str, &str)],
) -> Result<Outcome<SourceModuleCheck>, SourceModuleCheckError> {
    let names: Vec<_> = files.iter().map(|(name, _)| n(name)).collect();
    let inputs: Vec<_> = files
        .iter()
        .zip(&names)
        .map(|((_, source), name)| SourceModuleInput {
            name,
            source: source.as_bytes(),
        })
        .collect();
    base.check_source_modules(&inputs, &names[0], &KVMap::new(), limits())
}

fn complete(base: &Engine, files: &[(&str, &str)]) -> SourceModuleCheck {
    check(base, files)
        .unwrap_or_else(|error| panic!("{files:?}: {error:?}"))
        .into_complete()
        .unwrap()
}

const SECRET: &str = "prelude\ndef importedProof (P : Prop) (h : P) : P := h";
const API: &str = "module\nprelude\nimport Secret\nnamespace API\ndef localProof (P : Prop) (h : P) : P := importedProof P h\npublic theorem witness (P : Prop) (h : P) : P := localProof P h\nend API";
const MAIN: &str = "prelude\nimport Api\ntheorem client (P : Prop) (h : P) : P := API.witness P h";

#[test]
fn checked_private_proofs_export_only_their_exact_safe_signatures() {
    let base = Engine::builder().build_empty();
    let local = complete(&base, &[("Api", API), ("Secret", SECRET)]);
    let Some(ConstantInfo::Thm(proof)) = local.checked.engine.environment().find(&n("API.witness"))
    else {
        panic!("the defining module must retain its checked theorem");
    };
    assert!(
        local
            .checked
            .engine
            .environment()
            .contains(&private("Api", "API.localProof"))
    );
    let imported = complete(&base, &[("Main", MAIN), ("Api", API), ("Secret", SECRET)]);
    let env = imported.checked.engine.environment();
    let Some(ConstantInfo::Axiom(signature)) = env.find(&n("API.witness")) else {
        panic!("a dependent module must receive the theorem interface");
    };
    assert!(!signature.is_unsafe);
    assert_eq!(signature.base, proof.base);
    assert!(matches!(env.find(&n("client")), Some(ConstantInfo::Thm(_))));
    assert!(!env.contains(&n("importedProof")));
    assert!(!env.contains(&private("Api", "API.localProof")));
    assert!(base.environment().is_empty());

    // The retained imported-context front door uses the same private/public
    // source worlds even when no external olean is required by this fixture.
    let names = [n("Main"), n("Api"), n("Secret")];
    let inputs = [MAIN, API, SECRET].map(str::as_bytes);
    let modules: Vec<_> = names
        .iter()
        .zip(inputs)
        .map(|(name, source)| SourceModuleInput { name, source })
        .collect();
    let imported_context =
        fln::source_check::modules::imported::SourceOleanImport::empty(&KVMap::new())
            .check_source_modules(&modules, &names[0], &KVMap::new(), limits(), None)
            .unwrap()
            .into_complete()
            .unwrap();
    assert_eq!(
        imported_context.checked.result_logical_root,
        imported.checked.result_logical_root
    );
}

#[test]
fn execution_keeps_private_proof_admissions_and_replays_only_interfaces_to_clients() {
    let base = Engine::builder().build_empty();
    let names = [n("Main"), n("Api"), n("Secret")];
    let inputs = [MAIN, API, SECRET].map(str::as_bytes);
    let modules: Vec<_> = names
        .iter()
        .zip(inputs)
        .map(|(name, source)| SourceModuleInput { name, source })
        .collect();
    let executed = fln::source_check::modules::imported::SourceOleanImport::empty(&KVMap::new())
        .execute_source_modules(
            &modules,
            &names[0],
            &KVMap::new(),
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
    assert!(matches!(
        api.commands
            .batch
            .engine
            .environment()
            .find(&n("API.witness")),
        Some(ConstantInfo::Thm(_))
    ));
    assert!(api.commands.batch.source_admissions.iter().flat_map(|command| &command.admission.admissions).any(|row| matches!(&row.declaration, fln::Declaration::Thm(theorem) if theorem.base.name == n("API.witness"))));
    let client = executed.modules.last().unwrap();
    assert!(matches!(
        client
            .commands
            .batch
            .engine
            .environment()
            .find(&n("API.witness")),
        Some(ConstantInfo::Axiom(_))
    ));
    let checked = complete(&base, &[("Main", MAIN), ("Api", API), ("Secret", SECRET)]);
    assert_eq!(
        client.commands.batch.engine.logical_root(&KVMap::new()),
        checked.checked.result_logical_root
    );
}

#[test]
fn public_headers_and_private_proofs_select_their_own_instance_histories() {
    let base = Engine::builder().build_empty();
    let foundation = "prelude\ninductive Token where\n| left\n| right\nclass Pick (A : Type) where\n  value : A\ndef chosen {A : Type} [p : Pick A] : A := p.value";
    let api = "module\nprelude\npublic import Base\npublic instance visible : Pick Token := Pick.mk Token.left\nprivate instance hidden : Pick Token := Pick.mk Token.right\npublic theorem header (P : Token -> Prop) (h : P Token.left) : P chosen := h\npublic theorem body (P : Token -> Prop) (h : P Token.right) : P Token.right := by\n  have selected : P chosen := h\n  exact selected";
    let main = "prelude\nimport Api\ntheorem publicHeader (P : Token -> Prop) (h : P Token.left) : P Token.left := header P h\ntheorem privateBody (P : Token -> Prop) (h : P Token.right) : P Token.right := body P h";
    let imported = complete(&base, &[("Main", main), ("Api", api), ("Base", foundation)]);
    for name in ["header", "body"] {
        assert!(matches!(
            imported.checked.engine.environment().find(&n(name)),
            Some(ConstantInfo::Axiom(_))
        ));
    }
    assert!(
        !imported
            .checked
            .engine
            .environment()
            .contains(&private("Api", "hidden"))
    );

    let missing_public_instance = "module\nprelude\npublic import Base\ninstance hidden : Pick Token := Pick.mk Token.right\npublic theorem leak (P : Token -> Prop) (h : P Token.right) : P chosen := h";
    assert!(
        matches!(check(&base, &[("Api", missing_public_instance), ("Base", foundation)]), Err(SourceModuleCheckError::Source { module, .. }) if module == n("Api"))
    );
}

#[test]
fn public_sections_hide_proofs_even_under_inherited_exposure_and_restore_private_defaults() {
    let base = Engine::builder().build_empty();
    let api = "module\nprelude\npublic section\ntheorem first (P : Prop) (h : P) : P := h\nend\n@[expose] public section\ntheorem inherited (P : Prop) (h : P) : P := first P h\nend\ntheorem restored (P : Prop) (h : P) : P := inherited P h";
    let local = complete(&base, &[("Api", api)]);
    assert!(matches!(
        local
            .checked
            .engine
            .environment()
            .find(&private("Api", "restored")),
        Some(ConstantInfo::Thm(_))
    ));
    let imported = complete(&base, &[("Main", "prelude\nimport Api"), ("Api", api)]);
    for name in ["first", "inherited"] {
        assert!(matches!(
            imported.checked.engine.environment().find(&n(name)),
            Some(ConstantInfo::Axiom(_))
        ));
    }
    assert!(
        !imported
            .checked
            .engine
            .environment()
            .contains(&private("Api", "restored"))
    );
}

#[test]
fn private_types_bad_proofs_and_visibility_collisions_cannot_publish_interfaces() {
    let base = Engine::builder().build_empty();
    let secret = "prelude\ninductive Secret : Prop where\n| make";
    for declaration in [
        "public theorem leak : Secret := Secret.make",
        "public theorem notAProp : Type := Prop",
        "public theorem invalid (P Q : Prop) (h : P) : Q := h",
        "theorem repeated (P : Prop) (h : P) : P := h\npublic theorem repeated (P : Prop) (h : P) : P := h",
        "public theorem repeated (P : Prop) (h : P) : P := h\nprivate theorem repeated (P : Prop) (h : P) : P := h",
        "@[expose] public theorem tagged (P : Prop) (h : P) : P := h",
        "@[no_expose] public theorem tagged (P : Prop) (h : P) : P := h",
    ] {
        let api = format!("module\nprelude\nimport Secret\n{declaration}");
        assert!(
            matches!(check(&base, &[("Api", &api), ("Secret", secret)]), Err(SourceModuleCheckError::Source { module, .. }) if module == n("Api")),
            "{declaration}"
        );
        assert!(base.environment().is_empty());
    }
}

#[test]
fn header_universes_are_rigid_before_a_private_proof_starts() {
    let base = Engine::builder().build_empty();
    let foundation = "prelude\ninductive Truth : Prop where\n| make";
    let good = "module\nprelude\npublic import Base\npublic theorem polymorphic (x : Type _) : Truth := Truth.make";
    let checked = complete(&base, &[("Api", good), ("Base", foundation)]);
    assert_eq!(
        checked
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
    let bad = "module\nprelude\npublic import Base\npublic theorem restricted (x : Type _) : Truth := by\n  have value : Type := x\n  exact Truth.make";
    assert!(
        matches!(check(&base, &[("Api", bad), ("Base", foundation)]), Err(SourceModuleCheckError::Source { module, .. }) if module == n("Api"))
    );
}

#[test]
fn equation_style_public_theorems_preserve_authored_statement_binders() {
    let base = Engine::builder().build_empty();
    let api = "module\nprelude\npublic theorem equation (P : Prop) : P -> P\n| h => h";
    let local = complete(&base, &[("Api", api)]);
    let main = "prelude\nimport Api\ntheorem used (P : Prop) (h : P) : P := equation P h";
    let imported = complete(&base, &[("Main", main), ("Api", api)]);
    assert_eq!(
        local
            .checked
            .engine
            .environment()
            .find(&n("equation"))
            .unwrap()
            .constant_val(),
        imported
            .checked
            .engine
            .environment()
            .find(&n("equation"))
            .unwrap()
            .constant_val()
    );
}

#[test]
fn failed_theorems_leave_cached_private_and_exported_worlds_unchanged() {
    let options = KVMap::new();
    let mut session = SourceModuleSession::new(
        Engine::builder().build_empty(),
        options,
        limits(),
        SourceModuleCacheLimits::default(),
    );
    let names = [n("Main"), n("Api"), n("Secret")];
    let files = [
        SourceModuleInput {
            name: &names[0],
            source: MAIN.as_bytes(),
        },
        SourceModuleInput {
            name: &names[1],
            source: API.as_bytes(),
        },
        SourceModuleInput {
            name: &names[2],
            source: SECRET.as_bytes(),
        },
    ];
    let cold = session
        .check(&files, &names[0])
        .unwrap()
        .into_complete()
        .unwrap();
    let warm = session
        .check(&files, &names[0])
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!((cold.elaborated_modules, warm.reused_modules), (3, 3));
    assert_eq!(
        cold.checked.checked.result_logical_root,
        warm.checked.checked.result_logical_root
    );
    let retained = session.retained_modules();
    for api in [
        format!("{API}\npublic theorem bad (P Q : Prop) (h : P) : Q := h"),
        API.replace("public theorem witness", "private theorem witness"),
    ] {
        let mut changed = files;
        changed[1].source = api.as_bytes();
        assert!(matches!(
            session.check(&changed, &names[0]),
            Err(SourceModuleCheckError::Source { .. })
        ));
        assert_eq!(session.retained_modules(), retained);
        let recovered = session
            .check(&files, &names[0])
            .unwrap()
            .into_complete()
            .unwrap();
        assert_eq!(recovered.reused_modules, 3);
        assert_eq!(
            recovered.checked.checked.result_logical_root,
            cold.checked.checked.result_logical_root
        );
    }
}

#[test]
fn public_simp_and_protected_attributes_work_in_both_worlds_without_exposing_proofs() {
    let base = Engine::with_source_seed(limits().source.admission)
        .unwrap()
        .into_complete()
        .unwrap();
    let api = "module\nprelude\npublic inductive Good : Prop where\n| make\n@[simp] public theorem good : Good := Good.make\n@[simp] public theorem notFalse : Not False := by\n  intro h\n  exact h\nnamespace API\n@[expose] public def wrap (n : Nat) : Nat := n\n@[simp] public protected theorem unwrap (n : Nat) : wrap n = n := by rfl\nend API\ntheorem localUse : Good := by simp\ntheorem localEquation (n : Nat) : API.wrap n = n := by simp";
    let main = "prelude\nimport Api\ntheorem importedProp : Good := by simp\ntheorem importedEquation (n : Nat) : API.wrap n = n := by simp\ntheorem importedRefutation : Not False := by simp";
    let local = complete(&base, &[("Api", api)]);
    let imported = complete(&base, &[("Main", main), ("Api", api)]);
    for checked in [&local, &imported] {
        let rows =
            fln_elab::source::scope::simp::read(checked.checked.engine.environment()).unwrap();
        for name in ["good", "notFalse", "API.unwrap"] {
            assert!(rows.iter().any(|row| row.declaration == n(name)), "{name}");
        }
    }
    let env = imported.checked.engine.environment();
    for name in ["good", "notFalse", "API.unwrap"] {
        assert!(matches!(env.find(&n(name)), Some(ConstantInfo::Axiom(_))));
    }
    assert!(!env.contains(&private("Api", "localUse")));
    let unqualified =
        "prelude\nimport Api\nopen API\ntheorem inaccessible (n : Nat) : wrap n = n := unwrap n";
    assert!(
        matches!(check(&base, &[("Main", unqualified), ("Api", api)]), Err(SourceModuleCheckError::Source { module, .. }) if module == n("Main"))
    );
    let failed = format!("{api}\n@[simp] public theorem invalid (P Q : Prop) (h : P) : Q := h");
    assert!(check(&base, &[("Api", &failed)]).is_err());
    assert!(
        fln_elab::source::scope::simp::read(base.environment())
            .unwrap()
            .is_empty()
    );
}
