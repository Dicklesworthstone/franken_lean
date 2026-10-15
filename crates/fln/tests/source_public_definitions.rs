//! Public module signatures never substitute for checking private implementations.
#![forbid(unsafe_code)]

use fln::source_check::modules::{
    SourceModuleCheck, SourceModuleCheckError, SourceModuleCheckLimits,
};
use fln::{
    Budget, Engine, EngineAdmissionLimits, KVMap, Name, Outcome, SourceCheckLimits,
    SourceModuleInput,
};
use fln_env::constants::ConstantInfo;

fn n(name: &str) -> Name {
    Name::from_components(name.split('.'))
}
fn private(module: &str, name: &str) -> Name {
    Name::num(n(&format!("_private.{module}")), 0).append_core(&n(name))
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

const BASE: &str = "prelude\ninductive Bit where\n| off\n| on";
const SECRET: &str = "prelude\nimport Base\ndef secret : Bit := Bit.on";
const API: &str = "module\nprelude\npublic import Base\nimport Secret\ndef localValue : Bit := secret\npublic def chosen : Bit := localValue\npublic opaque sealed : Bit := localValue\ndef checkedInside (P : Bit -> Prop) (h : P Bit.on) : P chosen := h";

#[test]
fn public_definition_and_opaque_keep_checked_bodies_only_in_the_defining_module() {
    let base = Engine::builder().build_empty();
    let local = complete(&base, &[("Api", API), ("Base", BASE), ("Secret", SECRET)]);
    let client = complete(
        &base,
        &[
            (
                "Main",
                "prelude\nimport Api\nnoncomputable def used : Bit := chosen\nnoncomputable def usedOpaque : Bit := sealed",
            ),
            ("Api", API),
            ("Base", BASE),
            ("Secret", SECRET),
        ],
    );
    for (name, opaque) in [("chosen", false), ("sealed", true)] {
        let implementation = local.checked.engine.environment().find(&n(name)).unwrap();
        assert_eq!(matches!(implementation, ConstantInfo::Opaque(_)), opaque);
        assert_eq!(matches!(implementation, ConstantInfo::Defn(_)), !opaque);
        let Some(ConstantInfo::Axiom(signature)) =
            client.checked.engine.environment().find(&n(name))
        else {
            panic!("interface must hide {name}'s body");
        };
        assert!(!signature.is_unsafe);
        assert_eq!(&signature.base, implementation.constant_val());
    }
    for hidden in [
        n("secret"),
        private("Api", "localValue"),
        private("Api", "checkedInside"),
    ] {
        assert!(!client.checked.engine.environment().contains(&hidden));
    }
    assert!(base.environment().is_empty());
}

#[test]
fn hidden_bodies_support_polymorphism_equations_and_body_only_section_captures() {
    let base = Engine::builder().build_empty();
    let api = "module\nprelude\npublic def identity.{u} {A : Sort u} (x : A) : A := x\npublic def equation.{u} {A : Sort u} : A -> A\n| x => identity x\nsection\nvariable (A : Type) (x : A)\npublic def capture : A := identity x\npublic def inferred := identity x\nend";
    let local = complete(&base, &[("Api", api)]);
    let main = "prelude\nimport Api\nnoncomputable def use.{u} {A : Sort u} (x : A) : A := equation x\nnoncomputable def useCapture (A : Type) (x : A) : A := capture A x\nnoncomputable def useInferred (A : Type) (x : A) : A := inferred A x";
    let imported = complete(&base, &[("Main", main), ("Api", api)]);
    for name in ["identity", "equation", "capture", "inferred"] {
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
}

#[test]
fn exposing_a_body_cannot_use_private_dependencies_and_hiding_does_not_make_it_reducible() {
    let base = Engine::builder().build_empty();
    complete(&base, &[("Api", API), ("Base", BASE), ("Secret", SECRET)]);
    for api in [
        API.replace("public def chosen", "@[expose] public def chosen"),
        API.replace("public opaque sealed", "@[expose] public opaque sealed"),
    ] {
        assert!(
            matches!(check(&base, &[("Api", &api), ("Base", BASE), ("Secret", SECRET)]), Err(SourceModuleCheckError::Source { module, .. }) if module == n("Api"))
        );
    }
    let invalid =
        "prelude\nimport Api\ntheorem invented (P : Bit -> Prop) (h : P Bit.on) : P chosen := h";
    assert!(
        matches!(check(&base, &[("Main", invalid), ("Api", API), ("Base", BASE), ("Secret", SECRET)]), Err(SourceModuleCheckError::Source { module, .. }) if module == n("Main"))
    );
}

#[test]
fn invalid_hidden_bodies_and_private_signature_dependencies_never_export_axioms() {
    let base = Engine::builder().build_empty();
    let secret = "prelude\nimport Base\ninductive Secret where\n| make\ndef secret : Bit := Bit.on";
    for declaration in [
        "public def invalid (P Q : Prop) (h : P) : Q := h",
        "public opaque invalid (P Q : Prop) (h : P) : Q := h",
        "public def invalid : Secret := Secret.make",
        "public def invalid := Secret.make",
        "variable (x : Secret)\npublic def invalid := x",
        "def duplicate : Bit := secret\npublic def duplicate : Bit := secret",
        "public def duplicate : Bit := secret\nprivate def duplicate : Bit := secret",
    ] {
        let api = format!("module\nprelude\npublic import Base\nimport Secret\n{declaration}");
        let result = check(&base, &[("Api", &api), ("Base", BASE), ("Secret", secret)]);
        assert!(!matches!(result, Ok(Outcome::Complete(_))), "{declaration}");
        assert!(base.environment().is_empty());
    }
}

#[test]
fn hidden_definition_headers_and_bodies_use_their_own_instance_histories() {
    let base = Engine::builder().build_empty();
    let foundation = "prelude\ninductive Token where\n| left\n| right\nclass Pick where\n  value : Token\ndef selected [p : Pick] : Token := p.value";
    let api = "module\nprelude\npublic import Base\npublic instance visible : Pick := Pick.mk Token.left\nprivate instance hidden : Pick := Pick.mk Token.right\npublic def witness (P : Token -> Prop) (h : P Token.left) : P selected := h\npublic def chosen : Token := selected\ndef checkBody (P : Token -> Prop) (h : P Token.right) : P chosen := h";
    let main = "prelude\nimport Api\ntheorem use (P : Token -> Prop) (h : P Token.left) : P selected := witness P h";
    let imported = complete(&base, &[("Main", main), ("Api", api), ("Base", foundation)]);
    assert!(matches!(
        imported.checked.engine.environment().find(&n("witness")),
        Some(ConstantInfo::Axiom(_))
    ));
    assert!(
        !imported
            .checked
            .engine
            .environment()
            .contains(&private("Api", "hidden"))
    );
    let bad = api.replace("public instance visible : Pick := Pick.mk Token.left\n", "");
    assert!(check(&base, &[("Api", &bad), ("Base", foundation)]).is_err());
}

#[test]
fn proof_headers_are_rigid_but_data_headers_can_infer_universes_from_the_body() {
    let base = Engine::builder().build_empty();
    let api = "module\nprelude\npublic inductive True : Prop where\n| intro\npublic def data (x : Type _) : Type := x\npublic def proof (x : Type _) : True := True.intro";
    let result = complete(&base, &[("Api", api)]);
    assert!(
        result
            .checked
            .engine
            .environment()
            .find(&n("data"))
            .unwrap()
            .constant_val()
            .level_params
            .is_empty()
    );
    assert_eq!(
        result
            .checked
            .engine
            .environment()
            .find(&n("proof"))
            .unwrap()
            .constant_val()
            .level_params
            .len(),
        1
    );
    let invalid = api.replace(
        "True := True.intro",
        "True := by\n  have restricted : Type := x\n  exact True.intro",
    );
    assert!(check(&base, &[("Api", &invalid)]).is_err());
}

#[test]
fn hidden_unsafe_implementations_never_become_safe_exported_assumptions() {
    let base = Engine::builder().build_empty();
    let api = "module\nprelude\npublic unsafe def untrusted (P : Prop) (h : P) : P := h";
    let local = complete(&base, &[("Api", api)]);
    assert!(
        matches!(local.checked.engine.environment().find(&n("untrusted")), Some(ConstantInfo::Defn(d)) if d.safety == fln_env::constants::DefinitionSafety::Unsafe)
    );
    let imported = complete(&base, &[("Main", "prelude\nimport Api"), ("Api", api)]);
    assert!(
        matches!(imported.checked.engine.environment().find(&n("untrusted")), Some(ConstantInfo::Axiom(d)) if d.is_unsafe)
    );
    let invalid = "prelude\nimport Api\ntheorem unsound (P : Prop) (h : P) : P := untrusted P h";
    assert!(check(&base, &[("Main", invalid), ("Api", api)]).is_err());
}

#[test]
fn abbreviation_and_opaque_exposure_defaults_follow_declaration_kind() {
    let base = Engine::builder().build_empty();
    let api = "module\nprelude\npublic import Base\nimport Secret\npublic abbrev reduced : Bit := Bit.on\n@[no_expose] public abbrev hidden : Bit := secret\n@[expose] public section\ndef exposed : Bit := Bit.on\n@[no_expose] def rehidden : Bit := secret\nopaque sealed : Bit := secret\n@[expose] opaque visibleOpaque : Bit := Bit.on\nend";
    let main =
        "prelude\nimport Api\ntheorem reduction (P : Bit -> Prop) (h : P Bit.on) : P reduced := h";
    let imported = complete(
        &base,
        &[
            ("Main", main),
            ("Api", api),
            ("Base", BASE),
            ("Secret", SECRET),
        ],
    );
    let env = imported.checked.engine.environment();
    assert!(
        matches!(env.find(&n("reduced")), Some(ConstantInfo::Defn(d)) if d.hints == fln_env::constants::ReducibilityHints::Abbrev)
    );
    assert!(matches!(
        env.find(&n("exposed")),
        Some(ConstantInfo::Defn(_))
    ));
    assert!(matches!(
        env.find(&n("visibleOpaque")),
        Some(ConstantInfo::Opaque(_))
    ));
    for name in ["hidden", "rehidden", "sealed"] {
        assert!(
            matches!(env.find(&n(name)), Some(ConstantInfo::Axiom(a)) if !a.is_unsafe),
            "{name}"
        );
    }
    let invalid = api.replace(
        "public abbrev reduced : Bit := Bit.on",
        "public abbrev reduced : Bit := secret",
    );
    assert!(
        check(
            &base,
            &[("Api", &invalid), ("Base", BASE), ("Secret", SECRET)]
        )
        .is_err()
    );
}

#[test]
fn hidden_data_instances_keep_private_dictionaries_but_export_real_search_entries() {
    let base = Engine::builder().build_empty();
    let foundation =
        "prelude\ninductive Bit where\n| off\n| on\nclass Pick (A : Type) where\n  value : A";
    let secret = "prelude\nimport Base\ndef hiddenDictionary : Pick Bit := Pick.mk Bit.on";
    let api = "module\nprelude\npublic import Base\nimport Secret\n@[no_expose] public instance selected : Pick Bit := hiddenDictionary\ndef locally (P : Bit -> Prop) (h : P Bit.on) : P Pick.value := h";
    let main = "prelude\nimport Api\nnoncomputable def client : Bit := Pick.value";
    let imported = complete(
        &base,
        &[
            ("Main", main),
            ("Api", api),
            ("Base", foundation),
            ("Secret", secret),
        ],
    );
    let env = imported.checked.engine.environment();
    assert!(matches!(env.find(&n("selected")), Some(ConstantInfo::Axiom(a)) if !a.is_unsafe));
    assert!(
        fln_elab::instances::InstanceRegistry::read(env)
            .unwrap()
            .candidates(&n("Pick"))
            .iter()
            .any(|row| row.declaration == n("selected"))
    );
    assert!(!env.contains(&n("hiddenDictionary")));
    let bad = "prelude\nimport Api\ntheorem invented (P : Bit -> Prop) (h : P Bit.on) : P Pick.value := h";
    assert!(
        check(
            &base,
            &[
                ("Main", bad),
                ("Api", api),
                ("Base", foundation),
                ("Secret", secret)
            ]
        )
        .is_err()
    );
}

#[test]
fn hidden_implementation_edits_cannot_publish_stale_interfaces_or_partial_cache_updates() {
    use fln::source_check::modules::{SourceModuleCacheLimits, SourceModuleSession};
    let names = [n("Main"), n("Api"), n("Base"), n("Secret")];
    let main = "prelude\nimport Api\nnoncomputable def use : Bit := chosen";
    let inputs = [
        SourceModuleInput {
            name: &names[0],
            source: main.as_bytes(),
        },
        SourceModuleInput {
            name: &names[1],
            source: API.as_bytes(),
        },
        SourceModuleInput {
            name: &names[2],
            source: BASE.as_bytes(),
        },
        SourceModuleInput {
            name: &names[3],
            source: SECRET.as_bytes(),
        },
    ];
    let mut session = SourceModuleSession::new(
        Engine::builder().build_empty(),
        KVMap::new(),
        limits(),
        SourceModuleCacheLimits::default(),
    );
    let cold = session
        .check(&inputs, &names[0])
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(cold.elaborated_modules, 4);
    let warm = session
        .check(&inputs, &names[0])
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(warm.reused_modules, 4);
    for changed in [
        API.replace(
            "public def chosen : Bit := localValue",
            "public def chosen : Bit := missing",
        ),
        API.replace(
            "public def chosen : Bit",
            "@[expose] public def chosen : Bit",
        ),
        API.replace(
            "public opaque sealed : Bit := localValue",
            "public opaque sealed : Bit := missing",
        ),
    ] {
        let mut edited = inputs;
        edited[1].source = changed.as_bytes();
        assert!(matches!(session.check(&edited, &names[0]),
            Err(SourceModuleCheckError::Source { module, .. }) if module == n("Api")));
        assert_eq!(session.retained_modules(), 4);
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
        assert!(matches!(
            recovered
                .checked
                .checked
                .engine
                .environment()
                .find(&n("chosen")),
            Some(ConstantInfo::Axiom(_))
        ));
    }
}

#[test]
fn cancellation_at_every_observed_module_checkpoint_never_publishes_half_an_interface() {
    use fln::source_check::modules::{SourceModuleCacheLimits, SourceModuleSession};
    use std::sync::atomic::{AtomicUsize, Ordering};
    struct Stop {
        calls: AtomicUsize,
        at: usize,
    }
    impl fln::CancellationProbe for Stop {
        fn is_cancelled(&self) -> bool {
            self.calls.fetch_add(1, Ordering::Relaxed) + 1 >= self.at
        }
    }
    let names = [n("Main"), n("Api")];
    let inputs = [
        SourceModuleInput { name: &names[0], source: b"prelude\nimport Api\nnoncomputable def use.{u} {A : Sort u} (x : A) : A := identity x" },
        SourceModuleInput { name: &names[1], source: b"module\nprelude\nprivate def helper.{u} {A : Sort u} (x : A) : A := x\npublic def identity.{u} {A : Sort u} (x : A) : A := helper x" },
    ];
    let make_session = || {
        SourceModuleSession::new(
            Engine::builder().build_empty(),
            KVMap::new(),
            limits(),
            SourceModuleCacheLimits::default(),
        )
    };
    let count = Stop {
        calls: AtomicUsize::new(0),
        at: usize::MAX,
    };
    let good = make_session()
        .check_with_cancel(&inputs, &names[0], Some(&count))
        .unwrap()
        .into_complete()
        .unwrap();
    let total = count.calls.load(Ordering::Relaxed);
    assert!(total > 2);
    for at in 1..=total {
        let mut session = make_session();
        let stop = Stop {
            calls: AtomicUsize::new(0),
            at,
        };
        let outcome = session
            .check_with_cancel(&inputs, &names[0], Some(&stop))
            .unwrap();
        assert!(
            matches!(outcome, Outcome::Inconclusive(_)),
            "at={at}, total={total}"
        );
        assert_eq!(session.retained_modules(), 0, "at={at}");
        let recovered = session
            .check(&inputs, &names[0])
            .unwrap()
            .into_complete()
            .unwrap();
        assert_eq!(
            recovered.checked.checked.result_logical_root,
            good.checked.checked.result_logical_root
        );
    }
}

#[test]
fn hidden_local_and_where_helpers_are_checked_but_never_exported() {
    let base = Engine::builder().build_empty();
    let api = "module\nprelude\npublic import Base\nimport Secret\npublic def chosen : Bit :=\n  let rec helper : Bit :=\n    let rec nested : Bit := secret\n    nested\n  helper\npublic opaque sealed : Bit := value where\n  value : Bit := secret\ndef checkedHelper (P : Bit -> Prop) (h : P Bit.on) : P chosen.helper.nested := h";
    let local = complete(&base, &[("Api", api), ("Base", BASE), ("Secret", SECRET)]);
    for name in ["chosen.helper", "chosen.helper.nested", "sealed.value"] {
        let Some(ConstantInfo::Defn(helper)) = local.checked.engine.environment().find(&n(name))
        else {
            panic!("missing checked helper {name}");
        };
        assert_eq!(helper.safety, fln_env::constants::DefinitionSafety::Safe);
        for expr in [&helper.base.type_, &helper.value] {
            assert!(!expr.has_fvar() && !expr.has_loose_bvars());
            assert!(!expr.has_expr_mvar() && !expr.has_level_mvar());
        }
    }
    let imported = complete(
        &base,
        &[
            (
                "Main",
                "prelude\nimport Api\nnoncomputable def use : Bit := chosen",
            ),
            ("Api", api),
            ("Base", BASE),
            ("Secret", SECRET),
        ],
    );
    for hidden in [
        "secret",
        "chosen.helper",
        "chosen.helper.nested",
        "sealed.value",
    ] {
        assert!(
            !imported.checked.engine.environment().contains(&n(hidden)),
            "{hidden}"
        );
    }
    for source in [
        "prelude\nimport Api\nnoncomputable def leak : Bit := chosen.helper",
        "prelude\nimport Api\nnoncomputable def leak : Bit := sealed.value",
    ] {
        assert!(
            check(
                &base,
                &[
                    ("Main", source),
                    ("Api", api),
                    ("Base", BASE),
                    ("Secret", SECRET)
                ]
            )
            .is_err()
        );
    }
}

#[test]
fn hidden_helpers_close_polymorphic_captures_without_changing_public_signatures() {
    let base = Engine::builder().build_empty();
    let api = "module\nprelude\npublic def choose.{u} {A : Sort u} (unused x : A) : A :=\n  let rec helper : A := x\n  helper\ndef verify.{u} {A : Sort u} (x : A) : A := choose.helper x";
    let local = complete(&base, &[("Api", api)]);
    let Some(ConstantInfo::Defn(helper)) =
        local.checked.engine.environment().find(&n("choose.helper"))
    else {
        panic!("helper");
    };
    assert_eq!(helper.base.level_params.len(), 1);
    let imported = complete(&base, &[("Main", "prelude\nimport Api"), ("Api", api)]);
    assert_eq!(
        local
            .checked
            .engine
            .environment()
            .find(&n("choose"))
            .unwrap()
            .constant_val(),
        imported
            .checked
            .engine
            .environment()
            .find(&n("choose"))
            .unwrap()
            .constant_val(),
    );
    assert!(
        !imported
            .checked
            .engine
            .environment()
            .contains(&n("choose.helper"))
    );
}

#[test]
fn hidden_instance_helpers_do_not_duplicate_owner_metadata() {
    let base = Engine::builder().build_empty();
    let foundation =
        "prelude\ninductive Bit where\n| off\n| on\nclass Pick (A : Type) where\n  value : A";
    let api = "module\nprelude\npublic import Base\nimport Secret\n@[no_expose] public instance selected : Pick Bit :=\n  let rec dictionary : Pick Bit := Pick.mk secret\n  dictionary\ndef locally (P : Bit -> Prop) (h : P Bit.on) : P Pick.value := h";
    let local = complete(
        &base,
        &[("Api", api), ("Base", foundation), ("Secret", SECRET)],
    );
    assert!(matches!(
        local
            .checked
            .engine
            .environment()
            .find(&n("selected.dictionary")),
        Some(ConstantInfo::Defn(_))
    ));
    let imported = complete(
        &base,
        &[
            (
                "Main",
                "prelude\nimport Api\nnoncomputable def use : Bit := Pick.value",
            ),
            ("Api", api),
            ("Base", foundation),
            ("Secret", SECRET),
        ],
    );
    for engine in [&local.checked.engine, &imported.checked.engine] {
        let registry = fln_elab::instances::InstanceRegistry::read(engine.environment()).unwrap();
        assert_eq!(
            registry
                .candidates(&n("Pick"))
                .iter()
                .filter(|row| row.declaration == n("selected"))
                .count(),
            1
        );
    }
    assert!(
        !imported
            .checked
            .engine
            .environment()
            .contains(&n("selected.dictionary"))
    );
}

#[test]
fn hidden_helpers_preserve_safety_and_noncomputable_classification() {
    use fln_env::constants::DefinitionSafety;
    let base = Engine::builder().build_empty();
    let api = "module\nprelude\npublic import Base\nimport Secret\npublic unsafe def untrusted : Bit := let rec helper : Bit := secret; helper\npublic noncomputable def unavailable : Bit := let rec helper : Bit := secret; helper";
    let local = complete(&base, &[("Api", api), ("Base", BASE), ("Secret", SECRET)]);
    assert!(
        matches!(local.checked.engine.environment().find(&n("untrusted.helper")), Some(ConstantInfo::Defn(helper)) if helper.safety == DefinitionSafety::Unsafe)
    );
    let tags = fln_elab::noncomputable::read(local.checked.engine.environment()).unwrap();
    assert!(tags.contains(&n("unavailable")));
    assert!(tags.contains(&n("unavailable.helper")));
    let bad = format!("{api}\ndef unsafeLeak : Bit := untrusted.helper");
    assert!(check(&base, &[("Api", &bad), ("Base", BASE), ("Secret", SECRET)]).is_err());
    let imported = complete(
        &base,
        &[
            ("Main", "prelude\nimport Api"),
            ("Api", api),
            ("Base", BASE),
            ("Secret", SECRET),
        ],
    );
    assert!(
        matches!(imported.checked.engine.environment().find(&n("untrusted")), Some(ConstantInfo::Axiom(a)) if a.is_unsafe)
    );
    let tags = fln_elab::noncomputable::read(imported.checked.engine.environment()).unwrap();
    assert!(tags.contains(&n("unavailable")));
    assert!(!tags.contains(&n("unavailable.helper")));
}

#[test]
fn invalid_or_colliding_hidden_helpers_never_publish_a_partial_owner() {
    let base = Engine::builder().build_empty();
    let root = base.logical_root(&KVMap::new());
    for declaration in [
        "public def chosen : Bit := let rec helper : Bit := missing; secret",
        "public def chosen : Bit := let rec helper : Bit := secret; let rec helper : Bit := secret; helper",
        "@[expose] public def chosen.helper : Bit := Bit.off\npublic def chosen : Bit := let rec helper : Bit := secret; helper",
    ] {
        let api = format!("module\nprelude\npublic import Base\nimport Secret\n{declaration}");
        assert!(
            check(&base, &[("Api", &api), ("Base", BASE), ("Secret", SECRET)]).is_err(),
            "{declaration}"
        );
        assert_eq!(base.logical_root(&KVMap::new()), root);
    }
    let recovered = "module\nprelude\npublic import Base\nimport Secret\npublic def chosen : Bit := let rec helper : Bit := secret; helper";
    let result = complete(
        &base,
        &[("Api", recovered), ("Base", BASE), ("Secret", SECRET)],
    );
    assert!(
        result
            .checked
            .engine
            .environment()
            .contains(&n("chosen.helper"))
    );
}

#[test]
fn hidden_proof_instance_helpers_remain_private_checked_implementations() {
    let base = Engine::builder().build_empty();
    let foundation = "prelude\ninductive Truth : Prop where\n| make\nclass Law (P : Prop) : Prop where\n  proof : P";
    let secret = "prelude\nimport Base\ndef hiddenProof : Truth := Truth.make";
    let api = "module\nprelude\npublic import Base\nimport Secret\npublic instance selected : Law Truth := let rec helper : Law Truth := Law.mk hiddenProof; helper";
    let local = complete(
        &base,
        &[("Api", api), ("Base", foundation), ("Secret", secret)],
    );
    assert!(matches!(
        local.checked.engine.environment().find(&n("selected")),
        Some(ConstantInfo::Thm(_))
    ));
    assert!(matches!(
        local
            .checked
            .engine
            .environment()
            .find(&n("selected.helper")),
        Some(ConstantInfo::Thm(_))
    ));
    let imported = complete(
        &base,
        &[
            (
                "Main",
                "prelude\nimport Api\ntheorem use : Truth := Law.proof",
            ),
            ("Api", api),
            ("Base", foundation),
            ("Secret", secret),
        ],
    );
    assert!(matches!(
        imported.checked.engine.environment().find(&n("selected")),
        Some(ConstantInfo::Axiom(_))
    ));
    assert!(
        !imported
            .checked
            .engine
            .environment()
            .contains(&n("selected.helper"))
    );
}
