//! Authored module instances use the same checked export and instance journals
//! as derived dictionaries. Their data bodies are exposed by default at the pin.
#![forbid(unsafe_code)]

use fln::source_check::modules::{
    SourceModuleCacheLimits, SourceModuleCheck, SourceModuleCheckError, SourceModuleCheckLimits,
    SourceModuleSession,
};
use fln::{
    Budget, Engine, EngineAdmissionLimits, KVMap, Name, Outcome, SourceCheckLimits,
    SourceModuleInput,
};
use fln_elab::instances::InstanceRegistry;
use fln_elab::reducibility::{Reducibility, ReducibilityTable};

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

fn check_both(
    files: &[(&str, &str)],
) -> [Result<Outcome<SourceModuleCheck>, SourceModuleCheckError>; 2] {
    let names: Vec<_> = files.iter().map(|(name, _)| n(name)).collect();
    let inputs: Vec<_> = files
        .iter()
        .zip(&names)
        .map(|((_, source), name)| SourceModuleInput {
            name,
            source: source.as_bytes(),
        })
        .collect();
    let options = KVMap::new();
    [
        Engine::builder().build_empty().check_source_modules(
            &inputs,
            &names[0],
            &options,
            limits(),
        ),
        fln::source_check::modules::imported::SourceOleanImport::empty(&options)
            .check_source_modules(&inputs, &names[0], &options, limits(), None),
    ]
}

const BASE: &str = "prelude\ninductive Token where\n| left\n| right\n| extra\nclass Pick (A : Type) where\n  value : A\nstructure Box (A : Type) where\n  value : A\ndef chosen {A : Type} [p : Pick A] : A := p.value";
const HEADER: &str = "module\nprelude\npublic import Base\n";

#[test]
fn named_and_anonymous_parameterized_public_instances_export_reducible_dictionaries() {
    let api = format!(
        "{HEADER}namespace API\npublic instance tokenChoice : Pick Token := Pick.mk Token.left\npublic instance {{A : Type}} [p : Pick A] : Pick (Box A) := Pick.mk (Box.mk p.value)\nend API"
    );
    let main = "prelude\nimport Api\ndef boxed : Box Token := chosen\ndef correct (P : Token -> Prop) (h : P Token.left) : P boxed.value := h";
    for result in check_both(&[("Main", main), ("Api", &api), ("Base", BASE)]) {
        let checked = result.unwrap().into_complete().unwrap();
        let env = checked.checked.engine.environment();
        assert!(env.contains(&n("correct")));
        assert!(env.contains(&n("API.tokenChoice")));
        let registry = InstanceRegistry::read(env).unwrap();
        let candidates = registry.candidates(&n("Pick"));
        assert_eq!(candidates.len(), 2);
        let reducibility = ReducibilityTable::effective(env).unwrap();
        for candidate in candidates {
            assert_eq!(
                reducibility.status(&candidate.declaration),
                Reducibility::ImplicitReducible,
                "{:?}",
                candidate.declaration
            );
            assert!(
                !candidate
                    .declaration
                    .to_display_string()
                    .starts_with("_private.")
            );
        }
    }
}

#[test]
fn public_instances_with_universes_and_proof_fields_are_data_instances() {
    let api = "module\nprelude\npublic class Carry.{u} (A : Type u) where\n  value : A\npublic class Evidence (P : Prop) where\n  proof : P\npublic instance carry.{u} {A : Type u} (x : A) : Carry A := Carry.mk x\n@[expose] public instance evidence (P : Prop) (h : P) : Evidence P := Evidence.mk h";
    let main = "prelude\nimport Api\ndef fromCarry.{u} {A : Type u} (x : A) : A := (carry x).value\ndef fromEvidence (P : Prop) (h : P) : P := (evidence P h).proof";
    for result in check_both(&[("Main", main), ("Api", api)]) {
        let checked = result.unwrap().into_complete().unwrap();
        let env = checked.checked.engine.environment();
        assert!(env.contains(&n("fromCarry")));
        assert!(env.contains(&n("fromEvidence")));
        assert_eq!(
            ReducibilityTable::effective(env)
                .unwrap()
                .status(&n("evidence")),
            Reducibility::ImplicitReducible
        );
    }
}

#[test]
fn public_and_private_instance_priorities_keep_independent_recency() {
    for (tail, outside) in [
        ("", "left"),
        (
            "public instance (priority := 2000) newest : Pick Token := Pick.mk Token.extra",
            "extra",
        ),
    ] {
        let api = format!(
            "{HEADER}public instance (priority := 2000) first : Pick Token := Pick.mk Token.left\nprivate instance (priority := 2000) hidden : Pick Token := Pick.mk Token.right\npublic instance (priority := 500) lower : Pick Token := Pick.mk Token.extra\ndef localChoice : Token := chosen\ndef localCorrect (P : Token -> Prop) (h : P Token.right) : P localChoice := h\n@[expose] public def publicChoice : Token := chosen\n{tail}"
        );
        let main = format!(
            "prelude\nimport Api\ndef observed : Token := chosen\ndef correct (P : Token -> Prop) (h : P Token.{outside}) : P observed := h\ndef earlier (P : Token -> Prop) (h : P Token.left) : P publicChoice := h"
        );
        for result in check_both(&[("Main", &main), ("Api", &api), ("Base", BASE)]) {
            let checked = result.unwrap().into_complete().unwrap();
            let env = checked.checked.engine.environment();
            assert!(env.contains(&n("correct")));
            assert!(env.contains(&n("earlier")));
            assert!(!env.contains(&private("Api", "hidden")));
            assert!(!env.contains(&private("Api", "localChoice")));
        }
        let wrong = "prelude\nimport Api\ndef observed : Token := chosen\ndef wrong (P : Token -> Prop) (h : P Token.right) : P observed := h".to_owned();
        for result in check_both(&[("Main", &wrong), ("Api", &api), ("Base", BASE)]) {
            assert!(
                matches!(result, Err(SourceModuleCheckError::Source { module, .. }) if module == n("Main"))
            );
        }
    }
}

#[test]
fn public_sections_export_instances_and_restore_the_private_default() {
    let api = format!(
        "{HEADER}public section\ninstance visible : Pick Token := Pick.mk Token.left\nprivate instance (priority := 2000) hidden : Pick Token := Pick.mk Token.right\nend\ninstance (priority := 3000) restored : Pick Token := Pick.mk Token.extra\ndef localChoice : Token := chosen\ndef localCorrect (P : Token -> Prop) (h : P Token.extra) : P localChoice := h"
    );
    let main = "prelude\nimport Api\ndef observed : Token := chosen\ndef correct (P : Token -> Prop) (h : P Token.left) : P observed := h";
    for result in check_both(&[("Main", main), ("Api", &api), ("Base", BASE)]) {
        let checked = result.unwrap().into_complete().unwrap();
        let env = checked.checked.engine.environment();
        assert!(env.contains(&n("visible")));
        assert_eq!(
            InstanceRegistry::read(env)
                .unwrap()
                .candidates(&n("Pick"))
                .len(),
            1
        );
        for name in ["hidden", "restored", "localChoice"] {
            assert!(!env.contains(&private("Api", name)), "{name}");
        }
    }
}

#[test]
fn public_instance_signatures_and_bodies_cannot_use_private_dependencies() {
    let secret = "prelude\nimport Base\ninductive Secret where\n| make\ndef hidden : Token := Token.right\ninstance hiddenDictionary : Pick Token := Pick.mk Token.right";
    for declaration in [
        "public instance leak : Pick Token := Pick.mk hidden",
        "public instance leak : Pick Secret := Pick.mk Secret.make",
        "public instance leak : Pick (Box Token) := Pick.mk (Box.mk chosen)",
        "instance localDictionary : Pick Token := Pick.mk Token.left\npublic instance leak : Pick (Box Token) := Pick.mk (Box.mk chosen)",
        "def localValue : Token := Token.left\npublic instance leak : Pick Token := Pick.mk localValue",
        "variable (x : Secret)\npublic instance leak : Pick Secret := Pick.mk x",
    ] {
        let api = format!("{HEADER}import Secret\n{declaration}");
        for result in check_both(&[
            ("Main", "prelude\nimport Api"),
            ("Api", &api),
            ("Base", BASE),
            ("Secret", secret),
        ]) {
            assert!(
                matches!(result, Err(SourceModuleCheckError::Source { module, .. }) if module == n("Api")),
                "{declaration}"
            );
        }
    }
}

#[test]
fn public_instance_visibility_collisions_remain_explicit_refusals() {
    for declaration in [
        "instance duplicate : Pick Token := Pick.mk Token.left\npublic instance duplicate : Pick Token := Pick.mk Token.right",
        "public instance duplicate : Pick Token := Pick.mk Token.left\nprivate instance duplicate : Pick Token := Pick.mk Token.right",
    ] {
        let api = format!("{HEADER}{declaration}");
        for result in check_both(&[
            ("Main", "prelude\nimport Api"),
            ("Api", &api),
            ("Base", BASE),
        ]) {
            assert!(
                matches!(result, Err(SourceModuleCheckError::Source { module, .. }) if module == n("Api")),
                "{declaration}"
            );
        }
    }
}

#[test]
fn proof_class_instances_export_checked_interfaces_even_with_explicit_exposure() {
    for prefix in ["public", "@[expose] public"] {
        let api = format!(
            "module\nprelude\npublic class Law (P : Prop) : Prop where\n  proof : P\n{prefix} instance law (P : Prop) (h : P) : Law P := Law.mk h"
        );
        let main =
            "prelude\nimport Api\ntheorem used (P : Prop) (h : P) : P := @Law.proof P (law P h)";
        let local = check_both(&[("Api", &api)])
            .into_iter()
            .map(|result| result.unwrap().into_complete().unwrap())
            .collect::<Vec<_>>();
        for checked in &local {
            assert!(matches!(
                checked.checked.engine.environment().find(&n("law")),
                Some(fln::ConstantInfo::Thm(_))
            ));
        }
        for result in check_both(&[("Main", main), ("Api", &api)]) {
            let checked = result.unwrap().into_complete().unwrap();
            let env = checked.checked.engine.environment();
            let fln::ConstantInfo::Axiom(interface) = env.find(&n("law")).unwrap() else {
                panic!("a module proof instance must export its checked interface");
            };
            assert!(!interface.is_unsafe);
            for defining_module in &local {
                assert_eq!(
                    &interface.base,
                    defining_module
                        .checked
                        .engine
                        .environment()
                        .find(&n("law"))
                        .unwrap()
                        .constant_val()
                );
            }
            assert_eq!(
                ReducibilityTable::effective(env).unwrap().status(&n("law")),
                Reducibility::Semireducible
            );
        }
    }
}

#[test]
fn changed_or_failed_public_instances_do_not_publish_stale_cached_dictionaries() {
    let mut session = SourceModuleSession::new(
        Engine::builder().build_empty(),
        KVMap::new(),
        limits(),
        SourceModuleCacheLimits::default(),
    );
    let names = [n("Main"), n("Api"), n("Base")];
    let good = format!("{HEADER}public instance dictionary : Pick Token := Pick.mk Token.left");
    let main = "prelude\nimport Api\ndef observed : Token := chosen\ndef correct (P : Token -> Prop) (h : P Token.left) : P observed := h";
    let files = [
        SourceModuleInput {
            name: &names[0],
            source: main.as_bytes(),
        },
        SourceModuleInput {
            name: &names[1],
            source: good.as_bytes(),
        },
        SourceModuleInput {
            name: &names[2],
            source: BASE.as_bytes(),
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
    let retained = session.retained_modules();
    for changed in [
        format!("{HEADER}private instance dictionary : Pick Token := Pick.mk Token.left"),
        format!("{HEADER}public instance dictionary : Pick Token := Pick.mk Token.right"),
        format!("{good}\npublic instance broken : Pick Token := Token.left"),
    ] {
        let mut changed_files = files;
        changed_files[1].source = changed.as_bytes();
        assert!(matches!(
            session.check(&changed_files, &names[0]),
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
fn no_expose_overrides_explicit_and_inherited_data_instance_exposure() {
    for declaration in [
        "@[no_expose] public instance dictionary : Pick Token := Pick.mk Token.left",
        "@[expose, no_expose] public instance dictionary : Pick Token := Pick.mk Token.left",
        "@[expose] public section\n@[no_expose] instance dictionary : Pick Token := Pick.mk Token.left\nend",
    ] {
        let api = format!("{HEADER}{declaration}");
        for result in check_both(&[
            ("Main", "prelude\nimport Api"),
            ("Api", &api),
            ("Base", BASE),
        ]) {
            let checked = result.unwrap().into_complete().unwrap();
            let env = checked.checked.engine.environment();
            assert!(
                matches!(env.find(&n("dictionary")), Some(fln_env::constants::ConstantInfo::Axiom(signature)) if !signature.is_unsafe)
            );
            assert!(
                InstanceRegistry::read(env)
                    .unwrap()
                    .candidates(&n("Pick"))
                    .iter()
                    .any(|row| row.declaration == n("dictionary"))
            );
        }
    }
}
