//! Namespace-scoped instance commands publish only checked dormant dictionaries.
#![forbid(unsafe_code)]

use fln::source_check::modules::{
    SourceModuleCacheLimits, SourceModuleCheckLimits, SourceModuleSession,
};
use fln::{
    Budget, ConstantInfo, Engine, EngineAdmissionLimits, KVMap, Name, SourceCheckLimits,
    SourceModuleInput,
};
use fln_elab::instances::{InstanceRegistry, scoped};
use fln_elab::reducibility::{Reducibility, ReducibilityTable};

fn n(text: &str) -> Name {
    Name::from_components(text.split('.'))
}

fn limits() -> SourceCheckLimits {
    SourceCheckLimits::new(EngineAdmissionLimits::new(Budget::for_stack_bytes(
        2 * 1024 * 1024,
    )))
}

fn checked(engine: &Engine, source: &str) -> fln::SourceFileCheck {
    engine
        .check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .unwrap()
}

fn base() -> Engine {
    let engine = Engine::with_source_seed(limits().admission)
        .unwrap()
        .into_complete()
        .unwrap();
    checked(
        &engine,
        "class Pick where\n  value : Nat\ninstance fallback : Pick := Pick.mk 1\ndef chosen [p : Pick] : Nat := Pick.value",
    )
    .engine
}

#[test]
fn named_and_anonymous_scoped_commands_follow_namespace_lifetimes_and_priority() {
    let base = base();
    let result = checked(
        &base,
        r#"
namespace Alternative
scoped instance Nested.named : Pick := Pick.mk 2
theorem qualifiedName : chosen = 2 := by rfl
scoped instance (priority := 2000) : Pick := Pick.mk 3
theorem inside : chosen = 3 := by rfl
end Alternative
theorem outside : chosen = 1 := by rfl
section
open scoped Alternative
theorem opened : chosen = 3 := by rfl
end
theorem restored : chosen = 1 := by rfl
namespace Alternative
theorem reentered : chosen = 3 := by rfl
end Alternative
"#,
    );
    assert_eq!(result.theorems, 6);
    let env = result.engine.environment();
    let dormant = InstanceRegistry::read(env).unwrap();
    let [fallback] = dormant.candidates(&n("Pick")) else {
        panic!("neither scoped declaration may become a global candidate");
    };
    assert_eq!(fallback.declaration, n("fallback"));
    assert!(!result.scope.instance_scopes.is_active(&n("Alternative")));
    let mut active = scoped::ActiveScopes::default();
    active.activate(env, &n("Alternative")).unwrap();
    let registry = InstanceRegistry::read_with_scopes(env, &active).unwrap();
    let [anonymous, named, global] = registry.candidates(&n("Pick")) else {
        panic!("both scoped dictionaries and the fallback must participate");
    };
    assert_eq!(anonymous.priority, 2000);
    assert_eq!(anonymous.declaration.parent(), n("Alternative"));
    assert_eq!(named.declaration, n("Alternative.Nested.named"));
    assert_eq!(global.declaration, n("fallback"));
    let statuses = ReducibilityTable::effective(env).unwrap();
    for instance in [anonymous, named] {
        assert!(matches!(
            env.find(&instance.declaration),
            Some(ConstantInfo::Defn(_))
        ));
        assert_eq!(
            statuses.status(&instance.declaration),
            Reducibility::ImplicitReducible
        );
    }
    assert!(!base.environment().contains(&n("Alternative.Nested.named")));
}

#[test]
fn scoped_command_module_replay_keeps_imported_instances_dormant() {
    let mut session = SourceModuleSession::new(
        base(),
        KVMap::new(),
        SourceModuleCheckLimits::new(limits()),
        SourceModuleCacheLimits::default(),
    );
    let library = n("Library");
    let consumer = n("Consumer");
    let modules = [
        SourceModuleInput {
            name: &library,
            source: b"namespace Regional\nscoped instance regional : Pick := Pick.mk 7\nend Regional",
        },
        SourceModuleInput {
            name: &consumer,
            source: b"import Library\ntheorem dormant : chosen = 1 := by rfl\nopen scoped Regional\ntheorem active : chosen = 7 := by rfl",
        },
    ];
    let first = session
        .check(&modules, &consumer)
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(first.elaborated_modules, 2);
    let root = first.checked.checked.result_logical_root;
    let warm = session
        .check(&modules, &consumer)
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(warm.reused_modules, 2);
    assert_eq!(warm.checked.checked.result_logical_root, root);
    let registry = InstanceRegistry::read(warm.checked.checked.engine.environment()).unwrap();
    assert_eq!(registry.candidates(&n("Pick")).len(), 1);
    assert_eq!(
        registry.candidates(&n("Pick"))[0].declaration,
        n("fallback")
    );
    assert!(
        registry
            .instance_namespaces()
            .any(|name| name == &n("Regional"))
    );
}

#[test]
fn invalid_scoped_declarations_publish_no_dictionary_or_registration() {
    let base = base();
    let root = base.logical_root(&KVMap::new());
    for source in [
        "scoped instance bad : Pick := Pick.mk 2",
        "scoped instance : Pick := Pick.mk 2",
        "namespace Region\nscoped instance bad : Nat := 2",
        "namespace Region\nscoped instance bad : Pick := 2",
        "namespace Region\nscoped instance (priority := 4294967296) bad : Pick := Pick.mk 2",
    ] {
        assert!(
            base.check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
                .is_err(),
            "{source}"
        );
        assert_eq!(base.logical_root(&KVMap::new()), root);
        assert!(!base.environment().contains(&n("bad")));
        assert!(!base.environment().contains(&n("Region.bad")));
        assert!(
            InstanceRegistry::read(base.environment())
                .unwrap()
                .instance_namespaces()
                .next()
                .is_none()
        );
    }
    // The single-declaration entry point must not silently promote root-scoped
    // syntax to a global instance after the ordinary checker admits its body.
    assert!(
        base.admit_source_declaration(
            b"scoped instance bad : Pick := Pick.mk 2",
            &KVMap::new(),
            limits().admission,
        )
        .is_err()
    );
    assert_eq!(base.logical_root(&KVMap::new()), root);
}

#[test]
fn local_declarations_expire_instead_of_becoming_dormant_namespace_instances() {
    let base = base();
    let result = checked(
        &base,
        "namespace Region\nlocal instance choice : Pick := Pick.mk 2\n\
         theorem inside : chosen = 2 := by rfl\nend Region\n\
         theorem outside : chosen = 1 := by rfl\nnamespace Region\n\
         theorem reopened : chosen = 1 := by rfl\n\
         theorem explicitChoice : @chosen choice = 2 := by rfl\nend Region",
    );
    assert_eq!(result.theorems, 4);
    let registry = InstanceRegistry::read(result.engine.environment()).unwrap();
    assert_eq!(registry.candidates(&n("Pick")).len(), 1);
    assert!(registry.instance_namespaces().next().is_none());
    assert!(result.engine.environment().contains(&n("Region.choice")));
    assert!(!base.environment().contains(&n("Region.choice")));
}

#[test]
fn public_scoped_proof_instances_export_only_their_checked_interfaces() {
    let base = n("Base");
    let secret = n("Secret");
    let library = n("Library");
    let consumer = n("Consumer");
    let modules = [
        SourceModuleInput {
            name: &base,
            source: b"prelude\ninductive Truth : Prop where\n| make\nclass Law (P : Prop) : Prop where\n  proof : P\ndef chosenLaw (P : Prop) [law : Law P] : Law P := law",
        },
        SourceModuleInput {
            name: &secret,
            source: b"prelude\nimport Base\ndef hiddenProof : Truth := Truth.make",
        },
        SourceModuleInput {
            name: &library,
            source: b"module\nprelude\npublic import Base\nimport Secret\nnamespace API\npublic scoped instance witness : Law Truth := Law.mk hiddenProof\nend API",
        },
        SourceModuleInput {
            name: &consumer,
            source: b"prelude\nimport Library\nopen scoped API\ntheorem client : Truth := @Law.proof Truth (chosenLaw Truth)",
        },
    ];
    let engine = Engine::builder().build_empty();
    let checked = engine
        .check_source_modules(
            &modules,
            &consumer,
            &KVMap::new(),
            SourceModuleCheckLimits::new(limits()),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    let env = checked.checked.engine.environment();
    let Some(ConstantInfo::Axiom(interface)) = env.find(&n("API.witness")) else {
        panic!("a public proof instance must export only its checked interface");
    };
    assert!(!interface.is_unsafe);
    assert!(matches!(env.find(&n("client")), Some(ConstantInfo::Thm(_))));
    assert!(!env.contains(&n("hiddenProof")));
    assert!(
        InstanceRegistry::read(env)
            .unwrap()
            .candidates(&n("Law"))
            .is_empty()
    );
    let active =
        InstanceRegistry::read_with_scopes(env, &checked.checked.scope.instance_scopes).unwrap();
    assert_eq!(
        active.candidates(&n("Law"))[0].declaration,
        n("API.witness")
    );
    assert_eq!(
        ReducibilityTable::effective(env)
            .unwrap()
            .status(&n("API.witness")),
        Reducibility::Semireducible
    );
}
