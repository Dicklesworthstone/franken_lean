//! Generated references and instance names retain private module identities.
#![forbid(unsafe_code)]

use fln::source_check::modules::{SourceModuleCheck, SourceModuleCheckLimits};
use fln::{
    Budget, Engine, EngineAdmissionLimits, KVMap, Name, SourceCheckLimits, SourceModuleInput,
};

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

fn engine() -> Engine {
    Engine::with_source_seed(limits().source.admission)
        .unwrap()
        .into_complete()
        .unwrap()
}

fn checked(base: &Engine, files: &[(&str, &str)]) -> SourceModuleCheck {
    let names: Vec<_> = files.iter().map(|(name, _)| n(name)).collect();
    let modules: Vec<_> = files
        .iter()
        .zip(&names)
        .map(|((_, source), name)| SourceModuleInput {
            name,
            source: source.as_bytes(),
        })
        .collect();
    base.check_source_modules(&modules, &n("Main"), &KVMap::new(), limits())
        .unwrap_or_else(|error| panic!("{files:?}: {error:?}"))
        .into_complete()
        .unwrap()
}

#[test]
fn anonymous_instances_are_private_and_avoid_both_public_and_private_names() {
    // Elab/Util.lean's mkUnusedBaseName sees both visibility classes. The
    // source class is local, so the pin adds no project suffix to instPick.
    let base = engine();
    let source = "module\nprelude\nimport Existing\nnamespace Local\nclass Pick where\n  value : Nat\ndef instPick_1 : Nat := 1\ninstance : Pick := Pick.mk 7\ninstance : Pick := Pick.mk 13\ndef chosen : Pick := inferInstance\ntheorem selected : chosen.value = 13 := by rfl\nend Local";
    let result = checked(
        &base,
        &[
            ("Main", source),
            ("Existing", "prelude\ndef Local.instPick : Nat := 0"),
        ],
    );
    for declaration in [
        "Local.Pick",
        "Local.instPick_1",
        "Local.instPick_2",
        "Local.instPick_3",
        "Local.chosen",
        "Local.selected",
    ] {
        assert!(
            result
                .checked
                .engine
                .environment()
                .contains(&private("Main", declaration)),
            "{declaration}"
        );
        assert!(
            !result
                .checked
                .engine
                .environment()
                .contains(&n(declaration)),
            "{declaration}"
        );
    }
    assert!(
        result
            .checked
            .engine
            .environment()
            .contains(&n("Local.instPick"))
    );
    assert!(
        !result
            .checked
            .engine
            .environment()
            .contains(&private("Main", "Local.instPick"))
    );
    assert!(result.checked.scope.namespace.is_anonymous());
}

#[test]
fn derived_inhabited_instances_and_helpers_remain_private_and_resolve_locally() {
    let base = engine();
    let source = "module\nprelude\nnamespace Local\nstructure Box where\n  value : Nat := 37\nderiving Inhabited\ninductive Choice where\n| left\n| right\nderiving Inhabited\ndef box : Box := default\ndef choice : Choice := default\ntheorem field : box.value = 37 := by rfl\ntheorem constructor : choice = Choice.left := by rfl\nend Local\nopen Local\ndef use : Box := instInhabitedBox.default";
    let local = checked(&base, &[("Main", source)]);
    for declaration in [
        "Local.instInhabitedBox",
        "Local.instInhabitedBox.default",
        "Local.instInhabitedChoice",
        "Local.instInhabitedChoice.default",
        "Local.field",
        "Local.constructor",
        "use",
    ] {
        assert!(
            local
                .checked
                .engine
                .environment()
                .contains(&private("Main", declaration)),
            "{declaration}"
        );
        assert!(
            !local.checked.engine.environment().contains(&n(declaration)),
            "{declaration}"
        );
    }
    let imported = checked(
        &base,
        &[("Main", "prelude\nimport Library"), ("Library", source)],
    );
    assert_eq!(
        fln_elab::instances::InstanceRegistry::read(imported.checked.engine.environment()).unwrap(),
        fln_elab::instances::InstanceRegistry::read(base.environment()).unwrap(),
    );
    assert!(
        !imported
            .checked
            .engine
            .environment()
            .contains(&private("Library", "Local.instInhabitedBox"))
    );
    assert!(
        !imported
            .checked
            .engine
            .environment()
            .contains(&n("Local.instInhabitedBox"))
    );
}

#[test]
fn overloaded_private_candidates_remain_distinct_on_elaboration_reentry() {
    let base = engine();
    let module = n("Main");
    let source = b"module\nprelude\nnamespace Left\ndef choose (n : Nat) : Nat := n\nend Left\nnamespace Right\ndef choose (n : Nat) : Nat := n + 1\nend Right\nopen Left Right\ndef result : Nat := choose 7";
    let root = base.logical_root(&KVMap::new());
    let error = base
        .check_source_modules(
            &[SourceModuleInput {
                name: &module,
                source,
            }],
            &module,
            &KVMap::new(),
            limits(),
        )
        .unwrap_err();
    // Both exact internal candidates elaborate, so this is a true ambiguity,
    // not a failed lookup of a generated `_root_._private...` identifier.
    assert!(
        error.to_string().contains("Ambiguous term `choose`"),
        "{error}"
    );
    assert_eq!(error.disposition().0, "elaboration");
    assert_eq!(base.logical_root(&KVMap::new()), root);
}
