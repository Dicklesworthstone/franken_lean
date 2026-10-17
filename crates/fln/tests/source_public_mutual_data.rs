//! Export complete mutual data bundles through the normal two-world module path.
#![forbid(unsafe_code)]

use fln::source_check::modules::{
    SourceModuleCheck, SourceModuleCheckError, SourceModuleCheckLimits,
};
use fln::{
    Budget, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap, Name, Outcome,
    SourceCheckLimits, SourceModuleInput,
};
use fln_env::constants::ConstantInfo;

fn n(text: &str) -> Name {
    Name::from_components(text.split('.'))
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
fn check(
    base: &Engine,
    files: &[(&str, &str)],
) -> Result<Outcome<SourceModuleCheck>, SourceModuleCheckError> {
    let names: Vec<_> = files.iter().map(|(name, _)| n(name)).collect();
    let modules: Vec<_> = files
        .iter()
        .zip(&names)
        .map(|((_, source), name)| SourceModuleInput {
            name,
            source: source.as_bytes(),
        })
        .collect();
    base.check_source_modules(&modules, &names[0], &KVMap::new(), limits())
}
fn complete(base: &Engine, files: &[(&str, &str)]) -> SourceModuleCheck {
    check(base, files)
        .unwrap_or_else(|error| panic!("{files:?}\n{error:?}"))
        .into_complete()
        .unwrap()
}
fn run(base: &Engine, source: &str, expected: &str) {
    let result = base
        .execute_source_definitions(
            &[source.as_bytes()],
            &KVMap::new(),
            EngineExecutionLimits::new(limits().source.admission.kernel),
        )
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .unwrap();
    let fln::VmExit::Returned(value) = &result.executions.last().unwrap().exit else {
        panic!("expected native execution");
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
        Some(expected)
    );
}

const DATA: &str = r#"mutual
  /-- Public tree, including its constructors. -/
  public inductive Tree (A : Type) where
    | leaf (value : A)
    | node (children : Forest A)
  public inductive Forest (A : Type) where
    | nil
    | cons (head : Tree A) (tail : Forest A)
end
"#;

#[test]
fn public_families_export_constructors_recursors_and_execute_in_the_importer() {
    let base = engine();
    let api = format!("module\nprelude\nnamespace API\n{DATA}def secret : Nat := 89\nend API");
    let client = "prelude\nimport Api\ndef built : API.Tree Nat := API.Tree.node (API.Forest.cons (API.Tree.leaf 7) API.Forest.nil)\ndef inspect (t : API.Tree Nat) : Nat := match t with | API.Tree.leaf n => n | API.Tree.node _ => 23";
    let imported = complete(&base, &[("Main", client), ("Api", &api)]);
    let env = imported.checked.engine.environment();
    for family in ["API.Tree", "API.Forest"] {
        assert!(
            matches!(env.find(&n(family)), Some(ConstantInfo::Induct(info)) if info.all.len() == 2)
        );
        assert!(
            matches!(env.find(&n(&format!("{family}.rec"))), Some(ConstantInfo::Rec(info)) if info.num_motives == 2)
        );
        for helper in ["casesOn", "recOn"] {
            assert!(env.contains(&n(&format!("{family}.{helper}"))));
        }
    }
    for ctor in [
        "API.Tree.leaf",
        "API.Tree.node",
        "API.Forest.nil",
        "API.Forest.cons",
    ] {
        assert!(matches!(env.find(&n(ctor)), Some(ConstantInfo::Ctor(_))));
    }
    assert!(!env.contains(&n("API.secret")));
    assert!(!env.contains(&n("_private.Api.0.API.secret")));
    run(&imported.checked.engine, "#eval inspect built", "23");
    assert!(!base.environment().contains(&n("API.Tree")));
}

#[test]
fn public_section_defaults_and_explicit_private_groups_restore_lexical_visibility() {
    let base = engine();
    let public = DATA.replace("public inductive", "inductive");
    let private = DATA
        .replace("public inductive", "private inductive")
        .replace("Tree", "HiddenTree")
        .replace("Forest", "HiddenForest");
    let api =
        format!("module\nprelude\npublic section\n{public}{private}end\ndef secret : Nat := 89");
    let imported = complete(
        &base,
        &[
            (
                "Main",
                "prelude\nimport Api\ndef tree : Tree Nat := Tree.leaf 31",
            ),
            ("Api", &api),
        ],
    );
    let env = imported.checked.engine.environment();
    assert!(env.contains(&n("Tree.leaf")));
    assert!(!env.contains(&n("HiddenTree")));
    assert!(!env.contains(&n("_private.Api.0.HiddenTree")));
    assert!(!env.contains(&n("_private.Api.0.secret")));
    assert!(
        check(
            &base,
            &[
                (
                    "Main",
                    "prelude\nimport Api\ndef bad : HiddenTree Nat := HiddenTree.leaf 0"
                ),
                ("Api", &api)
            ]
        )
        .is_err()
    );
}

#[test]
fn exported_constructor_fields_require_public_import_dependencies() {
    let base = engine();
    let secret = "prelude\ninductive Token where\n| one\n| two";
    let group = "mutual\n  public inductive Box where\n    | token (x : Token)\n    | nest (x : Boxes)\n  public inductive Boxes where\n    | nil\n    | cons (x : Box) (xs : Boxes)\nend";
    let hidden = format!("module\nprelude\nimport Secret\n{group}");
    assert!(check(&base, &[("Api", &hidden), ("Secret", secret)]).is_err());
    let visible = format!("module\nprelude\npublic import Secret\n{group}");
    let imported = complete(
        &base,
        &[
            (
                "Main",
                "prelude\nimport Api\ndef box : Box := Box.token Token.two",
            ),
            ("Api", &visible),
            ("Secret", secret),
        ],
    );
    assert!(imported.checked.engine.environment().contains(&n("box")));
    assert!(!base.environment().contains(&n("Box")));
}

#[test]
fn public_mutual_propositions_retain_their_prop_only_recursors() {
    let base = engine();
    let api = "module\nprelude\nmutual\n  public inductive P : Prop where\n    | base\n    | step (q : Q)\n  public inductive Q : Prop where\n    | step (p : P)\nend\npublic theorem start : Q := Q.step P.base";
    let result = complete(
        &base,
        &[
            (
                "Main",
                "prelude\nimport Api\ntheorem proof : P := P.step start",
            ),
            ("Api", api),
        ],
    );
    let env = result.checked.engine.environment();
    assert!(matches!(env.find(&n("start")), Some(ConstantInfo::Axiom(info)) if !info.is_unsafe));
    assert!(
        matches!(env.find(&n("P.rec")), Some(ConstantInfo::Rec(info)) if info.base.level_params.is_empty())
    );
    assert!(matches!(env.find(&n("proof")), Some(ConstantInfo::Thm(_))));
}

#[test]
fn failed_export_rejects_the_entire_block_without_polluting_the_next_request() {
    let base = engine();
    let invalid = "module\nprelude\nmutual\n  public inductive A where\n    | mk (b : B)\n  public inductive B where\n    | bad (f : A -> Nat)\nend";
    assert!(check(&base, &[("Api", invalid)]).is_err());
    let mixed = DATA.replacen("public inductive Forest", "private inductive Forest", 1);
    assert!(check(&base, &[("Api", &format!("module\nprelude\n{mixed}"))]).is_err());
    // Executable companions require a different export representation. An
    // exposed modifier must not promote them along with public data bundles.
    let partial = "module\nprelude\nmutual\n  @[expose] public partial def left (n : Nat) : Nat := right n\n  @[expose] public partial def right (n : Nat) : Nat := left n\nend";
    assert!(check(&base, &[("Api", partial)]).is_err());
    for name in ["A", "B", "A.rec", "Tree", "Forest"] {
        assert!(!base.environment().contains(&n(name)));
    }
    let valid = format!("module\nprelude\n{DATA}");
    let one = complete(&base, &[("Api", &valid)]);
    let two = complete(&base, &[("Api", &valid)]);
    assert_eq!(
        one.checked.result_logical_root,
        two.checked.result_logical_root
    );
}

#[test]
fn public_mutual_data_runs_through_the_actual_source_module_execution_graph() {
    use fln::source_check::modules::{execution::SourceProgramLimits, imported::SourceOleanImport};
    let options = KVMap::new();
    let imported = SourceOleanImport::empty(&options);
    let names = [n("Main"), n("Facade"), n("Api")];
    // No ambient seed: every type needed by execution is an admitted source declaration.
    let api = b"module\nprelude\nmutual\n  public inductive Tree where | leaf | node (xs : Forest)\n  public inductive Forest where | nil | cons (head : Tree) (tail : Forest)\nend\n@[expose] public def selected : Tree := Tree.node Forest.nil";
    let modules = [
        SourceModuleInput {
            name: &names[0],
            source: b"prelude\nimport Facade\n#eval selected",
        },
        SourceModuleInput {
            name: &names[1],
            source: b"module\nprelude\npublic import Api",
        },
        SourceModuleInput {
            name: &names[2],
            source: api,
        },
    ];
    let program = imported
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
    assert_eq!(
        program
            .modules
            .iter()
            .map(|m| &m.module)
            .collect::<Vec<_>>(),
        vec![&names[2], &names[1], &names[0]]
    );
    let fln::VmExit::Returned(value) = &program
        .modules
        .last()
        .unwrap()
        .commands
        .batch
        .executions
        .last()
        .unwrap()
        .exit
    else {
        panic!("expected native result from exported constructor application");
    };
    assert_eq!(
        fln::vm_value_kind(&value.value),
        fln_vm::interpreter::ValueKind::Ctor(1)
    );
    let mut hidden = modules;
    hidden[1].source = b"module\nprelude\nimport Api";
    assert!(
        imported
            .execute_source_modules(
                &hidden,
                &names[0],
                &options,
                SourceProgramLimits::new(EngineExecutionLimits::new(
                    limits().source.admission.kernel
                )),
                None,
            )
            .is_err()
    );
}

#[test]
fn cached_exports_do_not_survive_a_visibility_change_and_failed_rebuild_is_atomic() {
    use fln::source_check::modules::{SourceModuleCacheLimits, SourceModuleSession};
    let mut session = SourceModuleSession::new(
        engine(),
        KVMap::new(),
        limits(),
        SourceModuleCacheLimits::default(),
    );
    let names = [n("Main"), n("Api")];
    let api = format!("module\nprelude\n{DATA}");
    let modules = [
        SourceModuleInput {
            name: &names[0],
            source: b"prelude\nimport Api\ndef tree : Tree Nat := Tree.leaf 31",
        },
        SourceModuleInput {
            name: &names[1],
            source: api.as_bytes(),
        },
    ];
    let cold = session
        .check(&modules, &names[0])
        .unwrap()
        .into_complete()
        .unwrap();
    let warm = session
        .check(&modules, &names[0])
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!((cold.elaborated_modules, warm.reused_modules), (2, 2));
    let private_api = api.replace("public inductive", "private inductive");
    let mut hidden = modules;
    hidden[1].source = private_api.as_bytes();
    assert!(session.check(&hidden, &names[0]).is_err());
    let recovered = session
        .check(&modules, &names[0])
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(recovered.reused_modules, 2);
    assert_eq!(
        cold.checked.checked.result_logical_root,
        recovered.checked.checked.result_logical_root
    );
}

#[test]
fn cancellation_and_exhaustion_never_replace_the_successful_module_cache() {
    use fln::source_check::modules::{SourceModuleCacheLimits, SourceModuleSession};
    use std::cell::Cell;
    let base = engine();
    let names = [n("Main"), n("Api")];
    let api = format!("module\nprelude\n{DATA}");
    let modules = [
        SourceModuleInput {
            name: &names[0],
            source: b"prelude\nimport Api\ndef tree : Tree Nat := Tree.leaf 31",
        },
        SourceModuleInput {
            name: &names[1],
            source: api.as_bytes(),
        },
    ];
    let mut session = SourceModuleSession::new(
        base.clone(),
        KVMap::new(),
        limits(),
        SourceModuleCacheLimits::default(),
    );
    struct StopAfter {
        calls: Cell<usize>,
        limit: usize,
    }
    impl fln::CancellationProbe for StopAfter {
        fn is_cancelled(&self) -> bool {
            self.calls.set(self.calls.get() + 1);
            self.calls.get() >= self.limit
        }
    }
    let probe = StopAfter {
        calls: Cell::new(0),
        limit: usize::MAX,
    };
    let cold = session
        .check_with_cancel(&modules, &names[0], Some(&probe))
        .unwrap()
        .into_complete()
        .unwrap();
    let total = probe.calls.get();
    assert!(total > 2);
    for boundary in [1, total / 2, total] {
        let mut empty = SourceModuleSession::new(
            base.clone(),
            KVMap::new(),
            limits(),
            SourceModuleCacheLimits::default(),
        );
        let cancelled = StopAfter {
            calls: Cell::new(0),
            limit: boundary,
        };
        assert!(matches!(
            empty
                .check_with_cancel(&modules, &names[0], Some(&cancelled))
                .unwrap(),
            Outcome::Inconclusive(_)
        ));
        assert_eq!(empty.retained_modules(), 0);
        let recovered = empty
            .check(&modules, &names[0])
            .unwrap()
            .into_complete()
            .unwrap();
        assert_eq!(
            recovered.checked.checked.result_logical_root,
            cold.checked.checked.result_logical_root
        );
    }
    let mut exhausted = limits();
    exhausted.max_work = 0;
    assert!(
        base.check_source_modules(&modules, &names[0], &KVMap::new(), exhausted)
            .is_err()
    );
    assert!(!base.environment().contains(&n("Tree")));
}
