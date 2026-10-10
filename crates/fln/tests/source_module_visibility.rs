//! Module-system declarations and imports retain their private source scope.
#![forbid(unsafe_code)]

use fln::source_check::modules::{
    SourceModuleBuildError, SourceModuleCacheLimits, SourceModuleCheck, SourceModuleCheckError,
    SourceModuleCheckLimits, SourceModuleSession,
};
use fln::{
    Budget, Engine, EngineAdmissionLimits, KVMap, Name, OleanWriteBudget, Outcome,
    SourceCheckError, SourceCheckLimits, SourceModuleInput,
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
    base.check_source_modules(&inputs, &n("Main"), &KVMap::new(), limits())
}

fn checked(base: &Engine, files: &[(&str, &str)]) -> SourceModuleCheck {
    check(base, files)
        .unwrap_or_else(|error| panic!("{files:?}: {error:?}"))
        .into_complete()
        .unwrap()
}

fn check_in_both_import_contexts(
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
    let initial = Engine::builder().build_empty();
    let receipt = fln::source_check::modules::imported::SourceOleanImport::empty(&options);
    [
        initial.check_source_modules(&inputs, &names[0], &options, limits()),
        receipt.check_source_modules(&inputs, &names[0], &options, limits(), None),
    ]
}

const ID: &str = "def identity.{u} {A : Sort u} (x : A) : A := x";
const PRIVATE_ID: &str = "module\nprelude\ndef identity.{u} {A : Sort u} (x : A) : A := x";

#[test]
fn private_declarations_resolve_within_their_module_and_keep_user_namespaces() {
    // PrivateName.lean's mkPrivateNameCore uses a numeric zero component.
    let initial = Engine::builder().build_empty();
    let source = "\u{feff}module\r\nprelude\r\nnamespace Local\r\ndef identity.{u} {A : Sort u} (x : A) : A := x\r\ndef again.{u} {A : Sort u} (x : A) : A := identity x\r\nend Local\r\nopen Local\r\ndef use.{u} {A : Sort u} (x : A) : A := again x\r\ndef rooted.{u} {A : Sort u} (x : A) : A := _root_.Local.identity x";
    let result = checked(&initial, &[("Main", source)]);
    let environment = result.checked.engine.environment();
    for declaration in ["Local.identity", "Local.again", "use", "rooted"] {
        assert!(
            environment.contains(&private("Main", declaration)),
            "{declaration}"
        );
        assert!(!environment.contains(&n(declaration)), "{declaration}");
    }
    assert_eq!(result.checked.scope.private_module, Some(n("Main")));
    assert!(result.checked.scope.namespace.is_anonymous());
    assert!(initial.environment().is_empty());
}

#[test]
fn private_sibling_definitions_do_not_collide_or_escape() {
    let initial = Engine::builder().build_empty();
    let result = checked(
        &initial,
        &[
            ("Main", "prelude\nimport A\nimport B"),
            ("A", PRIVATE_ID),
            ("B", PRIVATE_ID),
        ],
    );
    assert_eq!(result.module_order, [n("A"), n("B"), n("Main")]);
    assert_eq!(result.checked.commands, 2);
    assert!(result.checked.engine.environment().is_empty());
    let error = check(
        &initial,
        &[
            (
                "Main",
                "prelude\nimport A\ndef stolen.{u} {A : Sort u} (x : A) : A := identity x",
            ),
            ("A", PRIVATE_ID),
        ],
    )
    .unwrap_err();
    assert!(matches!(error, SourceModuleCheckError::Source { module, .. } if module == n("Main")));
    assert!(initial.environment().is_empty());
}

#[test]
fn private_imports_are_checked_but_do_not_transitively_export_names() {
    let initial = Engine::builder().build_empty();
    let library =
        "module\nprelude\nimport A\ndef localUse.{u} {A : Sort u} (x : A) : A := identity x";
    let main = "prelude\nimport B\ndef use.{u} {A : Sort u} (x : A) : A := identity x";
    let error = check(&initial, &[("Main", main), ("B", library), ("A", ID)]).unwrap_err();
    assert!(matches!(error, SourceModuleCheckError::Source { module, .. } if module == n("Main")));
    let visible = "prelude\nimport B\nimport A\ndef use.{u} {A : Sort u} (x : A) : A := identity x";
    let result = checked(&initial, &[("Main", visible), ("B", library), ("A", ID)]);
    assert_eq!(result.module_order, [n("A"), n("B"), n("Main")]);
    assert!(result.checked.engine.environment().contains(&n("identity")));
    assert!(
        !result
            .checked
            .engine
            .environment()
            .contains(&private("B", "localUse"))
    );
    // Even an unused private dependency must pass checking before publication.
    assert!(
        check(
            &initial,
            &[
                ("Main", "prelude\nimport B"),
                ("B", "module\nprelude\nimport A"),
                ("A", "def broken := absent")
            ]
        )
        .is_err()
    );
}

#[test]
fn private_records_inductives_recursion_and_simp_rules_work_locally() {
    let initial = Engine::with_source_seed(limits().source.admission)
        .unwrap()
        .into_complete()
        .unwrap();
    let source = "module\nprelude\nnamespace Local\nstructure Box where\n  value : Nat\ninductive Choice where\n| left\n| right\ndef tag (x : Choice) : Nat := match x with | Choice.left => 1 | Choice.right => 2\ndef record : Box := { value := 9 }\ndef count : Nat → Nat\n| 0 => 0\n| n + 1 => count n + 1\n@[simp] theorem unwrap (n : Nat) : count n = count n := by rfl\ntheorem field : record.value = 9 := by rfl\ntheorem chosen : tag Choice.left = 1 := by rfl\nend Local";
    let result = checked(&initial, &[("Main", source)]);
    for declaration in [
        "Local.Box",
        "Local.Choice",
        "Local.count",
        "Local.field",
        "Local.chosen",
    ] {
        assert!(
            result
                .checked
                .engine
                .environment()
                .contains(&private("Main", declaration)),
            "{declaration}"
        );
    }
    let imported = checked(&initial, &[("Main", "import Lib"), ("Lib", source)]);
    assert_eq!(
        fln_elab::source::scope::simp::read(imported.checked.engine.environment()).unwrap(),
        fln_elab::source::scope::simp::read(initial.environment()).unwrap(),
    );
    assert!(
        !imported
            .checked
            .engine
            .environment()
            .contains(&private("Lib", "Local.Box"))
    );
}

#[test]
fn implicit_init_remains_exported_through_a_module_with_other_private_imports() {
    // HeaderSyntax.imports gives implicit Init the public Import defaults;
    // only the explicitly written Secret import is private in this module.
    let names = [n("Main"), n("Lib"), n("Init"), n("Secret")];
    let sources = [
        "prelude\nimport Lib\ndef use.{u} {A : Sort u} (x : A) : A := identity x",
        "module\nimport Secret\ndef localUse.{u} {A : Sort u} (x : A) : A := hidden (identity x)",
        "prelude\ndef identity.{u} {A : Sort u} (x : A) : A := x",
        "prelude\ndef hidden.{u} {A : Sort u} (x : A) : A := x",
    ];
    let inputs: Vec<_> = names
        .iter()
        .zip(sources)
        .map(|(name, source)| SourceModuleInput {
            name,
            source: source.as_bytes(),
        })
        .collect();
    let options = KVMap::new();
    let initial = Engine::builder().build_empty();
    let direct = initial
        .check_source_modules(&inputs, &names[0], &options, limits())
        .unwrap()
        .into_complete()
        .unwrap();
    let receipt = fln::source_check::modules::imported::SourceOleanImport::empty(&options);
    let projected = receipt
        .check_source_modules(&inputs, &names[0], &options, limits(), None)
        .unwrap()
        .into_complete()
        .unwrap();
    for result in [&direct, &projected] {
        assert_eq!(
            result.module_order,
            [n("Init"), n("Secret"), n("Lib"), n("Main")]
        );
        let environment = result.checked.engine.environment();
        assert!(environment.contains(&n("identity")));
        assert!(environment.contains(&n("use")));
        assert!(!environment.contains(&n("hidden")));
        assert!(!environment.contains(&private("Lib", "localUse")));
    }
    let mut forbidden = inputs;
    forbidden[0].source = b"prelude\nimport Lib\ndef leak.{u} {A : Sort u} (x : A) : A := hidden x";
    assert!(
        initial
            .check_source_modules(&forbidden, &names[0], &options, limits())
            .is_err()
    );
    assert!(
        receipt
            .check_source_modules(&forbidden, &names[0], &options, limits(), None)
            .is_err()
    );
}

#[test]
fn public_imports_reexport_transitively_without_exposing_private_dependencies_or_declarations() {
    let files = [
        (
            "Main",
            "prelude\nimport Facade\ndef use.{u} {A : Sort u} (x : A) : A := identity x",
        ),
        ("Facade", "module\nprelude\npublic import Wrapper"),
        (
            "Wrapper",
            "module\nprelude\nimport Secret\npublic import Api\ndef localUse.{u} {A : Sort u} (x : A) : A := hidden (identity x)",
        ),
        (
            "Api",
            "prelude\ndef identity.{u} {A : Sort u} (x : A) : A := x",
        ),
        (
            "Secret",
            "prelude\ndef hidden.{u} {A : Sort u} (x : A) : A := x",
        ),
    ];
    for result in check_in_both_import_contexts(&files) {
        let checked = result.unwrap().into_complete().unwrap();
        assert_eq!(
            checked.module_order,
            [n("Secret"), n("Api"), n("Wrapper"), n("Facade"), n("Main")]
        );
        let environment = checked.checked.engine.environment();
        assert!(environment.contains(&n("identity")));
        assert!(environment.contains(&n("use")));
        assert!(!environment.contains(&n("hidden")));
        assert!(!environment.contains(&private("Wrapper", "localUse")));
    }
    for source in [
        "prelude\nimport Facade\ndef leak.{u} {A : Sort u} (x : A) : A := hidden x",
        "prelude\nimport Facade\ndef leak.{u} {A : Sort u} (x : A) : A := localUse x",
    ] {
        let mut invalid = files;
        invalid[0].1 = source;
        for result in check_in_both_import_contexts(&invalid) {
            assert!(
                matches!(result, Err(SourceModuleCheckError::Source { module, .. }) if module == n("Main"))
            );
        }
    }
}

#[test]
fn public_import_row_order_controls_instances_independently_of_earlier_private_rows() {
    // The module itself sees both import kinds in written order. Its consumer
    // sees only the public rows, so the equal-priority winning instance differs.
    for (imports, inside, outside) in [
        (
            "import A\npublic import B\npublic import A",
            "right",
            "left",
        ),
        (
            "import B\npublic import A\npublic import B",
            "left",
            "right",
        ),
    ] {
        let wrapper = format!(
            "module\nprelude\n{imports}\ndef localChoice : Token := Pick.value\ndef localProof (P : Token -> Prop) (h : P Token.{inside}) : P localChoice := h"
        );
        let main = format!(
            "prelude\nimport Wrapper\ndef chosen : Token := Pick.value\ndef choiceProof (P : Token -> Prop) (h : P Token.{outside}) : P chosen := h"
        );
        let files = [
            ("Main", main.as_str()),
            ("Wrapper", wrapper.as_str()),
            (
                "A",
                "prelude\nimport Base\ninstance first : Pick := Pick.mk Token.left",
            ),
            (
                "B",
                "prelude\nimport Base\ninstance second : Pick := Pick.mk Token.right",
            ),
            (
                "Base",
                "prelude\ninductive Token where\n| left\n| right\nclass Pick where\n  value : Token",
            ),
        ];
        for result in check_in_both_import_contexts(&files) {
            let checked = result.unwrap().into_complete().unwrap();
            assert!(
                checked
                    .checked
                    .engine
                    .environment()
                    .contains(&n("choiceProof"))
            );
        }
        let wrong = format!(
            "prelude\nimport Wrapper\ndef chosen : Token := Pick.value\ndef wrongChoice (P : Token -> Prop) (h : P Token.{inside}) : P chosen := h"
        );
        let mut invalid = files;
        invalid[0].1 = &wrong;
        for result in check_in_both_import_contexts(&invalid) {
            assert!(
                matches!(result, Err(SourceModuleCheckError::Source { module, .. }) if module == n("Main"))
            );
        }
    }
}

#[test]
fn changing_public_import_visibility_invalidates_cached_consumers_and_recovers() {
    let mut session = SourceModuleSession::new(
        Engine::builder().build_empty(),
        KVMap::new(),
        limits(),
        SourceModuleCacheLimits::default(),
    );
    let names = [n("Main"), n("Wrapper"), n("Api")];
    let inputs = [
        SourceModuleInput {
            name: &names[0],
            source: b"prelude\nimport Wrapper\ndef use.{u} {A : Sort u} (x : A) : A := identity x",
        },
        SourceModuleInput {
            name: &names[1],
            source: b"module\nprelude\npublic import Api",
        },
        SourceModuleInput {
            name: &names[2],
            source: ID.as_bytes(),
        },
    ];
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
    assert_eq!((cold.elaborated_modules, warm.reused_modules), (3, 3));
    let mut hidden = inputs;
    hidden[1].source = b"module\nprelude\nimport Api";
    assert!(matches!(
        session.check(&hidden, &names[0]),
        Err(SourceModuleCheckError::Source { module, .. }) if module == names[0]
    ));
    let recovered = session
        .check(&inputs, &names[0])
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(recovered.reused_modules, 3);
    assert_eq!(
        recovered.checked.checked.result_logical_root,
        cold.checked.checked.result_logical_root
    );
}

#[test]
fn private_names_cannot_shadow_an_imported_public_declaration() {
    let initial = Engine::builder().build_empty();
    let source = format!("module\nprelude\nimport Lib\n{ID}");
    let error = check(&initial, &[("Main", &source), ("Lib", ID)]).unwrap_err();
    assert!(
        error
            .to_string()
            .contains("conflicts with an existing public declaration"),
        "{error}"
    );
    assert!(initial.environment().is_empty());
}

#[test]
fn cached_module_scopes_and_private_dependency_changes_keep_visibility() {
    let initial = Engine::builder().build_empty();
    let mut session = SourceModuleSession::new(
        initial,
        KVMap::new(),
        limits(),
        SourceModuleCacheLimits::default(),
    );
    let names = [n("Main"), n("Lib")];
    let main = "module\nprelude\nimport Lib\ndef use.{u} {A : Sort u} (x : A) : A := identity x";
    let inputs = [
        SourceModuleInput {
            name: &names[0],
            source: main.as_bytes(),
        },
        SourceModuleInput {
            name: &names[1],
            source: ID.as_bytes(),
        },
    ];
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
    assert_eq!((cold.elaborated_modules, warm.reused_modules), (2, 2));
    assert_eq!(
        cold.checked.checked.result_logical_root,
        warm.checked.checked.result_logical_root
    );
    assert_eq!(
        warm.checked.checked.scope.private_module,
        Some(names[0].clone())
    );
    let hidden = [
        inputs[0],
        SourceModuleInput {
            name: &names[1],
            source: PRIVATE_ID.as_bytes(),
        },
    ];
    assert!(session.check(&hidden, &names[0]).is_err());
    assert_eq!(
        session
            .check(&inputs, &names[0])
            .unwrap()
            .into_complete()
            .unwrap()
            .reused_modules,
        2
    );
    let empty = [SourceModuleInput {
        name: &names[0],
        source: b"module\nprelude\n",
    }];
    let empty = session
        .check(&empty, &names[0])
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(
        empty.checked.checked.scope.private_module,
        Some(names[0].clone())
    );
}

#[test]
fn unsupported_import_modifiers_refuse_at_the_original_modifier_before_lookup() {
    let initial = Engine::builder().build_empty();
    for (clause, modifier) in [
        ("meta import Missing", "meta"),
        ("public meta import Missing", "meta"),
        ("import all Missing", "all"),
    ] {
        let source = format!("\u{feff}module\r\nprelude\r\n{clause}");
        let error = check(&initial, &[("Main", &source)]).unwrap_err();
        assert_eq!(error.disposition().0, "capability", "{error}");
        assert!(
            matches!(error, SourceModuleCheckError::Source { error: SourceCheckError::Command { offset, .. }, .. } if offset == source.find(modifier).unwrap())
        );
    }
}

#[test]
fn module_system_artifacts_refuse_until_split_visibility_can_be_encoded() {
    let initial = Engine::builder().build_empty();
    let main = n("Main");
    let input = SourceModuleInput {
        name: &main,
        source: PRIVATE_ID.as_bytes(),
    };
    let error = initial
        .compile_source_modules(
            &[input],
            &main,
            &KVMap::new(),
            limits(),
            OleanWriteBudget::default(),
        )
        .unwrap_err();
    assert!(matches!(
        error,
        SourceModuleBuildError::Check(SourceModuleCheckError::ImportContext { .. })
    ));
    assert!(error.to_string().contains("public/private split artifacts"));
    assert!(initial.environment().is_empty());
}

#[test]
fn module_without_prelude_requires_its_real_implicit_init_dependency() {
    let initial = Engine::builder().build_empty();
    let main = "module\ndef use.{u} {A : Sort u} (x : A) : A := identity x";
    assert!(matches!(
        check(&initial, &[("Main", main)]),
        Err(SourceModuleCheckError::MissingModule { module, .. }) if module == n("Init")
    ));
    let init = format!("prelude\n{ID}");
    let result = checked(&initial, &[("Main", main), ("Init", &init)]);
    assert_eq!(result.module_order, [n("Init"), n("Main")]);
    assert!(
        result
            .checked
            .engine
            .environment()
            .contains(&private("Main", "use"))
    );
}
