//! Real serialized artifact closures exercise the private per-module receipt.
#![forbid(unsafe_code)]
use super::*;
use fln::source_check::modules::{
    SourceModuleBuildError, SourceModuleCacheLimits, SourceModuleCheck, SourceModuleCheckError,
    SourceModuleCheckLimits, SourceModuleSession,
    imported::{SourceOleanImport, SourceOleanImportLimits},
};

fn limits() -> SourceModuleCheckLimits {
    SourceModuleCheckLimits::new(SourceCheckLimits::new(EngineAdmissionLimits::new(
        Budget::for_stack_bytes(2 * 1024 * 1024),
    )))
}

fn imported(project: &Project) -> SourceOleanImport {
    let names = [n("Core"), n("A"), n("B")];
    let bytes: Vec<_> = ["Core", "A", "B"]
        .iter()
        .map(|name| std::fs::read(project.0.join(format!("objects/{name}.olean"))).unwrap())
        .collect();
    let inputs: Vec<_> = names
        .iter()
        .zip(&bytes)
        .map(|(name, artifact)| OleanModuleInput {
            name,
            artifact,
            server_artifact: None,
            private_artifact: None,
        })
        .collect();
    Engine::from_environment(Environment::new())
        .import_olean_modules_for_source(
            &inputs,
            &[n("A"), n("B")],
            &KVMap::new(),
            SourceOleanImportLimits::new(OleanCheckLimits::new(
                1024 * 1024,
                limits().source.admission.kernel,
            )),
        )
        .unwrap()
        .into_complete()
        .unwrap()
}

fn inputs<'a>(names: &'a [Name], sources: &'a [&str]) -> Vec<SourceModuleInput<'a>> {
    names
        .iter()
        .zip(sources)
        .map(|(name, source)| SourceModuleInput {
            name,
            source: source.as_bytes(),
        })
        .collect()
}

fn checked(receipt: &SourceOleanImport, sources: &[(&str, &str)]) -> SourceModuleCheck {
    let names: Vec<_> = sources.iter().map(|(name, _)| n(name)).collect();
    let sources: Vec<_> = sources.iter().map(|(_, source)| *source).collect();
    receipt
        .check_source_modules(
            &inputs(&names, &sources),
            &n("Main"),
            &KVMap::new(),
            limits(),
            None,
        )
        .unwrap_or_else(|error| panic!("{sources:?}\n{error:?}"))
        .into_complete()
        .unwrap()
}

#[test]
fn siblings_select_different_dictionaries_without_changing_their_checked_types() {
    let receipt = imported(&fixture());
    let result = checked(
        &receipt,
        &[
            (
                "Left",
                "prelude\nimport A\ndef leftUse [d : Class] : Class := d\ndef left : Family leftUse := valueA\n",
            ),
            (
                "Right",
                "prelude\nimport B\ndef rightUse [d : Class] : Class := d\ndef right : Family rightUse := valueB\n",
            ),
            (
                "Main",
                "prelude\nimport Left Right\ndef leftAgain : Family a := left\ndef rightAgain : Family b := right\n",
            ),
        ],
    );
    assert_eq!(result.module_order, [n("Left"), n("Right"), n("Main")]);
    assert_eq!(result.checked.commands, 6);
}

#[test]
fn equal_external_sets_keep_each_modules_own_import_order() {
    let receipt = imported(&fixture());
    checked(
        &receipt,
        &[
            (
                "Left",
                "prelude\nimport A B\ndef leftUse [d : Class] : Class := d\ndef left : Family leftUse := valueB\n",
            ),
            (
                "Right",
                "prelude\nimport B A\ndef rightUse [d : Class] : Class := d\ndef right : Family rightUse := valueA\n",
            ),
            (
                "Main",
                "prelude\nimport Left Right\ndef checkLeft : Family b := left\ndef checkRight : Family a := right\n",
            ),
        ],
    );
}

#[test]
fn source_registrations_stay_between_the_external_imports_that_surround_them() {
    let receipt = imported(&fixture());
    for (order, value) in [("Local B", "valueB"), ("B Local", "valueA")] {
        let main = format!(
            "prelude\nimport {order}\ndef use [d : Class] : Class := d\ndef chosen : Family use := {value}\n"
        );
        checked(
            &receipt,
            &[
                (
                    "Local",
                    "prelude\nimport A\ninstance localChoice : Class := a\n",
                ),
                ("Main", &main),
            ],
        );
    }
}

#[test]
fn unrelated_external_constants_and_instances_cannot_leak_into_a_sibling() {
    let p = fixture();
    p.module(
        "A",
        &[axiom("onlyA", c("Class"))],
        &["Core"],
        vec![(INSTANCE, vec![instance("a", 1000)])],
    );
    let receipt = imported(&p);
    let root = receipt.engine.logical_root(&KVMap::new());
    for right in [
        "prelude\nimport B\ndef bad : Class := onlyA\n",
        "prelude\nimport Core\ndef use [d : Class] : Class := d\ndef bad : Class := use\n",
        "prelude\nimport B\ndef use [d : Class] : Class := d\ndef bad : Family use := valueA\n",
    ] {
        let names = [n("Right"), n("Main")];
        let source = [right, "prelude\nimport A Right\n"];
        assert!(
            receipt
                .check_source_modules(
                    &inputs(&names, &source),
                    &n("Main"),
                    &KVMap::new(),
                    limits(),
                    None
                )
                .is_err(),
            "{right}"
        );
        assert_eq!(receipt.engine.logical_root(&KVMap::new()), root);
    }
    checked(
        &receipt,
        &[("Main", "prelude\nimport A\ndef recovery : Class := onlyA\n")],
    );
}

#[test]
fn public_report_mutation_cannot_replace_the_private_admission_receipt() {
    let mut receipt = imported(&fixture());
    receipt.engine = Engine::from_environment(Environment::new());
    receipt.checked.engine = Engine::from_environment(Environment::new());
    receipt.modules.clear();
    receipt.checked.modules.clear();
    checked(
        &receipt,
        &[(
            "Main",
            "prelude\nimport A\ndef use [d : Class] : Class := d\ndef chosen : Family use := valueA\n",
        )],
    );
}

#[test]
fn source_graph_errors_and_request_budgets_remain_atomic() {
    let receipt = imported(&fixture());
    let names = [n("Left"), n("Main")];
    for sources in [
        ["prelude\nimport Main\n", "prelude\nimport Left A\n"],
        ["prelude\nimport Missing\n", "prelude\nimport Left A\n"],
        [
            "prelude\nimport A\ndef bad : Class := Family\n",
            "prelude\nimport Left B\n",
        ],
    ] {
        assert!(
            receipt
                .check_source_modules(
                    &inputs(&names, &sources),
                    &n("Main"),
                    &KVMap::new(),
                    limits(),
                    None
                )
                .is_err()
        );
    }
    let sources = [
        "prelude\nimport A\ndef first : Class := a\n",
        "prelude\nimport Left B\ndef second : Class := b\n",
    ];
    let inputs = inputs(&names, &sources);
    for budget in [0, 1, 8] {
        let mut limited = limits();
        limited.max_work = budget;
        assert!(matches!(
            receipt.check_source_modules(&inputs, &n("Main"), &KVMap::new(), limited, None),
            Err(SourceModuleCheckError::Limit { .. })
        ));
    }
    let mut limited = limits();
    limited.source.max_commands = 1;
    assert!(
        receipt
            .check_source_modules(&inputs, &n("Main"), &KVMap::new(), limited, None)
            .is_err()
    );
    struct Cancel;
    impl CancellationProbe for Cancel {
        fn is_cancelled(&self) -> bool {
            true
        }
    }
    assert!(matches!(
        receipt
            .check_source_modules(&inputs, &n("Main"), &KVMap::new(), limits(), Some(&Cancel))
            .unwrap(),
        Outcome::Inconclusive(_)
    ));
    checked(
        &receipt,
        &[("Main", "prelude\nimport B\ndef recovery : Class := b\n")],
    );
}

#[test]
fn separate_context_artifacts_round_trip_through_both_checkers() {
    let p = fixture();
    let receipt = imported(&p);
    let names = [n("Left"), n("Right"), n("Main")];
    let sources = [
        "prelude\nimport A\ndef leftUse [d : Class] : Class := d\ndef left : Family leftUse := valueA\n",
        "prelude\nimport B\ndef rightUse [d : Class] : Class := d\ndef right : Family rightUse := valueB\n",
        "prelude\nimport Left Right\ndef leftAgain : Family a := left\ndef rightAgain : Family b := right\n",
    ];
    let built = receipt
        .compile_source_modules(
            &inputs(&names, &sources),
            &n("Main"),
            &KVMap::new(),
            limits(),
            OleanWriteBudget::default(),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(built.artifacts.len(), 3);
    let external_names = [n("Core"), n("A"), n("B")];
    let bytes: Vec<_> = ["Core", "A", "B"]
        .iter()
        .map(|name| std::fs::read(p.0.join(format!("objects/{name}.olean"))).unwrap())
        .collect();
    let mut all: Vec<_> = external_names
        .iter()
        .zip(&bytes)
        .map(|(name, artifact)| OleanModuleInput {
            name,
            artifact,
            server_artifact: None,
            private_artifact: None,
        })
        .collect();
    all.extend(built.artifacts.iter().map(|artifact| OleanModuleInput {
        name: &artifact.name,
        artifact: &artifact.bytes,
        server_artifact: None,
        private_artifact: None,
    }));
    let verified = Engine::from_environment(Environment::new())
        .check_olean_modules(
            &all,
            &KVMap::new(),
            OleanCheckLimits::new(1024 * 1024, limits().source.admission.kernel),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert!(verified.engine.environment().contains(&n("leftAgain")));
    assert!(verified.engine.environment().contains(&n("rightAgain")));
}

#[test]
fn cancellation_at_each_observed_checkpoint_never_returns_a_partial_engine() {
    struct StopAfter {
        calls: AtomicUsize,
        after: usize,
    }
    impl CancellationProbe for StopAfter {
        fn is_cancelled(&self) -> bool {
            self.calls.fetch_add(1, Ordering::Relaxed) >= self.after
        }
    }
    let receipt = imported(&fixture());
    let root = receipt.engine.logical_root(&KVMap::new());
    let names = [n("Local"), n("Main")];
    let sources = [
        "prelude\nimport A\ninstance localChoice : Class := a\n",
        "prelude\nimport Local B\ndef use [d : Class] : Class := d\ndef chosen : Family use := valueB\n",
    ];
    let inputs = inputs(&names, &sources);
    let probe = StopAfter {
        calls: AtomicUsize::new(0),
        after: usize::MAX,
    };
    assert!(matches!(
        receipt
            .check_source_modules(&inputs, &n("Main"), &KVMap::new(), limits(), Some(&probe))
            .unwrap(),
        Outcome::Complete(_)
    ));
    let checkpoints = probe.calls.load(Ordering::Relaxed);
    assert!(checkpoints > 10);
    for after in 0..checkpoints {
        let probe = StopAfter {
            calls: AtomicUsize::new(0),
            after,
        };
        assert!(
            matches!(
                receipt
                    .check_source_modules(
                        &inputs,
                        &n("Main"),
                        &KVMap::new(),
                        limits(),
                        Some(&probe)
                    )
                    .unwrap(),
                Outcome::Inconclusive(_)
            ),
            "checkpoint {after}"
        );
        assert_eq!(receipt.engine.logical_root(&KVMap::new()), root);
    }
}

#[test]
fn metadata_and_encoding_budgets_remain_aggregate_and_unsupported_exports_refuse() {
    let receipt = imported(&fixture());
    let names = [n("Main")];
    let sources = ["prelude\nimport A\ndef chosen : Class := a\n"];
    let inputs = inputs(&names, &sources);
    let mut limited = limits();
    limited.max_extension_bytes = 0;
    assert!(matches!(
        receipt.check_source_modules(&inputs, &n("Main"), &KVMap::new(), limited, None),
        Err(SourceModuleCheckError::Limit { .. })
    ));
    let budget = OleanWriteBudget {
        max_bytes: 1,
        ..OleanWriteBudget::default()
    };
    assert!(
        receipt
            .compile_source_modules(&inputs, &n("Main"), &KVMap::new(), limits(), budget)
            .is_err()
    );
    let source = b"prelude\nimport A\ninstance localChoice : Class := a\n";
    let inputs = [SourceModuleInput {
        name: &names[0],
        source,
    }];
    assert!(matches!(
        receipt.compile_source_modules(
            &inputs,
            &n("Main"),
            &KVMap::new(),
            limits(),
            OleanWriteBudget::default()
        ),
        Err(SourceModuleBuildError::Check(
            SourceModuleCheckError::Extension { .. }
        ))
    ));
}

#[test]
fn full_receipt_retains_checked_repeated_proofs_without_lending_them_to_a_subset() {
    let project = Project::new();
    project.module(
        "Core",
        &[
            axiom("P", Expr::sort(Level::zero())),
            axiom("firstProof", c("P")),
            axiom("secondProof", c("P")),
        ],
        &[],
        vec![],
    );
    for (module, proof) in [("A", "firstProof"), ("B", "secondProof")] {
        let theorem = ConstantInfo::Thm(TheoremVal {
            base: ConstantVal {
                name: n("shared"),
                level_params: vec![],
                type_: c("P"),
            },
            value: c(proof),
            all: vec![n("shared")],
        });
        project.module(module, &[theorem], &["Core"], vec![]);
    }
    let receipt = imported(&project);
    checked(
        &receipt,
        &[(
            "Main",
            "prelude\nimport A B\ntheorem useShared : P := shared\n",
        )],
    );
    // The full checker keeps the first coherent copy. A receipt for B alone
    // must not silently substitute A's proof just because the names match.
    let names = [n("Main")];
    let source = ["prelude\nimport B\ntheorem useShared : P := shared\n"];
    assert!(matches!(
        receipt.check_source_modules(
            &inputs(&names, &source),
            &n("Main"),
            &KVMap::new(),
            limits(),
            None
        ),
        Err(SourceModuleCheckError::ImportContext { .. })
    ));
}

#[test]
fn private_context_sessions_reuse_artifacts_without_lending_sibling_dictionaries() {
    let mut receipt = imported(&fixture());
    receipt.engine = Engine::from_environment(Environment::new());
    receipt.checked.modules.clear();
    let mut session = SourceModuleSession::from_imports(
        receipt,
        KVMap::new(),
        limits(),
        SourceModuleCacheLimits::default(),
    );
    let names = [n("Left"), n("Right"), n("Main")];
    let sources = [
        "prelude\nimport A\ndef leftUse [d : Class] : Class := d\ndef left : Family leftUse := valueA\n",
        "prelude\nimport B\ndef rightUse [d : Class] : Class := d\ndef right : Family rightUse := valueB\n",
        "prelude\nimport Left Right\ndef checkLeft : Family a := left\ndef checkRight : Family b := right\n",
    ];
    let run = |session: &mut SourceModuleSession, sources: &[&str]| {
        session.compile(
            &inputs(&names, sources),
            &n("Main"),
            OleanWriteBudget::default(),
        )
    };
    let mut cold = run(&mut session, &sources)
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!((cold.elaborated_modules, cold.reused_modules), (3, 0));
    let original: Vec<_> = cold
        .artifacts
        .iter()
        .map(|a| (a.name.clone(), a.bytes.clone()))
        .collect();
    cold.artifacts[0].bytes.fill(0);
    let warm = run(&mut session, &sources)
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!((warm.elaborated_modules, warm.reused_modules), (0, 3));
    for (actual, (name, bytes)) in warm.artifacts.iter().zip(&original) {
        assert_eq!((&actual.name, &actual.bytes), (name, bytes));
    }
    let mut bad = sources;
    bad[1] = "prelude\nimport B\ndef rightUse [d : Class] : Class := d\ndef right : Family rightUse := valueA\n";
    assert!(run(&mut session, &bad).is_err());
    assert_eq!(session.retained_modules(), 3);
    let tiny = OleanWriteBudget {
        max_bytes: 1,
        ..OleanWriteBudget::default()
    };
    assert!(
        session
            .compile(&inputs(&names, &sources), &n("Main"), tiny)
            .is_err()
    );
    assert_eq!(session.retained_modules(), 3);
    let recovered = run(&mut session, &sources)
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(
        (recovered.elaborated_modules, recovered.reused_modules),
        (0, 3)
    );
}

#[test]
fn warm_context_session_cancellation_preserves_the_successful_cache() {
    struct StopAfter {
        calls: AtomicUsize,
        after: usize,
    }
    impl CancellationProbe for StopAfter {
        fn is_cancelled(&self) -> bool {
            self.calls.fetch_add(1, Ordering::Relaxed) >= self.after
        }
    }
    let mut session = SourceModuleSession::from_imports(
        imported(&fixture()),
        KVMap::new(),
        limits(),
        SourceModuleCacheLimits::default(),
    );
    let names = [n("Local"), n("Main")];
    let sources = [
        "prelude\nimport A\ndef localValue : Class := a\n",
        "prelude\nimport Local B\ndef mainValue : Class := b\n",
    ];
    let inputs = inputs(&names, &sources);
    session
        .compile(&inputs, &n("Main"), OleanWriteBudget::default())
        .unwrap()
        .into_complete()
        .unwrap();
    let probe = StopAfter {
        calls: AtomicUsize::new(0),
        after: usize::MAX,
    };
    let warm = session
        .compile_with_cancel(
            &inputs,
            &n("Main"),
            OleanWriteBudget::default(),
            Some(&probe),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(warm.reused_modules, 2);
    let checkpoints = probe.calls.load(Ordering::Relaxed);
    assert!(checkpoints > 5);
    for after in 0..checkpoints {
        let probe = StopAfter {
            calls: AtomicUsize::new(0),
            after,
        };
        assert!(
            matches!(
                session
                    .compile_with_cancel(
                        &inputs,
                        &n("Main"),
                        OleanWriteBudget::default(),
                        Some(&probe)
                    )
                    .unwrap(),
                Outcome::Inconclusive(_)
            ),
            "checkpoint {after}"
        );
        assert_eq!(session.retained_modules(), 2);
    }
    let recovered = session
        .compile(&inputs, &n("Main"), OleanWriteBudget::default())
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(
        (recovered.elaborated_modules, recovered.reused_modules),
        (0, 2)
    );
}
