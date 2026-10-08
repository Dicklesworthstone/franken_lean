//! Composed import reuse must preserve the cold council's answer in each import world.
use super::super::SourceModuleCheckLimits;
use super::super::imported::tests::{closure, inputs, limits, n, on_import_stack, pinned_lib};
use super::tests::{Memory, identity, import_with, reuse};
use super::*;

type Artifacts = Vec<(Name, [Vec<u8>; 3])>;

fn source_limits() -> SourceModuleCheckLimits {
    SourceModuleCheckLimits::new(SourceCheckLimits::new(EngineAdmissionLimits::new(
        Budget::for_stack_bytes(2 * 1024 * 1024),
    )))
}

/// Real native source compilation supplies independently owned declaration deltas.
fn source_diamond(extra_base: &str) -> Artifacts {
    let base = format!("prelude\ndef baseId.{{u}} {{A : Sort u}} (x : A) : A := x\n{extra_base}\n");
    let files = [
        (
            "Main",
            "prelude\nimport Left Right\ndef run.{u} {A : Sort u} (x : A) : A := leftId (rightId x)",
        ),
        (
            "Left",
            "prelude\nimport Base\ndef leftId.{u} {A : Sort u} (x : A) : A := baseId x",
        ),
        (
            "Right",
            "prelude\nimport Base\ndef rightId.{u} {A : Sort u} (x : A) : A := baseId x",
        ),
        ("Base", base.as_str()),
    ];
    let names: Vec<_> = files.iter().map(|(name, _)| n(name)).collect();
    let modules: Vec<_> = files
        .iter()
        .zip(&names)
        .map(|((_, source), name)| SourceModuleInput {
            name,
            source: source.as_bytes(),
        })
        .collect();
    Engine::builder()
        .build_empty()
        .compile_source_modules(
            &modules,
            &n("Main"),
            &KVMap::new(),
            source_limits(),
            OleanWriteBudget::default(),
        )
        .expect("the source definition diamond compiles")
        .into_complete()
        .expect("the diamond passes both checkers")
        .artifacts
        .into_iter()
        .map(|artifact| (artifact.name, [artifact.bytes, Vec::new(), Vec::new()]))
        .collect()
}

fn subset(artifacts: &Artifacts, names: &[&str]) -> Artifacts {
    artifacts
        .iter()
        .filter(|(name, _)| names.iter().any(|wanted| *name == n(wanted)))
        .cloned()
        .collect()
}

/// A retained checker projection is an execution detail of the council path;
/// all environment state, import identities, options and epochs must still agree.
fn same_engine(left: &Engine, right: &Engine, what: &str) {
    let mut left = left.clone();
    let mut right = right.clone();
    left.checker_environment = None;
    right.checker_environment = None;
    crate::assert_engines_identical(&left, &right, what);
}

fn same_import(council: &SourceOleanImport, composed: &SourceOleanImport) {
    let (left, right) = (&council.checked, &composed.checked);
    same_engine(&left.engine, &right.engine, "declaration engines");
    assert_eq!(left.base_logical_root, right.base_logical_root);
    assert_eq!(left.result_logical_root, right.result_logical_root);
    assert_eq!(left.modules.len(), right.modules.len());
    for (left, right) in left.modules.iter().zip(&right.modules) {
        assert_eq!(left.name, right.name, "checking order");
        let mut decoded = left.decoded.clone();
        // A cache hit does not ask the independent reader to decode again. Compare
        // every semantic artifact field while allowing precisely that provenance.
        decoded.independent = right.decoded.independent.clone();
        assert!(
            decoded == right.decoded,
            "decoded artifact {}",
            left.name.to_display_string()
        );
        assert_eq!(left.base_logical_root, right.base_logical_root);
        assert_eq!(left.result_logical_root, right.result_logical_root);
        assert_eq!(left.declarations, right.declarations, "checker rows");
    }
    same_engine(&council.engine, &composed.engine, "metadata engines");
    assert_eq!(council.result_logical_root, composed.result_logical_root);
    assert_eq!(council.modules, composed.modules, "metadata replay reports");
}

/// Exercise the private retained contexts through their consumer: a source file
/// imports one module, resolves its declarations, and reaches the cold world's roots.
fn same_source_contexts(council: &SourceOleanImport, composed: &SourceOleanImport) {
    for (module, left, right) in [
        ("Base", false, false),
        ("Left", true, false),
        ("Right", false, true),
        ("Main", true, true),
    ] {
        if !council.modules.iter().any(|row| row.module == n(module)) {
            continue;
        }
        let consumer = n("Consumer");
        let callee = match module {
            "Base" => "baseId",
            "Left" => "leftId",
            "Right" => "rightId",
            "Main" => "run",
            _ => unreachable!(),
        };
        let source = format!(
            "prelude\nimport {module}\ndef selected.{{u}} {{A : Sort u}} (x : A) : A := {callee} x\n"
        );
        let check = |receipt: &SourceOleanImport| {
            receipt
                .check_source_modules(
                    &[SourceModuleInput {
                        name: &consumer,
                        source: source.as_bytes(),
                    }],
                    &consumer,
                    &KVMap::new(),
                    source_limits(),
                    None,
                )
                .expect("the consumer resolves its own imported world")
                .into_complete()
                .expect("the consumer passes both checkers")
        };
        let cold = check(council);
        let warm = check(composed);
        assert_eq!(cold.module_order, warm.module_order);
        assert_eq!(
            cold.checked.base_logical_root,
            warm.checked.base_logical_root
        );
        assert_eq!(
            cold.checked.result_logical_root,
            warm.checked.result_logical_root
        );
        same_engine(&cold.checked.engine, &warm.checked.engine, module);
        assert_eq!(warm.checked.engine.environment.contains(&n("leftId")), left);
        assert_eq!(
            warm.checked.engine.environment.contains(&n("rightId")),
            right
        );
    }
}

#[test]
fn a_larger_verified_diamond_serves_subsets_and_reordered_roots() {
    on_import_stack(|| {
        let artifacts = source_diamond("");
        let all = inputs(&artifacts);
        let store = Memory::default();
        let checker = identity("composed source diamond");
        let (_, primed) = import_with(&all, &[n("Main")], reuse(checker, &store));
        assert_eq!((primed.reused_modules, primed.council_modules), (0, 4));

        let smaller = subset(&artifacts, &["Base", "Left"]);
        let smaller = inputs(&smaller);
        let (cold, _) = import_with(&smaller, &[n("Left")], ImportPostureRequest::Recheck);
        let (warm, report) = import_with(&smaller, &[n("Left")], reuse(checker, &store));
        assert_eq!(report.admission, ImportAdmission::Reused);
        assert_eq!((report.reused_modules, report.council_modules), (2, 0));
        assert_ne!(
            primed.key, report.key,
            "this cannot be an exact closure hit"
        );
        same_import(&cold, &warm);
        same_source_contexts(&cold, &warm);

        let siblings = subset(&artifacts, &["Base", "Left", "Right"]);
        let siblings = inputs(&siblings);
        let mut previous = None;
        for roots in [[n("Left"), n("Right")], [n("Right"), n("Left")]] {
            let (cold, _) = import_with(&siblings, &roots, ImportPostureRequest::Recheck);
            let (warm, report) = import_with(&siblings, &roots, reuse(checker, &store));
            assert_eq!(report.admission, ImportAdmission::Reused);
            assert_eq!((report.reused_modules, report.council_modules), (3, 0));
            same_import(&cold, &warm);
            same_source_contexts(&cold, &warm);
            if let Some(root) = previous {
                assert_eq!(
                    root, warm.result_logical_root,
                    "the same pure declaration world"
                );
            }
            previous = Some(warm.result_logical_root);
        }
    });
}

#[test]
fn extending_a_verified_closure_checks_the_delta_and_preserves_each_source_world() {
    on_import_stack(|| {
        let artifacts = source_diamond("");
        let smaller = subset(&artifacts, &["Base", "Left"]);
        let store = Memory::default();
        let checker = identity("composed growing diamond");
        let (_, first) = import_with(&inputs(&smaller), &[n("Left")], reuse(checker, &store));
        assert_eq!((first.reused_modules, first.council_modules), (0, 2));

        let all = inputs(&artifacts);
        let (cold, _) = import_with(&all, &[n("Main")], ImportPostureRequest::Recheck);
        let (mixed, report) = import_with(&all, &[n("Main")], reuse(checker, &store));
        assert_eq!(report.admission, ImportAdmission::Composed);
        assert_eq!((report.reused_modules, report.council_modules), (2, 2));
        same_import(&cold, &mixed);
        same_source_contexts(&cold, &mixed);
        let (warm, again) = import_with(&all, &[n("Main")], reuse(checker, &store));
        assert_eq!((again.reused_modules, again.council_modules), (4, 0));
        same_import(&cold, &warm);
    });
}

#[test]
fn changed_dependency_bytes_invalidate_transitive_module_records() {
    on_import_stack(|| {
        let first = source_diamond("def Base.original.{u} {A : Sort u} (x : A) : A := x");
        let changed = source_diamond("def Base.changed.{u} {A : Sort u} (x : A) : A := x");
        for module in ["Left", "Right", "Main"] {
            let bytes = |artifacts: &Artifacts| {
                artifacts
                    .iter()
                    .find(|(name, _)| *name == n(module))
                    .unwrap()
                    .1[0]
                    .clone()
            };
            assert_eq!(
                bytes(&first),
                bytes(&changed),
                "only dependency bytes changed"
            );
        }
        let store = Memory::default();
        let checker = identity("composed dependency invalidation");
        import_with(&inputs(&first), &[n("Main")], reuse(checker, &store));
        let (cold, _) = import_with(
            &inputs(&changed),
            &[n("Main")],
            ImportPostureRequest::Recheck,
        );
        let (actual, report) = import_with(&inputs(&changed), &[n("Main")], reuse(checker, &store));
        assert_eq!(report.admission, ImportAdmission::Council);
        assert_eq!((report.reused_modules, report.council_modules), (0, 4));
        same_import(&cold, &actual);
        assert!(actual.engine.environment.contains(&n("Base.changed")));
        assert!(!actual.engine.environment.contains(&n("Base.original")));
    });
}

fn module_records(store: &Memory) -> Vec<(ImportClosureKey, ModuleReuseRecord)> {
    store
        .0
        .lock()
        .unwrap()
        .iter()
        .filter(|(_, bytes)| bytes.starts_with(MODULE_RECORD_PREFIX))
        .map(|(&key, bytes)| {
            (
                key,
                ModuleReuseRecord::parse(bytes).expect("stored module record parses"),
            )
        })
        .collect()
}

#[test]
fn incomplete_rows_and_wrong_roots_recheck_only_the_affected_module() {
    on_import_stack(|| {
        let artifacts = source_diamond("");
        let store = Memory::default();
        let checker = identity("composed record refusal");
        import_with(&inputs(&artifacts), &[n("Main")], reuse(checker, &store));
        let records = module_records(&store);
        assert_eq!(records.len(), 4, "every module has its own-context record");
        let smaller = subset(&artifacts, &["Base", "Left"]);
        let smaller = inputs(&smaller);
        let (cold, _) = import_with(&smaller, &[n("Left")], ImportPostureRequest::Recheck);
        for damage in 0..3 {
            let planted = Memory::default();
            for (key, saved) in &records {
                let mut record = saved.clone();
                if record.0.modules[0].name == n("Left").to_canonical_bytes() {
                    match damage {
                        0 => {
                            record.0.modules[0]
                                .rows
                                .pop()
                                .expect("Left declares its own function");
                        }
                        1 => {
                            let row = record.0.modules[0].rows[0];
                            record.0.modules[0].rows.push(row);
                        }
                        2 => {
                            record.0.result_root =
                                fln_hash::domain::hash(Domain::CacheKey, b"wrong module result");
                            record.0.modules[0].result_root = record.0.result_root;
                        }
                        _ => unreachable!(),
                    }
                }
                planted.save(*key, &record.to_bytes()).unwrap();
            }
            let (actual, report) = import_with(&smaller, &[n("Left")], reuse(checker, &planted));
            assert_eq!(
                report.admission,
                ImportAdmission::Composed,
                "damage {damage}"
            );
            assert_eq!((report.reused_modules, report.council_modules), (1, 1));
            // This field describes the exact whole-closure key. The store here
            // contains only module records; the affected module's council count
            // above establishes that its planted record was not reused.
            assert_eq!(report.record, RecordLookup::Absent);
            same_import(&cold, &actual);
            let (_, retry) = import_with(&smaller, &[n("Left")], reuse(checker, &planted));
            assert_eq!((retry.reused_modules, retry.council_modules), (2, 0));
        }
    });
}

#[test]
fn cancelled_or_exhausted_composition_publishes_nothing_and_retries_cleanly() {
    use fln_core::outcome::InconclusiveCause;
    use std::sync::atomic::{AtomicBool, Ordering};

    struct CancelOnLoad<'a> {
        store: &'a Memory,
        target: ImportClosureKey,
        observed: AtomicBool,
    }
    impl ImportReuseStore for CancelOnLoad<'_> {
        fn load(&self, key: ImportClosureKey) -> std::result::Result<Option<Vec<u8>>, String> {
            let result = self.store.load(key);
            if key == self.target {
                self.observed.store(true, Ordering::SeqCst);
            }
            result
        }
        fn save(&self, key: ImportClosureKey, bytes: &[u8]) -> std::result::Result<(), String> {
            self.store.save(key, bytes)
        }
    }
    impl CancellationProbe for CancelOnLoad<'_> {
        fn is_cancelled(&self) -> bool {
            self.observed.load(Ordering::SeqCst)
        }
    }

    on_import_stack(|| {
        let artifacts = source_diamond("");
        let smaller = subset(&artifacts, &["Base", "Left"]);
        let store = Memory::default();
        let checker = identity("composed cancellation and exhaustion");
        import_with(&inputs(&smaller), &[n("Left")], reuse(checker, &store));
        let before = store.0.lock().unwrap().clone();
        let base_key = module_records(&store)
            .iter()
            .find(|(_, record)| record.0.modules[0].name == n("Base").to_canonical_bytes())
            .unwrap()
            .0;
        let all = inputs(&artifacts);
        let right = all
            .iter()
            .find(|module| *module.name == n("Right"))
            .unwrap();
        let cancel = CancelOnLoad {
            store: &store,
            target: module_reuse_key(right, &[base_key], &KVMap::new(), checker),
            observed: AtomicBool::new(false),
        };
        let cancelled = Engine::builder()
            .build_empty()
            .import_olean_modules_with_posture(
                &all,
                &[n("Main")],
                &KVMap::new(),
                limits(1),
                reuse(checker, &cancel),
                Some(&cancel),
            )
            .expect("cancellation is a nonanswer, not an import error");
        assert!(
            cancel.observed.load(Ordering::SeqCst),
            "composition reached the new sibling"
        );
        assert!(matches!(cancelled, Outcome::Inconclusive(reason)
            if matches!(reason.cause, InconclusiveCause::Cancelled { .. })));
        assert_eq!(
            *store.0.lock().unwrap(),
            before,
            "cancelled work publishes no records"
        );

        let mut limited = limits(1);
        let kernel = limited.check.admission.kernel;
        limited.check.admission.kernel = kernel.narrowed(0, kernel.depth);
        let exhausted = Engine::builder()
            .build_empty()
            .import_olean_modules_with_posture(
                &all,
                &[n("Main")],
                &KVMap::new(),
                limited,
                reuse(checker, &store),
                None,
            )
            .expect("an exhausted council is a nonanswer, not an import error");
        assert!(matches!(exhausted, Outcome::Inconclusive(reason)
            if matches!(reason.cause, InconclusiveCause::ResourceExhausted { .. })));
        assert_eq!(
            *store.0.lock().unwrap(),
            before,
            "exhausted work publishes no records"
        );

        let (cold, _) = import_with(&all, &[n("Main")], ImportPostureRequest::Recheck);
        let (recovered, report) = import_with(&all, &[n("Main")], reuse(checker, &store));
        assert_eq!((report.reused_modules, report.council_modules), (2, 2));
        same_import(&cold, &recovered);
    });
}

fn constant(name: &str) -> Expr {
    Expr::const_(n(name), Vec::new())
}

fn axiom(name: &str, type_: Expr) -> ConstantInfo {
    ConstantInfo::Axiom(AxiomVal {
        base: ConstantVal {
            name: n(name),
            level_params: Vec::new(),
            type_,
        },
        is_unsafe: false,
    })
}

fn theorem(name: &str, value: Expr) -> ConstantInfo {
    ConstantInfo::Thm(TheoremVal {
        base: ConstantVal {
            name: n(name),
            level_params: Vec::new(),
            type_: constant("Fixture.P"),
        },
        value,
        all: Vec::new(),
    })
}

fn raw_module(name: &str, constants: &[ConstantInfo], imports: &[&str]) -> (Name, [Vec<u8>; 3]) {
    let imports: Vec<_> = imports
        .iter()
        .map(|name| OleanModuleImport {
            module: n(name),
            import_all: false,
            is_exported: false,
            is_meta: false,
        })
        .collect();
    let encoded = encode_olean_module(
        OleanModuleWriteInput {
            is_module: false,
            imports: &imports,
            constants,
            extra_const_names: &[],
        },
        OleanWriteHeader {
            version: OLEAN_ACCEPTED_VERSIONS[0],
            flags: 1,
            lean_version: OLEAN_PIN_TAG.strip_prefix('v').unwrap(),
            githash: OLEAN_PIN_COMMIT,
            base_addr: (OLEAN_REGION_ALIGN as u64) * 2,
        },
        OleanWriteBudget::default(),
    )
    .expect("the native writer emits a real checking artifact");
    (n(name), [encoded.bytes, Vec::new(), Vec::new()])
}

#[test]
fn a_cached_sibling_repeat_keeps_its_own_proof_in_a_smaller_import_world() {
    on_import_stack(|| {
        let detour = Expr::app(
            Expr::lam(
                n("h"),
                constant("Fixture.P"),
                Expr::bvar(0).unwrap(),
                BinderInfo::Default,
            ),
            constant("Fixture.p"),
        );
        let own_proof = theorem("Fixture.s", detour);
        let artifacts = vec![
            raw_module(
                "Fixture.A",
                &[
                    axiom("Fixture.P", Expr::sort(Level::zero())),
                    axiom("Fixture.p", constant("Fixture.P")),
                ],
                &[],
            ),
            raw_module(
                "Fixture.B",
                &[theorem("Fixture.s", constant("Fixture.p"))],
                &["Fixture.A"],
            ),
            raw_module(
                "Fixture.C",
                std::slice::from_ref(&own_proof),
                &["Fixture.A"],
            ),
            raw_module(
                "Fixture.D",
                &[theorem("Fixture.u", constant("Fixture.s"))],
                &["Fixture.B", "Fixture.C"],
            ),
        ];
        let store = Memory::default();
        let checker = identity("composed sibling proofs");
        let (whole, _) = import_with(
            &inputs(&artifacts),
            &[n("Fixture.D")],
            reuse(checker, &store),
        );
        assert!(whole.engine.environment.find(&n("Fixture.s")) != Some(&own_proof));
        let smaller = subset(&artifacts, &["Fixture.A", "Fixture.C"]);
        let smaller = inputs(&smaller);
        let (cold, _) = import_with(&smaller, &[n("Fixture.C")], ImportPostureRequest::Recheck);
        let (warm, report) = import_with(&smaller, &[n("Fixture.C")], reuse(checker, &store));
        assert_eq!((report.reused_modules, report.council_modules), (2, 0));
        same_import(&cold, &warm);
        assert!(warm.engine.environment.find(&n("Fixture.s")) == Some(&own_proof));
        assert!(!warm.engine.environment.contains(&n("Fixture.u")));
    });
}

#[test]
fn a_resealed_record_cannot_hide_a_changed_subsumed_proof() {
    on_import_stack(|| {
        let artifacts = vec![
            raw_module(
                "Fixture.A",
                &[
                    axiom("Fixture.P", Expr::sort(Level::zero())),
                    axiom("Fixture.p", constant("Fixture.P")),
                ],
                &[],
            ),
            raw_module(
                "Fixture.B",
                &[theorem("Fixture.s", constant("Fixture.p"))],
                &["Fixture.A"],
            ),
            raw_module(
                "Fixture.C",
                &[theorem("Fixture.s", constant("Fixture.p"))],
                &["Fixture.B"],
            ),
        ];
        let store = Memory::default();
        let checker = identity("composed raw repeated proof");
        let roots = [n("Fixture.C")];
        let (accepted, _) = import_with(&inputs(&artifacts), &roots, reuse(checker, &store));
        let repeated = accepted.checked.modules.last().unwrap();
        assert_eq!(repeated.name, n("Fixture.C"));
        assert_eq!(
            repeated.base_logical_root, repeated.result_logical_root,
            "the effective world does not retain this repeated proof"
        );
        let records = module_records(&store);
        let dependency = records
            .iter()
            .find(|(_, record)| record.0.modules[0].name == n("Fixture.B").to_canonical_bytes())
            .unwrap()
            .0;

        // This repeat has the same name and type but an invalid proof body.
        // Effective before/after environment roots alone cannot detect it.
        let mut changed = artifacts.clone();
        changed[2] = raw_module(
            "Fixture.C",
            &[theorem("Fixture.s", Expr::sort(Level::zero()))],
            &["Fixture.B"],
        );
        let changed_inputs = inputs(&changed);
        let changed_key =
            module_reuse_key(&changed_inputs[2], &[dependency], &KVMap::new(), checker);
        let planted = Memory::default();
        for (key, mut record) in records {
            if record.0.modules[0].name == n("Fixture.C").to_canonical_bytes() {
                record.0.key = changed_key.0;
                planted.save(changed_key, &record.to_bytes()).unwrap();
            } else {
                planted.save(key, &record.to_bytes()).unwrap();
            }
        }
        let before = planted.0.lock().unwrap().clone();
        let run = |posture| {
            Engine::builder()
                .build_empty()
                .import_olean_modules_with_posture(
                    &changed_inputs,
                    &roots,
                    &KVMap::new(),
                    limits(1),
                    posture,
                    None,
                )
        };
        let cold = run(ImportPostureRequest::Recheck)
            .expect_err("the council rejects the invalid repeated proof");
        let warm = run(reuse(checker, &planted))
            .expect_err("a cache record cannot hide the invalid repeated proof");
        let (SourceOleanImportError::Check(cold), SourceOleanImportError::Check(warm)) =
            (cold, warm)
        else {
            panic!("the refusal must come from declaration checking")
        };
        assert_eq!(
            cold, warm,
            "the same invalid declaration reaches the council"
        );
        assert_eq!(
            *planted.0.lock().unwrap(),
            before,
            "failed imports publish no cache records"
        );
    });
}

#[test]
fn an_ambient_legacy_admission_does_not_seed_a_context_free_module_record() {
    on_import_stack(|| {
        let artifacts = vec![
            raw_module(
                "Fixture.A",
                &[
                    axiom("Fixture.P", Expr::sort(Level::zero())),
                    axiom("Fixture.p", constant("Fixture.P")),
                ],
                &[],
            ),
            raw_module(
                "Fixture.B",
                &[theorem("Fixture.b", constant("Fixture.p"))],
                &[],
            ),
        ];
        let store = Memory::default();
        let checker = identity("composed ambient refusal");
        let roots = [n("Fixture.A"), n("Fixture.B")];
        let (cold, _) = import_with(&inputs(&artifacts), &roots, ImportPostureRequest::Recheck);
        let (actual, report) = import_with(&inputs(&artifacts), &roots, reuse(checker, &store));
        assert_eq!(report.admission, ImportAdmission::Council);
        same_import(&cold, &actual);
        assert!(
            module_records(&store).is_empty(),
            "a legacy ambient result cannot seed modules"
        );
        let alone = subset(&artifacts, &["Fixture.B"]);
        let result = Engine::builder()
            .build_empty()
            .import_olean_modules_with_posture(
                &inputs(&alone),
                &[n("Fixture.B")],
                &KVMap::new(),
                limits(1),
                reuse(checker, &store),
                None,
            );
        assert!(matches!(result, Err(SourceOleanImportError::Check(error))
            if matches!(*error, OleanCheckError::MissingConstants { .. })));
        assert!(module_records(&store).is_empty());
    });
}

#[test]
fn an_actual_pinned_metadata_closure_reuses_modules_under_different_roots() {
    let Some(lib) = pinned_lib() else { return };
    let large = closure(
        &lib,
        &["Init.Data.Cast", "Init.Data.Option.Coe", "Init.Data.Zero"],
    );
    assert_eq!(
        large.len(),
        7,
        "the actual pinned closure this test exercises"
    );
    let small = closure(&lib, &["Init.Data.Option.Coe"]);
    assert!(small.len() < large.len());
    on_import_stack(|| {
        let store = Memory::default();
        let checker = identity("composed actual pinned metadata");
        let (large_council, first) = import_with(
            &inputs(&large),
            &[
                n("Init.Data.Cast"),
                n("Init.Data.Option.Coe"),
                n("Init.Data.Zero"),
            ],
            reuse(checker, &store),
        );
        assert_eq!(
            (first.reused_modules, first.council_modules),
            (0, large.len())
        );
        let roots = [n("Init.Data.Option.Coe")];
        let (cold, _) = import_with(&inputs(&small), &roots, ImportPostureRequest::Recheck);
        let (warm, report) = import_with(&inputs(&small), &roots, reuse(checker, &store));
        assert_eq!(report.admission, ImportAdmission::Reused);
        assert_eq!(
            (report.reused_modules, report.council_modules),
            (small.len(), 0)
        );
        same_import(&cold, &warm);
        assert!(
            warm.modules.iter().any(|module| module.instances > 0),
            "real metadata was replayed"
        );

        // Each root changes metadata replay order, but none changes a module's
        // declared dependency context or its module cache key.
        let reversed = [
            n("Init.Data.Zero"),
            n("Init.Data.Option.Coe"),
            n("Init.Data.Cast"),
        ];
        let (cold_reversed, _) =
            import_with(&inputs(&large), &reversed, ImportPostureRequest::Recheck);
        let (warm_reversed, report) =
            import_with(&inputs(&large), &reversed, reuse(checker, &store));
        assert_eq!(report.admission, ImportAdmission::Reused);
        assert_eq!(
            (report.reused_modules, report.council_modules),
            (large.len(), 0)
        );
        assert_ne!(
            first.key, report.key,
            "root order changes the exact closure key"
        );
        assert_ne!(
            large_council.modules, cold_reversed.modules,
            "actual metadata replay order changes"
        );
        assert_ne!(
            large_council.result_logical_root, cold_reversed.result_logical_root,
            "the pinned registration journals retain replay order"
        );
        same_import(&cold_reversed, &warm_reversed);

        let consumer = n("Consumer");
        let source =
            b"prelude\nimport Init.Data.Option.Coe\ntheorem keep (P : Prop) (h : P) : P := h\n";
        let check = |receipt: &SourceOleanImport| {
            receipt
                .check_source_modules(
                    &[SourceModuleInput {
                        name: &consumer,
                        source,
                    }],
                    &consumer,
                    &KVMap::new(),
                    source_limits(),
                    None,
                )
                .expect("the pinned downstream context resolves")
                .into_complete()
                .expect("the consumer passes both checkers")
        };
        let cold_source = check(&cold_reversed);
        let warm_source = check(&warm_reversed);
        assert_eq!(
            cold_source.checked.base_logical_root,
            warm_source.checked.base_logical_root
        );
        assert_eq!(
            cold_source.checked.result_logical_root,
            warm_source.checked.result_logical_root
        );
        same_engine(
            &cold_source.checked.engine,
            &warm_source.checked.engine,
            "pinned source context",
        );
    });
}
