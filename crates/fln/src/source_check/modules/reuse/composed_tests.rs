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
            "prelude\nimport Left\nimport Right\ndef run.{u} {A : Sort u} (x : A) : A := leftId (rightId x)",
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
fn ready_councils_overlap_and_each_waits_for_its_declared_dependencies() {
    use std::sync::{Condvar, Mutex};
    use std::time::Duration;

    #[derive(Default)]
    struct Visits {
        started: BTreeSet<Name>,
        finished: BTreeSet<Name>,
        active: usize,
        peak: usize,
    }

    on_import_stack(|| {
        let artifacts = source_diamond("");
        let all = inputs(&artifacts);
        let options = KVMap::new();
        let engine = Engine::builder().build_empty();
        let (cold, _) = import_with(&all, &[n("Main")], ImportPostureRequest::Recheck);
        for threads in [2, 8] {
            for warm_base in [false, true] {
                let store = Memory::default();
                let checker = identity("concurrent module councils");
                let visits = Mutex::new(Visits::default());
                let wake = Condvar::new();
                if warm_base {
                    let base = subset(&artifacts, &["Base"]);
                    import_with(&inputs(&base), &[n("Base")], reuse(checker, &store));
                    visits.lock().unwrap().finished.insert(n("Base"));
                }
                let limits = limits(threads);
                let council = |name: &Name, context: &Engine, decoded: DecodedOlean| {
                    let mut seen = visits.lock().unwrap();
                    for import in &decoded.module.imports {
                        assert!(
                            seen.finished.contains(&import.module),
                            "{} began before its import {} completed",
                            name.to_display_string(),
                            import.module.to_display_string(),
                        );
                    }
                    if *name == n("Left") {
                        assert!(!context.environment.contains(&n("rightId")));
                    }
                    if *name == n("Right") {
                        assert!(!context.environment.contains(&n("leftId")));
                    }
                    assert!(seen.started.insert(name.clone()), "one council per miss");
                    seen.active += 1;
                    seen.peak = seen.peak.max(seen.active);
                    wake.notify_all();
                    if *name == n("Left") || *name == n("Right") {
                        let other = if *name == n("Left") {
                            n("Right")
                        } else {
                            n("Left")
                        };
                        let (after, _) = wake
                            .wait_timeout_while(seen, Duration::from_secs(10), |seen| {
                                !seen.started.contains(&other)
                            })
                            .unwrap();
                        seen = after;
                        // The timeout is only a deadlock watchdog: correctness is
                        // the observed rendezvous, not either operation's speed.
                        assert!(
                            seen.started.contains(&other),
                            "ready councils were serialized"
                        );
                    }
                    drop(seen);
                    let result = context.check_decoded_olean(decoded, &options, limits.check);
                    let mut seen = visits.lock().unwrap();
                    seen.active -= 1;
                    if matches!(result, Ok(Outcome::Complete(_))) {
                        seen.finished.insert(name.clone());
                    }
                    wake.notify_all();
                    result
                };
                let composed = engine
                    .compose_recorded_modules_with(
                        &all,
                        &options,
                        limits,
                        &ReuseVerified {
                            checker,
                            store: &store,
                        },
                        None,
                        &council,
                    )
                    .expect("real councils complete")
                    .into_complete()
                    .expect("the scheduler returns a complete answer")
                    .expect("the diamond uses only declared imports");
                assert_eq!(composed.reused, usize::from(warm_base));
                assert_eq!(composed.records.len(), 4 - usize::from(warm_base));
                let seen = visits.lock().unwrap();
                assert_eq!(seen.active, 0);
                assert_eq!(
                    seen.peak, 2,
                    "the diamond has two ready independent siblings"
                );
                assert!(seen.peak <= threads);
                assert_eq!(seen.finished.len(), 4);
                drop(seen);
                let actual = engine
                    .activate_source_metadata(
                        composed.checked,
                        &all,
                        &[n("Main")],
                        &options,
                        limits,
                        None,
                    )
                    .expect("the common metadata activation succeeds")
                    .into_complete()
                    .expect("metadata is complete");
                same_import(&cold, &actual);
                same_source_contexts(&cold, &actual);
            }
        }
    });
}

#[test]
fn parallel_cold_mixed_and_reused_imports_publish_the_serial_roots() {
    on_import_stack(|| {
        let artifacts = source_diamond("");
        let all = inputs(&artifacts);
        let roots = [n("Main")];
        let options = KVMap::new();
        let engine = Engine::builder().build_empty();
        let (cold, _) = import_with(&all, &roots, ImportPostureRequest::Recheck);
        for threads in [1, 8] {
            for warm_base in [false, true] {
                let store = Memory::default();
                let checker = identity("public parallel module reuse");
                if warm_base {
                    let base = subset(&artifacts, &["Base"]);
                    import_with(&inputs(&base), &[n("Base")], reuse(checker, &store));
                }
                let import = || {
                    engine
                        .import_olean_modules_with_posture(
                            &all,
                            &roots,
                            &options,
                            limits(threads),
                            reuse(checker, &store),
                            None,
                        )
                        .expect("public import succeeds")
                        .into_complete()
                        .expect("public import is complete")
                };
                let (actual, report) = import();
                assert_eq!(report.reused_modules, usize::from(warm_base));
                assert_eq!(report.council_modules, 4 - usize::from(warm_base));
                assert_eq!(module_records(&store).len(), 4);
                same_import(&cold, &actual);
                same_source_contexts(&cold, &actual);
                let (again, report) = import();
                assert_eq!((report.reused_modules, report.council_modules), (4, 0));
                assert_eq!(report.record, RecordLookup::Hit);
                same_import(&cold, &again);
            }
        }
    });
}

#[test]
fn cancellation_after_parallel_councils_never_dispatches_their_importer() {
    use std::sync::Mutex;
    use std::sync::atomic::{AtomicBool, Ordering};

    struct Cancelled(AtomicBool);
    impl CancellationProbe for Cancelled {
        fn is_cancelled(&self) -> bool {
            self.0.load(Ordering::SeqCst)
        }
    }

    on_import_stack(|| {
        let artifacts = source_diamond("");
        let all = inputs(&artifacts);
        let options = KVMap::new();
        let store = Memory::default();
        let checker = identity("cancel parallel module councils");
        let cancelled = Cancelled(AtomicBool::new(false));
        let started = Mutex::new(BTreeSet::new());
        let limits = limits(8);
        let council = |name: &Name, context: &Engine, decoded: DecodedOlean| {
            started.lock().unwrap().insert(name.clone());
            let result = context.check_decoded_olean(decoded, &options, limits.check);
            if *name == n("Left") {
                cancelled.0.store(true, Ordering::SeqCst);
            }
            result
        };
        let outcome = Engine::builder()
            .build_empty()
            .compose_recorded_modules_with(
                &all,
                &options,
                limits,
                &ReuseVerified {
                    checker,
                    store: &store,
                },
                Some(&cancelled),
                &council,
            )
            .expect("cancellation remains a nonanswer");
        assert!(matches!(outcome, Outcome::Inconclusive(reason)
            if matches!(reason.cause, fln_core::outcome::InconclusiveCause::Cancelled { .. })));
        assert_eq!(
            *started.lock().unwrap(),
            [n("Base"), n("Left"), n("Right")].into_iter().collect(),
            "the already-dispatched siblings settle, and Main never starts",
        );
        assert!(store.0.lock().unwrap().is_empty());
        let (recovered, report) = import_with(&all, &[n("Main")], reuse(checker, &store));
        assert_eq!((report.reused_modules, report.council_modules), (0, 4));
        let (cold, _) = import_with(&all, &[n("Main")], ImportPostureRequest::Recheck);
        same_import(&cold, &recovered);
    });
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
        for threads in [1, 8] {
            cancel.observed.store(false, Ordering::SeqCst);
            let cancelled = Engine::builder()
                .build_empty()
                .import_olean_modules_with_posture(
                    &all,
                    &[n("Main")],
                    &KVMap::new(),
                    limits(threads),
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

            let mut limited = limits(threads);
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
        }

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
fn an_earlier_dependent_failure_wins_over_a_later_ready_failure() {
    use std::sync::{Condvar, Mutex};
    use std::time::Duration;

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
                &[theorem("Fixture.invalidProof", constant("Fixture.P"))],
                &["Fixture.A"],
            ),
            raw_module(
                "Fixture.C",
                &[axiom("Fixture.missingType", constant("Fixture.absent"))],
                &[],
            ),
            raw_module(
                "Fixture.D",
                &[axiom("Fixture.unneeded", Expr::sort(Level::zero()))],
                &[],
            ),
        ];
        let all = inputs(&artifacts);
        let options = KVMap::new();
        let engine = Engine::builder().build_empty();
        let serial = match engine.check_olean_modules(&all, &options, limits(1).check) {
            Err(error @ OleanCheckError::Admission(_)) => error,
            other => panic!("the serial door must reach B's bad proof: {other:?}"),
        };
        let store = Memory::default();
        let checker = identity("canonical parallel module refusal");
        let visits = Mutex::new((BTreeSet::new(), BTreeSet::new()));
        let wake = Condvar::new();
        let parallel = limits(2);
        let council = |name: &Name, context: &Engine, decoded: DecodedOlean| {
            let mut seen = visits.lock().unwrap();
            seen.0.insert(name.clone());
            if *name == n("Fixture.A") {
                let (after, _) = wake
                    .wait_timeout_while(seen, Duration::from_secs(10), |seen| {
                        !seen.1.contains(&n("Fixture.C"))
                    })
                    .unwrap();
                seen = after;
                assert!(seen.1.contains(&n("Fixture.C")), "C must settle first");
            }
            if *name == n("Fixture.B") {
                assert!(seen.1.contains(&n("Fixture.A")), "B waits for A");
                assert!(seen.1.contains(&n("Fixture.C")), "C has already failed");
            }
            drop(seen);
            let result = context.check_decoded_olean(decoded, &options, parallel.check);
            if *name == n("Fixture.C") {
                assert!(matches!(
                    result,
                    Err(OleanCheckError::MissingConstants { .. })
                ));
            }
            visits.lock().unwrap().1.insert(name.clone());
            wake.notify_all();
            result
        };
        let actual = engine.compose_recorded_modules_with(
            &all,
            &options,
            parallel,
            &ReuseVerified {
                checker,
                store: &store,
            },
            None,
            &council,
        );
        match actual {
            Err(error) => assert_eq!(error, serial, "canonical B wins over faster C"),
            _ => panic!("composition must preserve the serial failure"),
        }
        assert_eq!(
            visits.lock().unwrap().0,
            [n("Fixture.A"), n("Fixture.B"), n("Fixture.C")]
                .into_iter()
                .collect(),
            "no new work is dispatched beyond the known failure",
        );
        assert!(store.0.lock().unwrap().is_empty());
        for threads in [1, 8] {
            let outcome = engine.import_olean_modules_with_posture(
                &all,
                &[n("Fixture.B"), n("Fixture.C"), n("Fixture.D")],
                &options,
                limits(threads),
                reuse(checker, &store),
                None,
            );
            assert!(
                matches!(outcome, Err(SourceOleanImportError::Check(error)) if *error == serial)
            );
            assert!(
                store.0.lock().unwrap().is_empty(),
                "failed imports publish nothing"
            );
        }
    });
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
