//! Incremental module compilation uses only private, dual-checked source products.
#![forbid(unsafe_code)]
use fln::source_check::modules::{
    SourceModuleBuild, SourceModuleBuildError, SourceModuleCacheLimits, SourceModuleCheckError,
    SourceModuleCheckLimits, SourceModuleSession,
};
use fln::{
    Budget, CancellationProbe, Engine, EngineAdmissionLimits, KVMap, Name, OleanCheckLimits,
    OleanModuleInput, OleanWriteBudget, Outcome, SourceCheckLimits, SourceModuleInput,
};
use std::sync::atomic::{AtomicUsize, Ordering};

fn name(value: &str) -> Name {
    Name::from_components(value.split('.'))
}
fn limits() -> SourceModuleCheckLimits {
    SourceModuleCheckLimits::new(SourceCheckLimits::new(EngineAdmissionLimits::new(
        Budget::for_stack_bytes(2 * 1024 * 1024),
    )))
}
fn session() -> SourceModuleSession {
    SourceModuleSession::new(
        Engine::builder().build_empty(),
        KVMap::new(),
        limits(),
        SourceModuleCacheLimits::default(),
    )
}
fn inputs<'a>(files: &'a [(&str, &str)], names: &'a [Name]) -> Vec<SourceModuleInput<'a>> {
    files
        .iter()
        .zip(names)
        .map(|((_, source), name)| SourceModuleInput {
            name,
            source: source.as_bytes(),
        })
        .collect()
}
fn compile(
    session: &mut SourceModuleSession,
    files: &[(&str, &str)],
    budget: OleanWriteBudget,
    cancellation: Option<&dyn CancellationProbe>,
) -> Result<Outcome<SourceModuleBuild>, SourceModuleBuildError> {
    let names: Vec<_> = files.iter().map(|(module, _)| name(module)).collect();
    session.compile_with_cancel(&inputs(files, &names), &name("Main"), budget, cancellation)
}
fn build(session: &mut SourceModuleSession, files: &[(&str, &str)]) -> SourceModuleBuild {
    compile(session, files, OleanWriteBudget::default(), None)
        .unwrap_or_else(|error| panic!("{files:?}: {error:?}"))
        .into_complete()
        .unwrap()
}
fn products(build: &SourceModuleBuild) -> Vec<(Name, Vec<u8>)> {
    build
        .artifacts
        .iter()
        .map(|artifact| (artifact.name.clone(), artifact.bytes.clone()))
        .collect()
}
const GRAPH: [(&str, &str); 4] = [
    (
        "Main",
        "prelude\nimport Left Right\ntheorem use (P : Prop) (h : P) : P := left P (right P h)",
    ),
    (
        "Left",
        "prelude\nimport Base\ndef left (P : Prop) (h : P) : P := base P h",
    ),
    (
        "Right",
        "prelude\nimport Base\ndef right (P : Prop) (h : P) : P := base P h",
    ),
    ("Base", "prelude\ndef base (P : Prop) (h : P) : P := h"),
];

#[test]
fn warm_build_emits_all_byte_identical_artifacts_without_reelaboration_or_replay() {
    let mut session = session();
    let cold = build(&mut session, &GRAPH);
    assert_eq!((cold.reused_modules, cold.elaborated_modules), (0, 4));
    assert!(cold.checked.replayed_declarations > 0);
    let mut reversed = GRAPH;
    reversed.reverse();
    let warm = build(&mut session, &reversed);
    assert_eq!((warm.reused_modules, warm.elaborated_modules), (4, 0));
    assert_eq!(warm.checked.replayed_declarations, 0);
    assert_eq!(products(&cold), products(&warm));
    assert_eq!(
        warm.checked.checked.result_logical_root,
        cold.checked.checked.result_logical_root
    );
    let imports: Vec<_> = warm
        .artifacts
        .iter()
        .map(|artifact| OleanModuleInput {
            name: &artifact.name,
            artifact: &artifact.bytes,
            server_artifact: None,
            private_artifact: None,
        })
        .collect();
    let rechecked = Engine::builder()
        .build_empty()
        .check_olean_modules(
            &imports,
            &KVMap::new(),
            OleanCheckLimits::new(4 * 1024 * 1024, limits().source.admission.kernel),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(
        rechecked.engine.logical_root(&KVMap::new()),
        warm.checked.checked.result_logical_root
    );
    assert_eq!(rechecked.engine.environment().len(), 4);
}

#[test]
fn edits_invalidate_the_dependency_cone_and_preserve_cold_artifact_identity() {
    let mut session = session();
    build(&mut session, &GRAPH);
    let mut files = GRAPH;
    for (index, source, expected) in [
        (
            0,
            "prelude\nimport Left Right\ntheorem changed (P : Prop) (h : P) : P := left P (right P h)",
            (3, 1),
        ),
        (
            1,
            "prelude\nimport Base\ndef left (P : Prop) (h : P) : P := base P h\ndef extra (A : Type) (a : A) : A := a",
            (2, 2),
        ),
        (
            3,
            "prelude\ndef base (P : Prop) (h : P) : P := h\ndef extraBase (A : Type) (a : A) : A := a",
            (0, 4),
        ),
    ] {
        files[index].1 = source;
        let incremental = build(&mut session, &files);
        assert_eq!(
            (incremental.reused_modules, incremental.elaborated_modules),
            expected
        );
        let names: Vec<_> = files.iter().map(|(module, _)| name(module)).collect();
        let cold = Engine::builder()
            .build_empty()
            .compile_source_modules(
                &inputs(&files, &names),
                &name("Main"),
                &KVMap::new(),
                limits(),
                OleanWriteBudget::default(),
            )
            .unwrap()
            .into_complete()
            .unwrap();
        assert_eq!(products(&incremental), products(&cold));
    }
}

#[test]
fn failed_source_and_late_writer_failure_do_not_replace_the_successful_cache() {
    let mut session = session();
    let good = build(&mut session, &GRAPH);
    let mut changed = GRAPH;
    changed[3].1 =
        "prelude\ndef base (P : Prop) (h : P) : P := h\ndef added (A : Type) (a : A) : A := a";
    changed[0].1 = "prelude\nimport Left Right\ntheorem bad (P : Prop) : P := by rfl";
    assert!(compile(&mut session, &changed, OleanWriteBudget::default(), None).is_err());
    assert_eq!(build(&mut session, &GRAPH).reused_modules, 4);
    changed[0] = GRAPH[0];
    let budget = OleanWriteBudget {
        max_bytes: good.artifacts[0].report.file_bytes + 64,
        ..Default::default()
    };
    assert!(matches!(
        compile(&mut session, &changed, budget, None),
        Err(SourceModuleBuildError::Encode { .. })
    ));
    assert_eq!(session.retained_modules(), 4);
    let recovered = build(&mut session, &GRAPH);
    assert_eq!(recovered.reused_modules, 4);
    assert_eq!(products(&recovered), products(&good));
    assert_eq!(build(&mut session, &changed).elaborated_modules, 4);
}

#[test]
fn cached_products_cannot_bypass_fresh_aggregate_byte_or_object_budgets() {
    let mut session = session();
    let good = build(&mut session, &GRAPH);
    let bytes: u64 = good.artifacts.iter().map(|a| a.report.file_bytes).sum();
    let objects: u64 = good
        .artifacts
        .iter()
        .map(|a| a.report.runtime_objects)
        .sum();
    for budget in [
        OleanWriteBudget {
            max_bytes: bytes - 1,
            ..Default::default()
        },
        OleanWriteBudget {
            max_objects: objects - 1,
            ..Default::default()
        },
    ] {
        assert!(matches!(
            compile(&mut session, &GRAPH, budget, None),
            Err(SourceModuleBuildError::Encode { .. })
        ));
        assert_eq!(build(&mut session, &GRAPH).reused_modules, 4);
    }
    let exact = OleanWriteBudget {
        max_bytes: bytes,
        max_objects: objects,
    };
    let built = compile(&mut session, &GRAPH, exact, None)
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(products(&built), products(&good));
}

struct StopAfter {
    calls: AtomicUsize,
    after: usize,
}
impl CancellationProbe for StopAfter {
    fn is_cancelled(&self) -> bool {
        self.calls.fetch_add(1, Ordering::Relaxed) >= self.after
    }
}
#[test]
fn cancellation_during_warm_encoding_or_final_publication_keeps_the_previous_cache() {
    let mut session = session();
    let good = build(&mut session, &GRAPH);
    let count = StopAfter {
        calls: AtomicUsize::new(0),
        after: usize::MAX,
    };
    compile(
        &mut session,
        &GRAPH,
        OleanWriteBudget::default(),
        Some(&count),
    )
    .unwrap()
    .into_complete()
    .unwrap();
    let calls = count.calls.load(Ordering::Relaxed);
    assert!(calls > GRAPH.len());
    let mut stages = String::new();
    for after in 0..calls {
        let stop = StopAfter {
            calls: AtomicUsize::new(0),
            after,
        };
        let result = compile(
            &mut session,
            &GRAPH,
            OleanWriteBudget::default(),
            Some(&stop),
        )
        .unwrap();
        stages.push_str(&format!("{result:?}"));
        assert!(matches!(result, Outcome::Inconclusive(_)), "after={after}");
        let recovered = build(&mut session, &GRAPH);
        assert_eq!(recovered.reused_modules, 4);
        assert_eq!(products(&recovered), products(&good));
    }
    assert!(stages.contains("source-modules/before-encoding"));
    assert!(stages.contains("source-modules/before-build-publication"));
}

#[test]
fn checking_cache_cannot_skip_implicit_init_or_extension_serialization_refusals() {
    let mut session = session();
    for source in [
        "def identity (P : Prop) (h : P) : P := h",
        "prelude\nclass Container (A : Type) where\n  value : A\ninstance wrapped (A : Type) (a : A) : Container A := Container.mk a",
    ] {
        let files = [("Main", source)];
        let names = [name("Main")];
        session
            .check(&inputs(&files, &names), &name("Main"))
            .unwrap()
            .into_complete()
            .unwrap();
        assert!(compile(&mut session, &files, OleanWriteBudget::default(), None).is_err());
        assert_eq!(
            session
                .check(&inputs(&files, &names), &name("Main"))
                .unwrap()
                .into_complete()
                .unwrap()
                .reused_modules,
            1
        );
    }
}

#[test]
fn checking_and_compilation_caches_never_mix_header_semantics_or_resource_charges() {
    let mut session = session();
    let names: Vec<_> = GRAPH.iter().map(|(module, _)| name(module)).collect();
    session
        .check(&inputs(&GRAPH, &names), &name("Main"))
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(build(&mut session, &GRAPH).elaborated_modules, 4);
    assert_eq!(build(&mut session, &GRAPH).reused_modules, 4);
    let checked = session
        .check(&inputs(&GRAPH, &names), &name("Main"))
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(checked.elaborated_modules, 4);
    assert_eq!(build(&mut session, &GRAPH).elaborated_modules, 4);
}

#[test]
fn retention_eviction_and_mutated_returned_bytes_cannot_supply_a_false_cache_hit() {
    let mut empty = SourceModuleSession::new(
        Engine::builder().build_empty(),
        KVMap::new(),
        limits(),
        SourceModuleCacheLimits {
            max_modules: 0,
            max_source_bytes: 0,
        },
    );
    let baseline = build(&mut empty, &GRAPH);
    assert_eq!(build(&mut empty, &GRAPH).elaborated_modules, 4);
    assert_eq!(empty.retained_modules(), 0);
    let mut small = SourceModuleSession::new(
        Engine::builder().build_empty(),
        KVMap::new(),
        limits(),
        SourceModuleCacheLimits {
            max_modules: 1,
            max_source_bytes: 4096,
        },
    );
    let mut first = build(&mut small, &GRAPH);
    for artifact in &mut first.artifacts {
        artifact.bytes.fill(0);
    }
    let second = build(&mut small, &GRAPH);
    assert_eq!((second.reused_modules, second.elaborated_modules), (1, 3));
    assert_eq!(products(&second), products(&baseline));
    small.clear();
    assert_eq!(small.retained_source_bytes(), 0);
    assert_eq!(build(&mut small, &GRAPH).elaborated_modules, 4);
}

#[test]
fn warm_modules_still_consume_the_aggregate_command_budget() {
    let mut restricted = limits();
    restricted.source.max_commands = 4;
    let mut session = SourceModuleSession::new(
        Engine::builder().build_empty(),
        KVMap::new(),
        restricted,
        SourceModuleCacheLimits::default(),
    );
    build(&mut session, &GRAPH);
    let mut files = GRAPH;
    files[0].1 = "prelude\nimport Left Right\ndef one (P : Prop) (h : P) : P := left P h\ndef two (P : Prop) (h : P) : P := right P h";
    assert!(compile(&mut session, &files, OleanWriteBudget::default(), None).is_err());
    assert_eq!(build(&mut session, &GRAPH).reused_modules, 4);
}

#[test]
fn cache_cannot_lend_a_removed_dependency_or_export_an_unbound_seed() {
    let mut session = session();
    build(&mut session, &GRAPH);
    assert!(matches!(
        compile(&mut session, &[GRAPH[0]], OleanWriteBudget::default(), None),
        Err(SourceModuleBuildError::Check(
            SourceModuleCheckError::MissingModule { .. }
        ))
    ));
    let files = [(
        "Main",
        "prelude\ntheorem stolen (P : Prop) (h : P) : P := left P h",
    )];
    assert!(compile(&mut session, &files, OleanWriteBudget::default(), None).is_err());
    assert_eq!(build(&mut session, &GRAPH).reused_modules, 4);
    let seeded = Engine::with_source_seed(limits().source.admission)
        .unwrap()
        .into_complete()
        .unwrap();
    let mut seeded = SourceModuleSession::new(
        seeded,
        KVMap::new(),
        limits(),
        SourceModuleCacheLimits::default(),
    );
    assert!(matches!(
        compile(&mut seeded, &GRAPH, OleanWriteBudget::default(), None),
        Err(SourceModuleBuildError::UnboundBase)
    ));
}
