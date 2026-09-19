//! Real dual-checker module reuse, invalidation, rollback and bounded retention.
#![forbid(unsafe_code)]
use fln::{Budget, CancellationProbe, Engine, EngineAdmissionLimits, KVMap, Name, Outcome, SourceCheckLimits, SourceModuleInput};
use fln::source_check::modules::{SourceModuleCacheLimits, SourceModuleCheckError, SourceModuleCheckLimits, SourceModuleSession, SourceModuleSessionCheck};
use std::sync::atomic::{AtomicUsize, Ordering};

fn n(text: &str) -> Name { Name::from_components(text.split('.')) }
fn limits() -> SourceModuleCheckLimits {
    SourceModuleCheckLimits::new(SourceCheckLimits::new(EngineAdmissionLimits::new(
        Budget::for_stack_bytes(2 * 1024 * 1024),
    )))
}
fn engine() -> Engine {
    Engine::with_source_seed(limits().source.admission).unwrap().into_complete().unwrap()
}
fn session() -> SourceModuleSession {
    SourceModuleSession::new(engine(), KVMap::new(), limits(), SourceModuleCacheLimits::default())
}
fn check_with(
    session: &mut SourceModuleSession,
    files: &[(&str, &str)],
    cancellation: Option<&dyn CancellationProbe>,
) -> Result<Outcome<SourceModuleSessionCheck>, SourceModuleCheckError> {
    let names: Vec<_> = files.iter().map(|(name, _)| n(name)).collect();
    let inputs: Vec<_> = files.iter().zip(&names).map(|((_, source), name)| SourceModuleInput { name, source: source.as_bytes() }).collect();
    session.check_with_cancel(&inputs, &n("Main"), cancellation)
}
fn checked(session: &mut SourceModuleSession, files: &[(&str, &str)]) -> SourceModuleSessionCheck {
    check_with(session, files, None).unwrap_or_else(|error| panic!("{files:?}: {error:?}")).into_complete().unwrap()
}
const GRAPH: [(&str, &str); 4] = [
    ("Main", "import Left Right\ntheorem use : left = right := by rfl"),
    ("Left", "import Base\ndef left := value"),
    ("Right", "import Base\ndef right := value"),
    ("Base", "def value := 7"),
];

#[test]
fn unchanged_graph_reuses_checked_worlds_without_replay_and_matches_cold_roots() {
    let base = engine();
    let before = base.logical_root(&KVMap::new());
    let mut session = SourceModuleSession::new(base.clone(), KVMap::new(), limits(), SourceModuleCacheLimits::default());
    let cold = checked(&mut session, &GRAPH);
    assert_eq!((cold.reused_modules, cold.elaborated_modules), (0, 4));
    assert!(cold.checked.replayed_declarations > 0);
    let warm = checked(&mut session, &GRAPH);
    assert_eq!((warm.reused_modules, warm.elaborated_modules), (4, 0));
    assert_eq!(warm.checked.replayed_declarations, 0);
    assert_eq!(cold.checked.checked.result_logical_root, warm.checked.checked.result_logical_root);
    assert_eq!(cold.checked.checked.commands, warm.checked.checked.commands);
    assert_eq!(cold.checked.checked.theorems, warm.checked.checked.theorems);
    assert_eq!(before, base.logical_root(&KVMap::new()));
    assert!(!base.environment().contains(&n("use")));
    let mut reordered = GRAPH;
    reordered.reverse();
    assert_eq!(checked(&mut session, &reordered).reused_modules, 4);
}

#[test]
fn leaf_edits_reuse_dependencies_and_a_sibling_edit_invalidates_only_its_consumers() {
    let mut session = session();
    let original = checked(&mut session, &GRAPH);
    let original_root = original.checked.checked.result_logical_root;
    let mut changed = GRAPH;
    changed[0].1 = "import Left Right\ntheorem useAgain : left = right := by rfl";
    let leaf = checked(&mut session, &changed);
    assert_eq!((leaf.reused_modules, leaf.elaborated_modules), (3, 1));
    assert!(!leaf.checked.checked.engine.environment().contains(&n("use")));
    assert!(original.checked.checked.engine.environment().contains(&n("use")));
    assert_eq!(original.checked.checked.engine.logical_root(&KVMap::new()), original_root);
    changed[1].1 = "import Base\ndef left := value\ndef additional := 8";
    let sibling = checked(&mut session, &changed);
    assert_eq!((sibling.reused_modules, sibling.elaborated_modules), (2, 2));
    changed[3].1 = "def value := 9";
    let root = checked(&mut session, &changed);
    assert_eq!((root.reused_modules, root.elaborated_modules), (0, 4));
    assert_eq!(checked(&mut session, &changed).reused_modules, 4);
}

#[test]
fn late_false_proofs_do_not_publish_partial_cache_updates_or_stale_success() {
    let mut session = session();
    let good = checked(&mut session, &GRAPH);
    let mut broken = GRAPH;
    broken[3].1 = "def value := 9";
    broken[0].1 = "import Left Right\ntheorem bad : left = 7 := by rfl";
    assert!(check_with(&mut session, &broken, None).is_err());
    assert_eq!(session.retained_modules(), 4);
    let recovery = checked(&mut session, &GRAPH);
    assert_eq!(recovery.reused_modules, 4);
    assert_eq!(recovery.checked.checked.result_logical_root, good.checked.checked.result_logical_root);
    broken[0].1 = "import Left Right\ntheorem repaired : left = 9 := by rfl";
    assert_eq!(checked(&mut session, &broken).elaborated_modules, 4);
}

#[test]
fn cache_cannot_lend_removed_imports_names_or_metadata() {
    let mut session = session();
    let mut files = [
        ("Main", "import Rules\ntheorem use (n : Nat) : wrap (wrap n) = n := by simp"),
        ("Rules", "def wrap (n : Nat) : Nat := n\n@[simp] theorem unwrap (n : Nat) : wrap n = n := by rfl"),
    ];
    checked(&mut session, &files);
    files[1].1 = "def wrap (n : Nat) : Nat := n\ntheorem unwrap (n : Nat) : wrap n = n := by rfl";
    assert!(check_with(&mut session, &files, None).is_err());
    assert!(check_with(&mut session, &[("Main", "theorem stolen (n : Nat) : wrap n = n := by simp")], None).is_err());
    assert!(check_with(&mut session, &[files[0]], None).is_err());
    files[0].1 = "import Rules\ntheorem use (n : Nat) : wrap (wrap n) = n := by simp only [unwrap]";
    let repaired = checked(&mut session, &files);
    assert_eq!(repaired.reused_modules, 0);
    assert!(fln_elab::source::scope::simp::read(repaired.checked.checked.engine.environment()).unwrap().is_empty());
}

#[test]
fn changing_imported_instances_rechecks_consumers_but_not_independent_siblings() {
    let mut session = session();
    let mut files = [
        ("Main", "import Choice Independent\ntheorem fixed : independent = 0 := by rfl\ntheorem current : (default : Nat) = 7 := by rfl"),
        ("Choice", "instance seven : Inhabited Nat := Inhabited.mk 7"),
        ("Independent", "def independent : Nat := default"),
    ];
    checked(&mut session, &files);
    files[1].1 = "instance nine : Inhabited Nat := Inhabited.mk 9";
    assert!(check_with(&mut session, &files, None).is_err());
    files[0].1 = "import Choice Independent\ntheorem fixed : independent = 0 := by rfl\ntheorem current : (default : Nat) = 9 := by rfl";
    let result = checked(&mut session, &files);
    assert_eq!((result.reused_modules, result.elaborated_modules), (1, 2));
}

struct StopAfter { calls: AtomicUsize, after: usize }
impl CancellationProbe for StopAfter {
    fn is_cancelled(&self) -> bool { self.calls.fetch_add(1, Ordering::Relaxed) >= self.after }
}
#[test]
fn cancellation_also_vetoes_fully_cached_publication_and_keeps_the_prior_closure() {
    let mut session = session();
    checked(&mut session, &GRAPH);
    // before-plan, four before-module samples, then before-publication.
    for after in [0, 2, 5] {
        let stop = StopAfter { calls: AtomicUsize::new(0), after };
        assert!(matches!(check_with(&mut session, &GRAPH, Some(&stop)), Ok(Outcome::Inconclusive(_))));
        assert_eq!(session.retained_modules(), 4);
        assert_eq!(checked(&mut session, &GRAPH).reused_modules, 4);
    }
}

#[test]
fn retention_is_bounded_clearable_and_never_required_for_checking() {
    let mut session = SourceModuleSession::new(engine(), KVMap::new(), limits(), SourceModuleCacheLimits { max_modules: 1, max_source_bytes: 100 });
    checked(&mut session, &GRAPH);
    assert_eq!(session.retained_modules(), 1);
    assert_eq!(session.retained_source_bytes(), GRAPH[3].1.len());
    assert_eq!(checked(&mut session, &GRAPH).reused_modules, 1);
    session.clear();
    assert_eq!(session.retained_modules(), 0);
    assert_eq!(session.retained_source_bytes(), 0);
    assert_eq!(checked(&mut session, &GRAPH).reused_modules, 0);
    let mut disabled = SourceModuleSession::new(engine(), KVMap::new(), limits(), SourceModuleCacheLimits { max_modules: 0, max_source_bytes: 0 });
    checked(&mut disabled, &GRAPH);
    assert_eq!(checked(&mut disabled, &GRAPH).reused_modules, 0);
    assert_eq!(disabled.retained_modules(), 0);
}

#[test]
fn cached_modules_still_count_against_aggregate_source_command_limits() {
    let mut bounded = limits();
    bounded.source.max_commands = 3;
    let mut session = SourceModuleSession::new(engine(), KVMap::new(), bounded, SourceModuleCacheLimits::default());
    let mut files = [("Main", "import A B"), ("A", "def a := 1"), ("B", "def b := 2")];
    checked(&mut session, &files);
    files[1].1 = "def a := 1\ndef more := 2\ndef extra := 3";
    assert!(check_with(&mut session, &files, None).is_err());
    files[1].1 = "def a := 1";
    assert_eq!(checked(&mut session, &files).reused_modules, 3);
}

#[test]
fn replacing_the_successful_closure_evicts_old_unrelated_worlds() {
    let mut session = session();
    checked(&mut session, &GRAPH);
    let replacement = checked(&mut session, &[("Main", "def onlyHere := 11")]);
    assert_eq!(replacement.reused_modules, 0);
    assert_eq!(session.retained_modules(), 1);
    assert!(!replacement.checked.checked.engine.environment().contains(&n("value")));
    assert_eq!(checked(&mut session, &GRAPH).reused_modules, 0);
}
