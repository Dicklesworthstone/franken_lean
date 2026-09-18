//! Native source libraries retain module visibility, metadata and dual admission.
#![forbid(unsafe_code)]
use fln::{Budget, CancellationProbe, Engine, EngineAdmissionLimits, KVMap, Name, Outcome, SourceCheckLimits, SourceModuleInput};
use fln::source_check::modules::{SourceModuleCheck, SourceModuleCheckError, SourceModuleCheckLimits};

fn n(text: &str) -> Name { Name::from_components(text.split('.')) }
fn limits() -> SourceModuleCheckLimits {
    SourceModuleCheckLimits::new(SourceCheckLimits::new(EngineAdmissionLimits::new(
        Budget::for_stack_bytes(2 * 1024 * 1024),
    )))
}
fn engine() -> Engine {
    Engine::with_source_seed(limits().source.admission).unwrap().into_complete().unwrap()
}
fn check(base: &Engine, files: &[(&str, &str)]) -> Result<Outcome<SourceModuleCheck>, SourceModuleCheckError> {
    check_with(base, files, limits())
}
fn check_with(base: &Engine, files: &[(&str, &str)], limits: SourceModuleCheckLimits) -> Result<Outcome<SourceModuleCheck>, SourceModuleCheckError> {
    let names: Vec<_> = files.iter().map(|(name, _)| n(name)).collect();
    let modules: Vec<_> = files.iter().zip(&names).map(|((_, source), name)| SourceModuleInput { name, source: source.as_bytes() }).collect();
    base.check_source_modules(&modules, &n("Main"), &KVMap::new(), limits)
}
fn checked(base: &Engine, files: &[(&str, &str)]) -> SourceModuleCheck {
    check(base, files).unwrap_or_else(|error| panic!("{files:?}: {error:?}")).into_complete().unwrap()
}

#[test]
fn imported_polymorphic_theorems_use_the_ordinary_source_and_checker_path() {
    let base = engine();
    let before = base.logical_root(&KVMap::new());
    let result = checked(&base, &[
        ("Main", "import Lib\nopen Library\ntheorem use (n : Nat) : ident n = n := by exact identity n"),
        ("Lib", "namespace Library\ndef ident.{u} {A : Sort u} (x : A) : A := x\ntheorem identity.{u} {A : Sort u} (x : A) : ident x = x := by rfl\nend Library"),
    ]);
    assert_eq!(result.module_order, [n("Lib"), n("Main")]);
    assert_eq!(result.checked.files, 2);
    assert_eq!(result.checked.theorems, 2);
    assert_eq!(result.checked.base_logical_root, before);
    assert_eq!(base.logical_root(&KVMap::new()), before);
    assert!(result.checked.engine.environment().contains(&n("use")));
    assert!(!base.environment().contains(&n("use")));
    assert_eq!(result.checked.result_logical_root, result.checked.engine.logical_root(&KVMap::new()));
}

#[test]
fn diamonds_replay_shared_declarations_and_simp_journals_once() {
    let result = checked(&engine(), &[
        ("Main", "import Left Right Left\ntheorem use (n : Nat) : wrap (wrap n) = n := by simp"),
        ("Left", "import Base\ndef left := 1"),
        ("Right", "import Base\ndef right := 2"),
        ("Base", "def wrap (n : Nat) : Nat := n\n@[simp] theorem unwrap (n : Nat) : wrap n = n := by rfl"),
    ]);
    assert_eq!(result.module_order, [n("Base"), n("Left"), n("Right"), n("Main")]);
    assert_eq!(fln_elab::source::scope::simp::read(result.checked.engine.environment()).unwrap().len(), 1);
    assert_eq!(result.checked.theorems, 2);
}

#[test]
fn sibling_instances_cannot_change_previously_elaborated_definitions() {
    let result = checked(&engine(), &[
        ("Main", "import Choice Independent\ntheorem fixed : independent = 0 := by rfl\ntheorem current : (default : Nat) = 7 := by rfl"),
        ("Choice", "instance seven : Inhabited Nat := Inhabited.mk 7"),
        ("Independent", "def independent : Nat := default"),
    ]);
    assert!(result.checked.engine.environment().contains(&n("fixed")));
    assert!(result.checked.engine.environment().contains(&n("current")));
}

#[test]
fn siblings_cannot_lend_names_or_simp_rules_to_an_unimporting_module() {
    let base = engine();
    let before = base.logical_root(&KVMap::new());
    let result = check(&base, &[
        ("Main", "import A B"),
        ("A", "def secret := 7"),
        ("B", "def stolen := secret"),
    ]);
    assert!(matches!(result, Err(SourceModuleCheckError::Source { module, .. }) if module == n("B")));
    let result = check(&base, &[
        ("Main", "import A B"),
        ("Base", "def wrap (n : Nat) : Nat := n"),
        ("A", "import Base\n@[simp] theorem unwrap (n : Nat) : wrap n = n := by rfl"),
        ("B", "import Base\ntheorem stolen (n : Nat) : wrap n = n := by simp"),
    ]);
    assert!(matches!(result, Err(SourceModuleCheckError::Source { module, .. }) if module == n("B")));
    assert_eq!(base.logical_root(&KVMap::new()), before);
    checked(&base, &[("Main", "theorem recovery : (0 : Nat) = 0 := by rfl")]);
}

#[test]
fn import_order_controls_instance_recency_not_input_array_order() {
    let base = engine();
    for (imports, expected) in [("A B", 9), ("B A", 7)] {
        let main = format!("import {imports}\ntheorem chosen : (default : Nat) = {expected} := by rfl");
        let files = [("Main", main.as_str()), ("A", "instance seven : Inhabited Nat := Inhabited.mk 7"), ("B", "instance nine : Inhabited Nat := Inhabited.mk 9")];
        let first = checked(&base, &files);
        let second = checked(&base, &[files[2], files[0], files[1]]);
        assert_eq!(first.module_order, second.module_order);
        assert_eq!(first.checked.result_logical_root, second.checked.result_logical_root);
    }
}

#[test]
fn source_inductive_blocks_and_record_metadata_survive_imports() {
    checked(&engine(), &[
        ("Main", "import Data\ntheorem use : tag Choice.left = 1 := by rfl\ndef record : Box := { value := 9 }\ntheorem field : record.value = 9 := by rfl"),
        ("Data", "inductive Choice where\n| left\n| right\ndef tag (x : Choice) : Nat := match x with | Choice.left => 1 | Choice.right => 2\nstructure Box where\n  value : Nat"),
    ]);
}

#[test]
fn conflicting_sibling_declarations_are_not_deduplicated_by_spelling() {
    let result = check(&engine(), &[
        ("Main", "import A B"), ("A", "def collision := 1"), ("B", "def collision := 1"),
    ]);
    assert!(matches!(result, Err(SourceModuleCheckError::Replay { .. })));
}

#[test]
fn missing_cyclic_duplicate_and_unreachable_modules_refuse_before_publication() {
    let base = engine();
    assert!(matches!(check(&base, &[("Main", "import Missing")]), Err(SourceModuleCheckError::MissingModule { .. })));
    assert!(matches!(check(&base, &[("Main", "import A"), ("A", "import Main")]), Err(SourceModuleCheckError::Cycle(_))));
    assert!(matches!(check(&base, &[("Main", ""), ("Main", "")]), Err(SourceModuleCheckError::DuplicateModule(_))));
    assert!(matches!(check(&base, &[("Main", ""), ("Other", "def hidden := 1")]), Err(SourceModuleCheckError::UnreachableModule(_))));
}

#[test]
fn errors_retain_original_offsets_after_unicode_crlf_headers() {
    let source = "-- 🤖\r\nimport Base\r\ndef good := 0\r\ndef bad : Nat := missing";
    let result = check(&engine(), &[("Main", source), ("Base", "def imported := 1")]);
    let Err(SourceModuleCheckError::Source { module, error }) = result else { panic!("source error") };
    assert_eq!(module, n("Main"));
    let fln::SourceCheckError::Command { offset, .. } = error else { panic!("command error") };
    assert!(offset >= source.find("def bad").unwrap());
    assert!(offset <= source.len());
}

#[test]
fn resource_and_cancellation_stops_publish_no_successor() {
    let base = engine();
    let before = base.logical_root(&KVMap::new());
    let files = [("Main", "import A\ndef answer := fromA"), ("A", "def fromA := 7")];
    for kind in 0..4 {
        let mut low = limits();
        match kind { 0 => low.max_modules = 1, 1 => low.max_imports = 0, 2 => low.max_work = 0, _ => low.source.max_bytes = 1 }
        let error = check_with(&base, &files, low).unwrap_err();
        assert_eq!(error.disposition(), ("resource", false, 3));
        assert_eq!(base.logical_root(&KVMap::new()), before);
    }
    struct Cancelled;
    impl CancellationProbe for Cancelled { fn is_cancelled(&self) -> bool { true } }
    let name = n("Main");
    let modules = [SourceModuleInput { name: &name, source: b"def ignored := 1" }];
    assert!(matches!(base.check_source_modules_with_cancel(&modules, &name, &KVMap::new(), limits(), Some(&Cancelled)), Ok(Outcome::Inconclusive(_))));
    checked(&base, &files);
}

#[test]
fn admission_only_graphs_never_run_evaluations_or_accept_false_imported_proofs() {
    let base = engine();
    for body in ["#eval 7", "theorem falseProof : (0 : Nat) = 1 := by rfl"] {
        assert!(!matches!(check(&base, &[("Main", "import A"), ("A", body)]), Ok(Outcome::Complete(_))));
    }
    assert!(!base.environment().contains(&n("falseProof")));
}

#[test]
fn an_import_only_entry_uses_no_phantom_command_budget() {
    let mut exact = limits();
    exact.source.max_commands = 1;
    let result = check_with(&engine(), &[("Main", "import A"), ("A", "def value := 7")], exact)
        .unwrap().into_complete().unwrap();
    assert_eq!(result.checked.commands, 1);
    assert_eq!(result.checked.files, 2);
}

#[test]
fn extension_budgets_and_mid_replay_cancellation_retain_the_original_engine() {
    let base = engine();
    let root = base.logical_root(&KVMap::new());
    let files = [("Main", "import A"), ("A", "instance seven : Inhabited Nat := Inhabited.mk 7")];
    let mut low = limits();
    low.max_extension_bytes = 0;
    assert_eq!(check_with(&base, &files, low).unwrap_err().disposition(), ("resource", false, 3));
    struct Stop(std::sync::atomic::AtomicUsize);
    impl CancellationProbe for Stop {
        fn is_cancelled(&self) -> bool {
            self.0.fetch_add(1, std::sync::atomic::Ordering::Relaxed) >= 4
        }
    }
    let names = [n("Main"), n("A")];
    let inputs = files.iter().zip(&names).map(|((_, source), name)| SourceModuleInput {
        name, source: source.as_bytes(),
    }).collect::<Vec<_>>();
    let stop = Stop(std::sync::atomic::AtomicUsize::new(0));
    assert!(matches!(base.check_source_modules_with_cancel(&inputs, &names[0], &KVMap::new(), limits(), Some(&stop)), Ok(Outcome::Inconclusive(_))));
    assert_eq!(base.logical_root(&KVMap::new()), root);
    checked(&base, &files);
}
