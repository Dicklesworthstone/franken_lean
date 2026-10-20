//! Ordinary mutual blocks must publish a complete, dependency-ordered safe batch.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, SourceCheckLimits};

fn engine() -> (Engine, EngineAdmissionLimits) {
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    (
        Engine::with_source_seed(limits)
            .unwrap()
            .into_complete()
            .unwrap(),
        limits,
    )
}
fn check(source: &str) -> Engine {
    oracle(source, true);
    let (engine, limits) = engine();
    engine
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits),
        )
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .expect("both checkers complete")
        .engine
}
#[test]
fn forward_definitions_reduce_after_dependency_ordered_admission() {
    check(
        "mutual\n def first : Nat := second + 1\n def second : Nat := 41\nend\nexample : first = 42 := rfl\n",
    );
}
#[test]
fn forward_theorems_remain_theorems_and_need_no_placeholder_axioms() {
    check(
        "mutual\n theorem first : True := second\n theorem second : True := True.intro\nend\nexample : True := first\n",
    );
}
#[test]
fn definitions_and_abbreviations_preserve_their_written_kind() {
    check(
        "mutual\n def first : Nat := second\n abbrev second : Nat := 41\nend\nexample : first = 41 := rfl\n",
    );
}

fn name(text: &str) -> fln_core::name::Name {
    fln_core::name::Name::from_components(text.split('.'))
}
fn run(base: &Engine, query: &str, expected: &str) {
    let answer = base
        .execute_source_definitions(
            &[query.as_bytes()],
            &KVMap::new(),
            fln::EngineExecutionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024)),
        )
        .unwrap_or_else(|error| panic!("{query}: {error:?}"))
        .into_complete()
        .expect("runtime completed");
    let [execution] = answer.executions.as_slice() else {
        panic!("one execution");
    };
    let fln::VmExit::Returned(value) = &execution.exit else {
        panic!("{execution:?}");
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
        Some(expected)
    );
}
#[test]
fn checked_safe_members_execute_without_unsafe_companions() {
    use fln_env::constants::{ConstantInfo, DefinitionSafety, ReducibilityHints};
    let base = check(
        "mutual\n def first (n : Nat) : Nat := second n + 1\n abbrev second (n : Nat) : Nat := n + 40\nend\n",
    );
    run(&base, "#eval first 1", "42");
    for label in ["first", "second"] {
        let Some(ConstantInfo::Defn(definition)) = base.environment().find(&name(label)) else {
            panic!("safe def");
        };
        assert_eq!(definition.safety, DefinitionSafety::Safe);
        assert!(
            !base
                .environment()
                .contains(&name(&format!("{label}._unsafe_rec")))
        );
        if label == "second" {
            assert_eq!(definition.hints, ReducibilityHints::Abbrev);
        }
    }
    let proofs = check(
        "mutual\n theorem first : True := second\n theorem second : True := True.intro\nend\n",
    );
    for label in ["first", "second"] {
        assert!(matches!(
            proofs.environment().find(&name(label)),
            Some(ConstantInfo::Thm(_))
        ));
    }
}
#[test]
fn shared_section_captures_include_peer_only_dependencies() {
    let base = check(
        "section\nvariable (unused : String) (left right : Nat)\nmutual\n def first (n : Nat) : Nat := second n + left\n def second (n : Nat) : Nat := n + right\n def independent (n : Nat) : Nat := n\nend\nend\n",
    );
    run(&base, "#eval first 7 13 5", "25");
    run(&base, "#eval second 7 13 5", "18");
    run(&base, "#eval independent 7 13 5", "5");
}
#[test]
fn namespace_and_shadowed_parameters_do_not_create_false_cycles() {
    let base = check(
        "namespace N\nmutual\n def first (second : Nat) : Nat := second\n def second : Nat := first 42\nend\nend N\nexample : N.second = 42 := rfl\n",
    );
    run(&base, "#eval N.second", "42");
}
#[test]
fn polymorphic_forward_references_close_their_universe_parameters() {
    let base = check(
        "mutual\n def first.{u} (A : Type u) (a : A) : A := second A a\n def second.{u} (A : Type u) (a : A) : A := a\nend\nexample : first Nat 42 = 42 := rfl\n",
    );
    run(&base, "#eval first Nat 42", "42");
}
#[test]
fn every_cycle_is_refused_before_any_declaration_can_be_published() {
    for source in [
        "mutual\n def first : Nat := second\n def second : Nat := first\nend",
        "mutual\n theorem first : False := second\n theorem second : False := first\nend",
        "mutual\n def independent : Nat := 0\n def first (n : Nat) : Nat := second n\n def second (n : Nat) : Nat := first n\nend",
        "mutual\n def first (n : Nat) : Nat := first n\nend",
    ] {
        oracle(source, false);
        let (base, limits) = engine();
        let before = base.logical_root(&KVMap::new());
        let members = fln_parse::command_scope::mutual::parse(source.as_bytes())
            .unwrap()
            .unwrap();
        let result = fln_elab::source::partial::elaborate_ordinary_group(
            &members,
            base.environment(),
            limits.kernel,
            &fln_elab::source::scope::SourceScope::default(),
        );
        assert!(
            matches!(
                result,
                Err(fln_elab::NatDefinitionElabError::UnexpectedSyntax {
                    expected: "recursive ordinary mutual component requires termination elaboration"
                })
            ),
            "{source}"
        );
        assert_eq!(base.logical_root(&KVMap::new()), before);
        assert!(!base.environment().contains(&name("independent")));
    }
}
#[test]
fn header_dependencies_are_not_made_valid_by_sequentializing_the_group() {
    let (base, limits) = engine();
    let source = "mutual\n def carrier : Type := Nat\n def value : carrier := 41\nend";
    oracle(source, false);
    let members = fln_parse::command_scope::mutual::parse(source.as_bytes())
        .unwrap()
        .unwrap();
    let result = fln_elab::source::partial::elaborate_ordinary_group(
        &members,
        base.environment(),
        limits.kernel,
        &fln_elab::source::scope::SourceScope::default(),
    );
    assert!(matches!(
        result,
        Err(fln_elab::NatDefinitionElabError::Inference(
            fln_elab::source::SourceInferenceError::UnknownConstant(_)
        ))
    ));
    assert!(!base.environment().contains(&name("carrier")));
}

#[test]
fn a_safe_mutual_body_cannot_acquire_unsafe_dependencies() {
    let (base, limits) = engine();
    let source = "unsafe def dangerous : Nat := 42\nmutual\n def first : Nat := second\n def second : Nat := dangerous\nend\n";
    oracle(source, false);
    let result = base.check_source_files(
        &[source.as_bytes()],
        &KVMap::new(),
        SourceCheckLimits::new(limits),
    );
    assert!(
        result.is_err(),
        "unsafe dependency reached a safe declaration"
    );
    eprintln!("unsafe dependency: {:?}", result.err());
    assert!(!base.environment().contains(&name("first")));
}
#[test]
fn unhandled_modifiers_and_modern_visibility_are_not_silently_dropped() {
    let (base, limits) = engine();
    for source in [
        "mutual\n @[simp] theorem first : True := True.intro\nend",
        "mutual\n private def first : Nat := 42\nend",
        "mutual\n noncomputable def first : Nat := 42\nend",
    ] {
        let members = fln_parse::command_scope::mutual::parse(source.as_bytes())
            .unwrap()
            .unwrap();
        assert!(matches!(
            fln_elab::source::partial::elaborate_ordinary_group(
                &members,
                base.environment(),
                limits.kernel,
                &fln_elab::source::scope::SourceScope::default()
            ),
            Err(fln_elab::NatDefinitionElabError::UnexpectedSyntax { .. })
        ));
    }
    let members = fln_parse::command_scope::mutual::parse(b"mutual def first : Nat := 42 end")
        .unwrap()
        .unwrap();
    let scope = fln_elab::source::scope::SourceScope {
        private_module: Some(name("Hidden")),
        ..Default::default()
    };
    assert!(matches!(
        fln_elab::source::partial::elaborate_ordinary_group(
            &members,
            base.environment(),
            limits.kernel,
            &scope
        ),
        Err(fln_elab::NatDefinitionElabError::UnexpectedSyntax {
            expected: "ordinary mutual group outside module visibility projection"
        })
    ));
}
#[test]
fn duplicate_names_and_invalid_late_bodies_leave_the_predecessor_unchanged() {
    let (base, limits) = engine();
    let root = base.logical_root(&KVMap::new());
    for source in [
        "mutual\n def first : Nat := 0\n def first : Nat := 1\nend",
        "mutual\n theorem first : True := True.intro\n theorem second : False := True.intro\nend",
    ] {
        let members = fln_parse::command_scope::mutual::parse(source.as_bytes())
            .unwrap()
            .unwrap();
        let result = fln_elab::source::partial::elaborate_ordinary_group(
            &members,
            base.environment(),
            limits.kernel,
            &fln_elab::source::scope::SourceScope::default(),
        );
        assert!(result.is_err());
        assert_eq!(base.logical_root(&KVMap::new()), root);
        assert!(!base.environment().contains(&name("first")));
    }
}

fn oracle(source: &str, expected: bool) {
    use std::{
        path::PathBuf,
        process::Command,
        sync::{
            OnceLock,
            atomic::{AtomicUsize, Ordering},
        },
    };
    static REFERENCE: OnceLock<Option<PathBuf>> = OnceLock::new();
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    let reference = REFERENCE.get_or_init(|| {
        let pin = include_str!("../../../SUITE.lock")
            .lines()
            .find(|line| line.starts_with("reference leanprover/lean4 "))
            .unwrap();
        let field = |key: &str| {
            pin.split_whitespace()
                .find_map(|word| word.strip_prefix(key))
                .unwrap()
        };
        let tag = field("tag=");
        let commit = field("commit=");
        let lib = std::env::var_os("FLN_REFERENCE_LIB")
            .map(PathBuf::from)
            .or_else(|| {
                std::env::var_os("HOME").map(|home| {
                    PathBuf::from(home)
                        .join(".elan/toolchains")
                        .join(format!("leanprover--lean4---{tag}"))
                        .join("lib/lean")
                })
            });
        let executable = lib
            .and_then(|lib| lib.parent()?.parent().map(|p| p.join("bin/lean")))
            .filter(|path| path.is_file());
        let Some(executable) = executable else {
            assert!(
                std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
                "pinned Reference required"
            );
            eprintln!("SKIP: mutual differential requires the pinned compiler");
            return None;
        };
        let version = Command::new(&executable).arg("--version").output().unwrap();
        let text = String::from_utf8(version.stdout).unwrap();
        assert!(
            version.status.success()
                && text.contains(tag.trim_start_matches('v'))
                && text.contains(commit),
            "{text}"
        );
        Some(executable)
    });
    let Some(reference) = reference else {
        return;
    };
    let dir = std::env::temp_dir().join(format!("fln-ordinary-mutual-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join(format!("{}.lean", NEXT.fetch_add(1, Ordering::Relaxed)));
    std::fs::write(&path, source).unwrap();
    let output = Command::new(reference).arg(path).output().unwrap();
    assert_eq!(
        output.status.code(),
        Some(if expected { 0 } else { 1 }),
        "Reference mismatch: {source}\n{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn written_universe_lists_must_agree_before_body_elaboration() {
    let (base, limits) = engine();
    for source in [
        "mutual\n def first.{u} (A : Type u) (a : A) : A := second A a\n def second.{v} (A : Type v) (a : A) : A := a\nend",
        "mutual\n def first.{u,v} : Nat := 0\n def second.{v,u} : Nat := 1\nend",
        "mutual\n def first.{u} : Nat := 0\n def second : Nat := 1\nend",
    ] {
        oracle(source, false);
        let members = fln_parse::command_scope::mutual::parse(source.as_bytes())
            .unwrap()
            .unwrap();
        assert!(matches!(
            fln_elab::source::partial::elaborate_ordinary_group(
                &members,
                base.environment(),
                limits.kernel,
                &fln_elab::source::scope::SourceScope::default()
            ),
            Err(fln_elab::NatDefinitionElabError::UnexpectedSyntax {
                expected: "ordinary mutual universe parameters mismatch"
            })
        ));
    }
}
