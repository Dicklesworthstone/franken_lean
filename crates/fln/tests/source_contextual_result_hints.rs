//! First-order expected-type propagation preserves captured carrier parameters.
//! The pinned compiler is an oracle, never an elaboration fallback.
#![forbid(unsafe_code)]
use fln::source_check::modules::imported::SourceOleanImportLimits;
use fln::{
    Budget, Engine, EngineAdmissionLimits, KVMap, Name, OleanCheckLimits, OleanDecodeLimits,
    OleanModuleInput, SourceCheckLimits, olean_module_imports,
};
use std::{
    collections::BTreeSet,
    path::{Path, PathBuf},
    process::Command,
    sync::atomic::{AtomicUsize, Ordering},
};

const STACK: usize = 128 * 1024 * 1024;
const FIXTURE: &str = r#"
structure StatePair (A S : Type) where
  value : A
  state : S
def StateFamily (S A : Type) : Type := S -> StatePair A S
class ReadAt (S : Type) (M : Type -> Type) where
  read : M S
instance readFamily (S : Type) : ReadAt S (StateFamily S) :=
  { read := fun state => StatePair.mk state state }
def readAt (S : Type) {M : Type -> Type} [ReadAt S M] : M S := ReadAt.read
def delayedRead {S : Type} (unused : Nat) {M : Type -> Type} [ReadAt S M] : M S := ReadAt.read
"#;

fn limits() -> SourceCheckLimits {
    SourceCheckLimits::new(EngineAdmissionLimits::new(Budget::for_stack_bytes(STACK)))
}
fn seed() -> Engine {
    Engine::with_source_seed(limits().admission)
        .unwrap()
        .into_complete()
        .unwrap()
}
fn pin() -> Option<PathBuf> {
    let lock = include_str!("../../../SUITE.lock")
        .lines()
        .find(|line| line.starts_with("reference leanprover/lean4 "))
        .unwrap();
    let field = |key: &str| {
        lock.split_whitespace()
            .find_map(|word| word.strip_prefix(key))
            .unwrap()
    };
    let lib = std::env::var_os("FLN_REFERENCE_LIB")
        .map(PathBuf::from)
        .or_else(|| {
            std::env::var_os("HOME").map(|home| {
                PathBuf::from(home)
                    .join(".elan/toolchains")
                    .join(format!("leanprover--lean4---{}", field("tag=")))
                    .join("lib/lean")
            })
        })
        .filter(|lib| lib.join("Init/Prelude.olean").is_file());
    let Some(lib) = lib else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "pinned Reference required"
        );
        eprintln!("SKIP: pinned Reference absent");
        return None;
    };
    let output = Command::new(lib.parent().unwrap().parent().unwrap().join("bin/lean"))
        .arg("--version")
        .output()
        .unwrap();
    let version = String::from_utf8(output.stdout).unwrap();
    assert!(
        output.status.success()
            && version.contains(field("tag=").trim_start_matches('v'))
            && version.contains(field("commit=")),
        "{version}"
    );
    Some(lib)
}
fn reference(lib: &Path, source: &str, accepted: bool) {
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    let directory =
        std::env::temp_dir().join(format!("fln-contextual-hints-{}", std::process::id()));
    std::fs::create_dir_all(&directory).unwrap();
    let path = directory.join(format!("{}.lean", NEXT.fetch_add(1, Ordering::Relaxed)));
    std::fs::write(&path, source).unwrap();
    let output = Command::new(lib.parent().unwrap().parent().unwrap().join("bin/lean"))
        .arg(path)
        .output()
        .unwrap();
    assert_eq!(
        output.status.code(),
        Some(if accepted { 0 } else { 1 }),
        "{source}\n{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}
fn checked(base: &Engine, source: &str) {
    let options = KVMap::new();
    let before = base.logical_root(&options);
    let first = base
        .check_source_files(&[source.as_bytes()], &options, limits())
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .unwrap();
    let second = base
        .check_source_files(&[source.as_bytes()], &options, limits())
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(first.result_logical_root, second.result_logical_root);
    assert_eq!(base.logical_root(&options), before);
}

#[test]
fn captured_carrier_parameters_survive_positional_named_and_trailing_implicit_calls() {
    let lib = pin();
    let base = seed()
        .check_source_files(&[FIXTURE.as_bytes()], &KVMap::new(), limits())
        .unwrap()
        .into_complete()
        .unwrap()
        .engine;
    for body in [
        "def chosen {S : Type} : StateFamily S S := readAt S",
        "def chosen {S : Type} : StateFamily S S := readAt (S := S)",
        "def chosen {S : Type} : StateFamily S S := delayedRead 7",
        "def chosen {S : Type} : StateFamily S S := delayedRead (unused := 7)",
    ] {
        let source = format!(
            "{body}\ntheorem agrees (S : Type) : @chosen S = @readAt S (StateFamily S) (readFamily S) := rfl"
        );
        if let Some(lib) = &lib {
            reference(lib, &format!("{FIXTURE}\n{source}"), true);
        }
        checked(&base, &source);
    }
}

#[test]
fn a_written_argument_can_determine_an_applied_expected_type_hole() {
    let lib = pin();
    let source = format!(
        r#"{FIXTURE}
def consume {{S : Type}} {{M : Type -> Type}} [ReadAt S M] (action : M S) : M S := action
def chosen {{S : Type}} : StateFamily S S := consume (readAt S : StateFamily S S)
theorem agrees (S : Type) : @chosen S = @readAt S (StateFamily S) (readFamily S) := rfl
"#
    );
    if let Some(lib) = lib {
        reference(&lib, &source, true);
    }
    checked(&seed(), &source);
}

#[test]
fn hints_never_invent_missing_dictionaries_or_publish_a_bad_prefix() {
    let lib = pin();
    let base = seed()
        .check_source_files(&[FIXTURE.as_bytes()], &KVMap::new(), limits())
        .unwrap()
        .into_complete()
        .unwrap()
        .engine;
    let options = KVMap::new();
    let before = base.logical_root(&options);
    for bad in [
        "def missing {S : Type} {M : Type -> Type} : M S := readAt S",
        "def mismatch {S : Type} (action : StateFamily S Nat) : StateFamily S S := action",
        "def good {S : Type} : StateFamily S S := readAt S\ntheorem falseProof (P : Prop) : P := by rfl",
    ] {
        if let Some(lib) = &lib {
            reference(lib, &format!("{FIXTURE}\n{bad}"), false);
        }
        let error = base
            .check_source_files(&[bad.as_bytes()], &options, limits())
            .unwrap_err();
        assert!(
            matches!(error.disposition().0, "elaboration" | "kernel-rejection"),
            "{error:?}"
        );
        assert_eq!(base.logical_root(&options), before);
        assert!(
            !base
                .environment()
                .contains(&Name::from_components(["good"]))
        );
    }
    checked(
        &base,
        "def recovered {S : Type} {M : Type -> Type} [ReadAt S M] : M S := readAt S",
    );
}

fn imported_state(lib: &Path) -> Engine {
    let root = Name::from_components(["Init", "Control", "State"]);
    let mut pending = vec![root.clone()];
    let mut seen = BTreeSet::new();
    let mut names = Vec::new();
    let mut parts = Vec::new();
    while let Some(module) = pending.pop() {
        if !seen.insert(module.clone()) {
            continue;
        }
        let file = module
            .to_display_string()
            .split('.')
            .fold(lib.to_path_buf(), |p, s| p.join(s))
            .with_extension("olean");
        let exported = std::fs::read(&file).unwrap();
        pending.extend(
            olean_module_imports(&exported, OleanDecodeLimits::new(exported.len())).unwrap(),
        );
        parts.push([
            exported,
            std::fs::read(file.with_extension("olean.server")).unwrap(),
            std::fs::read(file.with_extension("olean.private")).unwrap(),
        ]);
        names.push(module);
    }
    let inputs: Vec<_> = names
        .iter()
        .zip(&parts)
        .map(|(name, [exported, server, private])| OleanModuleInput {
            name,
            artifact: exported,
            server_artifact: Some(server),
            private_artifact: Some(private),
        })
        .collect();
    Engine::builder()
        .build_empty()
        .import_olean_modules_for_source(
            &inputs,
            &[root],
            &KVMap::new(),
            SourceOleanImportLimits::new(OleanCheckLimits::new(
                256 * 1024 * 1024,
                limits().admission.kernel,
            )),
        )
        .unwrap()
        .into_complete()
        .unwrap()
        .engine
}

#[test]
fn the_real_state_transformer_stack_elaborates_without_abstracting_its_state_parameter() {
    let Some(lib) = pin() else {
        return;
    };
    std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(move || {
            let base = imported_state(&lib);
            let source = r#"
def k4 {σ : Type} : StateT σ Id σ := getThe σ
def f2 {σ δ : Type} : StateT δ (StateT σ Id) σ := getThe σ
def f3 {σ δ : Type} : StateT δ (StateT σ Id) σ := monadLift (get : StateT σ Id σ)
def named {σ : Type} : StateT σ Id σ := getThe (σ := σ)
def known {σ : Type} : MonadStateOf σ (StateT σ Id) := inferInstance
theorem same (σ : Type) : @k4 σ = @getThe σ (StateT σ Id) (known (σ := σ)) := rfl
universe u v
def genericState {σ : Type u} {m : Type u -> Type v} [Monad m] : StateT σ m σ := getThe σ
def genericLift {σ δ : Type u} {m : Type u -> Type v} [Monad m] : StateT δ (StateT σ m) σ := monadLift (get : StateT σ m σ)
"#;
            reference(
                &lib,
                &format!("prelude\nimport Init.Control.State\n{source}"),
                true,
            );
            checked(&base, source);
            let bad = "def impossible {σ : Type} {m : Type -> Type} : m σ := getThe σ";
            reference(
                &lib,
                &format!("prelude\nimport Init.Control.State\n{bad}"),
                false,
            );
            let root = base.logical_root(&KVMap::new());
            let error = base
                .check_source_files(&[bad.as_bytes()], &KVMap::new(), limits())
                .unwrap_err();
            assert_eq!(error.disposition().0, "elaboration", "{error:?}");
            assert_eq!(base.logical_root(&KVMap::new()), root);
        })
        .unwrap()
        .join()
        .unwrap();
}

/// Term elaboration runs without `quasiPatternApprox` (vendored `Lean/Elab/Config.lean`'s
/// `setElabConfig`); `apply` runs with it (`Lean/Meta/Tactic/Apply.lean:162`), and `rfl` takes
/// it only after `eq_refl` fails (`Init/Tactics.lean:427-430`, `Lean/Meta/Tactic/Rfl.lean:86`).
/// So a hole applied to a local of its own context is solved first-order in a term and by
/// `rfl` when it can be, and as a quasi-pattern under `apply` or `rfl`'s fallback; a term that
/// only the quasi-pattern solution would type is refused, by the pin and here (bead
/// fln-first-order-approximation-context-locals-6esd).
#[test]
fn only_apply_and_rfl_take_a_quasi_pattern_solution_for_a_captured_local() {
    let Some(lib) = pin() else {
        return;
    };
    std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(move || {
            let base = imported_state(&lib);
            let source = r#"
def lifted {σ δ : Type} : StateT δ (StateT σ Id) σ := do
  let s : σ ← monadLift (get : StateT σ Id σ)
  pure s
theorem keep {F : Type → Prop} {α : Type} (h : F α) : F α := h
theorem viaApply (σ : Type) : (σ × Nat) = (σ × Nat) := by
  apply keep (α := σ)
  exact rfl
theorem viaRfl (σ : Type) : Exists fun F : Type → Type => F σ = (σ × Nat) := by
  apply Exists.intro
  rfl
def pair (σ : Type) : PSigma fun F : Type → Type => F σ = (σ × σ) := by
  apply PSigma.mk
  rfl
theorem firstOrder (σ τ : Type) : (pair σ).1 τ = (σ × τ) := rfl
"#;
            reference(
                &lib,
                &format!("prelude\nimport Init.Control.State\n{source}"),
                true,
            );
            checked(&base, source);
            let keep = "theorem keep {F : Type → Prop} {α : Type} (h : F α) : F α := h\n";
            let pair = "def pair (σ : Type) : PSigma fun F : Type → Type => F σ = (σ × σ) := by\n  apply PSigma.mk\n  rfl\n";
            for bad in [
                "theorem viaExactRfl (σ : Type) : Exists fun F : Type → Type => F σ = (σ × Nat) := by\n  apply Exists.intro\n  exact rfl".to_string(),
                format!("{pair}theorem abstracted (σ τ : Type) : (pair σ).1 τ = (τ × τ) := rfl"),
                "def app {F : Type → Type} {α : Type} (x : F α) : F α := x\ndef t {σ : Type} (s : σ) : σ × Nat := app (α := σ) ((s, 0) : σ × Nat)".to_string(),
                format!("{keep}theorem viaTerm (σ : Type) : (σ × Nat) = (σ × Nat) := keep (α := σ) rfl"),
                format!("{keep}theorem viaRefine (σ : Type) : (σ × Nat) = (σ × Nat) := by\n  refine keep (α := σ) ?_\n  exact rfl"),
            ] {
                reference(
                    &lib,
                    &format!("prelude\nimport Init.Control.State\n{bad}"),
                    false,
                );
                let root = base.logical_root(&KVMap::new());
                let error = base
                    .check_source_files(&[bad.as_bytes()], &KVMap::new(), limits())
                    .unwrap_err();
                assert_eq!(error.disposition().0, "elaboration", "{bad}\n{error:?}");
                assert_eq!(base.logical_root(&KVMap::new()), root);
            }
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn exhausted_admission_can_retry_without_publishing_a_definition_prefix() {
    let base = seed()
        .check_source_files(&[FIXTURE.as_bytes()], &KVMap::new(), limits())
        .unwrap()
        .into_complete()
        .unwrap()
        .engine;
    let source = "def recovered {S : Type} : StateFamily S S := readAt S";
    let options = KVMap::new();
    let root = base.logical_root(&options);
    for allowance in [0, 1, 32] {
        let mut low = limits();
        low.admission.kernel = low.admission.kernel.narrowed(allowance, 32);
        match base.check_source_files(&[source.as_bytes()], &options, low) {
            Ok(fln::Outcome::Inconclusive(_)) => {}
            Err(error) => assert!(
                matches!(error.disposition(), ("resource" | "inconclusive", false, 3)),
                "{error:?}"
            ),
            other => panic!("expected a typed stop: {other:?}"),
        }
        assert_eq!(base.logical_root(&options), root);
        assert!(
            !base
                .environment()
                .contains(&Name::from_components(["recovered"]))
        );
    }
    checked(&base, source);
}
