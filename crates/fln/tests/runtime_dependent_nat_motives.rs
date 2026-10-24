//! Nat recursors whose motive depends on the index lower to native code when
//! every value the motive types has one runtime layout (bead
//! `fln-dependent-nat-recursor-motive-kz3j`). Matching a `Vec α (n+1)` index
//! used to stop at code generation: elaboration reduces `n + 1` by plain delta,
//! leaving `Nat.add`'s course-of-values scaffold `(Nat.rec … t).1` behind, and
//! that pair's history component is a type computed from the index. It is
//! refolded to the `Nat.brecOn` it unfolds, whose fold keeps only the observed
//! values. A motive with a different layout at each index remains a typed
//! refusal. Every program is first run through the pinned Reference, whose
//! `#eval` output the native results must equal.
#![forbid(unsafe_code)]

use fln::source_check::modules::imported::SourceOleanImportLimits;
use fln::{
    Budget, ClosedVmValue, Engine, EngineExecutionError, EngineExecutionLimits, Environment,
    IngressError, KVMap, Name, OleanCheckLimits, OleanModuleInput,
};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::OnceLock;

const STACK: usize = 256 * 1024 * 1024;

const VEC: &str = "inductive Vec (α : Type) : Nat → Type
| nil  : Vec α 0
| cons : α → {n : Nat} → Vec α n → Vec α (n+1)
open Vec
";

fn library() -> Option<PathBuf> {
    let lib = std::env::var_os("FLN_REFERENCE_LIB")
        .map(PathBuf::from)
        .or_else(|| {
            std::env::var_os("HOME").map(|home| {
                PathBuf::from(home).join(".elan/toolchains/leanprover--lean4---v4.32.0/lib/lean")
            })
        })
        .filter(|path| path.join("Init/Prelude.olean").is_file());
    if lib.is_none() {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "FLN_REQUIRE_REFERENCE is set but the pinned Reference is absent"
        );
        eprintln!("SKIP: dependent Nat motive programs require the pinned Reference");
    }
    lib
}

/// The pinned `lean` (implicit `import Init`) accepts the program, and its
/// numeric `#eval` lines are exactly `expected`.
fn reference(lib: &Path, source: &str, expected: &[u64]) {
    static VERIFIED: OnceLock<PathBuf> = OnceLock::new();
    let binary = VERIFIED.get_or_init(|| {
        let pin = include_str!("../../../SUITE.lock")
            .lines()
            .find(|line| line.starts_with("reference leanprover/lean4 "))
            .unwrap();
        let field = |key: &str| {
            pin.split_whitespace()
                .find_map(|word| word.strip_prefix(key))
                .unwrap()
        };
        let binary = lib.parent().unwrap().parent().unwrap().join("bin/lean");
        let result = Command::new(&binary).arg("--version").output().unwrap();
        let version = String::from_utf8(result.stdout).unwrap();
        assert!(
            result.status.success()
                && version.contains(field("tag=").trim_start_matches('v'))
                && version.contains(field("commit=")),
            "{version}"
        );
        binary
    });
    let root = std::env::temp_dir().join(format!(
        "fln-dependent-nat-motive-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos()
    ));
    std::fs::create_dir(&root).unwrap();
    let path = root.join("case.lean");
    std::fs::write(&path, source).unwrap();
    let result = Command::new(binary).arg(&path).output().unwrap();
    let stdout = String::from_utf8(result.stdout).unwrap();
    assert_eq!(
        result.status.code(),
        Some(0),
        "{source}\n{stdout}{}",
        String::from_utf8_lossy(&result.stderr)
    );
    let values: Vec<u64> = stdout
        .lines()
        .filter_map(|line| line.trim().parse().ok())
        .collect();
    assert_eq!(values, expected, "{source}\n{stdout}");
}

/// Run `check` against an engine holding the pinned `Init.Prelude`, admitted
/// from its `.olean` artifacts by both checkers.
fn with_prelude(check: impl FnOnce(&Engine, &Path) + Send + 'static) {
    let Some(lib) = library() else {
        return;
    };
    std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(move || {
            let path = lib.join("Init/Prelude.olean");
            let parts = [
                std::fs::read(&path).unwrap(),
                std::fs::read(path.with_extension("olean.server")).unwrap(),
                std::fs::read(path.with_extension("olean.private")).unwrap(),
            ];
            let name = Name::from_components(["Init", "Prelude"]);
            let inputs = [OleanModuleInput {
                name: &name,
                artifact: &parts[0],
                server_artifact: Some(&parts[1]),
                private_artifact: Some(&parts[2]),
            }];
            let imported = Engine::from_environment(Environment::new())
                .import_olean_modules_for_source(
                    &inputs,
                    std::slice::from_ref(&name),
                    &KVMap::new(),
                    SourceOleanImportLimits::new(OleanCheckLimits::new(
                        256 * 1024 * 1024,
                        Budget::for_stack_bytes(STACK),
                    )),
                )
                .unwrap()
                .into_complete()
                .unwrap();
            check(&imported.engine, &lib);
        })
        .unwrap()
        .join()
        .unwrap();
}

/// Every `#eval` result, in order. A refusal publishes nothing.
fn execute(engine: &Engine, source: &str) -> Result<Vec<ClosedVmValue>, EngineExecutionError> {
    let options = KVMap::new();
    let root = engine.logical_root(&options);
    let result = engine.execute_source_commands_with_checks(
        source.as_bytes(),
        &options,
        EngineExecutionLimits::new(Budget::for_stack_bytes(STACK)),
    );
    assert_eq!(root, engine.logical_root(&options), "{source}");
    let run = result?
        .into_complete()
        .unwrap_or_else(|outcome| panic!("{source}\n{outcome:?}"));
    Ok(run
        .batch
        .source_evaluation_indices
        .iter()
        .map(|index| {
            fln::closed_vm_value(&run.batch.executions[*index].exit)
                .unwrap()
                .unwrap_or_else(|| panic!("{source}: unclosed result"))
        })
        .collect())
}

/// The pin's output first, then the same values from the native VM.
fn agree(cases: &'static [(&'static str, &'static [u64])]) {
    with_prelude(move |engine, lib| {
        for (source, expected) in cases {
            let source = source.replace("{VEC}", VEC);
            reference(lib, &source, expected);
            let values =
                execute(engine, &source).unwrap_or_else(|error| panic!("{source}\n{error:?}"));
            let expected: Vec<ClosedVmValue> = expected
                .iter()
                .map(|value| ClosedVmValue::Scalar(usize::try_from(*value).unwrap()))
                .collect();
            assert_eq!(values, expected, "{source}");
        }
    });
}

#[test]
fn successor_index_patterns_execute_through_the_refolded_history() {
    agree(&[
        (
            "{VEC}def h1 : Vec Nat (n+1) → Nat
| cons b bv => b
#eval h1 (cons 7 nil)
#eval h1 (cons 3 (cons 4 nil))",
            &[7, 3],
        ),
        (
            "{VEC}def second : Vec Nat (n+2) → Nat
| cons _ (cons b _) => b
#eval second (cons 1 (cons 2 nil))
#eval second (cons 5 (cons 6 (cons 7 nil)))
def tail : Vec Nat (n+1) → Vec Nat n
| cons _ v => v
def len : Vec Nat n → Nat
| nil => 0
| cons _ v => len v + 1
#eval len (tail (cons 1 (cons 2 (cons 3 nil))))",
            &[2, 6, 2],
        ),
        (
            "{VEC}def h2 : (n : Nat) → Vec Nat n → Nat
| _, nil => 0
| _, cons b _ => b
#eval h2 0 nil
#eval h2 1 (cons 5 nil)
#eval h2 2 (cons 9 (cons 4 nil))",
            &[0, 5, 9],
        ),
    ]);
}

/// From `tests/elab/matchSparse2.lean`: two majors over one successor index.
#[test]
fn sparse_matches_over_a_shared_successor_index_execute() {
    agree(&[(
        "inductive Finn : Nat → Type where
  | fzero : {n : Nat} → Finn n
  | fsucc : {n : Nat} → Finn n → Finn (n+1)
open Finn
def Finn.min (x : Bool) {n : Nat} (m : Nat) : Finn n → (f : Finn n) → Unit
  | fzero, _ => ()
  | _, fzero => ()
  | fsucc i, fsucc j => ()
def Finn.code : Finn n → Finn n → Nat
  | fzero, _ => 1
  | _, fzero => 2
  | fsucc _, fsucc _ => 3
#eval Finn.code (n := 2) (fsucc fzero) (fsucc fzero)
#eval Finn.code (n := 2) (fsucc fzero) fzero
#eval Finn.code (n := 2) fzero (fsucc fzero)",
        &[3, 2, 1],
    )]);
}

/// Value parameters and indices erase, so these motives have one layout at
/// every index: written with `Nat.rec`/`Nat.casesOn` directly, by a match whose
/// result type depends on the index, or returning a function whose domain or
/// codomain depends on it.
#[test]
fn index_dependent_motives_with_one_runtime_layout_execute() {
    agree(&[
        (
            "def f : (n : Nat) → Fin (n+1)
| 0 => ⟨0, Nat.zero_lt_succ _⟩
| n+1 => ⟨n+1, Nat.lt_succ_self _⟩
#eval (f 0).val
#eval (f 5).val",
            &[0, 5],
        ),
        (
            "def g (n : Nat) : Fin (n+1) :=
  Nat.rec (motive := fun k => Fin (k+1)) ⟨0, Nat.zero_lt_succ _⟩ (fun k _ => ⟨k+1, Nat.lt_succ_self _⟩) n
#eval (g 0).val
#eval (g 4).val
def cs (n : Nat) : Fin (n+2) :=
  Nat.casesOn (motive := fun k => Fin (k+2)) n ⟨1, Nat.succ_le_succ (Nat.zero_lt_succ _)⟩
    (fun k => ⟨k+2, Nat.lt_succ_self _⟩)
#eval (cs 0).val
#eval (cs 3).val",
            &[0, 4, 1, 4],
        ),
        (
            "def tup (n : Nat) : Nat → Fin (n+1) :=
  Nat.rec (motive := fun k => Nat → Fin (k+1)) (fun _ => ⟨0, Nat.zero_lt_succ _⟩)
    (fun k ih m => if m = 0 then ⟨k+1, Nat.lt_succ_self _⟩
      else ⟨(ih (m - 1)).val, Nat.le_succ_of_le (ih (m - 1)).isLt⟩) n
#eval (tup 3 0).val
#eval (tup 3 1).val
#eval (tup 3 5).val
def dom (n : Nat) : Fin (n+1) → Nat :=
  Nat.rec (motive := fun k => Fin (k+1) → Nat) (fun i => i.val)
    (fun _ ih i => i.val + ih ⟨0, Nat.zero_lt_succ _⟩) n
#eval dom 3 ⟨2, Nat.le_of_ble_eq_true rfl⟩
#eval dom 0 ⟨0, Nat.zero_lt_succ _⟩",
            &[3, 2, 0, 2, 0],
        ),
    ]);
}

/// `Tower n` is `Nat` at zero and a function at every successor: no single
/// layout serves the recursor's results. The pin compiles it with uniformly
/// boxed objects and prints 7; this compiler has no such carrier for a motive
/// and refuses, typed, without publishing anything.
#[test]
fn a_motive_with_a_different_layout_per_index_stays_a_typed_refusal() {
    with_prelude(|engine, lib| {
        let source = "def Tower : Nat → Type
  | 0 => Nat
  | n+1 => Nat → Tower n
def build (n : Nat) : Tower n :=
  Nat.rec (motive := Tower) (7 : Nat) (fun _ ih => fun _ => ih) n
#eval (build 2 : Nat → Nat → Nat) 0 0";
        reference(lib, source, &[7]);
        let error = execute(engine, source).unwrap_err();
        assert!(
            matches!(
                &error,
                EngineExecutionError::BatchCommand { index: 1, error, .. }
                    if matches!(
                        **error,
                        EngineExecutionError::Ingress(IngressError::UnsupportedNode {
                            kind: "dependent Nat recursor motive"
                        })
                    )
            ),
            "{error:?}"
        );
    });
}
