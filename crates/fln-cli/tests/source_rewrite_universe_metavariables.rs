//! A definition whose universe is still being inferred (an auto-bound `α` of `Type _`, `Type u`
//! with `u` auto-bound) elaborates its body over its own universe metavariables: the pin's
//! `levelMVarToParamHeaders` (vendored `Lean/Elab/MutualDef.lean`) turns a header's universe
//! metavariables into parameters before the body only for a `theorem`. `simp` and `rw` rewrite
//! such a goal as the pin's do. Through `fln check-source` over `prelude` and
//! `Init.Data.List.Basic`. Every program is compared with the pinned `lean` v4.32.0 whenever it
//! is present.
#![forbid(unsafe_code)]

use std::path::{Path, PathBuf};
use std::process::Command;

const HEADER: &str = "prelude\nimport Init.Data.List.Basic\n";

/// Accepted at the pin and here.
const ACCEPTED: &[(&str, &str)] = &[
    // `tests/elab/4920.lean`: the anonymous constructor's proof field.
    (
        "constructor_field",
        "def Vect (n: Nat) (A: Type u) := {l: List A // l.length = n}\n\n\
         def Vect.cons (a: A) (v: Vect n A): Vect (n + 1) A :=\n  ⟨a::v.val, by simp [v.property]⟩\n",
    ),
    // `tests/elab/multiTargetCasesInductionIssue.lean`.
    (
        "explicit_universe_auto_bound_type",
        "def Vec (α : Type u) (n : Nat) : Type u := { a : List α // a.length = n }\n\
         def Vec.nil : Vec α 0 := ⟨[], rfl⟩\n\
         def Vec.cons (a : α) (as : Vec α n) : Vec α (n+1) := ⟨a :: as.val, by simp [as.property]⟩\n",
    ),
    (
        "definition_statement",
        "def three (a : α) (xs : List α) (h : xs.length = 2) : (a :: xs).length = 3 := by simp [h]\n",
    ),
    (
        "rewrite",
        "def keep (xs : List α) : (xs ++ []).length = xs.length := by rw [List.append_nil]\n",
    ),
];

/// Rejected at the pin and here: rewritten, then left unsolved.
const REJECTED: &[(&str, &str)] = &[(
    "unsolved",
    "def none (a : α) (xs : List α) : (a :: xs).length = 0 := by simp\n",
)];

fn pinned_lib() -> Option<PathBuf> {
    let lib = std::env::var_os("FLN_REFERENCE_LIB")
        .map(PathBuf::from)
        .or_else(|| {
            std::env::var_os("HOME").map(|home| {
                PathBuf::from(home)
                    .join(".elan/toolchains")
                    .join(format!("leanprover--lean4---{}", fln::OLEAN_PIN_TAG))
                    .join("lib/lean")
            })
        })
        .filter(|lib| lib.join("Init/Data/List/Basic.olean").is_file());
    assert!(
        lib.is_some() || std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
        "the pinned Reference library is required"
    );
    if lib.is_none() {
        eprintln!("SKIP: pinned Reference lib/lean absent");
    }
    lib
}

fn workspace() -> PathBuf {
    let path = std::env::temp_dir().join(format!(
        "fln-rewrite-universes-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos(),
    ));
    std::fs::create_dir(&path).unwrap();
    path
}

/// `fln check-source` on `HEADER` + `program`, and the pinned binary's exit code when present.
fn check(lib: &Path, root: &Path, name: &str, program: &str) -> (i32, String, Option<i32>) {
    let entry = root.join(format!("{name}.lean"));
    std::fs::write(&entry, format!("{HEADER}{program}")).unwrap();
    let theirs = lib
        .parent()
        .and_then(Path::parent)
        .map(|toolchain| toolchain.join("bin/lean"))
        .filter(|lean| lean.is_file())
        .map(|pinned| {
            Command::new(pinned)
                .arg(&entry)
                .env("LEAN_PATH", lib)
                .output()
                .expect("run the pinned lean")
                .status
                .code()
                .expect("normal pinned exit")
        });
    let ours = Command::new(env!("CARGO_BIN_EXE_fln"))
        .arg("check-source")
        .arg(&entry)
        .env("LEAN_PATH", lib)
        .env("FLN_IMPORT_REUSE_DIR", root.join("records"))
        .output()
        .expect("run the installed CLI");
    (
        ours.status.code().expect("normal process exit"),
        String::from_utf8_lossy(&ours.stderr).into_owned(),
        theirs,
    )
}

#[test]
fn a_definition_body_rewrites_over_its_own_universe_metavariables() {
    let Some(lib) = pinned_lib() else {
        return;
    };
    // One workspace, so the import closure is admitted once for every program.
    let root = workspace();
    for (name, program) in ACCEPTED {
        let (code, stderr, pinned) = check(&lib, &root, name, program);
        assert_eq!(code, 0, "{name}: {program}\n{stderr}");
        assert_eq!(pinned.unwrap_or(0), 0, "{name}: the pinned lean rejects it");
    }
    for (name, program) in REJECTED {
        let (code, stderr, pinned) = check(&lib, &root, name, program);
        assert_ne!(code, 0, "{name}: accepted {program}");
        assert!(
            !stderr.contains("unexpected syntax") && !stderr.contains("made no progress"),
            "{name}: refused or unrewritten, not rejected\n{stderr}"
        );
        assert_ne!(pinned.unwrap_or(1), 0, "{name}: the pinned lean accepts it");
    }
}
