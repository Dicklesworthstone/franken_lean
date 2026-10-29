//! The pin's default `Nat` simplification procedures (vendored
//! `Lean/Meta/Tactic/Simp/BuiltinSimprocs/Nat.lean`) through the installed drop-in `lean`, over
//! `prelude` with `Init.Data.Nat.Simproc` and `Init.Guard`: numerals are folded (`Nat.reduceAdd`,
//! `reduceMul`, `reduceSub`, `reduceDiv`, `reduceMod`, `reducePow`), comparisons of numerals are
//! decided (`reduceLT`, `reduceEqDiff`), and offsets are cancelled (`reduceEqDiff`,
//! `reduceLeDiff`, `reduceSubDiff`), in a goal and at a hypothesis; `dsimp` folds numerals too.
//! `simp only` and `dsimp only` run only the procedures they name, and `-` erases one.
//!
//! Every program was run through the pinned `lean` v4.32.0 with the same header first
//! (2026-10-29), and the pin is consulted again when it is present.
#![forbid(unsafe_code)]
use std::path::{Path, PathBuf};
use std::process::Command;

const HEADER: &str = "prelude\nimport Init.Data.Nat.Simproc\nimport Init.Guard\n";

/// Programs the pin accepts, printing nothing. The `guard_target`/`guard_hyp` lines check the
/// pin's normal form up to syntactic equality.
const ACCEPTED: &[&str] = &[
    "example (h : 0 + 1 + 1 = 3) : False := by simp at h\n",
    "example (h : 2 = 3) : False := by simp at h\n",
    "example : 2 + 3 = 5 := by simp\n",
    "example : (10 : Nat) - 3 * 2 = 4 := by simp\n",
    "example : (7 : Nat) / 2 % 2 = 1 := by simp\n",
    "example : 2 ^ 10 = 1024 := by simp\n",
    "example (h : 5 < 3) : False := by simp at h\n",
    "example (x : Nat) (h : x + 2 = 5) : x = 3 := by\n  simp at h\n  exact h\n",
    "example (x : Nat) (h : x + 5 ≤ 3) : False := by simp at h\n",
    "example (x : Nat) : x + 5 - 3 = x + 2 := by simp\n",
    "example (x : Nat) : x + 2 * 3 = 6 + x := by\n  simp only [Nat.reduceMul]\n  \
     guard_target =ₛ x + 6 = 6 + x\n  exact Nat.add_comm x 6\n",
    "example (h : 1 + 1 = 3) : False := by\n  simp only [Nat.reduceAdd] at h\n  \
     guard_hyp h :ₛ 2 = 3\n  exact absurd h (by decide)\n",
    "example : 2 + 3 = 5 := by simp [-Nat.reduceAdd]\n",
    "example (h : 2 * 3 = 7) : False := by simp at h\n",
    "example (x : Nat) (h : x = 2 + 3) : x = 5 := by\n  dsimp at h\n  \
     guard_hyp h :ₛ x = 5\n  exact h\n",
    "example (x : Nat) (h : x = 2 + 3) : x = 5 := by\n  dsimp only [Nat.reduceAdd] at h\n  \
     guard_hyp h :ₛ x = 5\n  exact h\n",
];

/// Programs the pin rejects: a false equation `simp` reduces to `False`; `simp only []`, which
/// runs no procedure, on a goal only a procedure would change; the last `simp` hypothesis above
/// with `Nat.reduceMul` erased, which leaves `simp` nothing to do; and `dsimp only`, which also
/// runs no procedure.
const REFUSED: &[&str] = &[
    "example : 2 + 2 = 5 := by simp\n",
    "example (x : Nat) : x + 2 * 3 = 6 + x := by\n  simp only []\n",
    "example (h : 2 * 3 = 7) : False := by simp [-Nat.reduceMul] at h\n",
    "example (x : Nat) (h : x = 2 + 3) : x = 5 := by\n  dsimp only at h\n  exact h\n",
];

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
        .filter(|lib| lib.join("Init/Core.olean").is_file());
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
        "fln-simp-nat-procedures-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos(),
    ));
    std::fs::create_dir(&path).unwrap();
    path
}

/// The pinned `lean`'s exit code and stdout on `entry`, when the binary is present.
fn pinned(lib: &Path, entry: &Path) -> Option<(i32, String)> {
    let lean = lib.parent()?.parent()?.join("bin/lean");
    if !lean.is_file() {
        return None;
    }
    let output = Command::new(lean)
        .arg(entry)
        .env("LEAN_PATH", lib)
        .output()
        .expect("run the pinned lean");
    Some((
        output.status.code().expect("normal pinned exit"),
        String::from_utf8(output.stdout).unwrap(),
    ))
}

/// The installed `lean` on `entry`: its exit code, stdout and stderr.
fn ours(lib: &Path, root: &Path, entry: &Path) -> (i32, String, String) {
    let output = Command::new(env!("CARGO_BIN_EXE_lean"))
        .arg(entry)
        .env("LEAN_PATH", lib)
        .env("FLN_IMPORT_REUSE_DIR", root.join("records"))
        .output()
        .expect("run lean");
    (
        output.status.code().expect("normal exit"),
        String::from_utf8(output.stdout).unwrap(),
        String::from_utf8(output.stderr).unwrap(),
    )
}

#[test]
fn nat_procedures_fold_decide_and_cancel_as_at_the_pin() {
    let Some(lib) = pinned_lib() else {
        return;
    };
    let root = workspace();
    for (index, program) in ACCEPTED.iter().enumerate() {
        let entry = root.join(format!("Accepted{index}.lean"));
        std::fs::write(&entry, format!("{HEADER}{program}")).unwrap();
        if let Some((code, stdout)) = pinned(&lib, &entry) {
            assert_eq!((code, stdout.as_str()), (0, ""), "the pin moved: {program}");
        }
        let (code, stdout, stderr) = ours(&lib, &root, &entry);
        assert_eq!((code, stdout.as_str()), (0, ""), "{program}: {stderr}");
    }
    for (index, program) in REFUSED.iter().enumerate() {
        let entry = root.join(format!("Refused{index}.lean"));
        std::fs::write(&entry, format!("{HEADER}{program}")).unwrap();
        if let Some((code, _)) = pinned(&lib, &entry) {
            assert_eq!(code, 1, "the pin rejects {program}");
        }
        let (code, stdout, stderr) = ours(&lib, &root, &entry);
        assert_ne!(code, 0, "{program}: {stdout}");
        assert!(stderr.contains("refused"), "{program}: {stderr}");
    }
}
