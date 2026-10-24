//! Where `simp` and `simp_all` leave the hypotheses they rewrite, through the installed drop-in
//! `lean`, over `prelude` + `import Init.SimpLemmas`. The pin's `simpGoal` (vendored
//! `Lean/Meta/Tactic/Simp/Main.lean:874-911`) asserts a located hypothesis whose simplification
//! needs a proof after every local, in located order, and changes one simplified only
//! definitionally (rfl-tagged theorems, unfolding) in place. `SimpAll.main` (vendored
//! `Simp/SimpAll.lean:125-147`) re-asserts the first hypothesis it changed and every hypothesis
//! after it, at the end of the context in their order, and clears one left as `True`.
//!
//! The program was run through the pinned `lean` v4.32.0 with the same header first (2026-10-22),
//! and its output is compared with the pinned binary's again when that is present.
#![forbid(unsafe_code)]
use std::path::{Path, PathBuf};
use std::process::Command;

const PROGRAM: &str = r#"prelude
import Init.SimpLemmas
example (a b : Nat) (h₁ : True ∧ a = 1) (q : Prop) (h₂ : True ∧ b = 2) (r : Prop) : r := by
  simp at h₂ h₁
  trace_state
  sorry
example (a b : Nat) (h₁ : a + 0 = 1) (q : Prop) (h₂ : b + 0 = 2) (r : Prop) : r := by
  simp at h₂ h₁
  trace_state
  sorry
example (a : Nat) (h₁ : True ∧ a + 0 = 1) (q : Prop) : q := by
  simp only [Nat.add_zero] at h₁
  trace_state
  simp only [true_and] at h₁
  trace_state
  sorry
example (a b : Nat) (h : a = b) (h₁ : a + 1 = 3) (q : Prop) : q := by
  simp [h] at h₁
  trace_state
  sorry
example (a b : Nat) (h₁ : a + 0 = 1) (q : Prop) (h₂ : True ∧ b = 2) (p : Prop) (hp : p) (r : Prop) : r := by
  simp at *
  trace_state
  sorry
example (a b : Nat) (h₀ : a = a) (h₁ : a + 0 = 1) (q : Prop) (h₂ : b = 2) (r : Prop) : r := by
  simp_all
  trace_state
  sorry
example (a b : Nat) (h₁ : a + 0 = 1) (q : Prop) (h₂ : True ∧ b = 2) (h₃ : b = 2) (r : Prop) : r := by
  simp_all
  trace_state
  sorry
"#;

/// The pin's output for [`PROGRAM`]. `true_and` and a local equation are proofs, so `h₁` moves
/// to the end; `Nat.add_zero` is rfl-tagged, so `h₁ : a + 0 = 1` becomes `a = 1` in place.
const EXPECTED: &str = "a b : Nat
q r : Prop
h₂ : b = 2
h₁ : a = 1
⊢ r
Placement.lean:3:0: warning: declaration uses `sorry`
a b : Nat
h₁ : a = 1
q : Prop
h₂ : b = 2
r : Prop
⊢ r
Placement.lean:7:0: warning: declaration uses `sorry`
a : Nat
h₁ : True ∧ a = 1
q : Prop
⊢ q
a : Nat
q : Prop
h₁ : a = 1
⊢ q
Placement.lean:11:0: warning: declaration uses `sorry`
a b : Nat
h : a = b
q : Prop
h₁ : b + 1 = 3
⊢ q
Placement.lean:17:0: warning: declaration uses `sorry`
a b : Nat
h₁ : a = 1
q p : Prop
hp : p
r : Prop
h₂ : b = 2
⊢ r
Placement.lean:21:0: warning: declaration uses `sorry`
a b : Nat
q r : Prop
h₁ : a = 1
h₂ : b = 2
⊢ r
Placement.lean:25:0: warning: declaration uses `sorry`
a b : Nat
q r : Prop
h₁ : a = 1
h₃ : b = 2
⊢ r
Placement.lean:29:0: warning: declaration uses `sorry`
";

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
        .filter(|lib| lib.join("Init/SimpLemmas.olean").is_file());
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
        "fln-simp-placement-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos(),
    ));
    std::fs::create_dir(&path).unwrap();
    path
}

/// The pinned `lean`'s stdout and exit code on `name` in `root`, when the binary is present.
/// Both binaries run from `root` on a relative name, so a message names the file as given.
fn pinned(lib: &Path, root: &Path, name: &str) -> Option<(i32, String)> {
    let lean = lib.parent()?.parent()?.join("bin/lean");
    if !lean.is_file() {
        return None;
    }
    let output = Command::new(lean)
        .arg(name)
        .current_dir(root)
        .env("LEAN_PATH", lib)
        .output()
        .expect("run the pinned lean");
    Some((
        output.status.code().expect("normal pinned exit"),
        String::from_utf8(output.stdout).unwrap(),
    ))
}

/// The installed `lean` on `name` in `root`: its exit code, stdout and stderr.
fn ours(lib: &Path, root: &Path, name: &str) -> (i32, String, String) {
    let output = Command::new(env!("CARGO_BIN_EXE_lean"))
        .arg(name)
        .current_dir(root)
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
fn rewritten_hypotheses_are_placed_where_the_pin_asserts_them() {
    let Some(lib) = pinned_lib() else {
        return;
    };
    let root = workspace();
    std::fs::write(root.join("Placement.lean"), PROGRAM).unwrap();
    if let Some((code, stdout)) = pinned(&lib, &root, "Placement.lean") {
        assert_eq!((code, stdout.as_str()), (0, EXPECTED), "the pin moved");
    }
    let (code, stdout, stderr) = ours(&lib, &root, "Placement.lean");
    assert_eq!(code, 0, "{stderr}");
    assert_eq!(stdout, EXPECTED, "{stderr}");
}
