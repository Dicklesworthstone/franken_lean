//! `delta` and `guard_expr` through the installed drop-in `lean`, over `prelude` with `Init.Core`
//! (and `Init.Guard` for `guard_expr`). The pin's `delta f+ (at loc)?` (vendored
//! `Lean/Elab/Tactic/Delta.lean`, `Lean/Meta/Tactic/Delta.lean`) replaces each selected type by
//! its `deltaExpand`: every application of a named definition, never a theorem, by the
//! definition's value beta-reduced with its arguments, outermost first; an unchanged type fails.
//! `guard_expr a r b` (vendored `Lean/Elab/Tactic/Guard.lean:84-90`) elaborates both sides with no
//! expected type, unifies their types, finishes synthesis with default instances and compares by
//! `=` (reducible), `=~` (default), `=ₛ` (syntactic) or `=ₐ` (alpha), at the relation's own
//! transparency whatever the ambient one; a source ascription is not part of a syntactic match.
//!
//! Every program was run through the pinned `lean` v4.32.0 with the same header first
//! (2026-10-25), and its output is compared with the pinned binary's again when that is present.
#![forbid(unsafe_code)]
use std::path::{Path, PathBuf};
use std::process::Command;

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
        .filter(|lib| lib.join("Init/WFTactics.olean").is_file());
    assert!(
        lib.is_some() || std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
        "the pinned Reference library is required"
    );
    if lib.is_none() {
        eprintln!("SKIP: pinned Reference lib/lean absent");
    }
    lib
}

fn workspace(label: &str) -> PathBuf {
    let path = std::env::temp_dir().join(format!(
        "fln-delta-guard-expr-{label}-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos(),
    ));
    std::fs::create_dir(&path).unwrap();
    path
}

/// The pinned `lean`'s exit code and stdout on `name` in `root`, when the binary is present.
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

/// The installed `lean` on `name` in `root`: its exit code, stdout and stderr. Every program of
/// a test shares one import record, so only the first admits its imports cold.
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

/// `(file, program, the pin's stdout)`: programs the pin accepts.
const ACCEPTED: &[(&str, &str, &str)] = &[
    (
        r#"Delta.lean"#,
        r#"prelude
import Init.Core
def f (n : Nat) := n + 1
example : f 1 = 2 := by
  delta f
  rfl
"#,
        r#""#,
    ),
    (
        r#"DeltaTrace.lean"#,
        r#"prelude
import Init.Core
def f (n : Nat) := n + 1
example (k : Nat) : f k = k + 1 := by
  delta f
  trace_state
  rfl
"#,
        r#"k : Nat
⊢ k + 1 = k + 1
"#,
    ),
    (
        r#"DeltaAt.lean"#,
        r#"prelude
import Init.Core
def P := True
example (h : P) : True := by
  delta P at h
  exact h
"#,
        r#""#,
    ),
    (
        r#"DeltaPartial.lean"#,
        r#"prelude
import Init.Core
def comp (f : Nat -> Nat) (g : Nat -> Nat) := fun x => f (g x)
example : comp id id 3 = 3 := by
  delta comp
  trace_state
  rfl
"#,
        r#"⊢ id (id 3) = 3
"#,
    ),
    (
        r#"DeltaAtStar.lean"#,
        r#"prelude
import Init.Core
def P := True
example (h : P) : P := by
  delta P at *
  trace_state
  exact h
"#,
        r#"h : True
⊢ True
"#,
    ),
    (
        r#"GuardExpr.lean"#,
        r#"prelude
import Init.Core
import Init.Guard
example : True := by
  guard_expr 1 + 1 =~ 2
  guard_expr (2 : Nat) = 2
  guard_expr (1 : Nat) =ₛ 1
  trivial
"#,
        r#""#,
    ),
    (
        r#"GuardExprDefault.lean"#,
        r#"prelude
import Init.Core
import Init.Guard
def two := 2
example : True := by
  guard_expr two =~ 2
  trivial
"#,
        r#""#,
    ),
    (
        r#"GuardInWithRed.lean"#,
        r#"prelude
import Init.Core
import Init.Guard
def two := 2
example : True := by
  with_reducible guard_expr two =~ 2
  trivial
"#,
        r#""#,
    ),
    (
        r#"S2.lean"#,
        r#"prelude
import Init.Core
import Init.Guard
example : True := by
  guard_expr 1 =ₛ (1 : Nat)
  trivial
"#,
        r#""#,
    ),
    (
        r#"S3.lean"#,
        r#"prelude
import Init.Core
import Init.Guard
example : True := by
  guard_expr (1 : Nat) =ₐ 1
  trivial
"#,
        r#""#,
    ),
    (
        r#"S4.lean"#,
        r#"prelude
import Init.Core
import Init.Guard
example : True := by
  guard_expr (id 1 : Nat) =ₛ id 1
  trivial
"#,
        r#""#,
    ),
];

/// Each program the pin accepts, run as `name`: the pin's output, which ours must equal.
#[test]
fn delta_and_guard_expr_run_as_the_pin_does() {
    let Some(lib) = pinned_lib() else {
        return;
    };
    let root = workspace("accepted");
    for (name, program, expected) in ACCEPTED {
        std::fs::write(root.join(name), program).unwrap();
        if let Some((code, stdout)) = pinned(&lib, &root, name) {
            assert_eq!(
                (code, stdout.as_str()),
                (0, *expected),
                "{name}: the pin moved"
            );
        }
        let (code, stdout, stderr) = ours(&lib, &root, name);
        assert_eq!(code, 0, "{name}: {stderr}");
        assert_eq!(stdout, *expected, "{name}: {stderr}");
    }
}

/// `(file, program, this engine's reason)`: programs the pin rejects.
const REFUSED: &[(&str, &str, &str)] = &[
    (
        r#"DeltaThmRefused.lean"#,
        r#"prelude
import Init.Core
theorem simpleThm : True := trivial
example : True := by delta simpleThm; trivial
"#,
        r#"elaboration refused source: Tactic `delta` failed: did not delta reduce [simpleThm]"#,
    ),
    (
        r#"DeltaUnchangedRefused.lean"#,
        r#"prelude
import Init.Core
def f (n : Nat) := n + 1
example : 2 = 2 := by
  delta f
  rfl
"#,
        r#"elaboration refused source: Tactic `delta` failed: did not delta reduce [f]"#,
    ),
    (
        r#"DeltaUnknownRefused.lean"#,
        r#"prelude
import Init.Core
example : True := by
  delta nosuch
  trivial
"#,
        r#"elaboration refused source: Unknown identifier `nosuch`"#,
    ),
    (
        r#"GuardExprRefused.lean"#,
        r#"prelude
import Init.Core
import Init.Guard
example : True := by
  guard_expr (1 + 1 : Nat) =ₛ 2
  trivial
"#,
        r#"elaboration refused source: guard_expr: the two terms do not match by the given relation"#,
    ),
    (
        r#"GuardExprRedRefused.lean"#,
        r#"prelude
import Init.Core
import Init.Guard
def two := 2
example : True := by
  guard_expr two = 2
  trivial
"#,
        r#"elaboration refused source: guard_expr: the two terms do not match by the given relation"#,
    ),
];

/// Each program the pin rejects (a theorem `delta` does not unfold, an unchanged target, an
/// unknown name, a failed guard): refused here with this engine's typed reason.
#[test]
fn delta_and_guard_expr_fail_where_the_pin_fails() {
    let Some(lib) = pinned_lib() else {
        return;
    };
    let root = workspace("refused");
    for (name, program, reason) in REFUSED {
        std::fs::write(root.join(name), program).unwrap();
        if let Some((code, stdout)) = pinned(&lib, &root, name) {
            assert_eq!(code, 1, "{name}: the pin moved: {stdout}");
        }
        let (code, stdout, stderr) = ours(&lib, &root, name);
        assert_eq!(code, 1, "{name}: {stdout}{stderr}");
        assert!(
            stderr
                .trim_end()
                .ends_with(&format!("refused source: {reason}")),
            "{name}: {stderr}"
        );
    }
}
