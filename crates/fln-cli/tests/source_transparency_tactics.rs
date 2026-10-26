//! `with_reducible`, `with_reducible_and_instances` and `with_unfolding_none` through the
//! installed drop-in `lean`, over `prelude` and `Init.Core`. The pin's `withReducible` &c.
//! (vendored `Lean/Elab/Tactic/BuiltinTactic.lean`, syntax in `Init/Tactics.lean:358-376`) run
//! their sequence on every goal with the transparency set: ordinary elaboration and the tactics'
//! own comparisons unfold reducible definitions only, instances too, or nothing, while instance
//! selection keeps its own `instances` transparency and an inner scope replaces an outer one.
//! Nat offsets still meet at reducible transparency (`isDefEqOffsetNat`). Also `rfl` on an `Iff`,
//! the pin's latest `rfl` rule `exact Iff.rfl` (vendored `Init/Core.lean:1042`).
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
        "fln-transparency-tactics-{label}-{}-{}",
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
        r#"RedRflAbbrev.lean"#,
        r#"prelude
import Init.Core
@[reducible] def myId (x : Nat) : Nat := x
example : myId 42 = 42 := by with_reducible rfl
"#,
        r#""#,
    ),
    (
        r#"NoneRflSyntactic.lean"#,
        r#"prelude
import Init.Core
example : (42 : Nat) = 42 := by with_unfolding_none rfl
"#,
        r#""#,
    ),
    (
        r#"RedExactOffset.lean"#,
        r#"prelude
import Init.Core
opaque bar : Nat → Nat
theorem foo : bar (Nat.succ a) = 0 := sorry
example : bar (a + 1) = 0 := by with_reducible exact foo
example : bar (a + a + 1) = 0 := by with_reducible exact foo
"#,
        r#"RedExactOffset.lean:4:8: warning: declaration uses `sorry`
"#,
    ),
    (
        r#"DefaultExactDef.lean"#,
        r#"prelude
import Init.Core
def two := 2
theorem t : two = 2 := rfl
example : 2 = 2 := by exact t
"#,
        r#""#,
    ),
    (
        r#"InstRfl.lean"#,
        r#"prelude
import Init.Core
instance myInst : Inhabited Nat := ⟨5⟩
example : (default : Nat) = 5 := by with_reducible_and_instances rfl
"#,
        r#""#,
    ),
    (
        r#"IffRfl.lean"#,
        r#"prelude
import Init.Core
example (p : Prop) : p ↔ p := by rfl
"#,
        r#""#,
    ),
    (
        r#"RwMvarRedRfl.lean"#,
        r#"prelude
import Init.Core
opaque f : Nat → Nat
opaque P : Nat → (Nat → Nat) → Prop
opaque Q : Nat → Prop
opaque foo (g : Nat → Nat) (x : Nat) : P x f ↔ Q (g x) := sorry
example : P x f ↔ Q (x + 10) := by
  rewrite [foo]
  with_reducible rfl
"#,
        r#"RwMvarRedRfl.lean:6:7: warning: declaration uses `sorry`
"#,
    ),
    (
        r#"ScopeRestores.lean"#,
        r#"prelude
import Init.Core
def two := 2
example : two = 2 := by
  with_reducible skip
  rfl
"#,
        r#""#,
    ),
    (
        r#"ListDiamond.lean"#,
        r#"prelude
import Init.Core
example : @List.instDecidableEqNil α List.nil = @List.instDecidableNilEq α List.nil := by
  with_reducible_and_instances rfl
section
variable {α : Type u} [DecidableEq α]
example (x : List α) : instDecidableEqList x List.nil = List.instDecidableEqNil x := by
  with_reducible_and_instances rfl
example (x : List α) : instDecidableEqList List.nil x = List.instDecidableNilEq x := by
  with_reducible_and_instances rfl
end
"#,
        r#""#,
    ),
];

/// Each program the pin accepts, run as `name`: the pin's output, which ours must equal.
#[test]
fn transparency_scopes_unfold_what_the_pin_unfolds() {
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
        r#"RedRflDefRefused.lean"#,
        r#"prelude
import Init.Core
def myId (x : Nat) : Nat := x
example : myId 42 = 42 := by with_reducible rfl
"#,
        r#"elaboration refused source: unification deferred: UnsupportedEquation"#,
    ),
    (
        r#"NoneRflRefused.lean"#,
        r#"prelude
import Init.Core
@[reducible] def myId (x : Nat) : Nat := x
example : myId 42 = 42 := by with_unfolding_none rfl
"#,
        r#"elaboration refused source: unification deferred: UnsupportedEquation"#,
    ),
    (
        r#"RedExactDefRefused.lean"#,
        r#"prelude
import Init.Core
def two := 2
theorem t : two = 2 := rfl
example : 2 = 2 := by with_reducible exact t
"#,
        r#"elaboration refused source: unification deferred: UnsupportedEquation"#,
    ),
    (
        r#"RedInstRefused.lean"#,
        r#"prelude
import Init.Core
instance myInst : Inhabited Nat := ⟨5⟩
example : (default : Nat) = 5 := by with_reducible rfl
"#,
        r#"elaboration refused source: unification deferred: UnsupportedEquation"#,
    ),
    (
        r#"IffRflRefused.lean"#,
        r#"prelude
import Init.Core
example (p q : Prop) : p ↔ q := by rfl
"#,
        r#"elaboration refused source: source conversion refused: Rejected { class: NotDefEq, message: "terms are not definitionally equal", consumption: Consumption { steps_used: 21, max_depth: 4 } }"#,
    ),
    (
        r#"NestedScope.lean"#,
        r#"prelude
import Init.Core
def two := 2
example : two = 2 := by
  with_unfolding_none (with_reducible_and_instances rfl)
"#,
        r#"elaboration refused source: unification deferred: UnsupportedEquation"#,
    ),
    (
        r#"RedAssumptionRefused.lean"#,
        r#"prelude
import Init.Core
def P := True
example (h : P) : True := by with_reducible assumption
"#,
        r#"elaboration refused source: no local assumption matches the goal"#,
    ),
    (
        r#"RedApplyRefused.lean"#,
        r#"prelude
import Init.Core
def two := 2
theorem t : two = 2 := rfl
example : 2 = 2 := by with_reducible apply t
"#,
        r#"elaboration refused source: apply conclusion does not match the goal"#,
    ),
    (
        r#"ListDiamondRedRefused.lean"#,
        r#"prelude
import Init.Core
example : @List.instDecidableEqNil α List.nil = @List.instDecidableNilEq α List.nil := by
  with_reducible rfl
"#,
        r#"elaboration refused source: unification deferred: UnsupportedEquation"#,
    ),
];

/// Each program the pin rejects, because the scope leaves a definition folded (or an `Iff`
/// whose sides differ): refused here with this engine's typed reason.
#[test]
fn transparency_scopes_refuse_what_the_pin_does_not_unfold() {
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
