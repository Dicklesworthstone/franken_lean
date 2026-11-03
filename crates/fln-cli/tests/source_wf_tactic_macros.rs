//! The well-founded recursion macros of `Init/WFTactics.lean` named in a script, through the
//! installed drop-in `lean` over `prelude` and `Init.WFTactics`: `decreasing_tactic` runs as the
//! default `decreasing_by` does, `decreasing_trivial_pre_omega` is its three `macro_rules` (most
//! recent first), and `simp_wf` is `try simp` where its configuration (`+unfoldPartialApp
//! +zetaDelta`) and its unfold set cannot act: a target that mentions one of its seven
//! definitions or a `let` variable is refused, typed, rather than simplified without them.
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
        "fln-wf-tactic-macros-{label}-{}-{}",
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
        r#"DecTac.lean"#,
        r#"prelude
import Init.WFTactics
def foo : Nat → Nat
  | 0 => 0
  | n+1 => foo n
decreasing_by decreasing_tactic
"#,
        r#""#,
    ),
    (
        r#"DecTacTerm.lean"#,
        r#"prelude
import Init.WFTactics
example (n : Nat) : n < n + 1 := by decreasing_tactic
"#,
        r#""#,
    ),
    (
        r#"PreOmega.lean"#,
        r#"prelude
import Init.WFTactics
def h (a i : Nat) : Nat :=
  if hi : i < a then h a (i + 1) + 1 else 0
termination_by a - i
decreasing_by simp_wf; decreasing_trivial_pre_omega
"#,
        r#""#,
    ),
];

/// Each program the pin accepts, run as `name`: the pin's output, which ours must equal.
#[test]
fn wf_tactic_macros_run_as_the_pin_does() {
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

/// `ite_eq_dite` in `Init/WF.lean` makes an unnamed conditional's fact available
/// to termination proofs. It runs after source elaboration at the pin, so the
/// same fact must remain unavailable to a tactic in the original branch, and
/// source proofs must still match ordinary conditional lemmas against `ite`.
#[test]
fn unnamed_conditional_facts_are_scoped_to_termination_proofs() {
    let Some(lib) = pinned_lib() else {
        return;
    };
    let root = workspace("conditional-facts");
    let name = "ConditionalFacts.lean";
    let program = r#"prelude
import Init.Omega
import Init.WFComputable
def downPositive (n : Nat) : Nat :=
  if 0 < n then downPositive (n - 1) + 1 else 0
termination_by n
decreasing_by omega
def downNegative (n : Nat) : Nat :=
  if n = 0 then 0 else downNegative (n - 1) + 1
termination_by n
decreasing_by omega
def downNested (n : Nat) : Nat :=
  if n = 0 then 0 else if n = 1 then 1 else downNested (n - 1) + 1
termination_by n
decreasing_by omega
def downNamed (n : Nat) : Nat :=
  if h : 0 < n then
    have h' : 0 < n := by assumption
    downNamed (n - 1) + 1
  else 0
termination_by n
decreasing_by omega
def wfSimp (n : Nat) : Nat :=
  have _h : (if n = 0 then 1 else 1) = 1 := by simp only [ite_self]
  have _typed : (if n = 0 then 1 else 1) = (1 : Int) := by simp only [ite_self]
  if h : n = 0 then 0 else wfSimp (n - 1) + 1
termination_by n
decreasing_by omega
def wfRewrite (n : Nat) : Nat :=
  have _h : ∀ p : Prop, ∀ _ : Decidable p, p → (if p then 1 else 2) = 1 := by
    intro p inst hp
    rw [if_pos hp]
  if h : n = 0 then 0 else wfRewrite (n - 1) + 1
termination_by n
decreasing_by omega
def keepImplicit {value : Nat} (x : Nat) (_ : x = value) : Nat := x
def downImplicit (n : Nat) : Nat :=
  if 0 < n then keepImplicit (downImplicit (n - 1) + 1) rfl else 0
termination_by n
decreasing_by omega
#eval downPositive 4
#eval downNegative 4
#eval downNested 4
#eval downNamed 4
#eval wfSimp 4
#eval wfRewrite 4
#eval downImplicit 4
"#;
    std::fs::write(root.join(name), program).unwrap();
    if let Some((code, stdout)) = pinned(&lib, &root, name) {
        assert_eq!(
            (code, stdout.as_str()),
            (0, "4\n4\n4\n4\n4\n4\n4\n"),
            "{stdout}"
        );
    }
    let (code, stdout, stderr) = ours(&lib, &root, name);
    assert_eq!(code, 0, "{stdout}{stderr}");
    assert_eq!(stdout, "4\n4\n4\n4\n4\n4\n4\n", "{stderr}");

    for (name, tactic) in [
        ("NoSourceAssumption.lean", "assumption"),
        ("NoSourceOmega.lean", "omega"),
    ] {
        let program = format!(
            r#"prelude
import Init.Omega
import Init.WFComputable
def bad (n : Nat) : Nat :=
  if 0 < n then
    have h : 0 < n := by {tactic}
    bad (n - 1) + 1
  else 0
termination_by n
decreasing_by omega
"#
        );
        std::fs::write(root.join(name), program).unwrap();
        if let Some((code, stdout)) = pinned(&lib, &root, name) {
            assert_eq!(code, 1, "{name}: the pin moved: {stdout}");
        }
        let (code, stdout, stderr) = ours(&lib, &root, name);
        assert_eq!(code, 1, "{name}: {stdout}{stderr}");
        assert!(stdout.is_empty(), "{name}: {stdout}");
    }
}

/// `(file, program, this engine's reason)`: programs the pin rejects.
const REFUSED: &[(&str, &str, &str)] = &[(
    r#"DecTacRefused.lean"#,
    r#"prelude
import Init.WFTactics
def bad (n : Nat) : Nat := bad (n + 1)
decreasing_by decreasing_tactic
"#,
    r#"elaboration refused source: omega requires its native provider and checked Init.Omega declarations"#,
)];

/// A recursion the pin's `decreasing_tactic` cannot prove: refused here.
#[test]
fn wf_tactic_macros_fail_where_the_pin_fails() {
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

/// `(file, program, this engine's exit code, its refusal)`: programs the pin accepts
/// and this engine refuses, typed.
const TYPED: &[(&str, &str, i32, &str)] = &[
    (
        r#"SimpWfMeasure.lean"#,
        r#"prelude
import Init.WFTactics
example : (measure id).rel 1 2 := by
  simp_wf
"#,
        1,
        r#"refused source: elaboration refused source: unsupported tactic `tacticSimp_wf`"#,
    ),
    (
        r#"SimpWfLet.lean"#,
        r#"prelude
import Init.WFTactics
example (n : Nat) : n < n + 1 := by
  let k := n
  show k < n + 1
  simp_wf
"#,
        1,
        r#"refused source: elaboration refused source: unsupported tactic `tacticSimp_wf`"#,
    ),
];

/// `simp_wf` on a target where its unfold set or `zetaDelta` would act: the pin runs it, and
/// this engine refuses it, typed.
#[test]
fn simp_wf_outside_its_fragment_is_refused_typed() {
    let Some(lib) = pinned_lib() else {
        return;
    };
    let root = workspace("typed");
    for (name, program, expected, reason) in TYPED {
        std::fs::write(root.join(name), program).unwrap();
        if let Some((code, stdout)) = pinned(&lib, &root, name) {
            assert_eq!(code, 0, "{name}: the pin moved: {stdout}");
        }
        let (code, stdout, stderr) = ours(&lib, &root, name);
        assert_eq!(code, *expected, "{name}: {stdout}{stderr}");
        assert!(stdout.is_empty(), "{name}: {stdout}");
        assert!(stderr.trim_end().ends_with(reason), "{name}: {stderr}");
    }
}
