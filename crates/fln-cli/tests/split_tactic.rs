//! `split` through the installed drop-in `lean`, over `prelude` and the smallest `Init` modules
//! that have it. The pin's `split` (vendored `Lean/Elab/Tactic/Split.lean`) splits the first `if`
//! of the goal, or of one hypothesis, by cases on its decision (`SplitIf.splitIfAt?`, vendored
//! `Lean/Meta/Tactic/SplitIf.lean:261-271`), tagging the cases `isTrue` and `isFalse` and naming
//! the hypothesis `h✝`, then reduces in each case every conditional a hypothesis decides
//! (`simpIfTarget`/`simpIfLocalDecl` under `backward.split`, lines 284-313). A `match` is split
//! with its matcher's splitter (vendored `Lean/Meta/Tactic/Split.lean`), which this engine
//! refuses, typed.
//!
//! Every program was run through the pinned `lean` v4.32.0 with the same header first
//! (2026-10-23), and its output is compared with the pinned binary's again when that is present.
#![forbid(unsafe_code)]
use std::path::{Path, PathBuf};
use std::process::Command;

/// Conditionals in the goal and in hypotheses: source `if`s on a proposition and on a `Bool`,
/// with and without evidence, nested, applied, under a binder, and the pin's `ite` written out;
/// `split at`, `split at *`, `split <;>`, `next` naming, and proofs closed after the split.
const PROGRAM: &str = r#"prelude
import Init.SimpLemmas
example (x : Nat) : (if x = 0 then 1 else 2) > 0 := by
  split
  trace_state
  all_goals sorry
example (x : Nat) (f : (x : Nat) → x ≠ 0 → Nat) : (if h : x ≠ 0 then f x h else 2) > 0 := by
  split
  trace_state
  all_goals sorry
example (x y : Nat) : (if x = 0 then (if y = 0 then 1 else 2) else 3) > 0 := by
  split
  split
  trace_state
  all_goals sorry
example (x y : Nat) (hy : y = 0) : (if x = 0 then (if y = 0 then 1 else 2) else 3) > 0 := by
  split
  trace_state
  all_goals sorry
example (x y : Nat) (h : (if x = y then 1 else 2) = 3) : False := by
  split at h
  trace_state
  all_goals sorry
example (p : Prop) [Decidable p] (h : ite p 1 2 = 3) (h2 : h = h) : True := by
  split at h
  trace_state
  all_goals sorry
example (b : Bool) (f g : Nat → Nat) : (if b then f else g) 3 = 37 := by
  split
  trace_state
  all_goals sorry
example (x : Nat) : ∀ y : Nat, (if x = 0 then y else 2) ≥ 0 := by
  split
  trace_state
  all_goals sorry
example (x y : Nat) : ite (x = 0) (ite (y = 0) 1 2) 3 > 0 := by
  split
  trace_state
  all_goals sorry
example (x : Nat) (h1 : True) (h : (if x = 0 then 1 else 2) = 5) : False := by
  split at *
  trace_state
  all_goals sorry
example (x : Nat) : (if x = 0 then 1 else 2) > 0 := by
  split
  next h =>
    trace_state
    decide
  next h => decide
example (b : Bool) : (if b then 1 else if b then 1 else 0) = (if b then 1 else 0) := by
  split <;> rfl
example (b : Bool) : (if _h : (if b then true else true) then 1 else 2) = 1 := by
  split
  next h' => rfl
  next h' => rfl
example (x : Nat) (f : (x : Nat) → x = 0 → Nat) (hf : ∀ x h, f x h = 0) :
    (if h : x = 0 then f x h else 0) = 0 := by
  split
  next h => exact hf x h
  next => rfl
example (x y : Nat) (h : (if x = y then 1 else 2) = 1) : x = y := by
  split at h
  next hxy => exact hxy
  next => exact Nat.noConfusion (Nat.succ.inj h)
example (p : Prop) [Decidable p] (a b : Nat) (h : (if p then a else b) = 3) (hb : b = 3) :
    (if p then a else b) = 3 := by
  split at h
  next hp =>
    split
    next => exact h
    next => contradiction
  next hp =>
    split
    next => contradiction
    next => exact hb
example {A B : Type} {p : Prop} [Decidable p] (h : if p then A else B) : Sum A B := by
  split at h
  next => exact .inl h
  next => exact .inr h
example (x : Nat) (h : ∀ y : Nat, (if x = 0 then y else 0) = y) : x = 0 := by
  split at h
  next hx => exact hx
  next => exact absurd (h 1) (fun h1 => Nat.noConfusion h1)
"#;

/// The pin's output for [`PROGRAM`]. A hypothesis decides every conditional it can, not only the
/// split one (`hy`); a dependent hypothesis stays, shadowed, beside its reduced copy.
const EXPECTED: &str = r#"case isTrue
x : Nat
h✝ : x = 0
⊢ 1 > 0

case isFalse
x : Nat
h✝ : ¬x = 0
⊢ 2 > 0
Split.lean:3:0: warning: declaration uses `sorry`
case isTrue
x : Nat
f : (x : Nat) → x ≠ 0 → Nat
h✝ : x ≠ 0
⊢ f x h✝ > 0

case isFalse
x : Nat
f : (x : Nat) → x ≠ 0 → Nat
h✝ : ¬x ≠ 0
⊢ 2 > 0
Split.lean:7:0: warning: declaration uses `sorry`
case isTrue.isTrue
x y : Nat
h✝¹ : x = 0
h✝ : y = 0
⊢ 1 > 0

case isTrue.isFalse
x y : Nat
h✝¹ : x = 0
h✝ : ¬y = 0
⊢ 2 > 0

case isFalse
x y : Nat
h✝ : ¬x = 0
⊢ 3 > 0
Split.lean:11:0: warning: declaration uses `sorry`
case isTrue
x y : Nat
hy : y = 0
h✝ : x = 0
⊢ 1 > 0

case isFalse
x y : Nat
hy : y = 0
h✝ : ¬x = 0
⊢ 3 > 0
Split.lean:16:0: warning: declaration uses `sorry`
case isTrue
x y : Nat
h✝ : x = y
h : 1 = 3
⊢ False

case isFalse
x y : Nat
h✝ : ¬x = y
h : 2 = 3
⊢ False
Split.lean:20:0: warning: declaration uses `sorry`
case isTrue
p : Prop
inst✝ : Decidable p
h✝¹ : ite p 1 2 = 3
h2 : h✝¹ = h✝¹
h✝ : p
h : 1 = 3
⊢ True

case isFalse
p : Prop
inst✝ : Decidable p
h✝¹ : ite p 1 2 = 3
h2 : h✝¹ = h✝¹
h✝ : ¬p
h : 2 = 3
⊢ True
Split.lean:24:0: warning: declaration uses `sorry`
case isTrue
b : Bool
f g : Nat → Nat
h✝ : b = true
⊢ f 3 = 37

case isFalse
b : Bool
f g : Nat → Nat
h✝ : ¬b = true
⊢ g 3 = 37
Split.lean:28:0: warning: declaration uses `sorry`
case isTrue
x : Nat
h✝ : x = 0
⊢ ∀ (y : Nat), y ≥ 0

case isFalse
x : Nat
h✝ : ¬x = 0
⊢ ∀ (y : Nat), 2 ≥ 0
Split.lean:32:0: warning: declaration uses `sorry`
case isTrue
x y : Nat
h✝ : x = 0
⊢ ite (y = 0) 1 2 > 0

case isFalse
x y : Nat
h✝ : ¬x = 0
⊢ 3 > 0
Split.lean:36:0: warning: declaration uses `sorry`
case isTrue
x : Nat
h1 : True
h✝ : x = 0
h : 1 = 5
⊢ False

case isFalse
x : Nat
h1 : True
h✝ : ¬x = 0
h : 2 = 5
⊢ False
Split.lean:40:0: warning: declaration uses `sorry`
x : Nat
h : x = 0
⊢ 1 > 0
"#;

/// An `ite` from an imported statement (`Nat.div_eq`), in the goal and in a hypothesis.
const IMPORTED: &str = r#"prelude
import Init.Data.Nat.Div.Basic
example (n : Nat) : (n + 2) / 2 < n + 3 := by
  rw [Nat.div_eq]
  split
  trace_state
  all_goals sorry
example (n : Nat) (h : n / 2 = 5) : 2 ≤ n := by
  rw [Nat.div_eq] at h
  split at h
  next hn => exact hn.2
  next => exact Nat.noConfusion h
"#;

/// The pin's output for [`IMPORTED`].
const IMPORTED_EXPECTED: &str = r#"case isTrue
n : Nat
h✝ : 0 < 2 ∧ 2 ≤ n + 2
⊢ (n + 2 - 2) / 2 + 1 < n + 3

case isFalse
n : Nat
h✝ : ¬(0 < 2 ∧ 2 ≤ n + 2)
⊢ 0 < n + 3
Imported.lean:3:0: warning: declaration uses `sorry`
"#;

/// Programs the pin refuses: the name, the program, the pin's message (before the goal it
/// appends), and this engine's refusal, which names the hypothesis where the pin prints its type.
const REFUSED: &[(&str, &str, &str, &str)] = &[
    (
        "Nothing.lean",
        "prelude\nimport Init.SimpLemmas\nexample (x : Nat) : x = x := by\n  split\n",
        "Tactic `split` failed: Could not split an `if` or `match` expression in the goal\n\nHint: Use `set_option trace.split.failure true` to display additional diagnostic information\n",
        "Tactic `split` failed: Could not split an `if` or `match` expression in the goal\n\nHint: Use `set_option trace.split.failure true` to display additional diagnostic information\n",
    ),
    (
        "Conj.lean",
        "prelude\nimport Init.SimpLemmas\nexample (p q : Prop) (h : p ∧ q) : p := by\n  split at h\n",
        "Tactic `split` failed: Could not split an `if` or `match` expression in the type `p ∧ q` of `h`\n\nHint: If you meant to destruct this conjunction, use the `cases` tactic instead\n\nHint: Use `set_option trace.split.failure true` to display additional diagnostic information\n",
        "Tactic `split` failed: Could not split an `if` or `match` expression in the type of `h`\n\nHint: If you meant to destruct this conjunction, use the `cases` tactic instead\n\nHint: Use `set_option trace.split.failure true` to display additional diagnostic information\n",
    ),
    (
        "Wild.lean",
        "prelude\nimport Init.SimpLemmas\nexample (x : Nat) (h1 : True) : x = x := by\n  split at *\n",
        "Tactic `split` failed: Could not split the goal or any of the following hypotheses: `h1`\n\nNote: `split at *` does not attempt to split at non-propositional hypotheses or those on which other hypotheses depend. It may still be possible to manually split a hypothesis using `split at`\n\nHint: Use `set_option trace.split.failure true` to display additional diagnostic information\n",
        "Tactic `split` failed: Could not split the goal or any of the following hypotheses: `h1`\n\nNote: `split at *` does not attempt to split at non-propositional hypotheses or those on which other hypotheses depend. It may still be possible to manually split a hypothesis using `split at`\n\nHint: Use `set_option trace.split.failure true` to display additional diagnostic information\n",
    ),
    (
        "Term.lean",
        "prelude\nimport Init.SimpLemmas\nexample (p : Prop) [Decidable p] (h : if p then True else True) : True := by\n  split h\n",
        "Tactic `split` failed: Specifying a term to split is not supported yet\n\nHint: To apply `split` at the hypothesis `h`, use `split at h`:\n  split a\u{332}t\u{332} \u{332}h\n",
        "Tactic `split` failed: Specifying a term to split is not supported yet\n\nHint: To apply `split` at the hypothesis `h`, use `split at h`:\n  split a\u{332}t\u{332} \u{332}h\n",
    ),
    (
        "Many.lean",
        "prelude\nimport Init.SimpLemmas\nexample (p q : Prop) (h : p) (h2 : q) : p := by\n  split at h h2\n",
        "Tactic `split` failed: Specifying multiple targets (hypotheses`h` and `h2`) is not supported\n\nHint: Specify a single target to split, or use `split at *` to split the first target that can be automatically split\n",
        "Tactic `split` failed: Specifying multiple targets (hypotheses`h` and `h2`) is not supported\n\nHint: Specify a single target to split, or use `split at *` to split the first target that can be automatically split\n",
    ),
];

/// A `match` the pin splits (`case h_1`, `case h_2`) and this engine refuses.
const MATCH: &str = "prelude\nimport Init.SimpLemmas\nexample (x : Nat) : (match x with | 0 => 1 | _ => 2) > 0 := by\n  split\n  all_goals sorry\n";

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
        .filter(|lib| lib.join("Init/Data/Nat/Div/Basic.olean").is_file());
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
        "fln-split-tactic-{}-{}",
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

/// `program` as `name` in `root`, its output compared with `expected`, the pin's.
fn accepted(lib: &Path, root: &Path, name: &str, program: &str, expected: &str) {
    std::fs::write(root.join(name), program).unwrap();
    if let Some((code, stdout)) = pinned(lib, root, name) {
        assert_eq!((code, stdout.as_str()), (0, expected), "the pin moved");
    }
    let (code, stdout, stderr) = ours(lib, root, name);
    assert_eq!(code, 0, "{stderr}");
    assert_eq!(stdout, expected, "{stderr}");
}

#[test]
fn split_cases_on_conditionals_as_the_pin_does() {
    let Some(lib) = pinned_lib() else {
        return;
    };
    let root = workspace();
    accepted(&lib, &root, "Split.lean", PROGRAM, EXPECTED);
}

#[test]
fn split_cases_on_an_imported_ite_as_the_pin_does() {
    let Some(lib) = pinned_lib() else {
        return;
    };
    let root = workspace();
    accepted(&lib, &root, "Imported.lean", IMPORTED, IMPORTED_EXPECTED);
}

#[test]
fn split_is_refused_where_the_pin_refuses_it() {
    let Some(lib) = pinned_lib() else {
        return;
    };
    let root = workspace();
    for (name, program, pin_message, message) in REFUSED {
        std::fs::write(root.join(name), program).unwrap();
        if let Some((code, stdout)) = pinned(&lib, &root, name) {
            assert_eq!(code, 1, "{name}: the pin moved: {stdout}");
            // The message, then the goal the pin appends after a blank line, if any.
            let at = stdout
                .find(&format!("error: {pin_message}"))
                .map(|at| at + "error: ".len() + pin_message.len());
            assert!(
                at.is_some_and(|at| stdout[at..].is_empty() || stdout[at..].starts_with('\n')),
                "{name}: the pin moved: {stdout}"
            );
        }
        let (code, stdout, stderr) = ours(&lib, &root, name);
        assert_eq!(code, 1, "{name}: {stdout}{stderr}");
        assert!(
            stderr.ends_with(&format!("refused source: {message}")),
            "{name}: {stderr}"
        );
    }
}

/// The pin splits a `match` with its matcher's splitter; this engine refuses it, typed, rather
/// than split something else or claim the goals the pin makes.
#[test]
fn split_on_a_match_is_refused_typed() {
    let Some(lib) = pinned_lib() else {
        return;
    };
    let root = workspace();
    std::fs::write(root.join("Match.lean"), MATCH).unwrap();
    if let Some((code, stdout)) = pinned(&lib, &root, "Match.lean") {
        assert_eq!(
            (code, stdout.as_str()),
            (0, "Match.lean:3:0: warning: declaration uses `sorry`\n"),
            "the pin moved"
        );
    }
    let (code, stdout, stderr) = ours(&lib, &root, "Match.lean");
    assert_eq!(code, 1, "{stdout}{stderr}");
    assert!(
        stderr.contains("split on a `match` expression is not implemented"),
        "{stderr}"
    );
}
