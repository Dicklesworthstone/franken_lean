//! `and_intros`, `refine`'s goal tags, `rename`, `exists`, `case'`, `rotate_left`/`rotate_right`
//! and `injections` through the installed drop-in `lean`, over `prelude` with `Init.Core` (and
//! `Init.NotationExtra` for `∃`). `and_intros` is the pin's `repeat' refine And.intro ?_ ?_`
//! (vendored `Init/Tactics.lean:1355-1357`) over every goal, its new goals tagged `refine_1` and
//! `refine_2` (`tagUntaggedGoals`); `rename e => h` renames the last hypothesis whose type unifies
//! with `e` (vendored `Lean/Elab/Tactic/ElabTerm.lean:344-359`); `exists es` is
//! `(refine ⟨es, ?_⟩; try trivial)`; `case'` runs its body on each selected goal without
//! requiring it closed, a single goal it leaves keeping the tag (vendored
//! `Lean/Elab/Tactic/BuiltinTactic.lean:589-604`); `rotate_left n` rotates the goal list; and
//! `injections` injects every constructor equation, the new ones next, at most five deep, then
//! tries `assumption` (vendored `Lean/Meta/Tactic/Injection.lean:119-146`). Names for
//! `injections` are refused, typed.
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
        "fln-goal-structuring-{label}-{}-{}",
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
        r#"AndIntros.lean"#,
        r#"prelude
import Init.Core
example (hp : p) (hq : q) (hr : r) : (p ∧ q) ∧ (q ∧ (r ∧ p)) := by
  and_intros
  exact hp
  exact hq
  exact hq
  exact hr
  exact hp
"#,
        r#""#,
    ),
    (
        r#"AndIntrosTags.lean"#,
        r#"prelude
import Init.Core
example (x : Nat) : x = 0 ∧ x = 1 ∧ x = 2 := by
  and_intros
  trace_state
  all_goals sorry
"#,
        r#"case refine_1
x : Nat
⊢ x = 0

case refine_2.refine_1
x : Nat
⊢ x = 1

case refine_2.refine_2
x : Nat
⊢ x = 2
AndIntrosTags.lean:3:0: warning: declaration uses `sorry`
"#,
    ),
    (
        r#"AndIntrosAllGoals.lean"#,
        r#"prelude
import Init.Core
example (hp : p) (hq : q) : (p ∧ q) ∧ (q ∧ p) := by
  constructor
  and_intros
  trace_state
  all_goals assumption
"#,
        r#"case left.refine_1
p q : Prop
hp : p
hq : q
⊢ p

case left.refine_2
p q : Prop
hp : p
hq : q
⊢ q

case right.refine_1
p q : Prop
hp : p
hq : q
⊢ q

case right.refine_2
p q : Prop
hp : p
hq : q
⊢ p
"#,
    ),
    (
        r#"AndIntrosNoop.lean"#,
        r#"prelude
import Init.Core
example (hp : p) : p := by
  and_intros
  exact hp
"#,
        r#""#,
    ),
    (
        r#"RefineTags.lean"#,
        r#"prelude
import Init.Core
example (x : Nat) : x = 0 ∧ x = 1 := by
  refine And.intro ?_ ?_
  trace_state
  all_goals sorry
"#,
        r#"case refine_1
x : Nat
⊢ x = 0

case refine_2
x : Nat
⊢ x = 1
RefineTags.lean:3:0: warning: declaration uses `sorry`
"#,
    ),
    (
        r#"Rename.lean"#,
        r#"prelude
import Init.Core
example (h : 1 = 1) : 1 = 1 := by
  rename 1 = 1 => k
  exact k
"#,
        r#""#,
    ),
    (
        r#"RenamePattern.lean"#,
        r#"prelude
import Init.Core
example (a b : Nat) (h : a = b) : b = a := by
  rename _ = _ => k
  exact k.symm
"#,
        r#""#,
    ),
    (
        r#"RenameLast.lean"#,
        r#"prelude
import Init.Core
example (h₁ : 1 = 1) (h₂ : 1 = 1) : True := by
  rename 1 = 1 => k
  trace_state
  trivial
"#,
        r#"h₁ k : 1 = 1
⊢ True
RenameLast.lean:3:9: warning: Variable name `h₁` is not explicitly referenced.

The binding can be removed (if unused) or named `_` (if used implicitly).

Note: This linter can be disabled with `set_option linter.unusedVariables false`
RenameLast.lean:3:22: warning: Variable name `h₂` is not explicitly referenced.

The binding can be removed (if unused) or named `_` (if used implicitly).

Note: This linter can be disabled with `set_option linter.unusedVariables false`
"#,
    ),
    (
        r#"Exists.lean"#,
        r#"prelude
import Init.Core
import Init.NotationExtra
example : ∃ x : Nat, x = x := by
  exists 0
"#,
        r#""#,
    ),
    (
        r#"ExistsTwo.lean"#,
        r#"prelude
import Init.Core
import Init.NotationExtra
example : ∃ x : Nat, ∃ y : Nat, x = y + 1 := by
  exists 1, 0
"#,
        r#""#,
    ),
    (
        r#"ExistsOpen.lean"#,
        r#"prelude
import Init.Core
import Init.NotationExtra
example : ∃ x : Nat, x = 2 + 3 := by
  exists 5
"#,
        r#""#,
    ),
    (
        r#"ExistsLeft.lean"#,
        r#"prelude
import Init.Core
import Init.NotationExtra
example (p : Nat → Prop) (h : p 3) : ∃ x, p x := by
  exists 3
"#,
        r#""#,
    ),
    (
        r#"CasePrime.lean"#,
        r#"prelude
import Init.Core
example (hp : p) (hq : p → q) (hr : p → r) : (s ∨ q) ∧ (r ∨ s) := by
  constructor
  case' left  => apply Or.inr
  case' right => apply Or.inl
  case' left  => apply hq
  case' right => apply hr
  all_goals assumption
"#,
        r#""#,
    ),
    (
        r#"CasePrimeMulti.lean"#,
        r#"prelude
import Init.Core
example (hp : p) (hq : p → q) (hr : p → r) : (p ∧ q) ∧ (r ∧ p) := by
  constructor
  case' left | right => constructor
  case' right.left => apply hr
  case' left.right => apply hq
  all_goals assumption
"#,
        r#""#,
    ),
    (
        r#"CasePrimeTrace.lean"#,
        r#"prelude
import Init.Core
example (hp : p) (hq : q) : p ∧ q := by
  constructor
  case' right => skip
  trace_state
  exact hq
  exact hp
"#,
        r#"case right
p q : Prop
hp : p
hq : q
⊢ q

case left
p q : Prop
hp : p
hq : q
⊢ p
"#,
    ),
    (
        r#"RotateLeft.lean"#,
        r#"prelude
import Init.Core
example (hp : p) (hq : q) : p ∧ q := by
  constructor
  rotate_left
  exact hq
  exact hp
"#,
        r#""#,
    ),
    (
        r#"RotateRight.lean"#,
        r#"prelude
import Init.Core
example (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
  refine ⟨?_, ?_, ?_⟩
  rotate_right
  trace_state
  exact hr
  exact hp
  exact hq
"#,
        r#"case refine_3
p q r : Prop
hp : p
hq : q
hr : r
⊢ r

case refine_1
p q r : Prop
hp : p
hq : q
hr : r
⊢ p

case refine_2
p q r : Prop
hp : p
hq : q
hr : r
⊢ q
"#,
    ),
    (
        r#"RotateN.lean"#,
        r#"prelude
import Init.Core
example (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
  refine ⟨?_, ?_, ?_⟩
  rotate_left 2
  exact hr
  exact hp
  exact hq
"#,
        r#""#,
    ),
    (
        r#"InjectionsAssumption.lean"#,
        r#"prelude
import Init.Core
example (a b : Nat) (h : Nat.succ a = Nat.succ b) : a = b := by
  injections
"#,
        r#""#,
    ),
    (
        r#"InjectionsNone.lean"#,
        r#"prelude
import Init.Core
example (a b : Nat) (h : a = b) : b = a := by
  injections
  exact h.symm
"#,
        r#""#,
    ),
];

/// Each program the pin accepts, run as `name`: the pin's output (goal tags included), which
/// ours must equal.
#[test]
fn goal_structuring_tactics_run_as_the_pin_does() {
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
        r#"AndIntrosWrongRefused.lean"#,
        r#"prelude
import Init.Core
example (hp : p) (hq : q) : p ∧ q := by
  and_intros
  exact hq
  exact hp
"#,
        r#"elaboration refused source: source conversion refused: Rejected { class: NotDefEq, message: "terms are not definitionally equal", consumption: Consumption { steps_used: 21, max_depth: 4 } }"#,
    ),
    (
        r#"RenameRefused.lean"#,
        r#"prelude
import Init.Core
variable {P Q : Prop}
example : P ↔ Q := by
  rename P ↔ Q => goal
  sorry
"#,
        r#"elaboration refused source: Failed to find a hypothesis with type"#,
    ),
    (
        r#"ExistsWrongRefused.lean"#,
        r#"prelude
import Init.Core
import Init.NotationExtra
example : ∃ x : Nat, x = 1 := by
  exists 0
"#,
        r#"elaboration refused source: proof script left 1 unsolved goals"#,
    ),
    (
        r#"CasePrimeMissingRefused.lean"#,
        r#"prelude
import Init.Core
example (hp : p) (hq : q) : p ∧ q := by
  constructor
  case' nope => skip
  all_goals assumption
"#,
        r#"elaboration refused source: Case tag `nope` not found."#,
    ),
    (
        r#"RotateWrongRefused.lean"#,
        r#"prelude
import Init.Core
example (hp : p) (hq : q) : p ∧ q := by
  constructor
  rotate_left
  exact hp
  exact hq
"#,
        r#"elaboration refused source: source conversion refused: Rejected { class: NotDefEq, message: "terms are not definitionally equal", consumption: Consumption { steps_used: 21, max_depth: 4 } }"#,
    ),
    (
        r#"Injections.lean"#,
        r#"prelude
import Init.Core
example (a b c d : Nat) (h : Nat.succ a = Nat.succ b) (h2 : Nat.succ c = Nat.succ d) : a = b := by
  injections
  assumption
"#,
        r#"elaboration refused source: tactic has no remaining goal"#,
    ),
    (
        r#"InjectionsClash.lean"#,
        r#"prelude
import Init.Core
example (h : Nat.succ 0 = 0) : False := by
  injections
"#,
        r#"elaboration refused source: proof script left 1 unsolved goals"#,
    ),
];

/// Each program the pin rejects: refused here with this engine's typed reason.
#[test]
fn goal_structuring_tactics_fail_where_the_pin_fails() {
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
const TYPED: &[(&str, &str, i32, &str)] = &[(
    r#"InjectionsNamed.lean"#,
    r#"prelude
import Init.Core
example (a b : Nat) (h : Nat.succ a = Nat.succ b) : b = a := by
  injections k
  exact k.symm
"#,
    1,
    r#"refused source: elaboration refused source: unsupported tactic `Lean.Parser.Tactic.injections`"#,
)];

/// `injections` with names: the pin runs it, and this engine refuses it, typed, rather than
/// guess which names its `injection` leaves unused.
#[test]
fn injection_names_are_refused_typed() {
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
