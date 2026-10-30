//! Tactic-mode `match` and `let rec`, and `refine'`, through the installed drop-in `lean` over
//! `prelude` and `Init.Core` (`Init.WFTactics` for a `match` in `decreasing_by`). The pin's
//! `match` (vendored `Lean/Elab/Tactic/Match.lean`) is `refine (match … with | p => ?rhs …)`,
//! one alternative per pattern group, then `case rhs => tac` for each tactic alternative in
//! order, each closing its goal; `let rec d` is `refine_lift let rec d; ?_`, the continuation
//! the main goal; `refine' e` is `refine e` whose `_`s are new goals too
//! (`holesAsSyntheticOpaque`), tagged `refine'_i`. A goal display this engine cannot name, and
//! a `let rec` by equations, are refused, typed.
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
        "fln-tactic-match-letrec-{label}-{}-{}",
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
        r#"Match.lean"#,
        r#"prelude
import Init.Core
example (n : Nat) : n = n := by
  match n with
  | 0 => rfl
  | k + 1 => rfl
"#,
        r#""#,
    ),
    (
        r#"MatchMulti.lean"#,
        r#"prelude
import Init.Core
def h (x : Nat) : Nat :=
  match x with
  | 0 | 1 => 1
  | x + 2 => x + 1
example : h x > 0 := by
  match x with
  | 0 | 1 => decide
  | x + 2 => exact Nat.zero_lt_succ x
"#,
        r#""#,
    ),
    (
        r#"LetRec.lean"#,
        r#"prelude
import Init.Core
theorem foo : True := by
  let rec f (n : Nat) : Nat :=
    match n with
    | .zero => 0
    | .succ n => f n
  trivial
"#,
        r#""#,
    ),
    (
        r#"LetRecUse.lean"#,
        r#"prelude
import Init.Core
theorem A : True ∧ True := by
  let rec B := trivial
  exact And.intro B B
"#,
        r#""#,
    ),
    (
        r#"RefinePrime.lean"#,
        r#"prelude
import Init.Core
example : Nat → Nat := by
  refine' (fun x => _)
  trace_state
  exact x
"#,
        r#"x : Nat
⊢ Nat
"#,
    ),
    (
        r#"RefinePrimeTwo.lean"#,
        r#"prelude
import Init.Core
example (hp : p) (hq : q) : p ∧ q := by
  refine' ⟨_, _⟩
  trace_state
  exact hp
  exact hq
"#,
        r#"case refine'_1
p q : Prop
hp : p
hq : q
⊢ p

case refine'_2
p q : Prop
hp : p
hq : q
⊢ q
"#,
    ),
    (
        r#"RefinePrimeSynth.lean"#,
        r#"prelude
import Init.Core
example (hp : p) (hq : q) : p ∧ q := by
  refine' ⟨?_, _⟩
  trace_state
  exact hp
  exact hq
"#,
        r#"case refine'_1
p q : Prop
hp : p
hq : q
⊢ p

case refine'_2
p q : Prop
hp : p
hq : q
⊢ q
"#,
    ),
    (
        r#"MatchInDecreasing.lean"#,
        r#"prelude
import Init.WFTactics
axiom testSorry {α : Sort _} : α
def foo (n : Nat)  : Nat := foo (n - 1)
decreasing_by
  skip
  match n with
  | 0 => exact testSorry
  | _ + 1 => exact testSorry
"#,
        r#""#,
    ),
    (
        r#"RefineHoleAssigned.lean"#,
        r#"prelude
import Init.Core
theorem assigned : Exists fun n : Nat => n = 3 := by
  refine ⟨_, rfl⟩
"#,
        r#""#,
    ),
];

/// Each program the pin accepts, run as `name`: the pin's output, which ours must equal.
#[test]
fn tactic_match_let_rec_and_refine_prime_run_as_the_pin_does() {
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
        r#"MatchRefused.lean"#,
        r#"prelude
import Init.Core
example (n : Nat) : n = 0 := by
  match n with
  | 0 => rfl
  | k + 1 => rfl
"#,
        r#"elaboration refused source: source conversion refused: Rejected { class: NotDefEq, message: "terms are not definitionally equal", consumption: Consumption { steps_used: 74, max_depth: 8 } }"#,
    ),
    (
        r#"MatchOpenRefused.lean"#,
        r#"prelude
import Init.Core
example (n : Nat) : n = n := by
  match n with
  | 0 => skip
  | k + 1 => rfl
"#,
        r#"elaboration refused source: proof script left 1 unsolved goals"#,
    ),
    (
        r#"RefineHoleRefused.lean"#,
        r#"prelude
import Init.Core
example (hp : p) (hq : q) : p ∧ q := by
  refine ⟨_, _⟩
  exact hp
  exact hq
"#,
        r#"elaboration refused source: refine left a placeholder it could not synthesize"#,
    ),
    (
        r#"RefineWitnessHole.lean"#,
        r#"prelude
import Init.Core
theorem witness : Exists fun n : Nat => n = 3 := by
  refine ⟨_, ?_⟩
  rfl
"#,
        r#"elaboration refused source: refine left a placeholder it could not synthesize"#,
    ),
    (
        r#"RefineHeadHoles.lean"#,
        r#"prelude
import Init.Core
theorem head : Exists fun F : Type → Type => Exists fun β : Type => F β = Option Nat := by
  refine ⟨_, _, ?_⟩
  rfl
"#,
        r#"elaboration refused source: refine left a placeholder it could not synthesize"#,
    ),
];

/// Each program the pin rejects (a false alternative, an alternative left open, a `_` that
/// `refine` cannot make a goal): refused here with this engine's typed reason.
#[test]
fn tactic_match_let_rec_and_refine_prime_fail_where_the_pin_fails() {
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
        r#"MatchTrace.lean"#,
        r#"prelude
import Init.Core
example (n : Nat) : n + 0 = n := by
  match n with
  | 0 => trace_state; rfl
  | k + 1 => trace_state; rfl
"#,
        5,
        r#"not implemented: the original inaccessible goal name is unavailable"#,
    ),
    (
        r#"LetRecTrace.lean"#,
        r#"prelude
import Init.Core
example : Nat := by
  let rec go : Nat → Nat
    | 0 => 0
    | k + 1 => go k
  trace_state
  exact go 3
"#,
        1,
        r#"refused source: elaboration refused source: recursive call is not on an immediate recursive constructor field"#,
    ),
];

/// Forms the pin runs and this engine refuses, typed: a goal display naming a local its
/// `match` keeps inaccessible, and a `let rec` defined by equations inside a tactic block. Its
/// equations now expand as the pin's `expandLetEqnsDecl` does, and the structural-recursion
/// check then refuses the tactic block's `go k` (a term-level `let rec` of the same shape is
/// admitted: `fln`'s `local_equations_compute_as_the_pin_expands_them`).
#[test]
fn unsupported_match_and_let_rec_forms_are_refused_typed() {
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
