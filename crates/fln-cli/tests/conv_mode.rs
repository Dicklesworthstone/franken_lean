//! Conversion mode (`conv`) through the installed drop-in `lean`, over `prelude` and the smallest
//! `Init` modules that have it (`Init.Conv`, `Init.Data.Nat.Basic`, `Init.SimpLemmas`, and
//! `Init.NotationExtra` for `calc`). The pin's
//! conv mode (vendored `Lean/Elab/Tactic/Conv/*.lean`, syntax and macros in `Init/Conv.lean`)
//! makes the conv goal `lhs = ?rhs`, shown as `| lhs`; each conv tactic replaces it by goals
//! closing it with an equation, and the block's end closes what is left by reflexivity and
//! replaces the target through `Eq.mpr` (`conv at h`: the hypothesis through `Eq.mp`), then tries
//! `with_reducible rfl`.
//!
//! The programs cover `lhs`/`rhs`/`arg i`/`arg @i`/`arg -i`/`arg 0`/`fun`, `enter [..]` with
//! indices, names and patterns, `congr` (with its case tags, over-applied functions and
//! implications), `ext`/`intro` into `∀`, `fun` and `let`, `pattern` (one occurrence, a list,
//! `*`) and `conv in`, `conv at h`, `rw`/`rewrite`, `change`, `zeta`, `unfold`, `simp only`,
//! `dsimp only`, `simp`, `clear`, `apply`, `tactic =>`, `rfl`, `skip`, `done`, `·`, `{ }`,
//! `( )`, `first`, `try`, `repeat`, `fail_if_success`, nested `conv =>` blocks, `calc` (with a
//! first step that has no proof), `rw` abstracting as the pin's `kabstract`, and goal display
//! through `trace_state`; then failures the pin reports, and a conv tactic this engine refuses,
//! typed.
//!
//! Every program was run through the pinned `lean` v4.32.0 with the same header first
//! (2026-10-24), and its output is compared with the pinned binary's again when that is present.
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
        .filter(|lib| lib.join("Init/Conv.olean").is_file());
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
        "fln-conv-mode-{label}-{}-{}",
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

/// Each program the pin accepts, run as `name`: the pin's output, which ours must equal.
#[test]
fn conv_mode_runs_as_the_pin_does() {
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

/// Conv failures the pin reports: the pin's exit 1 and its error, which this engine refuses with,
/// typed, in the pin's words (without the expression or goals the pin appends).
#[test]
fn conv_failures_are_refused_as_the_pin_reports_them() {
    let Some(lib) = pinned_lib() else {
        return;
    };
    let root = workspace("refused");
    for (name, program, message) in REFUSED {
        std::fs::write(root.join(name), program).unwrap();
        if let Some((code, stdout)) = pinned(&lib, &root, name) {
            assert_eq!(code, 1, "{name}: the pin moved: {stdout}");
            assert!(
                stdout.contains(&format!("error: {message}")),
                "{name}: the pin moved: {stdout}"
            );
        }
        let (code, stdout, stderr) = ours(&lib, &root, name);
        assert_eq!(code, 1, "{name}: {stdout}{stderr}");
        assert!(
            stderr
                .trim_end()
                .ends_with(&format!("refused source: {message}")),
            "{name}: {stderr}"
        );
    }
}

/// `delta` is a conv tactic the pin runs and this engine does not: it is refused, typed, rather
/// than approximated by another unfolding.
#[test]
fn an_unimplemented_conv_tactic_is_refused_typed() {
    let Some(lib) = pinned_lib() else {
        return;
    };
    let root = workspace("unsupported");
    let name = "Delta.lean";
    std::fs::write(root.join(name), DELTA).unwrap();
    if let Some((code, stdout)) = pinned(&lib, &root, name) {
        assert_eq!((code, stdout.as_str()), (0, ""), "the pin moved");
    }
    let (code, stdout, stderr) = ours(&lib, &root, name);
    assert_eq!(code, 1, "{stdout}{stderr}");
    assert!(
        stderr.contains("unsupported tactic `Lean.Parser.Tactic.Conv.delta`"),
        "{stderr}"
    );
}

/// Conv `rw` selects and abstracts occurrences as `rw` does, by the pin's `kabstract` (conv
/// `rewrite` is the same `MVarId.rewrite`, vendored Lean/Meta/Tactic/Rewrite.lean:47): every
/// instance at reducible transparency with offsets, and no instance the pin does not find. Each
/// program the pin rejects, with its error, is refused here with this engine's typed reason.
#[test]
fn conv_rewrite_abstracts_as_the_pins_kabstract() {
    let Some(lib) = pinned_lib() else {
        return;
    };
    let root = workspace("kabstract");
    for (name, program, pin_error, reason) in REWRITE_REFUSED {
        std::fs::write(root.join(name), program).unwrap();
        if let Some((code, stdout)) = pinned(&lib, &root, name) {
            assert_eq!(code, 1, "{name}: the pin moved: {stdout}");
            assert!(
                stdout.contains(&format!("error: {pin_error}")),
                "{name}: the pin moved: {stdout}"
            );
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

/// `(name, program, the pin's error, this engine's reason)`. `AllInstances`: the pin abstracts
/// `f (Nat.succ n)` with `f (n + 1)` (offsets), so the conv block closes the goal and `sorry`
/// has none; abstracting only exact copies would leave a goal for `sorry` and accept.
const REWRITE_REFUSED: &[(&str, &str, &str, &str)] = &[
    (
        "AllInstances.lean",
        r#"prelude
import Init.Conv
import Init.Data.Nat.Basic
import Init.SimpLemmas
import Init.NotationExtra
example (f : Nat → Nat) (n : Nat) (h : f (n + 1) = 0) : f (Nat.succ n) + f (n + 1) = 0 := by
  conv =>
    lhs
    rw [h]
  sorry
"#,
        "No goals to be solved",
        "tactic has no remaining goal",
    ),
    (
        "NoOffsetInstance.lean",
        r#"prelude
import Init.Conv
import Init.Data.Nat.Basic
import Init.SimpLemmas
import Init.NotationExtra
example (f : Nat → Nat) (n : Nat) (h : f n = 0) : f (n + 0) = 0 := by
  conv => lhs; rw [h]
"#,
        "Tactic `rewrite` failed: Did not find an occurrence of the pattern",
        "rewrite found no matching occurrence in the goal",
    ),
    (
        "LocalOnly.lean",
        r#"prelude
import Init.Conv
import Init.Data.Nat.Basic
import Init.SimpLemmas
import Init.NotationExtra
example (m n : Nat) (h : m = n) : m + 0 = n := by
  conv => lhs; rw [h]
"#,
        "unsolved goals",
        "proof script left 1 unsolved goals",
    ),
];

const DELTA: &str = r#"prelude
import Init.Conv
import Init.Data.Nat.Basic
import Init.SimpLemmas
import Init.NotationExtra
def double (n : Nat) : Nat := n + n

example (a : Nat) : double a = a + a := by
  conv =>
    lhs
    delta double
"#;

const ACCEPTED: &[(&str, &str, &str)] = &[
    (
        "Lhs.lean",
        r#"prelude
import Init.Conv
import Init.Data.Nat.Basic
import Init.SimpLemmas
import Init.NotationExtra
example (x y : Nat) (h : x = y) : x + 0 = y + 0 := by
  conv =>
    lhs
    trace_state
    rw [h]
"#,
        r#"x y : Nat
h : x = y
| x + 0
"#,
    ),
    (
        "Congr.lean",
        r#"prelude
import Init.Conv
import Init.Data.Nat.Basic
import Init.SimpLemmas
import Init.NotationExtra
theorem congr_good {x y : Nat} : x + y = y + x := by
  have I : True := True.intro
  conv =>
    congr
    trace_state
    . rw [Nat.add_comm]
    . rfl
"#,
        r#"case a
x y : Nat
I : True
| x + y

case a
x y : Nat
I : True
| y + x
"#,
    ),
    (
        "AtIntro.lean",
        r#"prelude
import Init.Conv
import Init.Data.Nat.Basic
import Init.SimpLemmas
import Init.NotationExtra
theorem ex1 : a * 2 = 2 * a := by
  have h : ∀ (a b : Nat), a * b = a * b := by
    intros; rfl
  conv at h =>
    intro a b; lhs; rw [Nat.mul_comm]
  trace_state
  exact h 2 a

theorem ex2 : a * 2 = 2 * a := by
  have h : (fun x y => x * y) = Nat.mul := by
    rfl
  conv at h =>
    lhs; intro x y; rw [Nat.mul_comm]
  trace_state
  exact congrFun (congrFun h 2) a
"#,
        r#"a : Nat
h : ∀ (a b : Nat), b * a = a * b
⊢ a * 2 = 2 * a
a : Nat
h : (fun x y => y * x) = Nat.mul
⊢ a * 2 = 2 * a
"#,
    ),
    (
        "Funext.lean",
        r#"prelude
import Init.Conv
import Init.Data.Nat.Basic
import Init.SimpLemmas
import Init.NotationExtra
example : (fun (u : Nat) => u + 0) = id := by
  conv =>
    lhs
    intro u
    trace_state
    change u
  rfl

example (a b : Nat) (h : a = b) : (fun x : Nat => x + a) = (fun x => x + b) := by
  conv =>
    lhs
    ext y
    trace_state
    rw [h]
"#,
        r#"u : Nat
| u + 0
a b : Nat
h : a = b
y : Nat
| y + a
"#,
    ),
    (
        "Forall.lean",
        r#"prelude
import Init.Conv
import Init.Data.Nat.Basic
import Init.SimpLemmas
import Init.NotationExtra
example (P : Nat → Prop) (q : Prop) (h : ∀ n, P n = q) (hq : q) :
    ∀ n, P n := by
  conv => enter [n]; rw [h]
  trace_state
  exact fun _ => hq

example (p : Prop) (P : p → Prop) (q : Prop) (h : ∀ n, P n = q) (hq : q) :
    ∀ n, P n := by
  conv => enter [n]; rw [h]
  trace_state
  exact fun _ => hq

example (p q : Prop) (h : p = q) (hq : q) : ∀ x : Nat, x = x → p := by
  conv =>
    ext x hx
    trace_state
    rw [h]
  intro _ _
  exact hq
"#,
        r#"P : Nat → Prop
q : Prop
h : ∀ (n : Nat), P n = q
hq : q
⊢ ∀ (n : Nat), q
p : Prop
P : p → Prop
q : Prop
h : ∀ (n : p), P n = q
hq : q
⊢ p → q
p q : Prop
h : p = q
hq : q
x : Nat
hx : x = x
| p
"#,
    ),
    (
        "Implies.lean",
        r#"prelude
import Init.Conv
import Init.Data.Nat.Basic
import Init.SimpLemmas
import Init.NotationExtra
example (p₁ p₂ q : Prop) (h : p₁ ↔ p₂) : (p₁ → q) ↔ (p₂ → q) := by
  conv => enter [1, 1]
  conv =>
    enter [1, 1]
    trace_state
    rw [h]

example (p q₁ q₂ : Prop) (h : q₁ ↔ q₂) : (p → q₁) ↔ (p → q₂) := by
  conv => enter [1, 2]
  conv =>
    enter [1, 2]
    rw [h]

example (p q : Prop) (h : p = q) : (p → p) = (q → q) := by
  conv =>
    lhs
    congr
    trace_state
    · rw [h]
    · rw [h]
"#,
        r#"p₁ p₂ q : Prop
h : p₁ ↔ p₂
| p₁
case h₁
p q : Prop
h : p = q
| p

case h₂
p q : Prop
h : p = q
| p
"#,
    ),
    (
        "DependentPi.lean",
        r#"prelude
import Init.Conv
import Init.Data.Nat.Basic
import Init.SimpLemmas
import Init.NotationExtra
example : ∀ (i : Nat) (h : i < 10), (⟨i, h⟩ : Fin 10).val = i := by
  conv =>
    enter [2,1]
    trace_state
  conv =>
    enter [2,2]
    trace_state
  intro i h
  rfl
"#,
        r#"i✝ : Nat
| i✝ < 10
a✝¹ : Nat
a✝ : a✝¹ < 10
| ↑⟨a✝¹, ⋯⟩ = a✝¹
"#,
    ),
    (
        "Explicit.lean",
        r#"prelude
import Init.Conv
import Init.Data.Nat.Basic
import Init.SimpLemmas
import Init.NotationExtra
example (f : {_ : Nat} → Nat → Nat) (h : n = n') : @f n m = @f n' m := by
  conv =>
    enter [1, @1]
    rw [h]

example (f : {_ : Nat} → Nat → Nat) (h : m = m') : @f n m = @f n m' := by
  conv =>
    enter [1, @2]
    rw [h]

example (a b : Nat) (h : b = a) : a + b = a + a := by
  conv =>
    enter [-2, -1]
    trace_state
    rw [h]
"#,
        r#"a b : Nat
h : b = a
| b
"#,
    ),
    (
        "OverApplied.lean",
        r#"prelude
import Init.Conv
import Init.Data.Nat.Basic
import Init.SimpLemmas
import Init.NotationExtra
example (a b : Nat) (g : {α : Type} → α → α) (f : Nat → Nat) (h : a = b) : g f a = g f b := by
  conv =>
    lhs
    congr
    trace_state
    · rfl
    · rw [h]

example (a b : Nat) (g : {α : Type} → α → α) (f : Nat → Nat) (h : a = b) : g f a = g f b := by
  conv =>
    conv => enter [1,2]; trace_state
    conv => enter [1,1]; trace_state
    conv => enter [1,@3]; trace_state
    conv => fail_if_success enter [1,@1]
    rw [h]
"#,
        r#"case a
a b : Nat
g : {α : Type} → α → α
f : Nat → Nat
h : a = b
| f

case a
a b : Nat
g : {α : Type} → α → α
f : Nat → Nat
h : a = b
| a
a b : Nat
g : {α : Type} → α → α
f : Nat → Nat
h : a = b
| a
a b : Nat
g : {α : Type} → α → α
f : Nat → Nat
h : a = b
| f
a b : Nat
g : {α : Type} → α → α
f : Nat → Nat
h : a = b
| a
"#,
    ),
    (
        "Repeat.lean",
        r#"prelude
import Init.Conv
import Init.Data.Nat.Basic
import Init.SimpLemmas
import Init.NotationExtra
example : (fun x y => (0 + x) + (0 + y)) = Nat.add := by
  conv =>
    lhs
    intro x y
    repeat rw [Nat.zero_add]
    trace_state
  rfl
"#,
        r#"x y : Nat
| x + y
"#,
    ),
    (
        "PatternBinders.lean",
        r#"prelude
import Init.Conv
import Init.Data.Nat.Basic
import Init.SimpLemmas
import Init.NotationExtra
def test : (fun x : Nat => id (id x)) = fun x => x := by
  conv in (id _) =>
    trace_state
    simp

def f (x : Nat) := x

def test2 : (fun x => f x)
           =
           (fun x : Nat =>
             have foo := fun y => id (id y)
             foo x) := by
  conv =>
    pattern (id _)
    trace_state
    simp
    trace_state
  rfl
"#,
        r#"x : Nat
| id (id x)
PatternBinders.lean:6:0: warning: Definition `test` is a proposition; use `theorem` instead of `def`

Note: This linter can be disabled with `set_option linter.defProp false`
x y : Nat
| id (id y)
x y : Nat
| y
PatternBinders.lean:13:0: warning: Definition `test2` is a proposition; use `theorem` instead of `def`

Note: This linter can be disabled with `set_option linter.defProp false`
"#,
    ),
    (
        "Occurrences.lean",
        r#"prelude
import Init.Conv
import Init.Data.Nat.Basic
import Init.SimpLemmas
import Init.NotationExtra
example (a b : Nat) : a + a = b := by
  conv =>
    pattern (occs := *) a
    trace_state
  sorry

example (a b : Nat) : a + a + a = b + b + b := by
  conv =>
    pattern (occs := 1 2 3) a
    trace_state
  sorry

example (a b : Nat) (h : a = b) : a + a + a = b + b + b := by
  conv =>
    pattern (occs := 3 1) a
    trace_state
    rw [h]
  trace_state
  rw [h]
"#,
        r#"a b : Nat
| a
Occurrences.lean:6:0: warning: declaration uses `sorry`
a b : Nat
| a

a b : Nat
| a

a b : Nat
| a
Occurrences.lean:12:0: warning: declaration uses `sorry`
a b : Nat
h : a = b
| a

a b : Nat
h : a = b
| a
a b : Nat
h : a = b
⊢ a + a + b = b + b + b
"#,
    ),
    (
        "ConvIn.lean",
        r#"prelude
import Init.Conv
import Init.Data.Nat.Basic
import Init.SimpLemmas
import Init.NotationExtra
example (a b c : Nat) (h : a = b) : c + a = c + b := by
  conv in a => rw [h]

example (a b c : Nat) (h : a = b) (h2 : c + a = 0) : c + b = 0 := by
  conv at h2 in a => rw [h]
  trace_state
  exact h2
"#,
        r#"a b c : Nat
h : a = b
h2 : c + b = 0
⊢ c + b = 0
"#,
    ),
    (
        "Lets.lean",
        r#"prelude
import Init.Conv
import Init.Data.Nat.Basic
import Init.SimpLemmas
import Init.NotationExtra
def g (n : Nat) := n + 1

example (k : Nat) (h : let x := 10; g x = k) : 11 = k := by
  have : g 10 = 11 := rfl
  conv at h => zeta; rw [this]
  trace_state
  exact h

example (k y : Nat) (h : let x := y; g (0+x) = k) : g y = k := by
  conv at h => ext x; lhs; arg 1; rw [Nat.zero_add]
  trace_state
  exact h

example (f : Nat → Nat) (y : Nat) (h : let x := y; let z := y + 1; f (0+x) = 0+z) : f y = y + 1 := by
  conv at h => enter [x, z, 1, 1]; rw [Nat.zero_add]
  conv at h => enter [x, z, 2]; rw [Nat.zero_add]
  trace_state
  exact h
"#,
        r#"k : Nat
h : 11 = k
this : g 10 = 11
⊢ 11 = k
k y : Nat
h :
  let x := y;
  g x = k
⊢ g y = k
f : Nat → Nat
y : Nat
h :
  let x := y;
  let z := y + 1;
  f x = z
⊢ f y = y + 1
"#,
    ),
    (
        "Clear.lean",
        r#"prelude
import Init.Conv
import Init.Data.Nat.Basic
import Init.SimpLemmas
import Init.NotationExtra
example (α : Type) (x y z : α) (h₁ : x = y) (h₂ : y = z) : x = y ∧ y = z := by
  conv =>
    clear h₁
    trace_state
    lhs
    clear h₂
    trace_state
  trace_state
  exact And.intro h₁ h₂

example (α : Type) (x y z : α) (h₁ : x = y) (h₂ : y = z) : x = y ∧ y = z := by
  conv =>
    rhs
    clear x h₁
    trace_state
    rhs
    clear h₂ y
    trace_state
  exact And.intro h₁ h₂
"#,
        r#"α : Type
x y z : α
h₂ : y = z
| x = y ∧ y = z
α : Type
x y z : α
| x = y
α : Type
x y z : α
h₁ : x = y
h₂ : y = z
⊢ x = y ∧ y = z
α : Type
y z : α
h₂ : y = z
| y = z
α : Type
z : α
| z
"#,
    ),
    (
        "Navigation.lean",
        r#"prelude
import Init.Conv
import Init.Data.Nat.Basic
import Init.SimpLemmas
import Init.NotationExtra
def double (n : Nat) : Nat := n + n

example (f g : Nat → Nat → Nat) (a : Nat) (h : f = g) : f a a = g a a := by
  conv =>
    lhs
    arg 0
    trace_state
    rw [h]

example (f : Nat → Nat → Nat) (a b : Nat) (h : a = b) : f a b = f b b := by
  conv =>
    lhs
    fun
    trace_state
    arg 1
    rw [h]

example (a : Nat) : double a = a + a := by
  conv =>
    lhs
    unfold double
    trace_state

example (a b : Nat) (h : a = b) : (let x := a; x + 1) = b + 1 := by
  conv =>
    lhs
    zeta
    trace_state
    rw [h]
"#,
        r#"f g : Nat → Nat → Nat
a : Nat
h : f = g
| f
f : Nat → Nat → Nat
a b : Nat
h : a = b
| f a
a : Nat
| a + a
a b : Nat
h : a = b
| a + 1
"#,
    ),
    (
        "Combinators.lean",
        r#"prelude
import Init.Conv
import Init.Data.Nat.Basic
import Init.SimpLemmas
import Init.NotationExtra
example (a b : Nat) (h : a = b) : a + 0 = b := by
  conv =>
    lhs
    first
      | rw [Nat.zero_add]
      | rw [Nat.add_zero]
    trace_state
  exact h

example (a b : Nat) (h : a = b) : a = b := by
  conv =>
    try rw [Nat.zero_add]
    rw [h]

example (a b : Nat) (h : a = b) : a + b = b + b := by
  conv =>
    lhs
    { arg 1
      rw [h] }
  trace_state

example (a b : Nat) (h : a = b) : a + b = b + b := by
  conv =>
    (lhs; arg 1)
    rw [h]
"#,
        r#"a b : Nat
h : a = b
| a

"#,
    ),
    (
        "Nested.lean",
        r#"prelude
import Init.Conv
import Init.Data.Nat.Basic
import Init.SimpLemmas
import Init.NotationExtra
example (a b : Nat) (h : a = b) : (a + 0) + 0 = b := by
  conv =>
    lhs
    conv =>
      arg 1
      rw [Nat.add_zero]
    trace_state
    rw [Nat.add_zero, h]

def twice : Nat → Nat := fun n => 2*n

def foo1 : (fun x : Nat => id (twice (id x))) = twice := by
  conv in (id _) =>
    trace_state
    conv =>
      enter [1,1]
      trace_state
      simp
      trace_state
    trace_state
  rfl
"#,
        r#"a b : Nat
h : a = b
| a + 0
x : Nat
| id (twice (id x))
x : Nat
| id x
x : Nat
| x
x : Nat
| id (twice x)
Nested.lean:17:0: warning: Definition `foo1` is a proposition; use `theorem` instead of `def`

Note: This linter can be disabled with `set_option linter.defProp false`
"#,
    ),
    (
        "Tactic.lean",
        r#"prelude
import Init.Conv
import Init.Data.Nat.Basic
import Init.SimpLemmas
import Init.NotationExtra
example (a b : Nat) (h : b = a) : a + 0 = b := by
  conv =>
    lhs
    apply Nat.add_zero
  exact h.symm

example (a b : Nat) (h : a = b) : a + 0 = b := by
  conv =>
    lhs
    tactic => exact Nat.add_zero a
  exact h

axiom div_self (x : Nat) : x ≠ 0 → x / x = 1

example (h : x ≠ 0) : x / x + x = x.succ := by
  conv =>
    lhs
    arg 1
    rw [div_self]
    rfl
    tactic => assumption
    done
  show 1 + x = x.succ
  rw [Nat.succ_add, Nat.zero_add]
"#,
        r#""#,
    ),
    (
        "Simp.lean",
        r#"prelude
import Init.Conv
import Init.Data.Nat.Basic
import Init.SimpLemmas
import Init.NotationExtra
def double (n : Nat) : Nat := n + n

example (a : Nat) : 0 + a = a := by
  conv =>
    lhs
    simp only [Nat.zero_add]
    trace_state

example (a : Nat) : double a = a + a := by
  conv =>
    lhs
    dsimp only [double]
    trace_state

example (y : Nat) : (fun x => x + y = 0) = (fun x => False) := by
  conv =>
    conv =>
      lhs
      intro x
      rw [Nat.add_comm]
      trace_state
    trace_state
  trace_state
  sorry
"#,
        r#"a : Nat
| a
a : Nat
| a + a
y x : Nat
| y + x = 0
y : Nat
| (fun x => y + x = 0) = fun x => False
y : Nat
⊢ (fun x => y + x = 0) = fun x => False
Simp.lean:20:0: warning: declaration uses `sorry`
"#,
    ),
    (
        "Calc.lean",
        r#"prelude
import Init.Conv
import Init.Data.Nat.Basic
import Init.SimpLemmas
import Init.NotationExtra
example (P : Nat → Prop) (h : P 4) : P ((1 + 1) + 2) := by
  conv => arg 1; calc
    (1 + 1) + 2
    _ = 2 + 2 := by simp
    _ = 4 := by simp
  exact h

example (a b c : Nat) (h1 : a = b) (h2 : b = c) (P : Nat → Prop) (h : P c) : P a := by
  conv =>
    arg 1
    calc a = b := h1
      _ = c := h2
  exact h

example (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c :=
  calc a
    _ = b := h1
    _ = c := h2
"#,
        r#""#,
    ),
    (
        "Kabstract.lean",
        r#"prelude
import Init.Conv
import Init.Data.Nat.Basic
import Init.SimpLemmas
import Init.NotationExtra
example (f : Nat → Nat) (n : Nat) (h : f (n + 1) = 0) : f (Nat.succ n) + f (n + 1) = 0 := by
  conv =>
    lhs
    rw [h]
    trace_state

example (h : (2:Nat) = 3) : (2:Nat) + 2 = 3 + 3 := by
  conv => lhs; rw [h]

example (a b : Nat) (h : a = b) : a + a = b + b := by
  conv => lhs; rw [h]

example (f : Nat → Nat) (h : f 6 = 0) : f (5 + 1) = 0 := by
  conv => lhs; rw [h]

example (a : Nat) : (a = a) = True := by
  conv => lhs; simp only []
"#,
        r#"f : Nat → Nat
n : Nat
h : f (n + 1) = 0
| 0 + 0
"#,
    ),
];

const REFUSED: &[(&str, &str, &str)] = &[
    (
        "ArgBounds.lean",
        r#"prelude
import Init.Conv
import Init.Data.Nat.Basic
import Init.SimpLemmas
import Init.NotationExtra
example (a b : Nat) (h : a = b) : a + b = b + b := by
  conv =>
    lhs
    arg 3
"#,
        r#"invalid `arg` tactic, application has 2 explicit argument(s) but the index is out of bounds"#,
    ),
    (
        "PatternMissing.lean",
        r#"prelude
import Init.Conv
import Init.Data.Nat.Basic
import Init.SimpLemmas
import Init.NotationExtra
example (a b : Nat) : a + b = b + b := by
  conv =>
    pattern (b + a)
"#,
        r#"'pattern' conv tactic failed, pattern was not found"#,
    ),
    (
        "Unsolved.lean",
        r#"prelude
import Init.Conv
import Init.Data.Nat.Basic
import Init.SimpLemmas
import Init.NotationExtra
axiom div_self (x : Nat) : x ≠ 0 → x / x = 1

example (x : Nat) : x / x = 1 := by
  conv =>
    lhs
    rw [div_self]
"#,
        r#"Tactic `conv` failed: There are unsolved goals"#,
    ),
    (
        "CongrLeaf.lean",
        r#"prelude
import Init.Conv
import Init.Data.Nat.Basic
import Init.SimpLemmas
import Init.NotationExtra
example (a : Nat) : a = a := by
  conv =>
    lhs
    congr
"#,
        r#"invalid 'congr' conv tactic, application or implication expected"#,
    ),
];
