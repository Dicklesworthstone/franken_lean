//! `f a ..` (`Term.ellipsis`) through the installed drop-in `lean`, over `prelude` headers. In
//! term position each parameter left after the written arguments becomes a natural hole, where a
//! plain under-application would eta-expand or stop; an `optParam` still takes its default unless
//! `@` was written (vendored `Lean/Elab/App.lean:809-857`, `ElabAppArgs.processExplicitArg`). A
//! strict implicit with nothing left to process still ends the application (`:891-897`). In a
//! pattern every remaining explicit argument is `_`, `optParam` fields included
//! (`Lean/Elab/PatternVar.lean:360-366`, `App.lean:810-825`). `x.f ..` has no arguments to
//! process, so a strict-implicit receiver is not instantiated before field lookup
//! (`App.lean:1850`).
//! `crates/fln/tests/source_ellipsis.rs` covers the term half through the library; this target
//! drives the installed door, and is where constructor patterns are covered.
//!
//! Every program was run through the pinned `lean` v4.32.0 with the same header first
//! (2026-10-23), and is compared with the pinned binary's output again when that is present.
//! FrankenLean refuses a whole command where the pin reports an error inside it, so a refusal is
//! compared by the command it names, not by the pin's message.
#![forbid(unsafe_code)]
use std::path::{Path, PathBuf};
use std::process::Command;

/// The two accepted commands of bead `fln-ellipsis-argument-elaboration-wj22`, over the module
/// that declares `Nat.add_comm`.
const GAP: &str = "prelude
import Init.Data.Nat.Basic
theorem t (a b : Nat) : a + b = b + a := Nat.add_comm ..
#check (Nat.add_comm .. : 1 + 2 = 2 + 1)
";

/// The pin's output for [`GAP`]: the holes are solved by the ascribed type.
const GAP_EXPECTED: &str = "Nat.add_comm 1 2 : 1 + 2 = 2 + 1\n";

/// The uses of `..` in the upstream tests `elab/2073.lean` (a `calc` step, whose holes the step's
/// relation solves) and `elab/4462.lean` (`Matrix ..` as an ascription's type), under a header.
const UPSTREAM: &str = "prelude
import Init.Data.Nat.Basic
import Init.NotationExtra
def Commute (a b : Nat) := a * b = b * a

example : Commute m n :=
  calc m * n = n * m := Nat.mul_comm ..

def Matrix (α β R : Type) := α → β → R

instance [DecidableEq α] : OfNat (Matrix α α Nat) 1 where
  ofNat x y := if x = y then 1 else 0

example [DecidableEq α] (x y : α) : (1 : Matrix α α Nat) x y = (1 : Matrix ..) x y := rfl
";

/// `..` with and without written arguments, after `@`, over an `optParam` (its default is taken,
/// `false` for `SourceInfo.synthetic`'s `canonical`), with a named argument, after field
/// notation, and as a type (`Mat ..`).
const TERMS: &str = "prelude
import Init.Core
axiom ac (n m : Nat) : n + m = m + n
theorem t (a b : Nat) : a + b = b + a := ac ..
#check (ac .. : 1 + 2 = 2 + 1)
#check (ac 1 .. : 1 + 2 = 2 + 1)
theorem t2 (a b : Nat) : a + b = b + a := ac a ..
theorem t3 (a b : Nat) : a + b = b + a := @ac ..
theorem t4 (a b : Nat) (h : a = b) : b = a := Eq.symm h ..
theorem u : (3 : Nat) = 3 := @Eq.refl ..
theorem pick (a : Nat) (_b : Nat := 7) : a = a := rfl
theorem p1 : (3 : Nat) = 3 := pick ..
theorem p2 (n : Nat) : n = n := pick n ..
theorem s1 : Lean.SourceInfo.synthetic ⟨0⟩ ⟨1⟩ .. = Lean.SourceInfo.synthetic ⟨0⟩ ⟨1⟩ false := rfl
def Mat (α β R : Type) := α → β → R
example (x : Mat Nat Nat Nat) : Nat := (x : Mat ..) 1 2
def three (_a : Nat) (_b : Nat) (c : Nat) : Nat := c
example : three 2 1 3 = 3 := @Eq.refl Nat (three (_b := 1) 2 ..)
structure P where
  x : Nat
  y : Nat
def P.add (p : P) (k : Nat) (_j : Nat := 0) : Nat := p.x + k
example (p : P) : p.add 5 = p.x + 5 := @Eq.refl Nat (p.add ..)
";

/// The pin's output for [`TERMS`].
const TERMS_EXPECTED: &str = "ac 1 2 : 1 + 2 = 2 + 1
ac 1 2 : 1 + 2 = 2 + 1
";

/// `..` in patterns: under a relative and an absolute head, after a written prefix, nested, beside
/// the same constructor written in full, against a catch-all, a numeral, in a second column, under
/// a named pattern, in a `match`, a `fun` and a structural recursion, and over
/// `SourceInfo.synthetic`'s `optParam` field `canonical`.
const PATTERNS: &str = "prelude
import Init.Core
def isCons : List Nat → Bool
  | .nil => false
  | .cons .. => true
theorem isCons1 : isCons (List.cons 1 List.nil) = true := rfl
def head0 : List Nat → Nat
  | .cons a .. => a
  | _ => 0
theorem head01 : head0 (List.cons 7 List.nil) = 7 := rfl
def isCons' : List Nat → Bool
  | List.cons .. => true
  | List.nil => false
theorem isCons'1 : isCons' List.nil = false := rfl
def second : List Nat → Nat
  | .cons _ (.cons b ..) => b
  | .cons .. => 1
  | .nil => 0
theorem second1 : second (List.cons 1 (List.cons 5 List.nil)) = 5 := rfl
theorem second2 : second (List.cons 1 List.nil) = 1 := rfl
def g (xs : List Nat) : Nat :=
  match xs with
  | .cons x .. => x
  | .nil => 0
theorem g1 : g (List.cons 9 List.nil) = 9 := rfl
def isSyn : Lean.SourceInfo → Bool
  | .synthetic .. => true
  | _ => false
theorem isSyn1 : isSyn (Lean.SourceInfo.synthetic ⟨0⟩ ⟨1⟩) = true := rfl
theorem isSyn2 : isSyn Lean.SourceInfo.none = false := rfl
def canon : Lean.SourceInfo → Bool
  | Lean.SourceInfo.synthetic _ _ c => c
  | .original .. => false
  | .none .. => false
theorem canon1 : canon (Lean.SourceInfo.synthetic ⟨0⟩ ⟨1⟩ true) = true := rfl
def start : Lean.SourceInfo → Nat
  | .synthetic p .. => p.byteIdx
  | .original _ p .. => p.byteIdx
  | .none => 0
theorem start1 : start (Lean.SourceInfo.synthetic ⟨4⟩ ⟨5⟩) = 4 := rfl
def isPos : Nat → Bool
  | 0 => false
  | .succ .. => true
theorem isPos1 : isPos 3 = true := rfl
def both : List Nat → List Nat → Nat
  | .cons .., .nil => 1
  | .nil, .cons .. => 2
  | _, _ => 0
theorem both1 : both (List.cons 1 List.nil) List.nil = 1 := rfl
theorem both2 : both List.nil List.nil = 0 := rfl
def whole : List Nat → List Nat
  | xs@(.cons ..) => xs
  | .nil => List.nil
theorem whole1 : whole (List.cons 2 List.nil) = List.cons 2 List.nil := rfl
def lam : List Nat → Nat := fun
  | .cons .. => 1
  | .nil => 0
theorem lam1 : lam (List.cons 2 List.nil) = 1 := rfl
def len : List Nat → Nat
  | .cons _ xs .. => len xs + 1
  | .nil .. => 0
theorem len1 : len (List.cons 2 (List.cons 3 List.nil)) = 2 := rfl
";

/// Programs the pin refuses, each with the command FrankenLean refuses, its reason, and the pin's
/// first error line. The first is the bead's third command: `Eq.symm`'s proof argument is a hole
/// nothing solves. `..` does not eta-expand, an `optParam` after `@` is a hole too, a pattern
/// cannot write more arguments than the constructor has, `..` stands only last, a strict
/// implicit still ends an application with nothing left to process, and a receiver whose type
/// starts with a strict implicit is looked up as a function under `x.f ..`, as without arguments.
const REFUSALS: &[(&str, &str, &str, &str)] = &[
    (
        "prelude
import Init.Core
example (a b : Nat) (h : a = b) : b = a := Eq.symm ..
",
        "command 0, byte 25:",
        "left 1 unresolved metavariables",
        "3:43: error: don't know how to synthesize implicit argument `h`",
    ),
    (
        "prelude
import Init.Core
theorem t (a b : Nat) : a = b → b = a := Eq.symm ..
",
        "command 0, byte 25:",
        "",
        "3:41: error: Type mismatch",
    ),
    (
        "prelude
import Init.Core
theorem pick (a : Nat) (_b : Nat := 7) : a = a := rfl
theorem p1 : (3 : Nat) = 3 := @pick ..
",
        "command 1, byte 79:",
        "left 1 unresolved metavariables",
        "4:30: error: don't know how to synthesize implicit argument `_b`",
    ),
    (
        "prelude
import Init.Core
def h : List Nat → Nat
  | List.cons _ _ _ .. => 0
  | .nil => 1
",
        "command 0, byte 25:",
        "constructor pattern has the wrong number of explicit fields",
        "4:4: error: Invalid pattern: Too many arguments to `List.cons`; expected 2 explicit \
         arguments",
    ),
    (
        "prelude
import Init.Core
def h : List Nat → Nat
  | .cons _ _ _ .. => 0
  | .nil => 1
",
        "command 0, byte 25:",
        "constructor pattern has the wrong number of explicit fields",
        "4:4: error: Function expected at",
    ),
    (
        "prelude
import Init.Core
def two (a : Nat) (_b : Bool) : Nat := a
theorem p : two .. 1 = 1 := rfl
",
        "command 1, byte 66:",
        "requires a function type",
        "4:16: error: unexpected '..'",
    ),
    (
        "prelude
import Init.Core
def si ⦃n : Nat⦄ (_h : n = n) : Nat := n
example : Nat := (si .. : Nat)
",
        "command 1, byte 70:",
        "Type mismatch",
        "4:17: error: Type mismatch",
    ),
    (
        "prelude
import Init.Core
example : Nat := id ..
",
        "command 0, byte 25:",
        "left 1 unresolved metavariables",
        "3:17: error: don't know how to synthesize implicit argument `a`",
    ),
    (
        "prelude
import Init.Core
def P (n : Nat) : Prop := n = n
theorem P.mk' (_h : P 0) : True := trivial
example (h : ∀ ⦃n : Nat⦄, P n) : True := h.mk' ..
",
        "command 2, byte 100:",
        "unknown record field mk'",
        "5:43: error(lean.invalidField): Invalid field `mk'`: The environment does not contain \
         `Function.mk'`",
    ),
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
        "fln-ellipsis-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos(),
    ));
    std::fs::create_dir(&path).unwrap();
    path
}

/// The pinned `lean`'s stdout and exit code on `entry`, when the binary is present.
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

/// The installed `lean` on `program`: its exit code, stdout and stderr.
fn ours(lib: &Path, root: &Path, program: &str) -> (Option<i32>, String, String) {
    let entry = root.join("Ellipsis.lean");
    std::fs::write(&entry, program).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_lean"))
        .arg(&entry)
        .current_dir(root)
        .env("LEAN_PATH", lib)
        .env("FLN_IMPORT_REUSE_DIR", root.join("records"))
        .output()
        .expect("run the installed lean");
    (
        output.status.code(),
        String::from_utf8(output.stdout).unwrap(),
        String::from_utf8(output.stderr).unwrap(),
    )
}

/// `program` is accepted with `expected` on stdout, here and at the pin.
fn accepted(lib: &Path, root: &Path, program: &str, expected: &str) {
    let (code, stdout, stderr) = ours(lib, root, program);
    assert_eq!(code, Some(0), "stderr: {stderr}");
    assert_eq!(stdout, expected);
    if let Some((code, stdout)) = pinned(lib, &root.join("Ellipsis.lean")) {
        assert_eq!((code, stdout.as_str()), (0, expected), "the pin moved");
    }
}

#[test]
fn an_ellipsis_makes_the_remaining_arguments_holes_as_at_the_pin() {
    let Some(lib) = pinned_lib() else { return };
    let root = workspace();
    accepted(&lib, &root, GAP, GAP_EXPECTED);
    accepted(&lib, &root, UPSTREAM, "");
    accepted(&lib, &root, TERMS, TERMS_EXPECTED);
}

#[test]
fn an_ellipsis_pattern_matches_as_at_the_pin() {
    let Some(lib) = pinned_lib() else { return };
    let root = workspace();
    accepted(&lib, &root, PATTERNS, "");
}

#[test]
fn an_ellipsis_the_pin_refuses_is_refused_at_its_command() {
    let Some(lib) = pinned_lib() else { return };
    let root = workspace();
    for (program, command, reason, pin) in REFUSALS {
        let (code, stdout, stderr) = ours(&lib, &root, program);
        assert_ne!(code, Some(0), "accepted {program}stdout: {stdout}");
        assert!(
            stderr.contains(command) && stderr.contains(reason),
            "{program}stderr: {stderr}"
        );
        if let Some((code, stdout)) = pinned(&lib, &root.join("Ellipsis.lean")) {
            assert_eq!(code, 1, "the pin moved on {program}");
            assert!(
                stdout.starts_with(&format!("{}:{pin}", root.join("Ellipsis.lean").display())),
                "the pin moved on {program}: {stdout}"
            );
        }
    }
}
