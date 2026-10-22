//! The pin's `linter.unusedVariables`, `linter.deprecated` and `linter.defProp` warnings, through the drop-in
//! `lean` over `prelude` with `Init.Core` (bead `fln-default-linters-unused-variables-mtnt`).
//! Each program runs through the pinned `lean` v4.32.0 in the same test: an `IDENTICAL` program
//! must print exactly what the pin prints, and every warning printed for a `SUBSET` program
//! must be one the pin prints too.
#![forbid(unsafe_code)]
use std::path::{Path, PathBuf};
use std::process::Command;

const HEADER: &str = "prelude\nimport Init.Core\n";

/// Used and unused binders, `_x`, a binder used only in a later binder's type, an implicit
/// type parameter, a theorem, an example, and a `sorry` command (which the pin never lints).
const LINTED: &str = "def f (x y : Nat) (h : x = x) : Nat := x
theorem t (p q : Prop) (hp : p) (hq : q) : p := hp
def g {α : Type} (a b : α) := b
def k (_unused : Nat) (n : Nat) : Nat := n
example (a b : Nat) (h : a = b) : b = a := Eq.symm h
def usesType (n : Nat) (v : Fin n) : Fin n := v
def s (x : Nat) : Nat := sorry
";

/// Pattern variables: equations, `match`, a named pattern, a tuple, constructor names that
/// bind nothing (`true`, `none`), and `_w`.
const PATTERNS: &str = "def p1 : Nat → Nat → Nat
  | 0, m => m
  | n+1, m => p1 n 0
def p2 (o : Option Nat) : Nat :=
  match o with
  | some v => 0
  | none => 1
def p3 : List Nat → Nat
  | x@(y :: ys) => 0
  | _ => 1
def p4 (b : Bool) : Nat := match b with
  | true => 1
  | false => 0
def p5 : Nat × Nat → Nat
  | (a, b) => a
def p6 (o : Option Nat) : Nat :=
  match o with
  | some _w => 0
  | none => 1
";

/// `fun` binders (plain, typed, grouped, a tuple pattern, `_`) and the binder of an implicit
/// dependent arrow, which the pin lints while it ignores an explicit one.
const FUNCTIONS: &str = "def f1 : Nat → Nat := fun x => 0
def f2 : Nat → Nat → Nat := fun x y => x
def f3 : Nat → Nat := fun (x : Nat) => 1
def f4 : Nat → Nat → Nat := fun (a b : Nat) => b
def f5 : Nat → Nat := fun _ => 2
def f6 : {β : Type} → Nat := fun {β} => 3
def f7 : Nat × Nat → Bool := fun (x, y) => true
def f8 := fun (n : Nat) => n
def f9 : (m : Nat) → Nat := fun _ => 4
";

/// `linter.deprecated`'s note on `structure`, `class` and `inductive … :=`, and
/// `linter.defProp`, after the unused-variables warning of the same command, as at the pin.
const DEPRECATED_AND_DEF_PROP: &str = "structure A :=
  x : Nat
class B (α : Type) :=
  b : α
inductive C :=
  | c : C
def inc : 1 = 1 := rfl
def p (n : Nat) (m : Nat) : n = n := rfl
abbrev q : 2 = 2 := rfl
theorem r : 3 = 3 := rfl
set_option linter.defProp false in
def s : 4 = 4 := rfl
set_option linter.deprecated false in
structure D :=
  y : Nat
";

/// Binders under no `fun` in the source: a subtype's and a structure-instance field's, linted
/// even with `funArgs` off; a named argument's name, which is no reference to a local of that
/// name; and the `fun` binders of a `mutual` block's members.
const SCOPES: &str = "def sub1 := { x : Nat // True }
def sub2 := { x : Nat // x = x }
structure CF where
  f : Nat → Nat
  h : ∀ a b : Nat, f a = f b
def cf : CF where
  f x := 0
  h a b := rfl
def cg : CF where
  f x := x
  h a b := sorry
def nf (a : Nat) (b : Nat := 2) : Nat := a
theorem na (b : Nat) : nf 1 (b := 5) = nf 1 5 := rfl
theorem nb (b : Nat) : nf 1 (b := b) = nf 1 b := rfl
mutual
  partial def pe (u : Unit) : Nat → Nat := fun i => po u 0
  partial def po (u : Unit) : Nat → Nat := fun j => pe u j
end
";

/// Binders under no `fun`: an `if h :`'s, a `let`'s (one shadowing a parameter of its name),
/// and a theorem's statement's, which are linted though its proof is a tactic block (only a
/// scope holding the block is not read).
const LOCALS: &str = "def a (n : Nat) : Nat := if h : n = 3 then 1 else 2
def b (n : Nat) : Nat := if h : n = 3 then n else 2
def c (n : Nat) (k : n = 3 → Nat) : Nat := if h : n = 3 then k h else 2
def h1 : Nat := let x := 1; 2
def h2 : Nat := let x := 1; x
def h3 (x : Nat) : Nat := let x := x; 2
theorem l (x y : Nat) : (match x with | 0 => y | n+1 => y) = y := by cases x <;> rfl
theorem m : ∀ x : Nat, x = x := by intro x; rfl
theorem m2 : ∀ x : Nat, True := by intro; trivial
theorem m3 (p : Prop) (hp : p) : p := by exact hp
def o : Nat := (fun (x : Nat) => 3) 1
";

/// Tactic bodies: the pin reads only the final term, so a binder a tactic's syntax names is
/// still unused when the term does not use it (`have h`, `clear`), `assumption` takes the
/// last matching hypothesis, `‹_›` is a tactic block, and a binder used only in a later
/// binder's type stays used.
const TACTICS: &str = "theorem ta (p q : Prop) (hp : p) (hq : q) : p := by exact hp
theorem tb (p : Prop) (hp : p) (hp2 : p) : p := by assumption
theorem tc (x y : Nat) (h : x = y) (k : 0 = 0) : y = x := by subst h; rfl
def td (x : Nat) (y : Subtype (fun v => v = x)) (z : Nat) : Nat := by clear y x; exact z
theorem te (n : Nat) (h : n = n) : True := by trivial
example (h : Nat) : Nat := by
  have h : Nat := 0
  exact h
theorem tf (p q : Prop) (hp : p) (hq : q) : p ∧ q := ⟨hp, by exact hq⟩
theorem tg (a b : Nat) (h : a = b) (h' : b = a) : b = a := by exact h'
theorem th (p q : Prop) (hq : q) (hp : p) : p := ‹p›
";

/// A tactic block anywhere in a body silences every binder the body introduces, not only
/// those whose scope holds it; without one they are linted.
const TACTIC_ELSEWHERE: &str =
    "def g8 (n : Nat) : Nat := Nat.add ((fun (x : Nat) => n) 0) (by exact 1)
def g9 (n : Nat) : Nat := Nat.add ((fun (x : Nat) => n) 0) 1
def g10 (n : Nat) : Nat := Nat.add (let k := 5; n) (by exact 1)
def g11 (n : Nat) : Nat := Nat.add (let k := 5; n) 1
theorem g13 (p : Prop) (hp : p) : p ∧ True := And.intro (have z := 3; hp) (by trivial)
";

const IDENTICAL: &[(&str, &str)] = &[
    ("tactics", TACTICS),
    ("tactic_elsewhere", TACTIC_ELSEWHERE),
    ("linted", LINTED),
    ("scopes", SCOPES),
    ("locals", LOCALS),
    ("patterns", PATTERNS),
    ("functions", FUNCTIONS),
    ("deprecated_and_def_prop", DEPRECATED_AND_DEF_PROP),
    (
        "pattern_vars_off",
        "set_option linter.unusedVariables.patternVars false\ndef p (o : Option Nat) : Nat :=\n  match o with\n  | some v => 0\n  | none => 1\n",
    ),
    (
        "switched_off",
        "set_option linter.unusedVariables false\ndef f (x y : Nat) : Nat := x\n",
    ),
    (
        "fun_args_off",
        "set_option linter.unusedVariables.funArgs false\ndef f (x y : Nat) : Nat := x\n",
    ),
    (
        "all_off",
        "set_option linter.all false\ndef f (x y : Nat) : Nat := x\n",
    ),
    (
        "all_off_but_this",
        "set_option linter.all false\nset_option linter.unusedVariables true\ndef f (x y : Nat) : Nat := x\n",
    ),
];

/// A tactic body with `where` helpers is left undecided: the pin warns about `m` here, and
/// this door prints nothing for it rather than read a term the pin need not share.
const SUBSET: &[(&str, &str)] = &[(
    "tactic_where",
    "def w (n : Nat) (m : Nat) : Nat := helper n
where helper (k : Nat) : Nat := by exact k
",
)];

fn pinned_toolchain() -> Option<PathBuf> {
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
        "fln-unused-variables-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos(),
    ));
    std::fs::create_dir(&path).unwrap();
    path
}

/// The stdout of this crate's `lean` and of the pinned `lean` on `HEADER` + `program`.
fn outputs(lib: &Path, root: &Path, name: &str, program: &str) -> (String, String) {
    let entry = format!("{name}.lean");
    std::fs::write(root.join(&entry), format!("{HEADER}{program}")).unwrap();
    let run = |binary: &Path| {
        let output = Command::new(binary)
            .arg(&entry)
            .current_dir(root)
            .env("LEAN_PATH", lib)
            .env("FLN_IMPORT_REUSE_DIR", root.join("records"))
            .output()
            .expect("run lean");
        assert_eq!(
            output.status.code(),
            Some(0),
            "{name}: {}\n{}",
            binary.display(),
            String::from_utf8_lossy(&output.stderr)
        );
        String::from_utf8(output.stdout).expect("UTF-8 output")
    };
    let pinned = lib
        .parent()
        .and_then(Path::parent)
        .map(|toolchain| toolchain.join("bin/lean"))
        .expect("the pinned toolchain's lean");
    (run(Path::new(env!("CARGO_BIN_EXE_lean"))), run(&pinned))
}

/// The output's messages, each a `FILE:LINE:COL: severity: …` line with its continuation lines.
fn messages(output: &str) -> Vec<String> {
    let mut messages: Vec<String> = Vec::new();
    for line in output.lines() {
        match messages.last_mut() {
            Some(last) if !line.contains(".lean:") => {
                last.push('\n');
                last.push_str(line);
            }
            _ => messages.push(line.to_owned()),
        }
    }
    messages
}

#[test]
fn signature_binder_warnings_match_the_pin_and_are_never_invented() {
    let Some(lib) = pinned_toolchain() else {
        return;
    };
    let root = workspace();
    for (name, program) in IDENTICAL {
        let (ours, pinned) = outputs(&lib, &root, name, program);
        assert_eq!(ours, pinned, "{name}: {program}");
    }
    // The programs must actually exercise the linter, binders and patterns both.
    for (name, program, count) in [
        ("linted", LINTED, 4),
        ("patterns", PATTERNS, 6),
        ("functions", FUNCTIONS, 8),
        ("scopes", SCOPES, 7),
        ("tactics", TACTICS, 8),
        ("tactic_elsewhere", TACTIC_ELSEWHERE, 2),
    ] {
        let (ours, _) = outputs(&lib, &root, name, program);
        assert_eq!(
            ours.matches("is not explicitly referenced").count(),
            count,
            "{ours}"
        );
    }
    for (name, program) in SUBSET {
        let (ours, pinned) = outputs(&lib, &root, name, program);
        let pinned = messages(&pinned);
        for message in messages(&ours) {
            assert!(
                pinned.contains(&message),
                "{name}: invented {message}\npin: {pinned:?}"
            );
        }
    }
}
