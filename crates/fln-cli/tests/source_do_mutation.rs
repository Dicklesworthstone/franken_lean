//! `let mut` and reassignment over the pin's own Init (`List`'s `ForIn`, `Id`): straight-line
//! reassignment, `x ← e`, loop state across iterations (one, two and three variables), `break` and
//! `continue` after a reassignment, nested loops, a `mut` local to the loop body, and branches that
//! reassign inside and outside a loop, on `Bool` and `Prop` conditions and with `unless`. Every program was run through the pinned `lean` v4.32.0 with
//! the same header first (2026-10-11), with the same verdict. Values are checked with `decide`;
//! each refused theorem is the value a lost reassignment would give. A `match` that reassigns
//! after an undefaulted `let mut x := 0` is here too: the match does not refine its unmentioned
//! discriminant, so the join's value type, a hole made outside the match, is solved inside it.
#![forbid(unsafe_code)]
use std::path::{Path, PathBuf};
use std::process::Command;

const HEADER: &str = "prelude\nimport Init.Data.List.Control\nimport Init.Control.Id\n";

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
        .filter(|lib| lib.join("Init/Data/List/Control.olean").is_file());
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
        "fln-do-mutation-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos(),
    ));
    std::fs::create_dir(&path).unwrap();
    path
}

/// `fln check-source` on `HEADER` + `program`: (exit code, stderr).
fn check(lib: &Path, root: &Path, name: &str, program: &str) -> (i32, String) {
    let entry = root.join(format!("{name}.lean"));
    std::fs::write(&entry, format!("{HEADER}{program}")).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_fln"))
        .arg("check-source")
        .arg(&entry)
        .env("LEAN_PATH", lib)
        .env("FLN_IMPORT_REUSE_DIR", root.join("records"))
        .output()
        .expect("run the installed CLI");
    (
        output.status.code().expect("normal process exit"),
        String::from_utf8(output.stderr).unwrap(),
    )
}

#[test]
fn mutable_variables_have_the_pins_values() {
    let Some(lib) = pinned_lib() else { return };
    let root = workspace();
    for (name, program) in [
        (
            "straight",
            "def f (n : Nat) : Nat := Id.run do\n  let mut x := n\n  x := x + 1\n  x := x * 2\n  return x\ntheorem t : f 3 = 8 := by decide\n",
        ),
        (
            "sum",
            "def sum (xs : List Nat) : Nat := Id.run do\n  let mut s := 0\n  for x in xs do\n    s := s + x\n  return s\ntheorem t : sum [1, 2, 3] = 6 := by decide\n",
        ),
        (
            "two",
            "def stats (xs : List Nat) : Nat × Nat := Id.run do\n  let mut s := 0\n  let mut c := 0\n  for x in xs do\n    s := s + x\n    c := c + 1\n  return (s, c)\ntheorem t : stats [4, 5] = (9, 2) := by decide\n",
        ),
        (
            "if",
            "def g (b : Bool) : Nat := Id.run do\n  let mut x := 1\n  if b then\n    x := 10\n  return x + 1\ntheorem t1 : g true = 11 := by decide\ntheorem t2 : g false = 2 := by decide\n",
        ),
        (
            "ifelse2",
            "def h (b : Bool) : Nat × Nat := Id.run do\n  let mut x := 1\n  let mut y := 2\n  if b then\n    x := 10\n  else\n    y := 20\n    x := 5\n  return (x, y)\ntheorem t1 : h true = (10, 2) := by decide\ntheorem t2 : h false = (5, 20) := by decide\n",
        ),
        (
            "unless",
            "def m14 (b : Bool) : Nat := Id.run do\n  let mut x := 1\n  unless b do\n    x := 2\n  return x\ntheorem t1 : m14 true = 1 := by decide\ntheorem t2 : m14 false = 2 := by decide\n",
        ),
        (
            "break",
            "def firstBig (xs : List Nat) : Nat := Id.run do\n  let mut s := 0\n  for x in xs do\n    if x > 5 then break\n    s := s + x\n  return s\ntheorem t : firstBig [1, 2, 9, 3] = 3 := by decide\n",
        ),
        (
            "ifloop",
            "def countEven (xs : List Nat) : Nat := Id.run do\n  let mut c := 0\n  for x in xs do\n    if x % 2 == 0 then\n      c := c + 1\n  return c\ntheorem t : countEven [1, 2, 4, 5] = 2 := by decide\n",
        ),
        (
            "continue",
            "def m8 (xs : List Nat) : Nat := Id.run do\n  let mut s := 0\n  for x in xs do\n    s := s + 1\n    if x == 2 then continue\n    s := s + 10\n  return s\ntheorem t : m8 [1, 2, 3] = 23 := by decide\n",
        ),
        (
            "nested",
            "def m9 (xs ys : List Nat) : Nat := Id.run do\n  let mut s := 0\n  for x in xs do\n    for y in ys do\n      s := s + x * y\n  return s\ntheorem t : m9 [1, 2] [3, 4] = 21 := by decide\n",
        ),
        (
            "arrow",
            "def m11 : Nat := Id.run do\n  let mut x := 1\n  x ← pure (x + 4)\n  return x\ntheorem t : m11 = 5 := by decide\n",
        ),
        (
            "letarrow",
            "def m12 : Nat := Id.run do\n  let mut x ← pure 3\n  x := x * x\n  return x\ntheorem t : m12 = 9 := by decide\n",
        ),
        (
            "finalif",
            "def m15 (xs : List Nat) : Nat := Id.run do\n  let mut s := 0\n  for x in xs do\n    if x > 1 then\n      s := s + x\n    else\n      s := s + 100\n  return s\ntheorem t : m15 [1, 2, 3] = 105 := by decide\n",
        ),
        (
            "local",
            "def m17 (xs : List Nat) : Nat := Id.run do\n  let mut total := 0\n  for x in xs do\n    let mut y := x\n    y := y * 2\n    total := total + y\n  return total\ntheorem t : m17 [1, 2] = 6 := by decide\n",
        ),
        (
            "elseif",
            "def m18 (n : Nat) : Nat := Id.run do\n  let mut r := 0\n  if n == 0 then\n    r := 10\n  else if n == 1 then\n    r := 20\n  return r\ntheorem t : m18 1 = 20 := by decide\ntheorem t2 : m18 5 = 0 := by decide\n",
        ),
        (
            "typed",
            "def m19 : Nat := Id.run do\n  let mut x : Nat := 0\n  x := 5\n  return x\ntheorem t : m19 = 5 := by decide\n",
        ),
        (
            "match",
            "def m13 (o : Option Nat) : Nat := Id.run do\n  let mut x := 0\n  match o with\n  | some n => x := n\n  | none => x := 7\n  return x + 1\ntheorem t1 : m13 (some 3) = 4 := by decide\ntheorem t2 : m13 none = 8 := by decide\n",
        ),
        (
            "three",
            "def m20 (xs : List Nat) : Nat × Nat × Nat := Id.run do\n  let mut a := 0\n  let mut b := 1\n  let mut c := 2\n  for x in xs do\n    a := a + x\n    b := b * x\n    if x > 2 then\n      c := c + 1\n  return (a, b, c)\ntheorem t : m20 [2, 3, 4] = (9, 24, 4) := by decide\n",
        ),
    ] {
        let (code, stderr) = check(&lib, &root, name, program);
        assert_eq!(code, 0, "{name}: {program}\n{stderr}");
    }
}

#[test]
fn mutation_the_pin_refuses_is_refused() {
    let Some(lib) = pinned_lib() else { return };
    let root = workspace();
    for (name, program, pin) in [
        (
            "notmut",
            "def n1 : Nat := Id.run do\n  let x := 1\n  x := 2\n  return x\n",
            "Variable `x` cannot be mutated",
        ),
        (
            "shadow",
            "def n2 : Nat := Id.run do\n  let mut x := 1\n  let x := 2\n  return x\n",
            "mutable variable `x` cannot be shadowed",
        ),
        (
            "type",
            "def n3 : Nat := Id.run do\n  let mut x := 1\n  x := \"a\"\n  return x\n",
            "Type mismatch",
        ),
        (
            "sum",
            "def sum (xs : List Nat) : Nat := Id.run do\n  let mut s := 0\n  for x in xs do\n    s := s + x\n  return s\ntheorem t : sum [1, 2, 3] = 7 := by decide\n",
            "Tactic `decide` proved that the proposition … is false",
        ),
        (
            "if",
            "def g (b : Bool) : Nat := Id.run do\n  let mut x := 1\n  if b then\n    x := 10\n  return x + 1\ntheorem t1 : g true = 2 := by decide\n",
            "Tactic `decide` proved that the proposition … is false",
        ),
        (
            "break",
            "def firstBig (xs : List Nat) : Nat := Id.run do\n  let mut s := 0\n  for x in xs do\n    if x > 5 then break\n    s := s + x\n  return s\ntheorem t : firstBig [1, 2, 9, 3] = 6 := by decide\n",
            "Tactic `decide` proved that the proposition … is false",
        ),
        (
            "forshadow",
            "def n7 (xs : List Nat) : Nat := Id.run do\n  let mut x := 0\n  for x in xs do\n    pure ()\n  return x\n",
            "mutable variable `x` cannot be shadowed",
        ),
        (
            "continue",
            "def m8 (xs : List Nat) : Nat := Id.run do\n  let mut s := 0\n  for x in xs do\n    s := s + 1\n    if x == 2 then continue\n    s := s + 10\n  return s\ntheorem t : m8 [1, 2, 3] = 33 := by decide\n",
            "Tactic `decide` proved that the proposition … is false",
        ),
        (
            "nestedterm",
            "def n9 : Nat := Id.run do\n  let mut x := 1\n  let f : Unit → Id Nat := fun _ => do\n    x := 2\n    return x\n  return x\n",
            "Variable `x` cannot be mutated",
        ),
        (
            "two",
            "def stats (xs : List Nat) : Nat × Nat := Id.run do\n  let mut s := 0\n  let mut c := 0\n  for x in xs do\n    s := s + x\n    c := c + 1\n  return (s, c)\ntheorem t : stats [4, 5] = (9, 3) := by decide\n",
            "Tactic `decide` proved that the proposition … is false",
        ),
        (
            "match",
            "def m13 (o : Option Nat) : Nat := Id.run do\n  let mut x := 0\n  match o with\n  | some n => x := n\n  | none => x := 7\n  return x + 1\ntheorem t : m13 none = 1 := by decide\n",
            "Tactic `decide` proved that the proposition … is false",
        ),
        (
            "finalif",
            "def m15 (xs : List Nat) : Nat := Id.run do\n  let mut s := 0\n  for x in xs do\n    if x > 1 then\n      s := s + x\n    else\n      s := s + 100\n  return s\ntheorem t : m15 [1, 2, 3] = 5 := by decide\n",
            "Tactic `decide` proved that the proposition … is false",
        ),
        (
            "unless",
            "def m14 (b : Bool) : Nat := Id.run do\n  let mut x := 1\n  unless b do\n    x := 2\n  return x\ntheorem t : m14 false = 1 := by decide\n",
            "Tactic `decide` proved that the proposition … is false",
        ),
        (
            "elseif",
            "def m18 (n : Nat) : Nat := Id.run do\n  let mut r := 0\n  if n == 0 then\n    r := 10\n  else if n == 1 then\n    r := 20\n  return r\ntheorem t : m18 5 = 20 := by decide\n",
            "Tactic `decide` proved that the proposition … is false",
        ),
    ] {
        let (code, _) = check(&lib, &root, name, program);
        assert_ne!(code, 0, "{name} was accepted; the pin: {pin}\n{program}");
    }
}
