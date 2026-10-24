//! `unless c do s`, `for x in xs do s` and `return e` in term position (`Term.termUnless`,
//! `Term.termFor`, `Term.termReturn`): the pin's `toDoElem` macros (`Lean/Elab/Do/Switch.lean`)
//! make each the one-element block `do <element>`, a fresh do block of its own. And `return` with
//! no value, in a do sequence or outside one: the pin's `elabDoReturn` returns `PUnit.unit`. Its
//! term is read only on the same line (`checkLineEq`).
//!
//! Through `fln check-source` over `prelude` with `Init.Control.Except`, `Init.Data.List.Control`
//! and `Init.System.IO`. Every program here was run through the pinned `lean` v4.32.0 with the same
//! header first (2026-10-12), with the same verdict, and is compared with the pinned binary again
//! when it is present.
#![forbid(unsafe_code)]
use std::path::{Path, PathBuf};
use std::process::Command;

const HEADER: &str =
    "prelude\nimport Init.Control.Except\nimport Init.Data.List.Control\nimport Init.System.IO\n";

const ACCEPTED: &[(&str, &str)] = &[
    (
        "unless_value",
        "def chk (b : Bool) : Except String Unit := unless b do throw \"no\"\nexample : chk false = Except.error \"no\" := rfl\nexample : chk true = Except.ok () := rfl\n",
    ),
    (
        "unless_io",
        "def check (b : Bool) : IO Unit :=\nunless b do throw (IO.userError \"no\")\n",
    ),
    (
        "unless_block",
        "def f (n : Nat) : IO Unit :=\n  unless n = 3 do\n    IO.println \"no\"\n    IO.println \"done\"\n",
    ),
    (
        "unless_argument",
        "def q (b : Bool) : IO Unit := (fun (x : IO Unit) => x) (unless b do pure ())\n",
    ),
    (
        "unless_bare_return",
        "def u (b : Bool) : IO Unit :=\n  unless b do\n    return\n",
    ),
    (
        "for_term",
        "def allSmall (xs : List Nat) : Except String Unit :=\n  for x in xs do\n    if x > 9 then throw \"big\"\n",
    ),
    (
        "for_pipe",
        "def p (xs : List Nat) : IO Unit := id <| for x in xs do IO.println \"x\"\n",
    ),
    (
        "for_mutable_body",
        "def m (xs : List Nat) : IO Unit :=\n  for x in xs do\n    let mut y := x\n    y := y + 1\n    IO.println \"y\"\n",
    ),
    (
        "return_value",
        "def r (n : Nat) : Except String Nat := return n + 1\nexample : r 2 = Except.ok 3 := rfl\n",
    ),
    (
        "return_bare",
        "def k : Except String Unit := return\nexample : k = Except.ok () := rfl\n",
    ),
    (
        "return_bare_in_branch",
        "def h (b : Bool) : Except String Unit := do\n  if b then\n    return\n  throw \"late\"\nexample : h true = Except.ok () := rfl\nexample : h false = Except.error \"late\" := rfl\n",
    ),
    ("return_bare_parenthesized", "def b : IO Unit := (return)\n"),
    (
        "do_pure_lets_at_id",
        "def v (x : Nat) : Id Nat := do\n  let y := x + x\n  pure (y * 2)\n",
    ),
    (
        "do_pure_lets_under_run",
        "def w (x : Nat) : Nat := Id.run do\n  let y := x + x\n  pure (y * 2)\n",
    ),
];

const REFUSED: &[(&str, &str)] = &[
    (
        "unless_wrong_value",
        "def chk (b : Bool) : Except String Unit := unless b do throw \"no\"\nexample : chk true = Except.error \"no\" := rfl\n",
    ),
    (
        "unless_body_type",
        "def f (b : Bool) : IO Unit := unless b do (5 : Nat)\n",
    ),
    (
        "unless_result_type",
        "def f (b : Bool) : IO Nat := unless b do pure ()\n",
    ),
    (
        "unless_then_statement",
        "def f : IO Unit :=\n  unless true do pure ()\n  pure ()\n",
    ),
    (
        "unless_then_argument",
        "def f (b : Bool) : IO Unit :=\n  unless b do pure ()\n    (pure ())\n",
    ),
    (
        "for_outer_mutable",
        "def f (xs : List Nat) : IO Unit := do\n  let mut s := 0\n  let _ ← (for x in xs do s := s + x)\n  pure ()\n",
    ),
    (
        "for_return_value",
        "def f (xs : List Nat) : Except String Nat := for x in xs do return x\n",
    ),
    (
        "return_wrong_value",
        "def r (n : Nat) : Except String Nat := return n + 1\nexample : r 2 = Except.ok 4 := rfl\n",
    ),
    (
        "return_bare_wrong_value",
        "def h (b : Bool) : Except String Unit := do\n  if b then\n    return\n  throw \"late\"\nexample : h true = Except.error \"late\" := rfl\n",
    ),
    (
        "return_value_on_next_line",
        "def bad : Except String Nat := do\n  return\n    5\n",
    ),
    (
        "return_bare_at_nat",
        "def bad : Except String Nat := return\n",
    ),
    // `extractMonadInfo` (vendored `Lean/Elab/Do/Basic.lean:741-760`): "invalid `do` notation,
    // expected type is not a monad application", even when every statement is a pure `let`
    // (upstream `elab_fail/770`).
    (
        "do_pure_lets_at_nat",
        "def u (x : Nat) : Nat := do\n  let y := x + x\n  y * (if y > 100 then 1 else (5 : Nat))\n",
    ),
    (
        "do_pure_let_at_bool",
        "def b : Bool := do\n  let y := true\n  y\n",
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
        "fln-term-do-elements-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos(),
    ));
    std::fs::create_dir(&path).unwrap();
    path
}

/// `fln check-source` on `HEADER` + `program`, and the pinned binary's exit code when present.
fn check(lib: &Path, root: &Path, name: &str, program: &str) -> (i32, String, Option<i32>) {
    let entry = root.join(format!("{name}.lean"));
    std::fs::write(&entry, format!("{HEADER}{program}")).unwrap();
    let ours = Command::new(env!("CARGO_BIN_EXE_fln"))
        .arg("check-source")
        .arg(&entry)
        .env("LEAN_PATH", lib)
        .env("FLN_IMPORT_REUSE_DIR", root.join("records"))
        .output()
        .expect("run the installed CLI");
    let theirs = lib
        .parent()
        .and_then(Path::parent)
        .map(|toolchain| toolchain.join("bin/lean"))
        .filter(|lean| lean.is_file())
        .map(|pinned| {
            Command::new(pinned)
                .arg(&entry)
                .env("LEAN_PATH", lib)
                .output()
                .expect("run the pinned lean")
                .status
                .code()
                .expect("normal pinned exit")
        });
    (
        ours.status.code().expect("normal process exit"),
        String::from_utf8_lossy(&ours.stderr).into_owned(),
        theirs,
    )
}

#[test]
fn term_position_do_elements_and_bare_returns_are_the_pins_blocks() {
    let Some(lib) = pinned_lib() else {
        return;
    };
    let root = workspace();
    for (name, program) in ACCEPTED {
        let (code, stderr, pinned) = check(&lib, &root, name, program);
        assert_eq!(code, 0, "{name}: {program}\n{stderr}");
        assert_eq!(pinned.unwrap_or(0), 0, "{name}: the pinned lean refuses it");
    }
    for (name, program) in REFUSED {
        let (code, _, pinned) = check(&lib, &root, name, program);
        assert_ne!(code, 0, "{name}: accepted {program}");
        assert_ne!(pinned.unwrap_or(1), 0, "{name}: the pinned lean accepts it");
    }
}
