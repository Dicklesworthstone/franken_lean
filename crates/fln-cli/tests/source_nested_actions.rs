//! `(← e)` in a do element: the pin's `expandNestedActions` (`Lean/Elab/Do/Basic.lean`) runs `e`
//! before the element, as `let x ← e`, inner actions first and then left to right. It never lifts
//! out of another do block, out of a pure `if` but its condition, or past a binder, and the pin
//! refuses those.
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
        "let_value",
        "def g : Except String Nat := return 5\ndef f : Except String Nat := do\n  let y := (← g) + 1\n  return y\nexample : f = Except.ok 6 := rfl\n",
    ),
    (
        "left_to_right",
        "def a : Except String Nat := throw \"a\"\ndef b : Except String Nat := throw \"b\"\ndef f : Except String Nat := do\n  return (← a) + (← b)\nexample : f = Except.error \"a\" := rfl\n",
    ),
    (
        "inner_first",
        "def m : Except String (Except String Nat) := return (return 3)\ndef f : Except String Nat := do\n  return (← (← m))\nexample : f = Except.ok 3 := rfl\n",
    ),
    (
        "if_condition",
        "def c : Except String Bool := return false\ndef f : Except String Nat := do\n  if (← c) then return 1 else return 2\nexample : f = Except.ok 2 := rfl\n",
    ),
    (
        "unless_condition",
        "def f (b : Except String Bool) : Except String Unit := do\n  unless (← b) do throw \"no\"\nexample : f (return false) = Except.error \"no\" := rfl\n",
    ),
    (
        "for_collection",
        "def xs : Except String (List Nat) := return [1, 2]\ndef f : Except String Unit := do\n  for x in (← xs) do\n    if x > 5 then throw \"big\"\n",
    ),
    (
        "return_value",
        "def f (g : Except String Nat) : Except String Nat := do\n  return (← g) + 1\nexample : f (return 1) = Except.ok 2 := rfl\n",
    ),
    (
        "reassignment",
        "def f (g : Except String Nat) : Except String Nat := do\n  let mut s := 0\n  s := s + (← g)\n  return s\nexample : f (return 4) = Except.ok 4 := rfl\n",
    ),
    (
        "match_discriminant",
        "def f (g : Except String (Option Nat)) : Except String Nat := do\n  match (← g) with\n  | some n => return n\n  | none => return 0\nexample : f (return (some 3)) = Except.ok 3 := rfl\n",
    ),
    (
        "io_argument",
        "def f (g : IO String) : IO Unit := do\n  IO.println (← g)\n",
    ),
    (
        "term_return",
        "def f (g : Except String Nat) : Except String Nat := return (← g) + 1\nexample : f (return 1) = Except.ok 2 := rfl\n",
    ),
    (
        "term_unless",
        "def f (b : Except String Bool) : Except String Unit := unless (← b) do throw \"no\"\nexample : f (return false) = Except.error \"no\" := rfl\n",
    ),
    (
        "bound_value",
        "def f (g : Except String Nat) : Except String Nat := do\n  let y ← (fun x => return x * 2) (← g)\n  return y\nexample : f (return 3) = Except.ok 6 := rfl\n",
    ),
    (
        "branch_only_when_taken",
        "def f (b : Bool) (g : Except String Nat) : Except String Nat := do\n  if b then\n    return (← g) + 1\n  else\n    return 0\nexample : f false (throw \"x\") = Except.ok 0 := rfl\n",
    ),
];

const REFUSED: &[(&str, &str)] = &[
    (
        "left_to_right_wrong",
        "def a : Except String Nat := throw \"a\"\ndef b : Except String Nat := throw \"b\"\ndef f : Except String Nat := do\n  return (← a) + (← b)\nexample : f = Except.error \"b\" := rfl\n",
    ),
    (
        "branch_wrong",
        "def f (b : Bool) (g : Except String Nat) : Except String Nat := do\n  if b then\n    return (← g) + 1\n  else\n    return 0\nexample : f false (throw \"x\") = Except.error \"x\" := rfl\n",
    ),
    (
        "pure_if_branch",
        "def boom : Except String Nat := throw \"x\"\ndef g (c : Bool) : Except String Nat := do\n  let x := if c then 1 else (← boom)\n  return x\n",
    ),
    (
        "under_fun",
        "def f (g : Nat → Except String Nat) (xs : List Nat) : Except String (List Nat) := do\n  return xs.map (fun x => (← g x))\n",
    ),
    (
        "outside_do",
        "def f (g : Except String Nat) : Except String Nat := Except.ok ((← g) + 1)\n",
    ),
    (
        "action_type",
        "def f (g : Except String String) : Except String Nat := do\n  return (← g) + 1\n",
    ),
    (
        "reassignment_wrong",
        "def f (g : Except String Nat) : Except String Nat := do\n  let mut s := 0\n  s := s + (← g)\n  return s\nexample : f (return 4) = Except.ok 0 := rfl\n",
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
        "fln-nested-actions-{}-{}",
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
fn nested_actions_run_before_their_element_as_the_pins() {
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
