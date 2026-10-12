//! `while c do s`, as the pin (`Lean/Elab/BuiltinDo/Repeat.lean`): `repeat if c then s else break`,
//! that is `for _ in Loop.mk do …` over `Lean.Loop` (`Init/While.lean`). The loop's `mut`
//! variables, `break`, `continue`, a named condition `h : c` and a nested action in the condition
//! are an ordinary `for` loop's.
//!
//! Through `fln check-source` over `prelude` with `Init.While`, `Init.Control.Except`,
//! `Init.Control.Id` and `Init.Data.List.Control`. Every program here was run through the pinned
//! `lean` v4.32.0 with the same header first (2026-10-12), with the same verdict, and is compared
//! with the pinned binary again when it is present.
#![forbid(unsafe_code)]
use std::path::{Path, PathBuf};
use std::process::Command;

const HEADER: &str = "prelude\nimport Init.While\nimport Init.Control.Except\nimport Init.Control.Id\nimport Init.Data.List.Control\n";

const ACCEPTED: &[(&str, &str)] = &[
    (
        "except_count",
        "def f (n : Nat) : Except String Nat := do\n  let mut i := n\n  let mut s := 0\n  while i != 0 do\n    s := s + i\n    i := i - 1\n  return s\n",
    ),
    (
        "id_count",
        "def f (n : Nat) : Id Nat := do\n  let mut i := n\n  let mut s := 0\n  while i != 0 do\n    s := s + i\n    i := i - 1\n  return s\n",
    ),
    (
        "except_break",
        "def f : Except String Nat := do\n  let mut i := 0\n  while true do\n    if i > 3 then break\n    i := i + 1\n  return i\n",
    ),
    (
        "except_named",
        "def f (n : Nat) : Except String Nat := do\n  let mut i := 0\n  while h : i < n do\n    i := i + 1\n  return i\n",
    ),
    (
        "except_nested_cond",
        "def f (c : Except String Bool) : Except String Unit := do\n  while (← c) do\n    throw \"again\"\n",
    ),
    (
        "except_inner",
        "def f (n : Nat) : Except String Nat := do\n  let mut i := 0\n  let mut t := 0\n  while i < n do\n    let mut j := 0\n    while j < i do\n      t := t + 1\n      j := j + 1\n    i := i + 1\n  return t\n",
    ),
    (
        "id_continue",
        "def f (n : Nat) : Id Nat := do\n  let mut i := 0\n  let mut s := 0\n  while i < n do\n    i := i + 1\n    if i % 2 == 0 then continue\n    s := s + i\n  return s\n",
    ),
    (
        "except_throw",
        "def f (n : Nat) : Except String Nat := do\n  let mut i := n\n  while i > 0 do\n    if i == 7 then throw \"seven\"\n    i := i - 1\n  return i\n",
    ),
];

const REFUSED: &[(&str, &str)] = &[
    (
        "nat_condition",
        "def f : Id Unit := do\n  while (3 : Nat) do\n    pure ()\n",
    ),
    (
        "body_type",
        "def f : Id Unit := do\n  while true do\n    (5 : Nat)\n",
    ),
    (
        "not_mutable",
        "def f : Id Unit := do\n  let i := 0\n  while i < 3 do\n    i := i + 1\n",
    ),
    (
        "result_type",
        "def f : Id Nat := do\n  let mut i := 0\n  while i < 3 do\n    i := i + 1\n",
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
        "fln-while-loops-{}-{}",
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
fn a_while_loop_is_its_loop_over_lean_loop() {
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
