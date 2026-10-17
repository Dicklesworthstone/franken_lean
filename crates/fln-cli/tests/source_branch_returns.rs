//! A `mut` variable reassigned in a branch that returns in one place and falls through in another
//! (`if c then i := i + 1; if i == n then return i`, then statements that read `i`), with and
//! without an enclosing loop. The pin's join point forwards the return (`Lean/Elab/Do/Basic.lean`);
//! here the statements after the branch end each branch that falls through (`close_over_rest`),
//! then `continue` in a loop body.
//!
//! Through the drop-in `lean` over `prelude` with `Init.While`, `Init.Control.Except`,
//! `Init.Control.Id`, `Init.Data.List.Control` and `Init.Data.Repr`: each program's `#eval` output
//! is the pinned `lean` v4.32.0's, recorded here (2026-10-12) and compared with the pinned binary
//! again when it is present. Every refused program is refused by the pin too.
#![forbid(unsafe_code)]
use std::path::{Path, PathBuf};
use std::process::Command;

const HEADER: &str = "prelude\nimport Init.While\nimport Init.Control.Except\nimport Init.Control.Id\nimport Init.Data.List.Control\nimport Init.Data.Repr\n";

/// (name, program, the pin's output)
const ACCEPTED: &[(&str, &str, &str)] = &[
    (
        "return_then_assign",
        "def f (n : Nat) : Id Nat := do\n  let mut i := 0\n  if n < 10 then\n    if i == n then return i\n    i := i + 1\n  return i\n#eval (f 0 : Nat)\n#eval (f 1 : Nat)\n#eval (f 2 : Nat)\n#eval (f 3 : Nat)\n#eval (f 5 : Nat)\n#eval (f 9 : Nat)\n#eval (f 12 : Nat)\n",
        "0\n1\n1\n1\n1\n1\n0\n",
    ),
    (
        "assign_then_return",
        "def f (n : Nat) : Id Nat := do\n  let mut i := 0\n  if n < 10 then\n    i := i + 1\n    if i == n then return i\n  return i\n#eval (f 0 : Nat)\n#eval (f 1 : Nat)\n#eval (f 2 : Nat)\n#eval (f 3 : Nat)\n#eval (f 5 : Nat)\n#eval (f 9 : Nat)\n#eval (f 12 : Nat)\n",
        "1\n1\n1\n1\n1\n1\n0\n",
    ),
    (
        "assignments_after",
        "def f (n : Nat) : Id Nat := do\n  let mut i := 0\n  if n < 10 then\n    i := i + 1\n    if i == n then return 100\n  i := i * 2\n  return i\n#eval (f 0 : Nat)\n#eval (f 1 : Nat)\n#eval (f 2 : Nat)\n#eval (f 3 : Nat)\n#eval (f 5 : Nat)\n#eval (f 9 : Nat)\n#eval (f 12 : Nat)\n",
        "2\n100\n2\n2\n2\n2\n0\n",
    ),
    (
        "both_branches_assign",
        "def f (n : Nat) : Id Nat := do\n  let mut i := 0\n  if n > 5 then\n    i := 1\n    if n > 8 then return 50\n  else\n    i := 2\n  return i + 10\n#eval (f 0 : Nat)\n#eval (f 1 : Nat)\n#eval (f 2 : Nat)\n#eval (f 3 : Nat)\n#eval (f 5 : Nat)\n#eval (f 9 : Nat)\n#eval (f 12 : Nat)\n",
        "12\n12\n12\n12\n12\n50\n50\n",
    ),
    (
        "match_alternatives",
        "def f (n : Nat) : Id Nat := do\n  let mut i := 0\n  match n with\n  | 0 => i := 5\n  | k + 1 =>\n    i := k\n    if k == 2 then return 100\n  return i + 1\n#eval (f 0 : Nat)\n#eval (f 1 : Nat)\n#eval (f 2 : Nat)\n#eval (f 3 : Nat)\n#eval (f 5 : Nat)\n#eval (f 9 : Nat)\n#eval (f 12 : Nat)\n",
        "6\n1\n2\n100\n5\n9\n12\n",
    ),
    (
        "loop_assign_then_return",
        "def f (n : Nat) : Id Nat := do\n  let mut i := 0\n  for _ in [1, 2, 3] do\n    if i < 10 then\n      i := i + 1\n      if i == n then return i\n  return 99\n#eval (f 0 : Nat)\n#eval (f 1 : Nat)\n#eval (f 2 : Nat)\n#eval (f 3 : Nat)\n#eval (f 5 : Nat)\n#eval (f 9 : Nat)\n#eval (f 12 : Nat)\n",
        "99\n1\n2\n3\n99\n99\n99\n",
    ),
    (
        "loop_return_else_assign",
        "def f (n : Nat) : Id Nat := do\n  let mut i := 0\n  for _ in [1, 2, 3] do\n    if i == n then\n      return i\n    else\n      i := i + 1\n  return 99\n#eval (f 0 : Nat)\n#eval (f 1 : Nat)\n#eval (f 2 : Nat)\n#eval (f 3 : Nat)\n#eval (f 5 : Nat)\n#eval (f 9 : Nat)\n#eval (f 12 : Nat)\n",
        "0\n1\n2\n99\n99\n99\n99\n",
    ),
    (
        "loop_return_then_assign",
        "def f (n : Nat) : Id Nat := do\n  let mut i := 0\n  for _ in [1, 2, 3] do\n    if i < 10 then\n      if i == n then return i\n      i := i + 1\n  return 99\n#eval (f 0 : Nat)\n#eval (f 1 : Nat)\n#eval (f 2 : Nat)\n#eval (f 3 : Nat)\n#eval (f 5 : Nat)\n#eval (f 9 : Nat)\n#eval (f 12 : Nat)\n",
        "0\n1\n2\n99\n99\n99\n99\n",
    ),
    (
        "while_return",
        "def f (n : Nat) : Id Nat := do\n  let mut i := 0\n  while i < 10 do\n    if i == n then return i\n    i := i + 1\n  return 99\n#eval (f 0 : Nat)\n#eval (f 1 : Nat)\n#eval (f 2 : Nat)\n#eval (f 3 : Nat)\n#eval (f 5 : Nat)\n#eval (f 9 : Nat)\n#eval (f 12 : Nat)\n",
        "0\n1\n2\n3\n5\n9\n99\n",
    ),
    (
        "except_throw",
        "def g (n : Nat) : Except String Nat := do\n  let mut i := 0\n  if n < 10 then\n    i := i + 1\n    if i == n then throw \"one\"\n  return i\n#eval g 0\n#eval g 1\n#eval g 5\n#eval g 20\n",
        "Except.ok 1\nExcept.error \"one\"\nExcept.ok 1\nExcept.ok 0\n",
    ),
];

const REFUSED: &[(&str, &str)] = &[
    (
        "ill_typed_return",
        "def f (n : Nat) : Id Nat := do\n  let mut i := 0\n  if n < 10 then\n    i := i + 1\n    if i == n then return \"no\"\n  return i\n",
    ),
    (
        "not_mutable",
        "def f (n : Nat) : Id Nat := do\n  let i := 0\n  if n < 10 then\n    i := i + 1\n    if i == n then return i\n  return i\n",
    ),
    (
        "ill_typed_rest",
        "def f (n : Nat) : Id Nat := do\n  let mut i := 0\n  if n < 10 then\n    i := i + 1\n    if i == n then return i\n  return i + \"a\"\n",
    ),
    (
        "wrong_value",
        "def f (n : Nat) : Id Nat := do\n  let mut i := 0\n  if n < 10 then\n    i := i + 1\n    if i == n then return 100\n  i := i * 2\n  return i\ntheorem t : f 5 = 1 := rfl\n",
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
        "fln-branch-returns-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos(),
    ));
    std::fs::create_dir(&path).unwrap();
    path
}

/// The drop-in `lean` on `HEADER` + `program`: (exit code, stdout, stderr), and the pinned
/// binary's (exit code, stdout) when present.
fn run(
    lib: &Path,
    root: &Path,
    name: &str,
    program: &str,
) -> (i32, String, String, Option<(i32, String)>) {
    let entry = root.join(format!("{name}.lean"));
    std::fs::write(&entry, format!("{HEADER}{program}")).unwrap();
    let ours = Command::new(env!("CARGO_BIN_EXE_lean"))
        .arg(&entry)
        .current_dir(root)
        .env("LEAN_PATH", lib)
        .env("FLN_IMPORT_REUSE_DIR", root.join("records"))
        .output()
        .expect("run the installed drop-in");
    let theirs = lib
        .parent()
        .and_then(Path::parent)
        .map(|toolchain| toolchain.join("bin/lean"))
        .filter(|lean| lean.is_file())
        .map(|pinned| {
            let output = Command::new(pinned)
                .arg(&entry)
                .env("LEAN_PATH", lib)
                .output()
                .expect("run the pinned lean");
            (
                output.status.code().expect("normal pinned exit"),
                String::from_utf8_lossy(&output.stdout).into_owned(),
            )
        });
    (
        ours.status.code().expect("normal process exit"),
        String::from_utf8_lossy(&ours.stdout).into_owned(),
        String::from_utf8_lossy(&ours.stderr).into_owned(),
        theirs,
    )
}

#[test]
fn branches_that_return_and_fall_through_compute_the_pins_values() {
    let Some(lib) = pinned_lib() else {
        return;
    };
    let root = workspace();
    for (name, program, expected) in ACCEPTED {
        let (code, stdout, stderr, pinned) = run(&lib, &root, name, program);
        assert_eq!(code, 0, "{name}: {program}\n{stderr}");
        assert_eq!(&stdout, expected, "{name}: {program}");
        if let Some((pinned_code, pinned_stdout)) = pinned {
            assert_eq!(
                (pinned_code, pinned_stdout.as_str()),
                (0, *expected),
                "{name}: the pin changed"
            );
        }
    }
    for (name, program) in REFUSED {
        let (code, _, _, pinned) = run(&lib, &root, name, program);
        assert_ne!(code, 0, "{name}: accepted {program}");
        assert_ne!(
            pinned.map_or(1, |(code, _)| code),
            0,
            "{name}: the pinned lean accepts it"
        );
    }
}
