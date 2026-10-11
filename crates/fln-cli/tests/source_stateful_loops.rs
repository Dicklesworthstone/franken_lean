//! Stateful `for` loops and staged callbacks, compiled and run by the installed drop-in `lean`
//! (`#eval`). `List`'s `ForIn` instance passes `forIn'` the two-binder `fun a _ => f a`, where
//! `forIn'` calls back with three arguments, so the callback's closure type differs from the
//! parameter's flat one until the lambda is eta-expanded at the call. Branches that reassign and
//! then `break` or `continue` leave the loop with the values they read. Every program here was run
//! through the pinned `lean` v4.32.0 with the same header first (2026-10-11), printing the value
//! asserted here, and is compared with the pinned binary's output again when it is present.
#![forbid(unsafe_code)]
use std::path::{Path, PathBuf};
use std::process::Command;

const HEADER: &str =
    "prelude\nimport Init.Data.List.Control\nimport Init.Control.Id\nimport Init.Data.Repr\n";

/// (name, program, the pin's output).
const PROGRAMS: &[(&str, &str, &str)] = &[
    (
        "for_in",
        "def f (xs : List Nat) : Id Nat := forIn xs 0 (fun x s => pure (ForInStep.yield (s + x)))\n\
         #eval (f [5, 6]).run\n",
        "11",
    ),
    (
        "sum",
        "def sum (xs : List Nat) : Nat := Id.run do\n  let mut s := 0\n  for x in xs do\n    \
         s := s + x\n  return s\n#eval sum [1, 2, 3, 4]\n",
        "10",
    ),
    (
        "continue",
        "def evens (xs : List Nat) : Nat := Id.run do\n  let mut c := 0\n  for x in xs do\n    \
         if x % 2 == 1 then\n      continue\n    c := c + 1\n  return c\n\
         #eval evens [1, 2, 4, 5, 6]\n",
        "3",
    ),
    (
        "nested",
        "def pairs (xs ys : List Nat) : Nat := Id.run do\n  let mut s := 0\n  for x in xs do\n    \
         for y in ys do\n      s := s + x * y\n  return s\n#eval pairs [1, 2] [3, 4]\n",
        "21",
    ),
    (
        "two_variables",
        "def two (xs : List Nat) : Nat := Id.run do\n  let mut a := 0\n  let mut b := 1\n  \
         for x in xs do\n    a := a + x\n    b := b * x\n  return a + b\n#eval two [2, 3]\n",
        "11",
    ),
    (
        "early_return",
        "def find? (xs : List Nat) : Nat := Id.run do\n  for x in xs do\n    if x == 4 then\n      \
         return x * 10\n  return 0\n#eval find? [3, 4, 5]\n",
        "40",
    ),
    (
        "partial_application",
        "def app3 (f : Nat → Nat → Nat → Nat) : Nat := f 1 2 3\n\
         #eval app3 (fun a b => Nat.add (a + b))\n",
        "6",
    ),
    (
        "strict_let_between_stages",
        "def app3 (f : Nat → Nat → Nat → Nat) : Nat := f 1 2 3\n\
         #eval app3 (fun a b => let y := a * 10 + b; fun c => y + c)\n",
        "15",
    ),
    (
        "break_after_reassignment",
        "def firstBig (xs : List Nat) : Nat := Id.run do\n\
         \x20 let mut r := 0\n\
         \x20 for x in xs do\n\
         \x20   if x > 3 then\n\
         \x20     r := x\n\
         \x20     break\n\
         \x20 return r\n\
         #eval firstBig [1, 5, 7]\n",
        "5",
    ),
    (
        "continue_after_reassignment",
        "def m (xs : List Nat) : Nat := Id.run do\n\
         \x20 let mut s := 0\n\
         \x20 for x in xs do\n\
         \x20   if x == 2 then\n\
         \x20     s := s + 100\n\
         \x20     continue\n\
         \x20   s := s + x\n\
         \x20 return s\n\
         #eval m [1, 2, 3]\n",
        "104",
    ),
    (
        "both_branches_jump",
        "def m (xs : List Nat) : Nat := Id.run do\n\
         \x20 let mut s := 0\n\
         \x20 for x in xs do\n\
         \x20   if x > 2 then\n\
         \x20     s := s + 1000\n\
         \x20     break\n\
         \x20   else\n\
         \x20     s := s + x\n\
         \x20     continue\n\
         \x20 return s\n\
         #eval m [1, 2, 3, 4]\n",
        "1003",
    ),
    (
        "match_alternatives_jump",
        "def m (xs : List (Option Nat)) : Nat := Id.run do\n\
         \x20 let mut s := 0\n\
         \x20 for o in xs do\n\
         \x20   match o with\n\
         \x20   | some n =>\n\
         \x20     s := s + n\n\
         \x20     continue\n\
         \x20   | none =>\n\
         \x20     s := s + 1000\n\
         \x20     break\n\
         \x20 return s\n\
         #eval m [some 1, some 2, none, some 5]\n",
        "1003",
    ),
    (
        "unless_continue",
        "def m (xs : List Nat) : Nat := Id.run do\n\
         \x20 let mut s := 0\n\
         \x20 for x in xs do\n\
         \x20   unless x % 2 == 0 do\n\
         \x20     s := s + 100\n\
         \x20     continue\n\
         \x20   s := s + x\n\
         \x20 return s\n\
         #eval m [1, 2, 3, 4]\n",
        "206",
    ),
    (
        "inner_loop_break",
        "def m (xs ys : List Nat) : Nat := Id.run do\n\
         \x20 let mut s := 0\n\
         \x20 for x in xs do\n\
         \x20   for y in ys do\n\
         \x20     if y > x then\n\
         \x20       s := s + 10\n\
         \x20       break\n\
         \x20     s := s + y\n\
         \x20 return s\n\
         #eval m [1, 2] [1, 2, 3]\n",
        "24",
    ),
    (
        "body_local_mut_and_break",
        "def m (xs : List Nat) : Nat := Id.run do\n\
         \x20 let mut s := 0\n\
         \x20 for x in xs do\n\
         \x20   let mut t := x\n\
         \x20   if t > 2 then\n\
         \x20     t := t * 2\n\
         \x20     s := s + t\n\
         \x20     break\n\
         \x20   s := s + t\n\
         \x20 return s\n\
         #eval m [1, 2, 3, 4]\n",
        "9",
    ),
    (
        "else_if_jumps",
        "def m (xs : List Nat) : Nat := Id.run do\n\
         \x20 let mut s := 0\n\
         \x20 for x in xs do\n\
         \x20   if x == 1 then\n\
         \x20     s := s + 10\n\
         \x20     continue\n\
         \x20   else if x == 2 then\n\
         \x20     s := s + 20\n\
         \x20     break\n\
         \x20   s := s + x\n\
         \x20 return s\n\
         #eval m [3, 1, 2, 5]\n",
        "33",
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
        "fln-stateful-loops-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos(),
    ));
    std::fs::create_dir(&path).unwrap();
    path
}

/// `binary` on `entry`: (exit code, trimmed stdout, stderr).
fn run(binary: &Path, lib: &Path, root: &Path, entry: &Path) -> (i32, String, String) {
    let output = Command::new(binary)
        .arg(entry)
        .current_dir(root)
        .env("LEAN_PATH", lib)
        .env("FLN_IMPORT_REUSE_DIR", root.join("records"))
        .output()
        .expect("run lean");
    (
        output.status.code().expect("normal process exit"),
        String::from_utf8_lossy(&output.stdout).trim().to_owned(),
        String::from_utf8_lossy(&output.stderr).into_owned(),
    )
}

#[test]
fn stateful_loops_compile_and_print_the_pins_values() {
    let Some(lib) = pinned_lib() else {
        return;
    };
    let root = workspace();
    let pinned = lib
        .parent()
        .and_then(Path::parent)
        .map(|toolchain| toolchain.join("bin/lean"))
        .filter(|lean| lean.is_file());
    for (name, program, value) in PROGRAMS {
        let entry = root.join(format!("{name}.lean"));
        std::fs::write(&entry, format!("{HEADER}{program}")).unwrap();
        let (code, stdout, stderr) =
            run(Path::new(env!("CARGO_BIN_EXE_lean")), &lib, &root, &entry);
        assert_eq!((code, stdout.as_str()), (0, *value), "{name}: {stderr}");
        if let Some(pinned) = &pinned {
            let (code, stdout, stderr) = run(pinned, &lib, &root, &entry);
            assert_eq!(
                (code, stdout.as_str()),
                (0, *value),
                "{name} (pinned lean): {stderr}"
            );
        }
    }
}
