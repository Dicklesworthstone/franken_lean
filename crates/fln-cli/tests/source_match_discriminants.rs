//! A `match` on a local refines it only where the pin's match elaborator would (vendored
//! `Lean/Elab/Match.lean`): where the motive mentions it (the expected type) or a later local
//! depends on it (`generalize`, `getFVarsToGeneralize … (ignoreLetDecls := true)`). Otherwise it
//! stays in scope unchanged. A hole made outside the match, such as the value type of
//! `let y ← match …`, can then be solved from inside a branch, and a branch does not know
//! `o = some n` unless something refined `o`. Through `fln check-source` over `prelude` +
//! `Init.Data.List.Control` + `Init.Control.Id`. Every program here was run through the pinned
//! `lean` v4.32.0 with the same header first (2026-10-11), with the same verdict, and is compared
//! with the pinned binary again when it is present.
#![forbid(unsafe_code)]
use std::path::{Path, PathBuf};
use std::process::Command;

const HEADER: &str = "prelude\nimport Init.Data.List.Control\nimport Init.Control.Id\n";

const ACCEPTED: &[(&str, &str)] = &[
    (
        "bound_match",
        "def f (o : Option Nat) : Id Nat := do\n  let y ← match o with\n    | some n => pure n\n    \
         | none => pure 0\n  return y\n",
    ),
    (
        "bound_match_values",
        "def f (o : Option Nat) : Id Nat := do\n  let y ← match o with\n    \
         | some n => pure (n * 2)\n    | none => pure 7\n  return y + 1\n\
         theorem t1 : (f (some 3)).run = 7 := by decide\ntheorem t2 : (f none).run = 8 := by decide\n",
    ),
    (
        "after_an_undefaulted_let",
        "def f (o : Option Nat) : Id Nat := do\n  let x := 0\n  let y : Nat ← match o with\n    \
         | some n => pure (n + x)\n    | none => pure x\n  return y\n",
    ),
    (
        "mutable_match",
        "def m13 (o : Option Nat) : Nat := Id.run do\n  let mut x := 0\n  match o with\n  \
         | some n => x := n\n  | none => x := 7\n  return x + 1\n\
         theorem t1 : m13 (some 3) = 4 := by decide\ntheorem t2 : m13 none = 8 := by decide\n",
    ),
    (
        "reads_the_discriminant",
        "def g (o : Option Nat) : Nat := match o with\n  | some n => n + o.getD 0\n  | none => 0\n\
         theorem t : g (some 2) = 4 := by decide\n",
    ),
    (
        "motive_mentions_it",
        "def g (o : Option Nat) : o = o := match o with\n  | some _ => rfl\n  | none => rfl\n",
    ),
    (
        "dependent_hypothesis",
        "def g (o : Option Nat) (h : o ≠ none) : Nat := match o with\n  | some n => n\n  \
         | none => absurd rfl h\n",
    ),
    (
        "let_reads_it",
        "def g (o : Option Nat) : Nat :=\n  let k := o.getD 5\n  match o with\n  | some n => n + k\n  \
         | none => k\ntheorem t : g none = 5 := by decide\n",
    ),
];

const REFUSED: &[(&str, &str)] = &[
    // Nothing mentions `o`, so the branch does not know `o = some n` ("Application type
    // mismatch"). Main (cb009b5d) refined `o` there and accepted it.
    (
        "unrefined_discriminant",
        "def g (o : Option Nat) : Nat := match o with\n  | some n => (fun (_ : o = some n) => n) rfl\n  \
         | none => 0\n",
    ),
    (
        "bound_match_wrong_value",
        "def f (o : Option Nat) : Id Nat := do\n  let y ← match o with\n    \
         | some n => pure (n * 2)\n    | none => pure 7\n  return y + 1\n\
         theorem t : (f none).run = 7 := by decide\n",
    ),
    (
        "mutable_match_wrong_value",
        "def m13 (o : Option Nat) : Nat := Id.run do\n  let mut x := 0\n  match o with\n  \
         | some n => x := n\n  | none => x := 7\n  return x + 1\ntheorem t : m13 none = 1 := by decide\n",
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
        "fln-match-discriminants-{}-{}",
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
fn a_discriminant_is_refined_only_where_the_pin_refines_it() {
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
