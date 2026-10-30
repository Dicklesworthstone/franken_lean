//! A local declared by equations, `let go : T | p => e …`, in `let`, `let rec` and `where`, through
//! the installed drop-in `lean`, over `prelude` with `Init.Data.List.Basic`. The pin's
//! `expandLetEqnsDecl` (`Lean/Elab/Binders.lean:885-889`) makes the declaration
//! `go : T := @fun x₁ … => match x₁, … with | p => e …`, and `expandWhereDecls` (`:472-476`) makes a
//! `where` block one `let rec` group, so a declaration may call one declared after it.
//!
//! Every program was run through the pinned `lean` v4.32.0 with the same header first
//! (2026-10-30), and the pin is consulted again when it is present.
#![forbid(unsafe_code)]
use std::path::{Path, PathBuf};
use std::process::Command;

const HEADER: &str = "prelude\nimport Init.Data.List.Basic\n";

/// Programs the pin accepts, printing nothing: a typed `let rec` by equations, with and without
/// binders before its type; a non-recursive `let` by equations; `where` declarations by
/// equations; and `where` declarations calling ones declared after them.
const ACCEPTED: &[&str] = &[
    "def f (xs : List Nat) : Nat :=\n\
     \x20\x20let rec go : List Nat → Nat → Nat\n\
     \x20\x20| [], r => r\n\
     \x20\x20| _ :: t, r => go t (r + 1)\n\
     \x20\x20go xs 0\n",
    "def f (n : Nat) : Nat :=\n\
     \x20\x20let g : Nat → Nat\n\
     \x20\x20\x20\x20| 0 => 1\n\
     \x20\x20\x20\x20| _ => 2\n\
     \x20\x20g n\n\
     example : f 0 = 1 := rfl\n\
     example : f 5 = 2 := rfl\n",
    "def sum (xs : List Nat) : Nat :=\n\
     \x20\x20let rec go (acc : Nat) : List Nat → Nat\n\
     \x20\x20\x20\x20| [] => acc\n\
     \x20\x20\x20\x20| x :: t => go (acc + x) t\n\
     \x20\x20go 0 xs\n\
     example : sum [1, 2, 3] = 6 := rfl\n",
    "def len (xs : List Nat) : Nat := go xs\n\
     where\n\
     \x20\x20go : List Nat → Nat\n\
     \x20\x20\x20\x20| [] => 0\n\
     \x20\x20\x20\x20| _ :: t => go t + 1\n\
     example : len [1, 2] = 2 := rfl\n",
    "def cnt (xs : List Nat) : Nat := go 0 xs\n\
     where\n\
     \x20\x20go (acc : Nat) : List Nat → Nat\n\
     \x20\x20\x20\x20| [] => acc\n\
     \x20\x20\x20\x20| _ :: t => go (acc + 1) t\n\
     example : cnt [1, 2, 3] = 3 := rfl\n",
    "def f (n : Nat) : Nat := loop n\n\
     where\n\
     \x20\x20loop : Nat → Nat\n\
     \x20\x20\x20\x20| 0 => 0\n\
     \x20\x20\x20\x20| k + 1 => helper (loop k)\n\
     \x20\x20helper (x : Nat) : Nat := x + 2\n\
     example : f 3 = 6 := rfl\n",
    "def g (n : Nat) : Nat := a n\n\
     where\n\
     \x20\x20a (x : Nat) : Nat := b x + c x\n\
     \x20\x20b (x : Nat) : Nat := c x * 2\n\
     \x20\x20c (x : Nat) : Nat := x + 1\n\
     example : g 1 = 6 := rfl\n",
];

/// Programs the pin rejects: a local by equations whose value disagrees with a stated equation,
/// and one whose alternatives miss a constructor.
const REFUSED: &[&str] = &[
    "def f (n : Nat) : Nat :=\n\
     \x20\x20let g : Nat → Nat\n\
     \x20\x20\x20\x20| 0 => 1\n\
     \x20\x20\x20\x20| _ => 2\n\
     \x20\x20g n\n\
     example : f 0 = 2 := rfl\n",
    "def f (n : Nat) : Nat :=\n\
     \x20\x20let g : Nat → Nat\n\
     \x20\x20\x20\x20| 0 => 1\n\
     \x20\x20g n\n",
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
        "fln-let-equations-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos(),
    ));
    std::fs::create_dir(&path).unwrap();
    path
}

/// The pinned `lean`'s exit code and stdout on `entry`, when the binary is present.
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

/// The installed `lean` on `entry`: its exit code, stdout and stderr.
fn ours(lib: &Path, root: &Path, entry: &Path) -> (i32, String, String) {
    let output = Command::new(env!("CARGO_BIN_EXE_lean"))
        .arg(entry)
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

#[test]
fn locals_by_equations_are_the_pins_declarations() {
    let Some(lib) = pinned_lib() else {
        return;
    };
    let root = workspace();
    for (index, program) in ACCEPTED.iter().enumerate() {
        let entry = root.join(format!("Accepted{index}.lean"));
        std::fs::write(&entry, format!("{HEADER}{program}")).unwrap();
        if let Some((code, stdout)) = pinned(&lib, &entry) {
            assert_eq!((code, stdout.as_str()), (0, ""), "the pin moved: {program}");
        }
        let (code, stdout, stderr) = ours(&lib, &root, &entry);
        assert_eq!((code, stdout.as_str()), (0, ""), "{program}: {stderr}");
    }
    for (index, program) in REFUSED.iter().enumerate() {
        let entry = root.join(format!("Refused{index}.lean"));
        std::fs::write(&entry, format!("{HEADER}{program}")).unwrap();
        if let Some((code, _)) = pinned(&lib, &entry) {
            assert_eq!(code, 1, "the pin rejects {program}");
        }
        let (code, stdout, stderr) = ours(&lib, &root, &entry);
        assert_ne!(code, 0, "{program}: {stdout}");
        assert!(stderr.contains("refused"), "{program}: {stderr}");
    }
}
