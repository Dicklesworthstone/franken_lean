//! `fun (x, y) => e`, a lambda whose binder is a tuple: the pin's `expandFunBinders` makes it the
//! pattern lambda `fun | (x, y) => e`, the tuple being `Prod.mk x y` (`expandTuple`), so it
//! matches a pair and never another structure. Through `fln check-source` over `prelude` +
//! `Init.Core`. Every program here was run through the pinned `lean` v4.32.0 with the same header
//! first (2026-10-11), with the same verdict, and is compared with the pinned binary again when it
//! is present.
#![forbid(unsafe_code)]
use std::path::{Path, PathBuf};
use std::process::Command;

const HEADER: &str = "prelude\nimport Init.Core\n";

const ACCEPTED: &[(&str, &str)] = &[
    (
        "pair",
        "def f : Nat × Nat → Nat := fun (x, y) => x + y\nexample : f (2, 3) = 5 := rfl\n",
    ),
    (
        "argument",
        "def g (h : Nat × Nat → Nat) : Nat := h (1, 2)\n\
         def f : Nat := g (fun (x, y) => x * 10 + y)\nexample : f = 12 := rfl\n",
    ),
    (
        "triple",
        "def f : Nat × Nat × Nat → Nat := fun (x, y, z) => x + y + z\n\
         example : f (1, 2, 3) = 6 := rfl\n",
    ),
];

const REFUSED: &[(&str, &str)] = &[
    (
        "wrong_value",
        "def f : Nat × Nat → Nat := fun (x, y) => x + y\nexample : f (2, 3) = 6 := rfl\n",
    ),
    (
        "not_a_pair",
        "structure P where\n  a : Nat\n  b : Nat\ndef f : P → Nat := fun (x, y) => x + y\n",
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
        "fln-fun-tuple-binders-{}-{}",
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
fn a_tuple_binder_is_a_pair_pattern() {
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
