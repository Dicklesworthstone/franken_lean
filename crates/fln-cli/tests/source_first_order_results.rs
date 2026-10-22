//! `pure 5 : Option Nat`: the application's type `?f ?α` meets `Option Nat` by the pin's first-order
//! approximation (`processAssignmentFOApprox`): the arguments from the right (`?α := Nat`), then the
//! head (`?f := Option`). Where no approximation can match (`?f ?α` against `Nat`; `?f Bool` against
//! `Option Nat`), it stays the pin's "Type mismatch". The same holds for an application with no
//! explicit argument (`get : ?m ?σ` against `StateM Nat Nat` decides `MonadState Nat (StateM Nat)`),
//! and for a polymorphic result (`modify f : ?m PUnit.{?u+1}` against `StateM Nat ?α`, where the
//! pin's `checkTypesAndAssign` also settles `?u`).
//!
//! Through `fln check-source` over `prelude` with `Init.Control.Except`, `Init.Data.List.Control`
//! and `Init.System.IO`. Every program here was run through the pinned `lean` v4.32.0 with the same
//! header first (2026-10-12; the `StateM` cases 2026-10-21), with the same verdict, and is compared with the pinned binary again
//! when it is present.
#![forbid(unsafe_code)]
use std::path::{Path, PathBuf};
use std::process::Command;

const HEADER: &str =
    "prelude\nimport Init.Control.Except\nimport Init.Data.List.Control\nimport Init.System.IO\n";

const ACCEPTED: &[(&str, &str)] = &[
    (
        "option",
        "def g : Option Nat := pure 5\nexample : g = some 5 := rfl\n",
    ),
    (
        "except",
        "def g : Except String Nat := pure 5\nexample : g = Except.ok 5 := rfl\n",
    ),
    (
        "except_conditional",
        "def g (x : Nat) : Except String Nat := if x > 3 then pure x else throw \"small\"\nexample : g 5 = Except.ok 5 := rfl\nexample : g 1 = Except.error \"small\" := rfl\n",
    ),
    (
        "option_of_list",
        "def g : Option (List Nat) := pure []\nexample : g = some [] := rfl\n",
    ),
    (
        "do_branches",
        "def f (b : Bool) : Except String Nat := do\n  if b then\n    pure 1\n  else\n    pure 0\nexample : f false = Except.ok 0 := rfl\n",
    ),
    ("io", "def g : IO Nat := pure 5\n"),
    ("state_get", "def x : StateM Nat Nat := get\n"),
    ("state_get_the", "def k : StateM Nat Nat := getThe Nat\n"),
    (
        "state_do",
        "def inc : StateM Nat Nat := do\n  let s ← get\n  modify (fun s => s + 1)\n  return s\n",
    ),
    (
        "state_modify_argument",
        "def c {α} (_x : StateM Nat α) : StateM Nat Nat := pure 0\ndef b : StateM Nat Nat := c (modify (fun s => s + 1))\n",
    ),
];

const REFUSED: &[(&str, &str)] = &[
    (
        "option_wrong_value",
        "def g : Option Nat := pure 5\nexample : g = some 6 := rfl\n",
    ),
    ("option_wrong_element", "def g : Option Nat := pure true\n"),
    ("no_type_constructor", "def g : Nat := pure 5\n"),
    ("no_pure_instance", "def g : List Nat := pure 5\n"),
    (
        "except_wrong_value",
        "def g : Except String Nat := pure 5\nexample : g = Except.error \"x\" := rfl\n",
    ),
    ("state_get_wrong_state", "def x : StateM Nat Bool := get\n"),
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
        "fln-first-order-results-{}-{}",
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
fn a_result_type_constructor_is_matched_first_order_as_the_pins() {
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
