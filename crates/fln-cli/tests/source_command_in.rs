//! `<command> in <command>` (`Lean.Parser.Command.in`): the pin's macro elaborates it as
//! `section <head> <body> end`, so what the head binds or opens holds for the body alone. Heads:
//! `variable`, `universe`, `include`, an explicit `open Ns (a)`. A global `attribute [a] x in …`
//! is the pin's error ("Despite the `in`, the attribute … is added globally").
//!
//! Through `fln check-source` over `prelude` with `Init.Core`, `Init.SimpLemmas` and
//! `Init.Data.Nat.Basic`. Every program here was run through the pinned `lean` v4.32.0 with the
//! same header first (2026-10-12), with the same verdict, and is compared with the pinned binary
//! again when it is present.
#![forbid(unsafe_code)]
use std::path::{Path, PathBuf};
use std::process::Command;

const HEADER: &str =
    "prelude\nimport Init.Core\nimport Init.SimpLemmas\nimport Init.Data.Nat.Basic\n";

const ACCEPTED: &[(&str, &str)] = &[
    (
        "variable_definition",
        "variable (n : Nat) in\ndef f := n + 1\ntheorem t : f 2 = 3 := rfl\n",
    ),
    (
        "variable_implicit",
        "variable {n : Nat} in\ntheorem t1 : n = n := rfl\ntheorem t2 : (5 : Nat) = 5 := t1\n",
    ),
    (
        "universe",
        "universe u in\ndef idd (α : Sort u) (a : α) : α := a\ntheorem t : idd Nat 3 = 3 := rfl\n",
    ),
    (
        "explicit_open",
        "open Nat (succ) in\ntheorem t : succ 1 = 2 := rfl\n",
    ),
    (
        "include",
        "variable (n : Nat) (h : n = n)\ninclude h in\ntheorem t : True := trivial\n",
    ),
];

const REFUSED: &[(&str, &str)] = &[
    (
        "variable_scope_ends",
        "variable (n : Nat) in\ndef f := n + 1\ndef g := n\n",
    ),
    (
        "variable_wrong_value",
        "variable (n : Nat) in\ndef f := n + 1\ntheorem t : f 2 = 4 := rfl\n",
    ),
    (
        "explicit_open_scope_ends",
        "open Nat (succ) in\ntheorem t : succ 1 = 2 := rfl\ntheorem t2 : succ 1 = 2 := rfl\n",
    ),
    (
        "global_simp_attribute",
        "def two : Nat := 2\ntheorem two_eq : two = 2 := rfl\nattribute [simp] two_eq in\nexample : two + 1 = 3 := by simp\n",
    ),
    (
        "global_instance_attribute",
        "class C where\n  v : Nat\ndef inst : C := ⟨3⟩\nattribute [instance] inst in\nexample : C.v = 3 := rfl\n",
    ),
    ("nothing_after", "variable (n : Nat) in\n"),
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
        "fln-command-in-{}-{}",
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
fn a_command_in_a_command_is_a_section_around_both() {
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
