//! Reducibility attributes on a declaration, over the pinned `Init.Core` closure: `@[reducible]`,
//! `@[irreducible]`, `@[implicit_reducible]` and its alias `@[instance_reducible]` set the status
//! the pin's `setReducibilityStatus` sets (vendored Lean/ReducibilityAttrs.lean). It decides what
//! elaboration unfolds: `1 + 2 : T` needs `T := Nat` unfolded, which a semireducible or reducible
//! `T` allows and an irreducible one does not, and `rfl` cannot see through an irreducible `g`. The
//! pin's `validate` transitions are refused as it refuses them. Every program here was run through
//! the pinned `lean` v4.32.0 with the same header first (2026-10-11), with the same verdict.
#![forbid(unsafe_code)]
use std::path::{Path, PathBuf};
use std::process::Command;

const HEADER: &str = "prelude\nimport Init.Core\n";

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

fn workspace(case: &str) -> PathBuf {
    let path = std::env::temp_dir().join(format!(
        "fln-reducibility-attributes-{case}-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos(),
    ));
    std::fs::create_dir(&path).unwrap();
    path
}

/// `fln check-source --json` on `HEADER` + `program`: (exit code, stdout, stderr).
fn check(lib: &Path, root: &Path, name: &str, program: &str) -> (i32, String, String) {
    let entry = root.join(format!("{name}.lean"));
    std::fs::write(&entry, format!("{HEADER}{program}")).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["check-source", "--json"])
        .arg(&entry)
        .env("LEAN_PATH", lib)
        .env("FLN_IMPORT_REUSE_DIR", root.join("records"))
        .output()
        .expect("run the installed CLI");
    (
        output.status.code().expect("normal process exit"),
        String::from_utf8(output.stdout).unwrap(),
        String::from_utf8(output.stderr).unwrap(),
    )
}

#[test]
fn reducibility_attributes_set_the_pins_status() {
    let Some(lib) = pinned_lib() else { return };
    let root = workspace("accepted");
    for (name, program) in [
        (
            "reducible_rfl",
            "@[reducible] def f (n : Nat) : Nat := n + 1\ntheorem t : f 1 = 2 := rfl\n",
        ),
        (
            "irreducible_self",
            "@[irreducible] def g : Nat := 5\ntheorem t : g = g := rfl\n",
        ),
        (
            "reducible_alias",
            "@[reducible] def T := Nat\ndef y : T := 1 + 2\n",
        ),
        (
            "implicit_alias",
            "@[implicit_reducible] def T := Nat\ndef y : T := 1 + 2\n",
        ),
        (
            "instance_reducible",
            "@[instance_reducible] def T := Nat\ndef y : T := 1 + 2\n",
        ),
        (
            "simp_reducible",
            "@[simp, reducible] def f (n : Nat) : Nat := n + 1\ntheorem t : f 1 = 2 := rfl\n",
        ),
        (
            "irreducible_then_use",
            "@[irreducible] def g : Nat := 5\ndef h : Nat := g + 1\n",
        ),
        (
            "namespaced",
            "namespace A\n@[reducible] def T := Nat\nend A\ndef y : A.T := 1 + 2\n",
        ),
        (
            "implicit_then_irreducible",
            "@[implicit_reducible, irreducible] def g : Nat := 5\ntheorem t : g = g := rfl\n",
        ),
        ("plain_alias", "def T := Nat\ndef y : T := 1 + 2\n"),
    ] {
        let (code, _, stderr) = check(&lib, &root, name, program);
        assert_eq!(code, 0, "{name}: {program}\n{stderr}");
    }
}

#[test]
fn reducibility_attributes_the_pin_refuses_are_refused() {
    let Some(lib) = pinned_lib() else { return };
    let root = workspace("refused");
    for (name, program, pin) in [
        (
            "irreducible_rfl",
            "@[irreducible] def g : Nat := 5\ntheorem t : g = 5 := rfl\n",
            "Type mismatch",
        ),
        (
            "irreducible_reducible",
            "@[irreducible, reducible] def f : Nat := 1\n",
            "failed to set `[reducible]`, `f` is not currently `[semireducible]`",
        ),
        (
            "semireducible",
            "@[semireducible] def f : Nat := 1\n",
            "declarations are `[semireducible]` by default",
        ),
        (
            "theorem",
            "@[reducible] theorem t : True := trivial\n",
            "`t` is not a definition",
        ),
        (
            "reducible_abbrev",
            "@[reducible] abbrev A := Nat\n",
            "`A` is not currently `[semireducible]`",
        ),
        (
            "irreducible_abbrev",
            "@[irreducible] abbrev A := Nat\n",
            "`A` is not currently `[semireducible]`",
        ),
        (
            "scoped",
            "@[scoped reducible] def f : Nat := 1\n",
            "Scoped attributes must be used inside namespaces",
        ),
        (
            "args",
            "@[reducible 3] def f : Nat := 1\n",
            "This attribute takes no arguments",
        ),
        (
            "irreducible_alias",
            "@[irreducible] def T := Nat\ndef y : T := 1 + 2\n",
            "failed to synthesize instance",
        ),
        (
            "reducible_twice",
            "@[reducible, reducible] def f : Nat := 1\n",
            "`f` is not currently `[semireducible]`",
        ),
        (
            "opaque",
            "@[reducible] opaque o : Nat\n",
            "`o` is not a definition",
        ),
    ] {
        let (code, _, _) = check(&lib, &root, name, program);
        assert_ne!(code, 0, "{name} was accepted; the pin: {pin}\n{program}");
    }
}
