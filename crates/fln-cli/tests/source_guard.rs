//! `#guard e` through the drop-in `lean`, over the pinned `Init.Guard` closure (which declares the
//! `#guard` syntax, `Bool`, `Decidable` and the notation these programs use). Every program here
//! was run through the pinned `lean` v4.32.0 with the same header first (2026-10-11): the accepted
//! ones print nothing there, and the refused ones fail there ("did not evaluate to `true`", or
//! no `OfNat Bool 3`).
#![forbid(unsafe_code)]
use std::path::{Path, PathBuf};
use std::process::Command;

const HEADER: &str = "prelude\nimport Init.Guard\n";

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
        .filter(|lib| lib.join("Init/Guard.olean").is_file());
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
        "fln-guard-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos(),
    ));
    std::fs::create_dir(&path).unwrap();
    path
}

/// The drop-in `lean` on `HEADER` + `program`: (exit code, stdout, stderr).
fn lean(lib: &Path, root: &Path, name: &str, program: &str) -> (i32, String, String) {
    let entry = root.join(format!("{name}.lean"));
    std::fs::write(&entry, format!("{HEADER}{program}")).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_lean"))
        .arg(&entry)
        .env("LEAN_PATH", lib)
        .env("FLN_IMPORT_REUSE_DIR", root.join("records"))
        .output()
        .expect("run the installed lean");
    (
        output.status.code().expect("normal process exit"),
        String::from_utf8(output.stdout).unwrap(),
        String::from_utf8(output.stderr).unwrap(),
    )
}

#[test]
fn guards_pass_silently_and_a_false_guard_fails() {
    let Some(lib) = pinned_lib() else { return };
    let root = workspace();
    for (name, program) in [
        // The first command of the body: `#guard` is not a header token (`many import` stops).
        ("first", "#guard 1 + 1 == 2\n"),
        ("after_definition", "def x : Nat := 1\n#guard 1 + 1 == 2\n"),
        ("two", "#guard 1 == 1\n#guard 2 == 2\n"),
        ("boolean_operators", "#guard true && !false\n"),
        // A decidable proposition is decided (`decPropToBool`).
        (
            "proposition",
            "def f (n : Nat) : Nat := n * 2\n#guard f 3 = 6\n",
        ),
        ("ascribed_order", "#guard (2 : Nat) < 3\n"),
    ] {
        let (code, stdout, stderr) = lean(&lib, &root, name, program);
        assert_eq!(code, 0, "{program}\n{stdout}\n{stderr}");
        assert!(stdout.is_empty(), "{program}\n{stdout}");
    }
    for (name, program) in [
        ("false", "#guard 1 + 1 == 3\n"),
        (
            "false_proposition",
            "def f (n : Nat) : Nat := n * 2\n#guard f 3 = 7\n",
        ),
    ] {
        let (code, stdout, stderr) = lean(&lib, &root, name, program);
        assert_eq!(code, 1, "{program}\n{stdout}\n{stderr}");
        assert!(
            stderr.contains("did not evaluate to `true`"),
            "{program}\n{stderr}"
        );
    }
    // Not a `Bool` and not a proposition: the pin finds no `OfNat Bool 3`.
    let (code, stdout, stderr) = lean(&lib, &root, "number", "#guard 3\n");
    assert_eq!(code, 1, "#guard 3\n{stdout}\n{stderr}");
}
