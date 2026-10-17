//! Name literals (`` `a.b ``, `Term.quotedName`), checked over the pinned `Init.Core` closure. The
//! pin's `elabQuotedName` is `toExpr` of the name (`Name.toExprAux`, Lean/ToExpr.lean): for one to
//! eight components it is `Lean.Name.mkStrN`, otherwise `Lean.Name.str` nested from
//! `Lean.Name.anonymous`. Every program here was run through the pinned `lean` v4.32.0 with the
//! same header first (2026-10-11), with the same verdict.
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
        "fln-quoted-names-{case}-{}-{}",
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
fn name_literals_are_the_pins_name_values() {
    let Some(lib) = pinned_lib() else { return };
    let root = workspace("accepted");
    for (name, program) in [
        (
            "dotted",
            "theorem t : `foo.bla = Lean.Name.str (Lean.Name.str Lean.Name.anonymous \"foo\") \"bla\" := rfl\n",
        ),
        (
            "escaped",
            "theorem t : `«a b».c = Lean.Name.mkStr2 \"a b\" \"c\" := rfl\n",
        ),
        (
            "simple",
            "theorem t : `foo = Lean.Name.mkStr1 \"foo\" := rfl\n",
        ),
        (
            "nine",
            "theorem t : `a.b.c.d.e.f.g.h.i = Lean.Name.str `a.b.c.d.e.f.g.h \"i\" := rfl\n",
        ),
    ] {
        let (code, stdout, stderr) = check(&lib, &root, name, program);
        assert_eq!(code, 0, "{name}: {program}\n{stdout}\n{stderr}");
    }
}

#[test]
fn name_literal_refusals_match_the_pin() {
    let Some(lib) = pinned_lib() else { return };
    let root = workspace("refused");
    for (name, program, pin) in [
        (
            "different",
            "theorem t : `foo = `bar := rfl\n",
            "Not a definitional equality",
        ),
        ("type", "def n : String := `foo\n", "Type mismatch"),
        (
            "unknown_constant",
            "def n := ``doesNotExist\n",
            "Unknown constant `doesNotExist`",
        ),
    ] {
        let (code, stdout, stderr) = check(&lib, &root, name, program);
        assert_ne!(
            code, 0,
            "{name} accepted (the pin: {pin}): {program}\n{stdout}"
        );
        assert!(stderr.contains("\"outcome\""), "{name}: {stderr}");
    }
}
