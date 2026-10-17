//! A `protected` declaration of this file, through the installed drop-in `lean`, which compiles
//! what it checks: an atomic name does not reach it through its namespace, an `open` or an
//! `export` alias (the pin's `resolveQualifiedName` and `getAliases … (skipProtected :=
//! id.isAtomic)`, vendored `Lean/ResolveName.lean`), and it still runs under its full name. The
//! refused programs include the pin's `tests/elab_fail/protectedAlias.lean`. Over `prelude` +
//! `import Init.Core` + `import Init.Data.Repr`. Every program here was run through the pinned
//! `lean` v4.32.0 with the same header first (2026-10-11), with the same verdict and output, and
//! is compared with the pinned binary again when it is present.
#![forbid(unsafe_code)]
use std::path::{Path, PathBuf};
use std::process::Command;

const HEADER: &str = "prelude\nimport Init.Core\nimport Init.Data.Repr\n";
const DOUBLE: &str = "protected def Nat.double (x : Nat) := 2*x\n";

const REFUSED: &[(&str, &str)] = &[
    (
        "export_alias",
        "namespace Ex\nexport Nat (double)\nend Ex\nopen Ex\n#check Ex.double\n#check double\n",
    ),
    (
        "export_alias_use",
        "namespace Ex\nexport Nat (double)\nend Ex\nopen Ex\ndef y := double 3\n",
    ),
    ("root_alias", "export Nat (double)\ndef y := double 3\n"),
    ("open_namespace", "open Nat\ndef y := double 3\n"),
    (
        "inside_namespace",
        "namespace Nat\ndef y := double 3\nend Nat\n",
    ),
];

const ACCEPTED: &[(&str, &str, &str)] = &[
    (
        "qualified_alias",
        "namespace Ex\nexport Nat (double)\nend Ex\nopen Ex\n#eval Ex.double 3\n",
        "6",
    ),
    (
        "full_name",
        "open Nat\n#eval Nat.double 3\ndef twice (x : Nat) : Nat := Nat.double (Nat.double x)\n\
         #eval twice 5\n",
        "6\n20",
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
        "fln-protected-aliases-{}-{}",
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
fn an_atomic_name_reaches_no_protected_declaration_of_this_file() {
    let Some(lib) = pinned_lib() else {
        return;
    };
    let root = workspace();
    let ours = Path::new(env!("CARGO_BIN_EXE_lean"));
    let pinned = lib
        .parent()
        .and_then(Path::parent)
        .map(|toolchain| toolchain.join("bin/lean"))
        .filter(|lean| lean.is_file());
    for (name, program) in REFUSED {
        let entry = root.join(format!("{name}.lean"));
        std::fs::write(&entry, format!("{HEADER}{DOUBLE}{program}")).unwrap();
        let (code, stdout, _) = run(ours, &lib, &root, &entry);
        assert_ne!(code, 0, "{name}: accepted, printing {stdout}");
        if let Some(pinned) = &pinned {
            assert_ne!(
                run(pinned, &lib, &root, &entry).0,
                0,
                "{name}: the pin accepts it"
            );
        }
    }
    for (name, program, value) in ACCEPTED {
        let entry = root.join(format!("{name}.lean"));
        std::fs::write(&entry, format!("{HEADER}{DOUBLE}{program}")).unwrap();
        let (code, stdout, stderr) = run(ours, &lib, &root, &entry);
        assert_eq!((code, stdout.as_str()), (0, *value), "{name}: {stderr}");
        if let Some(pinned) = &pinned {
            let (code, stdout, stderr) = run(pinned, &lib, &root, &entry);
            assert_eq!(
                (code, stdout.as_str()),
                (0, *value),
                "{name} (pinned): {stderr}"
            );
        }
    }
}
