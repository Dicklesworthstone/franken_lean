//! Layout columns the pin's parser checks, through the installed drop-in `lean` over `prelude` +
//! `import Init.Core` (bead `fln-layout-column-false-accepts-cbfm`). An application argument must
//! start right of the saved position (`Term.argument := checkWsBefore >> checkColGt >> …`,
//! vendored `Lean/Parser/Term.lean:885`). A command saves its own start (`withPosition`,
//! `Lean/Parser/Module.lean:133`), and a bracket clears the saved position (`withoutPosition`).
//!
//! The pin rejects each refused program below: the term ends before the argument, and the next
//! line is no command. This door refuses them. The accepted controls print what the pin prints.
//! Every program was run through the pinned `lean` v4.32.0 with the same header first
//! (2026-10-22), and the pin is consulted again when it is present.
#![forbid(unsafe_code)]
use std::path::{Path, PathBuf};
use std::process::Command;

const HEADER: &str = "prelude\nimport Init.Core\n";

/// Programs the pin rejects: an argument at the command's own column.
const REFUSED: &[&str] = &[
    "def f (n : Nat) : Nat := n\ndef g : Nat := f\n2\n",
    "def f (n m : Nat) : Nat := n\ndef g : Nat := f 1\n2\n",
];

/// Programs the pin accepts, with its output: the argument indented, inside a bracket, and a
/// whole body starting at column 0 after `:=`, which is no argument.
const ACCEPTED: &[(&str, &str)] = &[
    (
        "def f (n : Nat) : Nat := n\ndef g : Nat := f\n  2\n#check g\n",
        "g : Nat\n",
    ),
    (
        "def f (n : Nat) : Nat := n\ndef g : Nat := (f\n2)\n#check g\n",
        "g : Nat\n",
    ),
    ("def g : Nat :=\n2\n#check g\n", "g : Nat\n"),
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
        "fln-layout-columns-{}-{}",
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
fn an_argument_at_the_commands_column_ends_the_term_as_at_the_pin() {
    let Some(lib) = pinned_lib() else {
        return;
    };
    let root = workspace();
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
    for (index, (program, expected)) in ACCEPTED.iter().enumerate() {
        let entry = root.join(format!("Accepted{index}.lean"));
        std::fs::write(&entry, format!("{HEADER}{program}")).unwrap();
        if let Some((code, stdout)) = pinned(&lib, &entry) {
            assert_eq!((code, stdout.as_str()), (0, *expected), "the pin moved");
        }
        let (code, stdout, stderr) = ours(&lib, &root, &entry);
        assert_eq!(code, 0, "{program}: {stderr}");
        assert_eq!(stdout, *expected, "{program}: {stderr}");
    }
}
