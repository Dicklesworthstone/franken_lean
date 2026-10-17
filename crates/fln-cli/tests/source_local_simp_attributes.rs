//! `attribute [local simp] x`: a rule of `simp`'s default set until the enclosing `section` or
//! `namespace` ends (or for the body of `… in`), never registered, as the pin keeps local
//! attributes out of the `.olean`. `simp only` does not read it. Through `fln check-source` over
//! `prelude` with `Init.Core`, `Init.SimpLemmas` and `Init.Data.Nat.Basic`. Every program here was
//! run through the pinned `lean` v4.32.0 with the same header first (2026-10-12), with the same
//! verdict, and is compared with the pinned binary again when it is present.
#![forbid(unsafe_code)]
use std::path::{Path, PathBuf};
use std::process::Command;

const HEADER: &str =
    "prelude\nimport Init.Core\nimport Init.SimpLemmas\nimport Init.Data.Nat.Basic\n";

const ACCEPTED: &[(&str, &str)] = &[
    (
        "section",
        "def two : Nat := 2\ntheorem two_eq : two = 2 := rfl\nsection\nattribute [local simp] two_eq\nexample : two + 1 = 3 := by simp\nend\n",
    ),
    (
        "in",
        "def two : Nat := 2\ntheorem two_eq : two = 2 := rfl\nattribute [local simp] two_eq in\nexample : two + 1 = 3 := by simp\n",
    ),
    (
        "namespace",
        "def two : Nat := 2\ntheorem two_eq : two = 2 := rfl\nnamespace N\nattribute [local simp] two_eq\nexample : two + 1 = 3 := by simp\nend N\n",
    ),
    (
        "top",
        "def two : Nat := 2\ntheorem two_eq : two = 2 := rfl\nattribute [local simp] two_eq\nexample : two + 1 = 3 := by simp\n",
    ),
];

const REFUSED: &[(&str, &str)] = &[
    (
        "after_end",
        "def two : Nat := 2\ntheorem two_eq : two = 2 := rfl\nsection\nattribute [local simp] two_eq\nend\nexample : two + 1 = 3 := by simp\n",
    ),
    (
        "in_after",
        "def two : Nat := 2\ntheorem two_eq : two = 2 := rfl\nattribute [local simp] two_eq in\nexample : two + 1 = 3 := by simp\nexample : two + 1 = 3 := by simp\n",
    ),
    (
        "only",
        "def two : Nat := 2\ntheorem two_eq : two = 2 := rfl\nsection\nattribute [local simp] two_eq\nexample : two + 1 = 3 := by simp only []\nend\n",
    ),
    (
        "unknown",
        "section\nattribute [local simp] nothingHere\nend\n",
    ),
    (
        "wrong",
        "def two : Nat := 2\ntheorem two_eq : two = 2 := rfl\nsection\nattribute [local simp] two_eq\nexample : two + 1 = 4 := by simp\nend\n",
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
        "fln-local-simp-{}-{}",
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
fn a_local_simp_rule_holds_to_the_end_of_its_scope() {
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
