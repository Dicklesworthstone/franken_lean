//! Installed-command coverage for native proof-carrying equality decisions.
#![forbid(unsafe_code)]
use std::{
    path::PathBuf,
    process::Command,
    sync::atomic::{AtomicUsize, Ordering},
};
static NEXT: AtomicUsize = AtomicUsize::new(0);

fn pinned_reference() -> (PathBuf, PathBuf) {
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
        .filter(|lib| lib.join("Init/Data/Repr.olean").is_file())
        .expect("the pinned Reference library is required for this comparison");
    let reference = lib.parent().unwrap().parent().unwrap().join("bin/lean");
    assert!(reference.is_file());
    let version = Command::new(&reference).arg("--githash").output().unwrap();
    assert!(version.status.success(), "{reference:?}: {version:?}");
    assert_eq!(
        String::from_utf8_lossy(&version.stdout).trim(),
        fln::OLEAN_PIN_COMMIT,
        "the comparison requires the pinned Reference commit"
    );
    (lib, reference)
}

#[test]
fn installed_command_executes_imported_native_natural_equality_decisions() {
    let (lib, reference) = pinned_reference();
    let directory = std::env::temp_dir().join(format!(
        "fln-native-nat-equality-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::create_dir(&directory).unwrap();
    let path = directory.join("proof.lean");
    let source = "prelude\nimport Init.Data.Repr\n\
        def chooseEq (n m : Nat) : Nat := if _h : n = m then 7 else 9\n\
        #eval chooseEq 0 0\n\
        #eval chooseEq 0 7\n\
        #eval chooseEq 18446744073709551616 18446744073709551616\n\
        #eval chooseEq 18446744073709551617 18446744073709551616\n";
    std::fs::write(&path, source).unwrap();
    for mut command in [
        Command::new(reference),
        Command::new(env!("CARGO_BIN_EXE_lean")),
    ] {
        let executable = command.get_program().to_owned();
        let output = command.arg(&path).env("LEAN_PATH", &lib).output().unwrap();
        assert_eq!(
            output.status.code(),
            Some(0),
            "{executable:?}: {}{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
        assert_eq!(output.stdout, b"7\n9\n7\n9\n", "{executable:?}");
        assert!(output.stderr.is_empty(), "{executable:?}: {output:?}");
    }
    assert_eq!(std::fs::read_to_string(&path).unwrap(), source);
}

#[test]
#[ignore = "whole pinned Init cold admission; required scheduled Reference release lane"]
fn installed_command_imports_headerless_init_and_repeated_tag_module_closure() {
    let (lib, reference) = pinned_reference();
    for suffix in ["olean", "olean.server", "olean.private", "ir"] {
        assert!(
            lib.join(format!("Init.{suffix}")).is_file(),
            "missing pinned Init.{suffix}"
        );
    }
    let directory = std::env::temp_dir().join(format!(
        "fln-init-tag-import-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::create_dir(&directory).unwrap();
    let records = directory.join("records");
    std::fs::create_dir(&records).unwrap();
    let cases: [(&str, &str, &[u8]); 2] = [
        ("warm.lean", "def warm : Nat := 1\n#eval warm\n", b"1\n"),
        (
            "control.lean",
            "prelude\nimport Init.Control.Except\nimport Init.Data.List.Control\nimport Init.System.IO\ndef x : Nat := 1\n",
            b"",
        ),
    ];
    for (file, source, _) in &cases {
        std::fs::write(directory.join(file), source).unwrap();
    }
    for (native, executable) in [
        (false, reference.as_path()),
        (true, std::path::Path::new(env!("CARGO_BIN_EXE_lean"))),
    ] {
        if native {
            assert_eq!(
                std::fs::read_dir(&records).unwrap().count(),
                0,
                "the first native import must use a fresh record store"
            );
        }
        for (file, source, expected) in &cases {
            eprintln!("checking installed Init import: {executable:?} {file}");
            let mut command = Command::new(executable);
            command.arg(directory.join(file)).env("LEAN_PATH", &lib);
            if native {
                command.env("FLN_IMPORT_REUSE_DIR", &records);
            }
            let output = command.output().unwrap();
            assert_eq!(
                output.status.code(),
                Some(0),
                "{executable:?} {file}: {output:?}"
            );
            assert_eq!(output.stdout.as_slice(), *expected, "{executable:?} {file}");
            assert!(
                output.stderr.is_empty(),
                "{executable:?} {file}: {output:?}"
            );
            assert_eq!(
                std::fs::read_to_string(directory.join(file)).unwrap(),
                *source
            );
        }
    }
}

#[test]
fn installed_command_checks_generic_equality_without_publishing_a_bad_suffix() {
    let directory = std::env::temp_dir().join(format!(
        "fln-equality-decisions-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::create_dir(&directory).unwrap();
    let prefix = directory.join("prefix.lean");
    let proof = directory.join("proof.lean");
    let prefix_source =
        "def choose {A : Type} [DecidableEq A] (a b : A) : Nat := if a = b then 7 else 9";
    let valid = r#"
        theorem arithmetic : 2 + 3 = 5 := by decide
        theorem different : Not (2 = 3) := by decide
        theorem booleans : Not (true = false) := by decide
        theorem positive_branch : choose 4 4 = 7 := by rfl
        theorem negative_branch : choose true false = 9 := by rfl
    "#;
    std::fs::write(&prefix, prefix_source).unwrap();
    let mut successful_output = None;
    for source in [
        valid,
        "theorem invalid : 2 = 3 := by decide",
        "theorem invalid : Not (true = true) := by decide",
        valid,
    ] {
        std::fs::write(&proof, source).unwrap();
        let output = Command::new(env!("CARGO_BIN_EXE_fln"))
            .args(["check-source", "--json"])
            .arg(&prefix)
            .arg(&proof)
            .output()
            .unwrap();
        if source == valid {
            assert_eq!(
                output.status.code(),
                Some(0),
                "{}",
                String::from_utf8_lossy(&output.stderr)
            );
            assert!(output.stderr.is_empty());
            let text = String::from_utf8(output.stdout).unwrap();
            for required in [
                "\"schema\":\"fln.source-check/1\"",
                "\"outcome\":\"complete\"",
                "\"authority\":true",
                "\"files\":2",
                "\"commands\":6",
                "\"theorems\":5",
                "\"executed\":false",
            ] {
                assert!(text.contains(required), "{text}");
            }
            if let Some(previous) = &successful_output {
                assert_eq!(&text, previous, "recovery must be deterministic");
            } else {
                successful_output = Some(text);
            }
        } else {
            assert_eq!(output.status.code(), Some(1));
            assert!(output.stdout.is_empty(), "no partial successful receipt");
            assert!(!output.stderr.is_empty());
            assert!(!String::from_utf8_lossy(&output.stderr).contains("\"authority\":true"));
        }
        assert_eq!(std::fs::read_to_string(&prefix).unwrap(), prefix_source);
        assert_eq!(std::fs::read_to_string(&proof).unwrap(), source);
        assert_eq!(std::fs::read_dir(&directory).unwrap().count(), 2);
    }
}
