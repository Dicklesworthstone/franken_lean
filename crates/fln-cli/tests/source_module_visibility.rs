//! Installed source doors preserve the module header's private semantics.
#![forbid(unsafe_code)]

use std::path::PathBuf;
use std::process::{Command, Output};
use std::sync::atomic::{AtomicUsize, Ordering};

static NEXT: AtomicUsize = AtomicUsize::new(0);
struct Project(PathBuf);
impl Project {
    fn new() -> Self {
        let path = std::env::temp_dir().join(format!(
            "fln-module-visibility-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed),
        ));
        std::fs::create_dir(&path).unwrap();
        Self(path)
    }
    fn write(&self, path: &str, source: &str) {
        std::fs::write(self.0.join(path), source).unwrap();
    }
    fn fln(&self, command: &str) -> Output {
        Command::new(env!("CARGO_BIN_EXE_fln"))
            .args([command, "--json", "Main.lean"])
            .current_dir(&self.0)
            .env("LEAN_PATH", &self.0)
            .output()
            .unwrap()
    }
    fn complete(&self, command: &str) -> String {
        let output = self.fln(command);
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert!(output.stderr.is_empty());
        let result = String::from_utf8(output.stdout).unwrap();
        assert!(result.contains("\"outcome\":\"complete\""), "{result}");
        result
    }
    fn refused(&self, command: &str) -> String {
        let output = self.fln(command);
        assert!(!output.status.success());
        assert!(
            output.stdout.is_empty(),
            "failed module exposed partial output"
        );
        String::from_utf8(output.stderr).unwrap()
    }
}
impl Drop for Project {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

const ID: &str = "def identity.{u} {A : Sort u} (x : A) : A := x";
const PRIVATE_ID: &str = "module\nprelude\ndef identity.{u} {A : Sort u} (x : A) : A := x\ndef again.{u} {A : Sort u} (x : A) : A := identity x";

#[test]
fn installed_check_run_and_lean_accept_private_module_commands() {
    let p = Project::new();
    p.write("Main.lean", PRIVATE_ID);
    p.complete("check-source");
    p.complete("run");
    let output = Command::new(env!("CARGO_BIN_EXE_lean"))
        .arg("Main.lean")
        .current_dir(&p.0)
        .env("LEAN_PATH", &p.0)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(output.stdout.is_empty());
    assert!(output.stderr.is_empty());
    p.write("Main.lean", &format!("{PRIVATE_ID}\n#check identity"));
    assert!(p.complete("run").contains("\"checks\":1"));
    let output = Command::new(env!("CARGO_BIN_EXE_lean"))
        .arg("Main.lean")
        .current_dir(&p.0)
        .env("LEAN_PATH", &p.0)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(output.stdout, b"identity.{u} {A : Sort u} (x : A) : A\n");
    assert!(output.stderr.is_empty());
    // A module-system prelude receives no synthetic Nat declarations.
    p.write("Main.lean", "module\nprelude\ndef seedLeak : Nat := 0");
    p.refused("check-source");
    p.refused("run");
    p.write("Main.lean", PRIVATE_ID);
    p.complete("check-source");
}

#[test]
fn installed_imports_keep_private_siblings_and_transitive_imports_hidden() {
    let p = Project::new();
    p.write("A.lean", PRIVATE_ID);
    p.write("B.lean", PRIVATE_ID);
    p.write("Main.lean", "prelude\nimport A\nimport B");
    assert!(p.complete("check-source").contains("\"files\":3"));
    p.complete("run");
    p.write(
        "Main.lean",
        "prelude\nimport A\ndef stolen.{u} {A : Sort u} (x : A) : A := identity x",
    );
    p.refused("check-source");
    p.refused("run");
    p.write("A.lean", ID);
    p.write(
        "B.lean",
        "module\nprelude\nimport A\ndef localUse.{u} {A : Sort u} (x : A) : A := identity x",
    );
    p.write(
        "Main.lean",
        "prelude\nimport B\ndef use.{u} {A : Sort u} (x : A) : A := identity x",
    );
    p.refused("check-source");
    p.refused("run");
    p.write(
        "Main.lean",
        "prelude\nimport B\nimport A\ndef use.{u} {A : Sort u} (x : A) : A := identity x",
    );
    p.complete("check-source");
    p.complete("run");
}

#[test]
fn installed_module_uses_actual_init_and_prelude_suppresses_it() {
    let p = Project::new();
    p.write("Init.lean", &format!("prelude\n{ID}"));
    p.write(
        "Main.lean",
        "module\ndef use.{u} {A : Sort u} (x : A) : A := identity x",
    );
    assert!(p.complete("check-source").contains("\"files\":2"));
    p.complete("run");
    p.write(
        "Main.lean",
        "module\nprelude\ndef use.{u} {A : Sort u} (x : A) : A := identity x",
    );
    p.refused("check-source");
    p.refused("run");
}

#[test]
fn unsupported_visibility_refuses_before_missing_import_io() {
    let p = Project::new();
    for clause in [
        "public import Missing",
        "meta import Missing",
        "import all Missing",
    ] {
        p.write(
            "Main.lean",
            &format!("\u{feff}module\r\nprelude\r\n{clause}"),
        );
        for command in ["check-source", "run"] {
            let error = p.refused(command);
            let field = if command == "check-source" {
                "outcome"
            } else {
                "class"
            };
            assert!(
                error.contains(&format!("\"{field}\":\"capability\"")),
                "{error}"
            );
            assert!(error.contains("\"authority\":false"), "{error}");
            assert!(error.contains("not implemented"), "{error}");
        }
    }
    for modifier in ["public", "meta", "expose"] {
        p.write("Main.lean", &format!("module\nprelude\n{modifier} {ID}"));
        p.refused("check-source");
        p.refused("run");
    }
    p.write("Main.lean", PRIVATE_ID);
    p.complete("check-source");
}
