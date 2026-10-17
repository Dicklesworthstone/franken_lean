//! Installed commands replay only the syntax exported by actual source imports.
#![forbid(unsafe_code)]

use std::path::PathBuf;
use std::process::{Command, Output};
use std::sync::atomic::{AtomicUsize, Ordering};

static NEXT: AtomicUsize = AtomicUsize::new(0);

struct Project(PathBuf);

impl Project {
    fn new() -> Self {
        let path = std::env::temp_dir().join(format!(
            "fln-cli-module-grammar-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed),
        ));
        std::fs::create_dir(&path).unwrap();
        Self(path)
    }

    fn write(&self, name: &str, source: &str) {
        std::fs::write(self.0.join(name), source).unwrap();
    }

    fn invoke(&self, command: &str) -> Output {
        Command::new(env!("CARGO_BIN_EXE_fln"))
            .args([command, "--json", "Main.lean"])
            .current_dir(&self.0)
            .env("LEAN_PATH", self.0.join("no-installed-artifacts"))
            .env("FLN_IMPORT_REUSE_DIR", self.0.join("records"))
            .output()
            .unwrap()
    }

    fn complete(&self, command: &str) -> String {
        let output = self.invoke(command);
        assert!(
            output.status.success(),
            "{command}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert!(output.stderr.is_empty());
        let stdout = String::from_utf8(output.stdout).unwrap();
        assert!(stdout.contains("\"outcome\":\"complete\""), "{stdout}");
        assert_eq!(stdout.lines().count(), 1, "{stdout}");
        stdout
    }

    fn refused(&self, command: &str) -> String {
        let output = self.invoke(command);
        assert!(!output.status.success(), "{command} unexpectedly succeeded");
        assert!(
            output.stdout.is_empty(),
            "a failed source graph exposed a partial result: {}",
            String::from_utf8_lossy(&output.stdout)
        );
        let stderr = String::from_utf8(output.stderr).unwrap();
        assert!(!stderr.is_empty());
        stderr
    }
}

impl Drop for Project {
    fn drop(&mut self) {
        std::fs::remove_dir_all(&self.0).unwrap();
    }
}

#[test]
fn installed_checker_loads_syntax_only_diamonds_before_parsing_consumers() {
    let p = Project::new();
    p.write(
        "Lib.lean",
        "notation \"⟪\" x \"⟫\" => Nat.add x x\nmacro \"checked_rfl\" : tactic => `(tactic| rfl)\n",
    );
    p.write("Left.lean", "import Lib\ndef left := ⟪(10 : Nat)⟫\n");
    p.write("Right.lean", "import Lib\ndef right := ⟪(11 : Nat)⟫\n");
    let main = "import Left\nimport Right\nimport Left\ntheorem answer : left + right = 42 := by checked_rfl\n";
    p.write("Main.lean", main);
    let result = p.complete("check-source");
    assert!(result.contains("\"files\":4"), "{result}");
    assert!(result.contains("\"theorems\":1"), "{result}");
    assert!(result.contains("\"executed\":false"), "{result}");
    assert_eq!(
        std::fs::read(p.0.join("Main.lean")).unwrap(),
        main.as_bytes()
    );
}

#[test]
fn installed_checker_keeps_import_and_scope_boundaries_for_custom_tokens() {
    let p = Project::new();
    p.write("Lib.lean", "notation \"⟪\" x \"⟫\" => Nat.add x x\n");
    p.write("Other.lean", "def stolen := ⟪(2 : Nat)⟫\n");
    p.write("Main.lean", "import Lib\nimport Other\n");
    assert!(p.refused("check-source").contains("Other"));

    p.write(
        "Lib.lean",
        "section\nlocal notation \"⟪\" x \"⟫\" => Nat.add x x\ntheorem internal : ⟪(2 : Nat)⟫ = 4 := rfl\nend\n",
    );
    p.write("Main.lean", "import Lib\n");
    p.complete("check-source");
    p.write(
        "Main.lean",
        "import Lib\ntheorem leaked : ⟪(2 : Nat)⟫ = 4 := rfl\n",
    );
    p.refused("check-source");

    p.write(
        "Lib.lean",
        "namespace Ops\nscoped infixl:65 \" +++ \" => Nat.add\nend Ops\n",
    );
    p.write(
        "Main.lean",
        "import Lib\nsection\nopen scoped Ops\ntheorem works : (2 : Nat) +++ 3 = 5 := rfl\nend\n",
    );
    p.complete("check-source");
    p.write(
        "Main.lean",
        "import Lib\nsection\nopen scoped Ops\ntheorem works : (2 : Nat) +++ 3 = 5 := rfl\nend\ntheorem leaked : (2 : Nat) +++ 3 = 5 := rfl\n",
    );
    p.refused("check-source");
}

#[test]
fn installed_executor_replays_imported_quoted_rules_without_an_ambient_prelude() {
    let p = Project::new();
    p.write(
        "Core.lean",
        "prelude\ninductive Bool where\n  | false\n  | true\n",
    );
    p.write(
        "Lib.lean",
        "prelude\nimport Core\nsyntax (name := «quoted.kind») \"selected \" term:max : term\nmacro_rules | `(selected $x) => `($x)\n",
    );
    p.write(
        "Main.lean",
        "prelude\nimport Lib\n#check Bool\n#eval selected Bool.true\n",
    );
    let result = p.complete("run");
    assert!(
        result.contains("\"kind\":\"bool\",\"value\":true"),
        "{result}"
    );
    assert!(result.contains("\"module\":\"Core\""), "{result}");
    assert!(result.contains("\"module\":\"Lib\""), "{result}");
    assert!(result.contains("\"module\":\"Main\""), "{result}");

    // A fresh invocation must observe the edited syntax-only dependency, even
    // though it contains no ordinary declaration that could anchor a change.
    p.write(
        "Lib.lean",
        "prelude\nimport Core\nsyntax (name := «quoted.kind») \"selected \" term:max : term\nmacro_rules | `(selected $x) => `(Bool.false)\n",
    );
    let changed = p.complete("run");
    assert!(
        changed.contains("\"kind\":\"bool\",\"value\":false"),
        "{changed}"
    );

    p.write(
        "Main.lean",
        "prelude\nimport Lib\n#eval selected Bool.true\n#eval missing\n",
    );
    p.refused("run");
}
