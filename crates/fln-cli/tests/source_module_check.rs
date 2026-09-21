//! Installed-command source libraries: imports are checked, never executed.
#![forbid(unsafe_code)]
use std::path::PathBuf;
use std::process::{Command, Output};
use std::sync::atomic::{AtomicUsize, Ordering};

static NEXT: AtomicUsize = AtomicUsize::new(0);
struct Project(PathBuf);
impl Project {
    fn new() -> Self {
        let path = std::env::temp_dir().join(format!(
            "fln-source-modules-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed),
        ));
        std::fs::create_dir(&path).unwrap();
        Self(path)
    }
    fn write(&self, path: &str, text: &str) {
        let path = self.0.join(path);
        std::fs::create_dir_all(path.parent().unwrap()).unwrap();
        std::fs::write(path, text).unwrap();
    }
    fn run(&self, args: &[&str]) -> Output {
        Command::new(env!("CARGO_BIN_EXE_fln"))
            .args(["check-source", "--json"])
            .args(args)
            .current_dir(&self.0)
            .output()
            .unwrap()
    }
    fn complete(&self) -> String {
        let output = self.run(&["Main.lean"]);
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert!(output.stderr.is_empty());
        let stdout = String::from_utf8(output.stdout).unwrap();
        assert!(stdout.contains("\"outcome\":\"complete\""), "{stdout}");
        assert!(stdout.contains("\"executed\":false"), "{stdout}");
        assert_eq!(stdout.lines().count(), 1);
        stdout
    }
    fn refused(&self) -> String {
        let output = self.run(&["Main.lean"]);
        assert!(!output.status.success());
        assert!(
            output.stdout.is_empty(),
            "failed imports exposed a partial receipt"
        );
        let stderr = String::from_utf8(output.stderr).unwrap();
        assert!(
            stderr.contains("\"schema\":\"fln.source-check/1\""),
            "{stderr}"
        );
        stderr
    }
}
impl Drop for Project {
    fn drop(&mut self) {
        std::fs::remove_dir_all(&self.0).unwrap();
    }
}

#[test]
fn checked_libraries_load_nested_imports_records_and_automation_once() {
    let p = Project::new();
    let common = "namespace Library\nstructure Box where\n  value : Nat\ndef wrap.{u} {A : Sort u} (x : A) : A := x\n@[simp] theorem unwrap.{u} {A : Sort u} (x : A) : wrap x = x := by rfl\nend Library";
    let main = "\u{feff}-- 🤖 original file\r\nimport Left Right\r\nopen Library\r\ndef record : Box := { value := 9 }\r\ntheorem use : wrap record.value = 9 := by simp [record]";
    p.write("Lib/Common.lean", common);
    p.write("Left.lean", "import Lib.Common\ndef left := 1");
    p.write("Right.lean", "import Lib.Common\ndef right := 2");
    p.write("Main.lean", main);
    let result = p.complete();
    assert!(result.contains("\"files\":4"), "{result}");
    assert!(result.contains("\"theorems\":2"), "{result}");
    assert_eq!(
        std::fs::read(p.0.join("Main.lean")).unwrap(),
        main.as_bytes()
    );
    assert_eq!(
        std::fs::read(p.0.join("Lib/Common.lean")).unwrap(),
        common.as_bytes()
    );
    assert_eq!(std::fs::read_dir(&p.0).unwrap().count(), 4);
    assert_eq!(std::fs::read_dir(p.0.join("Lib")).unwrap().count(), 1);
}

#[test]
fn isolated_module_elaboration_preserves_instance_choices() {
    let p = Project::new();
    p.write(
        "Choice.lean",
        "instance seven : Inhabited Nat := Inhabited.mk 7",
    );
    p.write("Independent.lean", "def chosen : Nat := default");
    p.write("Main.lean", "import Choice Independent\ntheorem original : chosen = 0 := by rfl\ntheorem current : (default : Nat) = 7 := by rfl");
    p.complete();
    p.write("Independent.lean", "def stolen : Nat := seven.default");
    p.refused();
    p.write("Independent.lean", "def chosen : Nat := default");
    p.complete();
}

#[test]
fn false_dependency_proofs_cycles_and_missing_imports_refuse_and_recover() {
    let p = Project::new();
    p.write(
        "Main.lean",
        "import A\ntheorem use : (0 : Nat) = 0 := by rfl",
    );
    assert!(p.refused().contains("A.lean"));
    for source in [
        "import Main",
        "theorem bad : (0 : Nat) = 1 := by rfl",
        "#eval 42",
    ] {
        p.write("A.lean", source);
        p.refused();
    }
    p.write("A.lean", "theorem good : (1 : Nat) = 1 := by rfl");
    assert!(p.complete().contains("\"files\":2"));
}

#[test]
fn quoted_structural_names_are_not_split_on_literal_dots() {
    let p = Project::new();
    p.write("A.B.lean", "def literal := 7");
    p.write("A/B.lean", "def nested := 9");
    p.write(
        "Main.lean",
        "import «A.B» A.B\ntheorem a : literal = 7 := by rfl\ntheorem b : nested = 9 := by rfl",
    );
    assert!(p.complete().contains("\"files\":3"));
}

#[test]
fn closure_byte_limits_and_multiple_entry_ambiguity_are_fail_closed() {
    let p = Project::new();
    let main = "import A\ndef result := value";
    p.write("Main.lean", main);
    p.write("A.lean", "def value := 7");
    let max = main.len().to_string();
    let output = p.run(&["--max-bytes", &max, "Main.lean"]);
    assert!(!output.status.success());
    assert!(output.stdout.is_empty());
    let output = p.run(&["Main.lean", "A.lean"]);
    assert!(!output.status.success());
    assert!(output.stdout.is_empty());
    assert!(
        String::from_utf8(output.stderr)
            .unwrap()
            .contains("one entry file")
    );
    p.complete();
}

#[test]
fn import_path_traversal_never_becomes_an_outside_file_read() {
    let p = Project::new();
    for module in [
        "«..».Secret",
        "«../Secret»",
        "«/tmp/Secret»",
        "«C:Secret»",
        "«A\\B»",
    ] {
        p.write("Main.lean", &format!("import {module}\ndef use := 0"));
        let error = p.refused();
        assert!(
            error.contains("unsafe filesystem component"),
            "{module}: {error}"
        );
    }
}

#[cfg(unix)]
#[test]
fn symlinked_import_files_and_directories_are_refused() {
    let p = Project::new();
    p.write("Real.lean", "def real := 0");
    std::os::unix::fs::symlink(p.0.join("Real.lean"), p.0.join("Alias.lean")).unwrap();
    p.write("Main.lean", "import Alias");
    assert!(p.refused().contains("symlink"));
    std::fs::create_dir(p.0.join("RealDir")).unwrap();
    p.write("RealDir/Value.lean", "def nested := 1");
    std::os::unix::fs::symlink(p.0.join("RealDir"), p.0.join("AliasDir")).unwrap();
    p.write("Main.lean", "import AliasDir.Value");
    assert!(p.refused().contains("symlink"));
}

#[test]
fn import_free_batch_behavior_and_root_independent_receipts_are_preserved() {
    let first = Project::new();
    let second = Project::new();
    for p in [&first, &second] {
        p.write("Main.lean", "import A\ntheorem use : value = 7 := by rfl");
        p.write("A.lean", "def value := 7");
    }
    assert_eq!(first.complete(), second.complete());
    first.write("Main.lean", "theorem use : value = 7 := by rfl");
    let output = first.run(&["A.lean", "Main.lean"]);
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        String::from_utf8(output.stdout)
            .unwrap()
            .contains("\"files\":2")
    );
}

#[test]
fn shipped_source_library_example_is_checked_by_the_installed_command() {
    let path = fln_core::checked_workspace_root!().join("examples/native_modules/Main.lean");
    let output = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["check-source", "--json"])
        .arg(path)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        String::from_utf8(output.stdout)
            .unwrap()
            .contains("\"files\":3")
    );
}
