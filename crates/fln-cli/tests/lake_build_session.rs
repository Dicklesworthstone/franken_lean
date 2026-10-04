//! Real installed multi-target builds reuse checks, never trusted disk artifacts.
#![forbid(unsafe_code)]
use std::{
    path::{Path, PathBuf},
    process::{Command, Output},
    sync::atomic::{AtomicUsize, Ordering},
};

static NEXT: AtomicUsize = AtomicUsize::new(0);
struct Package(PathBuf);
impl Package {
    fn new(root: &str) -> Self {
        let path = std::env::temp_dir().join(format!(
            "fln-lake-session-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        let package = Self(path);
        package.write(
            "lakefile.toml",
            format!("name = \"incremental\"\n[[lean_lib]]\nname = \"{root}\"\n"),
        );
        package
    }
    fn write(&self, relative: &str, bytes: impl AsRef<[u8]>) {
        let path = self.0.join(relative);
        std::fs::create_dir_all(path.parent().unwrap()).unwrap();
        std::fs::write(path, bytes).unwrap();
    }
    fn build(&self, targets: &[&str], imports: Option<&Path>) -> Output {
        Command::new(env!("CARGO_BIN_EXE_lake"))
            .arg("--dir")
            .arg(&self.0)
            .args(["--json", "build"])
            .args(targets)
            .env("LEAN_PATH", imports.unwrap_or(&self.0.join("no-imports")))
            .output()
            .unwrap()
    }
    fn artifact(&self, name: &str) -> Vec<u8> {
        std::fs::read(
            self.output_dir()
                .join(format!("{}.olean", name.replace('.', "/"))),
        )
        .unwrap()
    }
    fn output_dir(&self) -> PathBuf {
        self.0.join(".lake/build/lib/lean")
    }
}
impl Drop for Package {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}
fn success(output: Output, modules: usize, elaborated: usize, reused: usize) {
    assert!(output.status.success(), "{output:?}");
    assert!(output.stderr.is_empty(), "{output:?}");
    let report = String::from_utf8(output.stdout).unwrap();
    for field in [
        format!("\"modules_built\":{modules}"),
        format!("\"module_elaborations\":{elaborated}"),
        format!("\"module_checks_reused\":{reused}"),
        "\"modules_cached\":0".to_owned(),
        "\"admission\":\"K1+independent-checker\"".to_owned(),
    ] {
        assert!(report.contains(&field), "{field}: {report}");
    }
}
fn failure(output: Output) {
    assert!(!output.status.success(), "{output:?}");
    assert!(output.stdout.is_empty(), "{output:?}");
    assert!(!output.stderr.is_empty(), "{output:?}");
}
const BASE: &str = "prelude\ndef Lib.identity (P : Prop) (h : P) : P := h\n";
fn library() -> Package {
    let package = Package::new("Lib");
    package.write("Lib/Base.lean", BASE);
    for side in ["Left", "Right"] {
        package.write(
            &format!("Lib/{side}.lean"),
            format!("prelude\nimport Lib.Base\ntheorem Lib.{side} (P : Prop) (h : P) : P := Lib.identity P h\n"),
        );
    }
    package
}

#[test]
fn sibling_targets_share_the_checked_dependency_and_keep_artifact_bytes() {
    let package = library();
    success(package.build(&["+Lib.Left:olean"], None), 2, 2, 0);
    let base = package.artifact("Lib.Base");
    let left = package.artifact("Lib.Left");
    success(
        package.build(&["+Lib.Left:olean", "+Lib.Right:olean"], None),
        3,
        3,
        1,
    );
    assert_eq!(package.artifact("Lib.Base"), base);
    assert_eq!(package.artifact("Lib.Left"), left);
    let right = package.artifact("Lib.Right");
    success(
        package.build(&["+Lib.Right:olean", "+Lib.Left:olean"], None),
        3,
        3,
        1,
    );
    assert_eq!(package.artifact("Lib.Right"), right);
    assert_eq!(package.artifact("Lib.Left"), left);
}

#[test]
fn requested_dependency_is_not_elaborated_again_and_duplicate_targets_are_deduplicated() {
    let package = library();
    for targets in [
        ["+Lib.Base:olean", "+Lib.Left:olean", "+Lib.Base:olean"],
        ["+Lib.Left:olean", "+Lib.Base:olean", "+Lib.Left:olean"],
    ] {
        success(package.build(&targets, None), 2, 2, 1);
    }
}

#[test]
fn a_new_invocation_rechecks_source_and_ignores_forged_previous_products() {
    let package = library();
    let targets = ["+Lib.Left:olean", "+Lib.Right:olean"];
    success(package.build(&targets, None), 3, 3, 1);
    let original = package.artifact("Lib.Base");
    package.write(
        ".lake/build/lib/lean/Lib/Base.olean",
        b"forged cache success",
    );
    success(package.build(&targets, None), 3, 3, 1);
    assert_eq!(package.artifact("Lib.Base"), original);
    package.write(
        "Lib/Base.lean",
        format!("{BASE}def Lib.extra (P : Prop) (h : P) : P := h\n"),
    );
    success(package.build(&targets, None), 3, 3, 1);
    assert_ne!(package.artifact("Lib.Base"), original);
}

#[test]
fn a_late_target_failure_cannot_publish_any_cached_or_changed_artifact() {
    let package = library();
    let targets = ["+Lib.Left:olean", "+Lib.Right:olean"];
    success(package.build(&targets, None), 3, 3, 1);
    let original: Vec<_> = ["Lib.Base", "Lib.Left", "Lib.Right"]
        .iter()
        .map(|name| (*name, package.artifact(name)))
        .collect();
    package.write(
        "Lib/Base.lean",
        format!("{BASE}def Lib.changed (P : Prop) (h : P) : P := h\n"),
    );
    package.write(
        "Lib/Right.lean",
        "prelude\nimport Lib.Base\ntheorem invalid (P : Prop) : P := by rfl\n",
    );
    failure(package.build(&targets, None));
    for (name, bytes) in original {
        assert_eq!(package.artifact(name), bytes);
    }
}

#[test]
fn a_previous_target_cannot_lend_an_unimported_source_declaration() {
    let package = library();
    package.write(
        "Lib/Steal.lean",
        "prelude\ndef stolen (P : Prop) (h : P) : P := Lib.identity P h\n",
    );
    failure(package.build(&["+Lib.Left:olean", "+Lib.Steal:olean"], None));
    assert!(!package.output_dir().exists());
}

#[test]
fn changing_external_roots_replaces_the_bound_import_world_without_name_leakage() {
    let producer = Package::new("Ext");
    for side in ["A", "B"] {
        producer.write(
            &format!("Ext/{side}.lean"),
            format!("prelude\ndef Ext.{side} (P : Prop) (h : P) : P := h\n"),
        );
    }
    success(
        producer.build(&["+Ext.A:olean", "+Ext.B:olean"], None),
        2,
        2,
        0,
    );
    let package = Package::new("Lib");
    for (module, import) in [("First", "A"), ("Second", "B"), ("Third", "A")] {
        package.write(
            &format!("Lib/{module}.lean"),
            format!("prelude\nimport Ext.{import}\ndef Lib.{module} (P : Prop) (h : P) : P := Ext.{import} P h\n"),
        );
    }
    let search = producer.output_dir();
    success(
        package.build(
            &["+Lib.First:olean", "+Lib.Second:olean", "+Lib.Third:olean"],
            Some(&search),
        ),
        3,
        3,
        0,
    );
    let before = package.artifact("Lib.Second");
    package.write(
        "Lib/Second.lean",
        "prelude\nimport Ext.B\ndef stolen (P : Prop) (h : P) : P := Ext.A P h\n",
    );
    failure(package.build(&["+Lib.First:olean", "+Lib.Second:olean"], Some(&search)));
    assert_eq!(package.artifact("Lib.Second"), before);
}

/// A module that cannot parse is refused before its implicit `Init` import is
/// resolved or admitted (bead `fln-parse-before-imports-j8p6`). With an empty
/// search path the refusal is the parse error; a parseable module still reaches
/// the import, so the preflight cannot be skipping the import step.
#[test]
fn an_unparseable_module_is_refused_before_its_imports_are_resolved() {
    let package = Package::new("Demo");
    package.write("Demo/Basic.lean", "this is not lean @@@ garbage\n");
    let garbage = package.build(&["+Demo.Basic:olean"], None);
    let stderr = String::from_utf8_lossy(&garbage.stderr).into_owned();
    failure(garbage);
    assert!(stderr.contains("parse refused source"), "{stderr}");
    assert!(!stderr.contains("is neither a source file"), "{stderr}");

    package.write("Demo/Basic.lean", "def answer : Nat := 6 * 7\n");
    let parseable = package.build(&["+Demo.Basic:olean"], None);
    let stderr = String::from_utf8_lossy(&parseable.stderr).into_owned();
    failure(parseable);
    assert!(
        stderr.contains("import `Init` is neither a source file"),
        "{stderr}"
    );
    assert!(!package.output_dir().exists());
}
