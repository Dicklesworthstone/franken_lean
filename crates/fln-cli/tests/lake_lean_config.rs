//! Installed native Lake configuration loading and checked `.olean` publication.
//! The only imported implementation data is the actual pinned Init/FilePath closure.
#![forbid(unsafe_code)]

use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::{Instant, SystemTime, UNIX_EPOCH};

static NEXT: AtomicUsize = AtomicUsize::new(0);

struct Package {
    root: PathBuf,
    reference: PathBuf,
}

impl Package {
    fn new(reference: PathBuf) -> Self {
        let stamp = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let root = std::env::temp_dir().join(format!(
            "fln-lake-lean-config-{}-{stamp}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed),
        ));
        // A fresh test invocation must not inherit an earlier artifact or record,
        // including hosts whose isolated process namespaces reuse the same PID.
        std::fs::create_dir(&root).unwrap();
        Self { root, reference }
    }

    fn write(&self, relative: &str, source: impl AsRef<[u8]>) {
        let path = self.root.join(relative);
        std::fs::create_dir_all(path.parent().unwrap()).unwrap();
        std::fs::write(path, source).unwrap();
    }

    fn lake(&self, arguments: &[&str]) -> Output {
        let started = Instant::now();
        eprintln!(
            "[lake-lean-config] {arguments:?} in {}: starting",
            self.root.display()
        );
        let output = Command::new(env!("CARGO_BIN_EXE_lake"))
            .arg("--dir")
            .arg(&self.root)
            .args(["--json", "--jobs", "1"])
            .args(arguments)
            .env("LEAN_PATH", &self.reference)
            .env("FLN_IMPORT_REUSE_DIR", self.root.join(".records"))
            .output()
            .unwrap();
        eprintln!(
            "[lake-lean-config] {arguments:?}: {} after {:?}",
            output.status,
            started.elapsed()
        );
        output
    }

    fn artifact(&self, module: &str) -> PathBuf {
        self.root
            .join("products/native/lib/lean")
            .join(module.replace('.', "/"))
            .with_extension("olean")
    }
}

fn reference_lib() -> Option<PathBuf> {
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
        .filter(|lib| lib.join("Init/System/FilePath.olean").is_file());
    assert!(
        lib.is_some() || std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
        "the actual pinned Reference FilePath artifacts are required"
    );
    if lib.is_none() {
        eprintln!("SKIP: pinned Reference FilePath artifacts absent");
    }
    lib
}

fn success(output: Output) -> String {
    assert!(output.status.success(), "{output:?}");
    assert!(output.stderr.is_empty(), "{output:?}");
    String::from_utf8(output.stdout).unwrap()
}

fn failure(output: Output) -> String {
    assert_eq!(output.status.code(), Some(1), "{output:?}");
    assert!(
        output.stdout.is_empty(),
        "partial output escaped: {output:?}"
    );
    String::from_utf8(output.stderr).unwrap()
}

fn assert_reused_configuration(report: &str) {
    assert!(
        report.contains(
            "\"configuration_imports\":[{\"trust\":\"reuse-verified\",\"admission\":\"reused\""
        ),
        "unchanged configuration imports must reuse the recorded admission: {report}"
    );
    assert!(report.contains("\"councilModules\":0"), "{report}");
    assert!(report.contains("\"record\":\"hit\""), "{report}");
}

fn inspect(path: &Path) -> String {
    success(
        Command::new(env!("CARGO_BIN_EXE_fln"))
            .args(["olean", "inspect", "--constants"])
            .arg(path)
            .output()
            .unwrap(),
    )
}

const CONFIG: &str = r#"import Lake
open System Lake DSL
def folder (suffix : String) : FilePath := FilePath.mk ("sources/" ++ suffix)
def products (suffix : String) : FilePath := FilePath.mk ("products/" ++ suffix)
def countDown : Nat → Nat
  | 0 => 0
  | Nat.succ n => countDown n + 1
def unusedComputation : Nat := countDown 10000000
local notation "◆" s => folder s
package native where
  srcDir := ◆ "first"
  buildDir := products "native"
@[default_target] lean_lib Demo where
  srcDir := FilePath.mk ("pro" ++ "ofs")
"#;

#[test]
fn checked_lean_configuration_builds_real_modules_and_refuses_atomically() {
    let Some(reference) = reference_lib() else {
        return;
    };
    let package = Package::new(reference);
    package.write("lakefile.lean", CONFIG);
    package.write("lean-toolchain", "leanprover/lean4:v4.32.0\n");
    for (source, declaration) in [("first", "original"), ("second", "changed")] {
        package.write(
            &format!("sources/{source}/proofs/Demo/Base.lean"),
            format!("prelude\ndef Demo.{declaration} (A : Type) (a : A) : A := a\n"),
        );
        package.write(
            &format!("sources/{source}/proofs/Demo.lean"),
            format!("prelude\nimport Demo.Base\ndef Demo.exported (A : Type) (a : A) : A := Demo.{declaration} A a\n"),
        );
        package.write(
            &format!("sources/{source}/proofs/Demo/Unused.lean"),
            "this unrelated source is deliberately invalid\n",
        );
    }

    let presence = success(package.lake(&["check-build"]));
    assert!(presence.contains("\"targets\":[\"Demo\"]"), "{presence}");
    assert!(
        presence.contains("\"configuration_imports\":[{"),
        "{presence}"
    );
    // This is the one cold configuration admission. A fresh directory and a
    // fixed installed executable make the following cache hits meaningful.
    assert!(presence.contains("\"admission\":\"council\""), "{presence}");
    assert!(
        presence.contains("\"recordWrite\":\"stored\""),
        "{presence}"
    );
    assert!(!package.root.join("products").exists());
    let built = success(package.lake(&["build", "+Demo:olean"]));
    assert!(built.contains("\"modules_built\":2"), "{built}");
    assert!(
        built.contains("\"imports\":[],\"configuration_imports\":[{"),
        "{built}"
    );
    assert_reused_configuration(&built);
    assert!(inspect(&package.artifact("Demo.Base")).contains("Demo.original"));
    assert!(inspect(&package.artifact("Demo")).contains("Demo.exported"));
    assert!(!package.artifact("Demo.Unused").exists());
    assert!(
        !package
            .root
            .join(".lake/build/lib/lean/Demo.olean")
            .exists()
    );

    // The same checked helper, called with different user data, chooses the other
    // source tree. Neither its body nor the field is parsed as a Rust path string.
    let changed_config = CONFIG.replace("◆ \"first\"", "◆ \"second\"");
    package.write("lakefile.lean", &changed_config);
    let rebuilt = success(package.lake(&["build", "+Demo:olean"]));
    assert_reused_configuration(&rebuilt);
    let changed = inspect(&package.artifact("Demo.Base"));
    assert!(changed.contains("Demo.changed"), "{changed}");
    assert!(!changed.contains("Demo.original"), "{changed}");

    // Independently re-admit the produced closure and check a downstream client.
    package.write(
        "Use.lean",
        "prelude\nimport Demo\ndef imported (A : Type) (a : A) : A := Demo.exported A a\n",
    );
    let checked = success(
        Command::new(env!("CARGO_BIN_EXE_fln"))
            .args(["check-source", "--json", "--import-posture", "recheck"])
            .arg(package.root.join("Use.lean"))
            .env("LEAN_PATH", package.root.join("products/native/lib/lean"))
            .env("FLN_IMPORT_REUSE_DIR", package.root.join(".records"))
            .output()
            .unwrap(),
    );
    assert!(checked.contains("\"outcome\":\"complete\""), "{checked}");

    let base = std::fs::read(package.artifact("Demo.Base")).unwrap();
    let top = std::fs::read(package.artifact("Demo")).unwrap();
    for (case, invalid) in [
        changed_config.replace("srcDir := ◆ \"second\"", "srcDir := (42 : Nat)"),
        format!("{changed_config}\ndef invalidUnused : Nat := \"wrong\"\n"),
        changed_config.replace("products \"native\"", "FilePath.mk \"../escape\""),
        changed_config.replace(
            "srcDir := ◆ \"second\"",
            "srcDir := ◆ \"second\"\n  moreLeanArgs := #[\"--unexpected\"]",
        ),
        format!("{changed_config}\nlean_exe Main\n"),
        changed_config
            .replace(
                "package native where",
                "unsafe def unavailable : FilePath := FilePath.mk \"sources/second\"\npackage native where",
            )
            .replace("srcDir := ◆ \"second\"", "srcDir := unavailable"),
        changed_config
            .replace(
                "package native where",
                "@[extern \"foreign\"] def unavailable : FilePath := FilePath.mk \"sources/second\"\npackage native where",
            )
            .replace("srcDir := ◆ \"second\"", "srcDir := unavailable"),
        format!("{changed_config}{}", " ".repeat(65 * 1024)),
    ].into_iter().enumerate() {
        eprintln!("[lake-lean-config] atomic refusal case {case}");
        package.write("lakefile.lean", invalid);
        failure(package.lake(&["build", "+Demo:olean"]));
        assert_eq!(std::fs::read(package.artifact("Demo.Base")).unwrap(), base);
        assert_eq!(std::fs::read(package.artifact("Demo")).unwrap(), top);
        assert!(!package.root.join(".lake/build/lib/lean").exists());
    }

    package.write(
        "lakefile.lean",
        changed_config.replace("@[default_target] ", ""),
    );
    let no_default = failure(package.lake(&["check-build"]));
    assert!(
        no_default.contains("no default build targets"),
        "{no_default}"
    );
    assert_eq!(std::fs::read(package.artifact("Demo")).unwrap(), top);
}
