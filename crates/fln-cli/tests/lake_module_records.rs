//! Installed `lake build` reuses checked source modules across invocations by content,
//! re-admitting each one from its record, and never by path or mtime (bead
//! `franken_lean-z8j.1.1`, criterion 3). Every invocation logs its argv, exit code,
//! stdout and stderr, so a failure shows the whole exchange.
#![forbid(unsafe_code)]
use std::{
    path::{Path, PathBuf},
    process::{Command, Output},
    sync::atomic::{AtomicUsize, Ordering},
};

static NEXT: AtomicUsize = AtomicUsize::new(0);

/// A fresh package with its own record store, so no test reads another's records or
/// the user's.
struct Package(PathBuf);
impl Package {
    fn new() -> Self {
        let path = std::env::temp_dir().join(format!(
            "fln-lake-records-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        std::fs::create_dir_all(&path).unwrap();
        let package = Self(path);
        package.write(
            "lakefile.toml",
            "name = \"records\"\n[[lean_lib]]\nname = \"Library\"\nroots = [\"Lib\"]\n",
        );
        package.write("Lib/Base.lean", BASE);
        package.write("Lib/Left.lean", LEFT);
        package.write("Lib/Right.lean", RIGHT);
        package.write("Lib/Top.lean", TOP);
        package
    }
    fn write(&self, relative: &str, bytes: impl AsRef<[u8]>) {
        let path = self.0.join(relative);
        std::fs::create_dir_all(path.parent().unwrap()).unwrap();
        std::fs::write(path, bytes).unwrap();
    }
    fn store(&self) -> PathBuf {
        self.0.join(".records")
    }
    fn run(&self, extra: &[&str], target: &str) -> Output {
        let mut command = Command::new(env!("CARGO_BIN_EXE_lake"));
        command
            .arg("--dir")
            .arg(&self.0)
            .args(["--json", "build"])
            .args(extra)
            .arg(target)
            .env("LEAN_PATH", self.0.join("no-imports"))
            .env("FLN_IMPORT_REUSE_DIR", self.store());
        let output = command.output().unwrap();
        eprintln!(
            "argv: {:?}\nexit: {:?}\nstdout: {}\nstderr: {}",
            command,
            output.status.code(),
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
        output
    }
    fn build(&self) -> Report {
        let output = self.run(&[], "+Lib.Top:olean");
        assert!(output.status.success(), "{output:?}");
        assert!(output.stderr.is_empty(), "{output:?}");
        Report(String::from_utf8(output.stdout).unwrap())
    }
    fn artifact(&self, module: &str) -> Vec<u8> {
        std::fs::read(self.artifact_path(module)).unwrap()
    }
    fn artifact_path(&self, module: &str) -> PathBuf {
        self.0
            .join(".lake/build/lib/lean")
            .join(format!("{}.olean", module.replace('.', "/")))
    }
    fn artifacts(&self) -> Vec<Vec<u8>> {
        MODULES.iter().map(|module| self.artifact(module)).collect()
    }
    fn record_path(&self, key: &str) -> PathBuf {
        self.store()
            .join("source-modules")
            .join(format!("{key}.record"))
    }
    fn set_mtime(&self, relative: &str, time: std::time::SystemTime) {
        std::fs::File::options()
            .write(true)
            .open(self.0.join(relative))
            .unwrap()
            .set_times(std::fs::FileTimes::new().set_modified(time))
            .unwrap();
    }
}
impl Drop for Package {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

const MODULES: [&str; 4] = ["Lib.Base", "Lib.Left", "Lib.Right", "Lib.Top"];
const BASE: &str = "prelude\ndef Lib.identity (A : Type) (a : A) : A := a\n";
const LEFT: &str =
    "prelude\nimport Lib.Base\ndef Lib.left (A : Type) (a : A) : A := Lib.identity A a\n";
const RIGHT: &str =
    "prelude\nimport Lib.Base\ndef Lib.right (A : Type) (a : A) : A := Lib.identity A a\n";
const TOP: &str =
    "prelude\nimport Lib.Left\nimport Lib.Right\ntheorem Lib.top (P : Prop) (h : P) : P := h\n";

/// One `lake build --json` success report.
struct Report(String);
impl Report {
    fn count(&self, field: &str) -> usize {
        let start = self
            .0
            .find(&format!("\"{field}\":"))
            .unwrap_or_else(|| panic!("{field}: {}", self.0))
            + field.len()
            + 3;
        self.0[start..]
            .chars()
            .take_while(char::is_ascii_digit)
            .collect::<String>()
            .parse()
            .unwrap()
    }
    /// The module's row: (decision, record lookup, record write, key).
    fn module(&self, name: &str) -> (String, String, String, String) {
        let rows = &self.0[self.0.find("\"modules\":[").expect("modules array")..];
        let marker = format!("{{\"name\":\"{name}\"");
        let row = &rows[rows
            .find(&marker)
            .unwrap_or_else(|| panic!("{name}: {}", self.0))..];
        let row = &row[..row.find('}').unwrap()];
        let field = |key: &str| {
            row.find(&format!("\"{key}\":\""))
                .map(|start| {
                    let value = &row[start + key.len() + 4..];
                    value[..value.find('"').unwrap()].to_owned()
                })
                .unwrap_or_default()
        };
        (
            field("decision"),
            field("record"),
            field("recordWrite"),
            field("key"),
        )
    }
    fn decisions(&self) -> Vec<(String, String)> {
        MODULES
            .iter()
            .map(|name| {
                let (decision, record, _, _) = self.module(name);
                (decision, record)
            })
            .collect()
    }
}

fn row(decision: &str, record: &str) -> (String, String) {
    (decision.to_owned(), record.to_owned())
}

#[test]
fn a_no_op_rebuild_and_an_mtime_touch_reuse_every_module_by_content() {
    let package = Package::new();
    let cold = package.build();
    assert_eq!(cold.count("modules_built"), 4);
    assert_eq!(cold.count("modules_cached"), 0);
    assert_eq!(cold.count("module_elaborations"), 4);
    for name in MODULES {
        let (decision, record, write, key) = cold.module(name);
        assert_eq!(
            (decision.as_str(), record.as_str(), write.as_str()),
            ("elaborated", "absent", "stored")
        );
        assert!(package.record_path(&key).is_file(), "{name}");
    }
    let artifacts = package.artifacts();

    // (b) A no-op rebuild elaborates nothing and republishes the same bytes.
    let warm = package.build();
    assert_eq!(warm.count("modules_built"), 4);
    assert_eq!(warm.count("modules_cached"), 4);
    assert_eq!(warm.count("module_elaborations"), 0);
    assert_eq!(warm.decisions(), vec![row("cached", "hit"); 4]);
    assert_eq!(package.artifacts(), artifacts);
    for name in MODULES {
        assert_eq!(
            warm.module(name).3,
            cold.module(name).3,
            "{name}: key moved"
        );
    }

    // (c) Touching every source's mtime, forward and backward, changes no key.
    let later = std::time::SystemTime::now() + std::time::Duration::from_secs(3600);
    let earlier = std::time::SystemTime::UNIX_EPOCH + std::time::Duration::from_secs(86_400);
    for time in [later, earlier] {
        for name in MODULES {
            package.set_mtime(&format!("{}.lean", name.replace('.', "/")), time);
        }
        let touched = package.build();
        assert_eq!(touched.count("modules_cached"), 4);
        assert_eq!(touched.count("module_elaborations"), 0);
        assert_eq!(package.artifacts(), artifacts);
    }
}

#[test]
fn a_body_edit_rebuilds_exactly_the_module_and_its_dependents() {
    let package = Package::new();
    package.build();
    let before = package.artifacts();
    package.write(
        "Lib/Left.lean",
        "prelude\nimport Lib.Base\ndef Lib.left (A : Type) (a : A) : A := a\n",
    );
    let edited = package.build();
    assert_eq!(edited.count("modules_cached"), 2);
    assert_eq!(edited.count("module_elaborations"), 2);
    assert_eq!(
        edited.decisions(),
        vec![
            row("cached", "hit"),
            row("elaborated", "absent"),
            row("cached", "hit"),
            row("elaborated", "absent"),
        ]
    );
    let after = package.artifacts();
    assert_eq!(after[0], before[0], "Lib.Base");
    assert_ne!(after[1], before[1], "Lib.Left");
    assert_eq!(after[2], before[2], "Lib.Right");
    // Top's own declarations did not change, so neither do its bytes; it was rebuilt
    // because the environment it is checked in did.
    assert_eq!(after[3], before[3], "Lib.Top");

    // A dependency edit that leaves its checked declarations unchanged (a comment)
    // rebuilds that module only: its dependents' imported environment is the same.
    package.write(
        "Lib/Base.lean",
        format!("{BASE}-- a comment changes no declaration\n"),
    );
    let comment = package.build();
    assert_eq!(
        comment.decisions(),
        vec![
            row("elaborated", "absent"),
            row("cached", "hit"),
            row("cached", "hit"),
            row("cached", "hit"),
        ]
    );
}

#[test]
fn a_content_change_under_a_preserved_mtime_rebuilds() {
    let package = Package::new();
    package.build();
    let base = package.artifact("Lib.Base");
    let modified = std::fs::metadata(package.0.join("Lib/Base.lean"))
        .unwrap()
        .modified()
        .unwrap();
    package.write(
        "Lib/Base.lean",
        format!("{BASE}def Lib.second (A : Type) (a : A) : A := a\n"),
    );
    package.set_mtime("Lib/Base.lean", modified);
    let changed = package.build();
    assert_eq!(changed.count("module_elaborations"), 4);
    assert_eq!(changed.count("modules_cached"), 0);
    assert_ne!(package.artifact("Lib.Base"), base);
}

#[test]
fn a_damaged_or_misfiled_record_falls_back_to_elaboration_and_is_rewritten() {
    let package = Package::new();
    let cold = package.build();
    let artifacts = package.artifacts();
    let key = |name: &str| cold.module(name).3;

    // One flipped byte in Base's record; Right's record replaced by Left's; Top's
    // record truncated below its seal.
    let base = package.record_path(&key("Lib.Base"));
    let mut bytes = std::fs::read(&base).unwrap();
    bytes[100] ^= 1;
    std::fs::write(&base, bytes).unwrap();
    std::fs::copy(
        package.record_path(&key("Lib.Left")),
        package.record_path(&key("Lib.Right")),
    )
    .unwrap();
    std::fs::write(package.record_path(&key("Lib.Top")), b"fln.source").unwrap();

    let fallback = package.build();
    assert_eq!(
        fallback.decisions(),
        vec![
            row("elaborated", "refused:seal"),
            row("cached", "hit"),
            row("elaborated", "refused:key"),
            row("elaborated", "refused:malformed"),
        ]
    );
    for name in ["Lib.Base", "Lib.Right", "Lib.Top"] {
        assert_eq!(fallback.module(name).2, "stored", "{name}");
    }
    assert_eq!(package.artifacts(), artifacts);

    let repaired = package.build();
    assert_eq!(repaired.decisions(), vec![row("cached", "hit"); 4]);
    assert_eq!(package.artifacts(), artifacts);
}

#[test]
fn a_forged_build_output_is_neither_read_nor_kept() {
    let package = Package::new();
    package.build();
    let artifacts = package.artifacts();
    for name in MODULES {
        std::fs::write(package.artifact_path(name), "fln-olean-artifact:forged").unwrap();
    }
    let warm = package.build();
    assert_eq!(warm.count("modules_cached"), 4);
    assert_eq!(package.artifacts(), artifacts);
}

#[test]
fn recheck_consults_and_writes_no_record() {
    let package = Package::new();
    package.build();
    let records = || {
        let mut names: Vec<_> = std::fs::read_dir(package.store().join("source-modules"))
            .unwrap()
            .map(|entry| entry.unwrap().file_name())
            .collect();
        names.sort();
        names
    };
    let stored = records();
    package.write(
        "Lib/Base.lean",
        format!("{BASE}def Lib.extra (A : Type) (a : A) : A := a\n"),
    );
    let output = package.run(&["--import-posture", "recheck"], "+Lib.Top:olean");
    assert!(output.status.success(), "{output:?}");
    let report = Report(String::from_utf8(output.stdout).unwrap());
    assert_eq!(report.count("module_elaborations"), 4);
    assert_eq!(report.count("modules_cached"), 0);
    assert!(
        report.0.contains("\"module_records\":\"off\""),
        "{}",
        report.0
    );
    assert!(!report.0.contains("\"record\":"), "{}", report.0);
    assert_eq!(records(), stored);
}

#[test]
fn an_unavailable_store_still_builds_and_says_why() {
    let package = Package::new();
    let output = Command::new(env!("CARGO_BIN_EXE_lake"))
        .arg("--dir")
        .arg(&package.0)
        .args(["--json", "build", "+Lib.Top:olean"])
        .env("LEAN_PATH", package.0.join("no-imports"))
        .env("FLN_IMPORT_REUSE_DIR", "relative/records")
        .output()
        .unwrap();
    assert!(output.status.success(), "{output:?}");
    let report = String::from_utf8(output.stdout).unwrap();
    assert!(
        report.contains("\"module_records\":\"unavailable\""),
        "{report}"
    );
    assert!(report.contains("is not absolute"), "{report}");
    assert!(report.contains("\"module_elaborations\":4"), "{report}");
}

/// Criterion 1's position half: a refused module is named with the byte of the first
/// token the grammar cannot accept, in a `prelude` module, an importing module and an
/// implicit-`Init` module. The last is refused before any import is resolved.
#[test]
fn garbage_names_the_failing_module_and_the_first_unacceptable_byte() {
    let garbage = "this is not lean )))(\n";
    for (module, source) in [
        ("Lib.Base", format!("{BASE}{garbage}")),
        ("Lib.Top", format!("{TOP}{garbage}")),
        ("Lib.Base", format!("def Lib.answer := 42\n{garbage}")),
    ] {
        let package = Package::new();
        package.write(&format!("{}.lean", module.replace('.', "/")), &source);
        let output = package.run(&[], "+Lib.Top:olean");
        assert_eq!(output.status.code(), Some(1), "{output:?}");
        assert!(output.stdout.is_empty(), "{output:?}");
        let error = String::from_utf8(output.stderr).unwrap();
        let byte = source.find(")))(").unwrap();
        assert!(
            error.contains(&format!(
                "module `{module}`: file 0, command 0, byte {byte}:"
            )) && error.contains("expected EndOfCommand"),
            "{module} at byte {byte}: {error}"
        );
        assert!(!package.0.join(".lake").exists(), "{error}");
        assert!(
            !package.store().exists(),
            "a refused build stored a record: {error}"
        );
    }
}

fn inspect(path: &Path) -> String {
    let output = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["olean", "inspect", "--constants"])
        .arg(path)
        .output()
        .unwrap();
    assert!(output.status.success(), "{output:?}");
    String::from_utf8(output.stdout).unwrap()
}

/// Every artifact a hit publishes decodes, as a cold build's does (criterion 2).
#[test]
fn re_admitted_artifacts_decode_like_elaborated_ones() {
    let package = Package::new();
    package.build();
    let cold: Vec<_> = MODULES
        .iter()
        .map(|name| inspect(&package.artifact_path(name)))
        .collect();
    let warm = package.build();
    assert_eq!(warm.count("modules_cached"), 4);
    for (name, cold) in MODULES.iter().zip(cold) {
        assert_eq!(inspect(&package.artifact_path(name)), cold, "{name}");
    }
    assert!(inspect(&package.artifact_path("Lib.Top")).contains("Lib.top"));
}
