//! Installed `fln build explain` over the snapshot `lake build` writes (bead
//! `franken_lean-z8j.1.2`). Every invocation logs argv, exit code, stdout and stderr.
//! The projects are `prelude` modules, so no `Init` closure is admitted.
#![forbid(unsafe_code)]
use fln_hash::domain::{Domain, DomainHasher};
use std::{
    path::{Path, PathBuf},
    process::{Command, Output},
    sync::atomic::{AtomicUsize, Ordering},
};

static NEXT: AtomicUsize = AtomicUsize::new(0);

struct Package(PathBuf);
impl Package {
    fn new(roots: &str) -> Self {
        let path = std::env::temp_dir().join(format!(
            "fln-build-explain-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        std::fs::create_dir_all(&path).unwrap();
        let package = Self(path);
        package.write(
            "lakefile.toml",
            format!("name = \"explained\"\n[[lean_lib]]\nname = \"Library\"\nroots = [{roots}]\n"),
        );
        package
    }
    fn diamond() -> Self {
        let package = Self::new("\"Lib\"");
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
    fn logged(&self, command: &mut Command) -> Output {
        command.env("FLN_IMPORT_REUSE_DIR", self.0.join(".records"));
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
    fn build(&self, target: &str, search: Option<&Path>) -> Output {
        self.logged(
            Command::new(env!("CARGO_BIN_EXE_lake"))
                .arg("--dir")
                .arg(&self.0)
                .args(["--json", "build", target])
                .env("LEAN_PATH", search.unwrap_or(&self.0.join("no-imports"))),
        )
    }
    fn built(&self, target: &str, search: Option<&Path>) {
        let output = self.build(target, search);
        assert!(output.status.success(), "{output:?}");
        assert!(String::from_utf8_lossy(&output.stdout).contains("\"snapshot\":\"written\""));
    }
    fn explain(&self, extra: &[&str], search: Option<&Path>) -> Output {
        self.logged(
            Command::new(env!("CARGO_BIN_EXE_fln"))
                .args(["build", "explain", "--json", "--dir"])
                .arg(&self.0)
                .args(extra)
                .env("LEAN_PATH", search.unwrap_or(&self.0.join("no-imports"))),
        )
    }
    fn explained(&self, extra: &[&str], search: Option<&Path>) -> Explanation {
        let output = self.explain(extra, search);
        assert_eq!(output.status.code(), Some(0), "{output:?}");
        assert!(output.stderr.is_empty(), "{output:?}");
        Explanation(String::from_utf8(output.stdout).unwrap())
    }
}
impl Drop for Package {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

const BASE: &str = "prelude\ndef Lib.identity (A : Type) (a : A) : A := a\n";
const LEFT: &str =
    "prelude\nimport Lib.Base\ndef Lib.left (A : Type) (a : A) : A := Lib.identity A a\n";
const RIGHT: &str =
    "prelude\nimport Lib.Base\ndef Lib.right (A : Type) (a : A) : A := Lib.identity A a\n";
const TOP: &str =
    "prelude\nimport Lib.Left\nimport Lib.Right\ntheorem Lib.top (P : Prop) (h : P) : P := h\n";

/// The snapshot's content digest, recomputed here from the bytes on disk.
fn digest(bytes: &[u8]) -> String {
    let mut hasher = DomainHasher::new(Domain::ArtifactClosureComponent);
    hasher.update(b"fln.lake-file/1\0");
    hasher.update(bytes);
    hasher.finalize().to_hex()
}

/// One `fln build explain --json` report.
struct Explanation(String);
impl Explanation {
    fn field(&self, key: &str) -> String {
        let start = self
            .0
            .find(&format!("\"{key}\":\""))
            .unwrap_or_else(|| panic!("{key}: {}", self.0))
            + key.len()
            + 4;
        let rest = &self.0[start..];
        rest[..rest.find('"').unwrap()].to_owned()
    }
    fn array(&self, key: &str) -> &str {
        let start = self
            .0
            .find(&format!("\"{key}\":["))
            .unwrap_or_else(|| panic!("{key}: {}", self.0))
            + key.len()
            + 4;
        let rest = &self.0[start..];
        let mut depth = 0usize;
        for (index, c) in rest.char_indices() {
            match c {
                '[' | '{' => depth += 1,
                '}' => depth -= 1,
                ']' if depth == 0 => return &rest[..index],
                ']' => depth -= 1,
                _ => {}
            }
        }
        panic!("{key}: unterminated: {}", self.0)
    }
    /// `(module, kind, subject, old, new)` for every changed input, `""` for absent.
    fn changed(&self, key: &str) -> Vec<[String; 5]> {
        let array = self.array(key);
        if array.is_empty() {
            return Vec::new();
        }
        array
            .trim_start_matches('{')
            .trim_end_matches('}')
            .split("},{")
            .map(|row| {
                let value = |field: &str| {
                    let marker = format!("\"{field}\":");
                    let rest = &row[row.find(&marker).unwrap() + marker.len()..];
                    if rest.starts_with("null") {
                        String::new()
                    } else {
                        rest[1..rest[1..].find('"').unwrap() + 1].to_owned()
                    }
                };
                [
                    value("module"),
                    value("kind"),
                    value("subject"),
                    value("old"),
                    value("new"),
                ]
            })
            .collect()
    }
    /// `(module, decision)` in the report's order.
    fn decisions(&self) -> Vec<(String, String)> {
        self.array("modules")
            .split("{\"name\":\"")
            .skip(1)
            .map(|row| {
                let name = row[..row.find('"').unwrap()].to_owned();
                let marker = "\"reference_decision\":\"";
                let rest = &row[row.find(marker).unwrap() + marker.len()..];
                (name, rest[..rest.find('"').unwrap()].to_owned())
            })
            .collect()
    }
    /// The changed inputs without their hashes: what the decision depends on.
    fn shape(&self) -> Vec<[String; 3]> {
        self.changed("changed_inputs")
            .into_iter()
            .map(|[module, kind, subject, _, _]| [module, kind, subject])
            .collect()
    }
}

fn decisions(rows: &[(&str, &str)]) -> Vec<(String, String)> {
    rows.iter()
        .map(|(name, decision)| ((*name).to_owned(), (*decision).to_owned()))
        .collect()
}

#[test]
fn explain_refuses_without_a_snapshot_and_a_failed_build_writes_none() {
    let package = Package::diamond();
    for _ in 0..2 {
        let output = package.explain(&["Lib.Top"], None);
        assert_eq!(output.status.code(), Some(5), "{output:?}");
        assert!(output.stdout.is_empty(), "{output:?}");
        let error = String::from_utf8(output.stderr).unwrap();
        assert!(
            error.contains("\"schema\":\"fln.build-explain/2\""),
            "{error}"
        );
        assert!(error.contains("\"status\":\"unsupported\""), "{error}");
        assert!(error.contains("provenance is unavailable"), "{error}");
        assert!(!error.contains("reference_decision"), "{error}");
        package.write("Lib/Base.lean", format!("{BASE}this is not lean )))(\n"));
        assert_eq!(package.build("+Lib.Top:olean", None).status.code(), Some(1));
    }
}

/// Criterion 1: an edited module is named, with the content hashes of its old and
/// new bytes; its dependents rebuild through it and nothing else does.
#[test]
fn a_body_edit_is_named_with_the_hashes_of_its_old_and_new_bytes() {
    let package = Package::diamond();
    package.built("+Lib.Top:olean", None);
    let clean = package.explained(&["Lib.Top"], None);
    assert_eq!(clean.field("reference_decision"), "up-to-date");
    assert!(clean.changed("changed_inputs").is_empty());

    let edited = "prelude\nimport Lib.Base\ndef Lib.left (A : Type) (a : A) : A := a\n";
    package.write("Lib/Left.lean", edited);
    for target in ["Lib.Top", "+Lib.Top:olean", "Lib/Top.lean"] {
        let report = package.explained(&[target], None);
        assert_eq!(report.field("target"), "Lib.Top");
        assert_eq!(report.field("reference_model"), "file-cone");
        assert_eq!(report.field("reference_decision"), "rebuild");
        assert_eq!(
            report.changed("changed_inputs"),
            vec![[
                "Lib.Left".to_owned(),
                "source".to_owned(),
                "Lib/Left.lean".to_owned(),
                digest(LEFT.as_bytes()),
                digest(edited.as_bytes()),
            ]]
        );
        assert_eq!(
            report.decisions(),
            decisions(&[
                ("Lib.Base", "up-to-date"),
                ("Lib.Left", "rebuild"),
                ("Lib.Right", "up-to-date"),
                ("Lib.Top", "rebuild"),
            ])
        );
        assert!(
            report
                .0
                .contains("\"reasons\":[\"imports Lib.Left, which rebuilds\"]")
        );
    }
    // The tree explained as the recorded build is again: nothing changed.
    package.write("Lib/Left.lean", LEFT);
    assert_eq!(
        package.explained(&[], None).field("reference_decision"),
        "up-to-date"
    );
}

/// Criterion 2: what cannot be computed is labelled, never filled in.
#[test]
fn the_native_decision_is_unavailable_and_no_cache_outcome_is_invented() {
    let package = Package::diamond();
    package.built("+Lib.Top:olean", None);
    package.write(
        "Lib/Base.lean",
        format!("{BASE}def Lib.more (A : Type) (a : A) : A := a\n"),
    );
    let report = package.explained(&[], None);
    assert_eq!(report.field("native_decision"), "unavailable");
    assert_eq!(report.field("native_reason"), "no Ledger records");
    for invented in [
        "cache_outcome",
        "\"hit\"",
        "early-cutoff",
        "opaque_barriers",
    ] {
        assert!(!report.0.contains(invented), "{invented}: {}", report.0);
    }
    let human = package.logged(
        Command::new(env!("CARGO_BIN_EXE_fln"))
            .args(["build", "explain", "--dir"])
            .arg(&package.0),
    );
    assert_eq!(human.status.code(), Some(0), "{human:?}");
    let text = String::from_utf8(human.stdout).unwrap();
    assert!(
        text.contains("Native decision:    unavailable (no Ledger records)"),
        "{text}"
    );
    assert!(text.contains("Reference decision: rebuild"), "{text}");
}

/// Criterion 3, metamorphic. The changed-input set and every decision depend on which
/// files changed, never on what changed in them. Adding comment, whitespace, `axiom `
/// and magic-comment churn to an edit, or making only that churn, moves the hashes
/// and nothing else. The same strings present at build time change nothing either.
#[test]
fn comment_whitespace_and_magic_text_move_only_the_hashes() {
    let package = Package::diamond();
    package.write(
        "Lib/Base.lean",
        format!("{BASE}-- fln-interface-change\n-- axiom Lib.ax : False\n"),
    );
    package.built("+Lib.Top:olean", None);
    assert_eq!(
        package.explained(&[], None).field("reference_decision"),
        "up-to-date"
    );
    let edit = "prelude\nimport Lib.Base\ndef Lib.left (A : Type) (a : A) : A := a\n";
    let churned = "prelude\nimport Lib.Base\n-- axiom Lib.bad : False\n-- fln-interface-change\n\ndef Lib.left  (A : Type)\n    (a : A) : A := a   \n";
    let only_churn = format!("{LEFT}\n-- fln-interface-change\n-- axiom Lib.bad : False\n  \n");
    let mut reports = Vec::new();
    for source in [edit, churned, only_churn.as_str()] {
        package.write("Lib/Left.lean", source);
        let report = package.explained(&["Lib.Top"], None);
        let new = report.changed("changed_inputs")[0][4].clone();
        assert_eq!(new, digest(source.as_bytes()));
        reports.push((report.shape(), report.decisions(), new));
    }
    let (shape, decided, _) = &reports[0];
    for (other_shape, other_decided, _) in &reports[1..] {
        assert_eq!(other_shape, shape);
        assert_eq!(other_decided, decided);
    }
    let hashes: std::collections::BTreeSet<_> = reports.iter().map(|(_, _, new)| new).collect();
    assert_eq!(hashes.len(), 3, "each edit has its own hash");
}

/// A missing output rebuilds that module alone; a changed output is reported, and it
/// changes no decision: outputs are not inputs.
#[test]
fn a_missing_output_rebuilds_its_module_alone_and_a_changed_one_is_only_reported() {
    let package = Package::diamond();
    package.built("+Lib.Top:olean", None);
    let output = package.0.join(".lake/build/lib/lean/Lib/Right.olean");
    let original = std::fs::read(&output).unwrap();
    std::fs::write(&output, b"forged").unwrap();
    let forged = package.explained(&[], None);
    assert_eq!(forged.field("reference_decision"), "up-to-date");
    assert_eq!(
        forged.changed("changed_outputs"),
        vec![[
            "Lib.Right".to_owned(),
            "output".to_owned(),
            ".lake/build/lib/lean/Lib/Right.olean".to_owned(),
            digest(&original),
            digest(b"forged"),
        ]]
    );
    std::fs::remove_file(&output).unwrap();
    let missing = package.explained(&[], None);
    assert_eq!(
        missing.decisions(),
        decisions(&[
            ("Lib.Base", "up-to-date"),
            ("Lib.Left", "up-to-date"),
            ("Lib.Right", "rebuild"),
            ("Lib.Top", "up-to-date"),
        ])
    );
    assert!(
        missing.0.contains("\"reasons\":[\"output missing\"]"),
        "{}",
        missing.0
    );
}

/// An external `.olean` that changed is named with its old and new hashes, and only
/// the modules whose import cone contains it rebuild.
#[test]
fn an_external_import_change_is_named_and_rebuilds_only_its_cone() {
    let producer = Package::new("\"Ext\"");
    for side in ["A", "B"] {
        producer.write(
            &format!("Ext/{side}.lean"),
            format!("prelude\ndef Ext.{side} (P : Prop) (h : P) : P := h\n"),
        );
    }
    producer.built("+Ext.A:olean", None);
    producer.built("+Ext.B:olean", None);
    let search = producer.0.join(".lake/build/lib/lean");
    let consumer = Package::new("\"Use\"");
    consumer.write(
        "Use/First.lean",
        "prelude\nimport Ext.A\ndef Use.first (P : Prop) (h : P) : P := Ext.A P h\n",
    );
    consumer.write(
        "Use/Second.lean",
        "prelude\nimport Ext.B\ndef Use.second (P : Prop) (h : P) : P := Ext.B P h\n",
    );
    consumer.write(
        "Use/Top.lean",
        "prelude\nimport Use.First\nimport Use.Second\ntheorem Use.top (P : Prop) (h : P) : P := h\n",
    );
    consumer.built("+Use.Top:olean", Some(&search));
    assert_eq!(
        consumer
            .explained(&[], Some(&search))
            .field("reference_decision"),
        "up-to-date"
    );
    let before = std::fs::read(search.join("Ext/A.olean")).unwrap();
    producer.write(
        "Ext/A.lean",
        "prelude\ndef Ext.A (P : Prop) (h : P) : P := h\ndef Ext.extra (P : Prop) (h : P) : P := h\n",
    );
    producer.built("+Ext.A:olean", None);
    let report = consumer.explained(&[], Some(&search));
    let changed = report.changed("changed_inputs");
    assert_eq!(changed.len(), 1, "{}", report.0);
    let [module, kind, subject, old, new] = &changed[0];
    assert_eq!(
        (module.as_str(), kind.as_str(), subject.as_str()),
        ("Use.First", "external", "Ext.A")
    );
    assert_ne!(old, new);
    assert_ne!(std::fs::read(search.join("Ext/A.olean")).unwrap(), before);
    assert_eq!(
        report.decisions(),
        decisions(&[
            ("Use.First", "rebuild"),
            ("Use.Second", "up-to-date"),
            ("Use.Top", "rebuild"),
        ])
    );
}

/// When an input cannot be read the decision is `unknown`, the report says why, and
/// the exit code is the documented 5, not a guessed answer.
#[test]
fn an_unreadable_input_makes_the_decision_unknown_with_exit_5() {
    let package = Package::diamond();
    package.built("+Lib.Top:olean", None);
    std::fs::remove_file(package.0.join("Lib/Left.lean")).unwrap();
    let output = package.explain(&["Lib.Top"], None);
    assert_eq!(output.status.code(), Some(5), "{output:?}");
    let report = Explanation(String::from_utf8(output.stdout).unwrap());
    assert_eq!(report.field("status"), "incomplete");
    assert_eq!(report.field("reference_decision"), "unknown");
    assert!(report.0.contains("source unreadable"), "{}", report.0);
    assert!(
        report
            .0
            .contains("imports Lib.Left, whose decision is unknown"),
        "{}",
        report.0
    );
}

#[test]
fn a_failed_build_leaves_the_last_successful_snapshot_and_unknown_targets_are_refused() {
    let package = Package::diamond();
    package.built("+Lib.Top:olean", None);
    package.write("Lib/Right.lean", format!("{RIGHT}this is not lean )))(\n"));
    assert_eq!(package.build("+Lib.Top:olean", None).status.code(), Some(1));
    let report = package.explained(&[], None);
    assert_eq!(
        report.shape(),
        vec![[
            "Lib.Right".to_owned(),
            "source".to_owned(),
            "Lib/Right.lean".to_owned(),
        ]]
    );
    let output = package.explain(&["Lib.Missing"], None);
    assert_eq!(output.status.code(), Some(1), "{output:?}");
    assert!(String::from_utf8_lossy(&output.stderr).contains("not part of the recorded build"));
}
