//! The installed FlN raw-result front door over actual admitted import bytes.
//! Reference `#eval` formatting is a different surface: Init.Prelude alone
//! does not supply Repr/ToString for these natural-number evaluations.
#![forbid(unsafe_code)]

use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};

static NEXT: AtomicUsize = AtomicUsize::new(0);

struct Workspace(PathBuf);
impl Workspace {
    fn new(case: &str) -> Self {
        let path = std::env::temp_dir().join(format!(
            "fln-program-{case}-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed),
        ));
        std::fs::create_dir_all(&path).unwrap();
        Self(path)
    }

    fn write(&self, name: &str, source: impl AsRef<[u8]>) -> PathBuf {
        let path = self.0.join(name);
        std::fs::write(&path, source).unwrap();
        path
    }

    fn run(&self, entry: &Path, lib: Option<&Path>, extra: &[&str]) -> Run {
        self.invoke("run", entry, lib, extra)
    }

    fn invoke(&self, verb: &str, entry: &Path, lib: Option<&Path>, extra: &[&str]) -> Run {
        let output = Command::new(env!("CARGO_BIN_EXE_fln"))
            .args([verb, "--json"])
            .args(extra)
            .arg(entry)
            .env("LEAN_PATH", lib.unwrap_or(&self.0))
            .env("FLN_IMPORT_REUSE_DIR", self.0.join("records"))
            .output()
            .expect("run the installed CLI");
        Run {
            code: output.status.code().expect("normal process exit"),
            stdout: String::from_utf8(output.stdout).unwrap(),
            stderr: String::from_utf8(output.stderr).unwrap(),
        }
    }
}

#[derive(Debug)]
struct Run {
    code: i32,
    stdout: String,
    stderr: String,
}
impl Run {
    fn complete(&self) -> &str {
        assert_eq!(self.code, 0, "{self:?}");
        assert!(self.stderr.is_empty(), "{self:?}");
        assert!(self.stdout.contains("\"outcome\":\"complete\""), "{self:?}");
        &self.stdout
    }
    fn refused(&self, class: &str, code: i32) -> &str {
        assert_eq!(self.code, code, "{self:?}");
        assert!(self.stdout.is_empty(), "partial output escaped: {self:?}");
        assert!(
            self.stderr.contains(&format!("\"class\":\"{class}\"")),
            "{self:?}"
        );
        &self.stderr
    }
}

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
        .filter(|lib| lib.join("Init/Prelude.olean").is_file());
    assert!(
        lib.is_some() || std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
        "the pinned Reference library is required"
    );
    if lib.is_none() {
        eprintln!("SKIP: pinned Reference lib/lean absent");
    }
    lib
}

/// These fields contain only module names and digest hex, never escaped strings.
fn string_member<'a>(text: &'a str, member: &str) -> &'a str {
    text.split_once(&format!("\"{member}\":\""))
        .unwrap_or_else(|| panic!("missing {member}: {text}"))
        .1
        .split_once('"')
        .unwrap()
        .0
}

fn module_rows(text: &str) -> Vec<&str> {
    text.split("{\"module\":").skip(1).collect()
}

fn without_import_report(text: &str) -> String {
    let (before, rest) = text.split_once(",\"oleanImports\":{").unwrap();
    let (_, after) = rest.split_once('}').unwrap();
    format!("{before}{after}")
}

#[test]
fn actual_prelude_runs_with_recheck_reuse_isolation_order_and_atomic_failures() {
    let Some(lib) = pinned_lib() else { return };
    let ws = Workspace::new("pinned");
    let source =
        "prelude\nimport Init.Prelude\n#check Nat\ndef answer : Nat := id 42\n#eval answer\n";
    let main = ws.write("Main.lean", source);
    let rechecked = ws.run(
        &main,
        Some(&lib),
        &["--import-posture", "recheck", "--jobs", "1"],
    );
    let first = rechecked.complete();
    assert!(
        first.contains("\"schema\":\"fln.source-program/1\""),
        "{first}"
    );
    assert!(
        first.contains("\"trust\":\"recheck\",\"admission\":\"council\""),
        "{first}"
    );
    assert!(first.contains("\"declarations\":2314"), "{first}");
    assert!(first.contains("\"event\":\"check\""), "{first}");
    assert!(
        first.contains("\"command\":2,\"event\":\"evaluation\",\"kind\":\"nat\",\"value\":42"),
        "{first}"
    );
    assert_eq!(module_rows(first).len(), 1);

    // First reuse run creates the real binary-bound record; the second re-proves it.
    ws.run(&main, Some(&lib), &[]).complete();
    let reused = ws.run(
        &main,
        Some(&lib),
        &["--jobs=3", "--import-posture=reuse-verified"],
    );
    let reused = reused.complete();
    assert!(reused.contains("\"trust\":\"reuse-verified\""), "{reused}");
    assert!(reused.contains("\"admission\":\"reused\""), "{reused}");
    assert_eq!(without_import_report(first), without_import_report(reused));

    ws.write(
        "Left.lean",
        "prelude\nimport Init.Prelude\n#eval (11 : Nat)\ndef left : Nat := id 20\n",
    );
    ws.write(
        "Right.lean",
        "prelude\nimport Init.Prelude\n#eval (12 : Nat)\ndef right : Nat := id 22\n",
    );
    ws.write(
        "Main.lean",
        "prelude\nimport Left\nimport Right\n#check left\n#eval left\n#eval right\n",
    );
    let graph = ws.run(&main, Some(&lib), &[]);
    let rows = module_rows(graph.complete());
    assert_eq!(rows.len(), 3, "{graph:?}");
    for (row, name, value) in [
        (rows[0], "Left", 11),
        (rows[1], "Right", 12),
        (rows[2], "Main", 22),
    ] {
        assert!(row.starts_with(&format!("\"{name}\"")), "{row}");
        assert!(row.contains(&format!("\"value\":{value}")), "{row}");
    }
    assert!(rows[2].contains("\"value\":20"));
    assert_eq!(
        string_member(rows[0], "baseLogicalRoot"),
        string_member(rows[1], "baseLogicalRoot")
    );
    assert_ne!(
        string_member(rows[0], "resultLogicalRoot"),
        string_member(rows[1], "baseLogicalRoot"),
        "sibling roots must not be flattened into an invented chain"
    );

    // An earlier executed sibling remains outside the later sibling's imports.
    ws.write(
        "Right.lean",
        "prelude\nimport Init.Prelude\ndef right : Nat := left\n",
    );
    let isolated = ws.run(&main, Some(&lib), &[]);
    assert_ne!(isolated.code, 0, "{isolated:?}");
    assert!(isolated.stdout.is_empty(), "{isolated:?}");
    assert!(
        isolated.stderr.contains("Right") && isolated.stderr.contains("left"),
        "{isolated:?}"
    );

    ws.write(
        "Base.lean",
        "prelude\nimport Init.Prelude\nclass Pick where\n  value : Nat\n",
    );
    ws.write(
        "Low.lean",
        "prelude\nimport Base\ninstance low : Pick := Pick.mk 11\n",
    );
    ws.write(
        "High.lean",
        "prelude\nimport Base\ninstance high : Pick := Pick.mk 22\n",
    );
    for (imports, expected) in [("Low\nimport High", 22), ("High\nimport Low", 11)] {
        ws.write(
            "Main.lean",
            format!("prelude\nimport {imports}\n#eval Pick.value (self := inferInstance)\n"),
        );
        let run = ws.run(&main, Some(&lib), &[]);
        let rows = module_rows(run.complete());
        assert_eq!(rows.len(), 4, "{run:?}");
        assert!(
            rows[3].contains(&format!("\"value\":{expected}")),
            "{run:?}"
        );
    }

    ws.write("Main.lean", "prelude\nimport Init.Prelude\ndef stagedResult : Nat := 42\n#eval stagedResult\ntheorem falseClaim : (1 : Nat) = 2 := rfl\n");
    let invalid = ws.run(&main, Some(&lib), &[]);
    assert_ne!(invalid.code, 0, "{invalid:?}");
    assert!(
        invalid.stdout.is_empty(),
        "the valid prefix must stay buffered: {invalid:?}"
    );
    assert!(
        invalid.stderr.contains("command 2") && invalid.stderr.contains("byte "),
        "{invalid:?}"
    );
    ws.write("Main.lean", source);
    assert_eq!(
        without_import_report(ws.run(&main, Some(&lib), &[]).complete()),
        without_import_report(first)
    );
}

#[test]
fn prelude_is_an_empty_world_and_local_legacy_runs_keep_their_contract() {
    let ws = Workspace::new("empty");
    let main = ws.write(
        "Main.lean",
        "prelude\ninductive Token where\n  | mk\n#check Token\n",
    );
    let empty = ws.run(&main, None, &[]);
    let text = empty.complete();
    assert!(text.contains("\"oleanImports\":null"), "{text}");
    assert!(text.contains("\"executions\":0"), "{text}");
    ws.write("Main.lean", "prelude\n#check Nat\n");
    let unknown = ws.run(&main, None, &[]);
    assert!(unknown.refused("input", 1).contains("\"authority\":false"));

    ws.write("Local.lean", "prelude\ninductive Token where\n  | mk\n");
    ws.write("Main.lean", "prelude\nimport Local\n#check Token\n");
    let local_empty = ws.run(&main, None, &[]);
    assert_eq!(module_rows(local_empty.complete()).len(), 2);
    ws.write("Local.lean", "def part : Nat := 40\n");
    ws.write("Main.lean", "import Local\ndef answer : Nat := part + 2\n");
    let legacy = ws.run(&main, None, &[]);
    assert!(
        legacy
            .complete()
            .contains("\"schema\":\"fln.source-run/9\""),
        "{legacy:?}"
    );
    std::fs::create_dir_all(ws.0.join("Nested")).unwrap();
    let nested = ws.write(
        "Nested/Main.lean",
        "import Local\ndef answer : Nat := part + 2\n",
    );
    let ancestor = ws.run(&nested, None, &[]);
    assert!(
        ancestor
            .complete()
            .contains("\"schema\":\"fln.source-run/9\""),
        "{ancestor:?}"
    );
    assert!(
        ancestor.stdout.contains("\"finalValue\":42"),
        "{ancestor:?}"
    );
    ws.write("Main.lean", "def answer : Nat := 42\n");
    let legacy = ws.run(&main, None, &[]);
    assert!(
        legacy
            .complete()
            .contains("\"schema\":\"fln.source-run/9\""),
        "{legacy:?}"
    );
}

#[test]
fn imports_limits_original_offsets_and_publication_refusals_are_atomic() {
    let ws = Workspace::new("refusals");
    let main = ws.write(
        "Main.lean",
        "prelude\nimport NoSuchModule\n#eval (42 : Nat)\n",
    );
    let missing = ws.run(&main, None, &[]);
    let error = missing.refused("input", 1);
    assert!(
        error.contains("NoSuchModule") && error.contains("search path"),
        "{error}"
    );
    assert!(error.contains("\"authority\":false"), "{error}");

    // Legacy discovery returns a single-file fallback for an unpartitioned
    // body. It must not turn an explicit external import into a seed world.
    ws.write("Main.lean", "import NoSuchModule\n#eval (\n");
    let malformed_import = ws.run(&main, None, &[]);
    let error = malformed_import.refused("input", 1);
    assert!(
        error.contains("\"schema\":\"fln.source-program/1\""),
        "{error}"
    );
    assert!(
        error.contains("NoSuchModule") && error.contains("search path"),
        "{error}"
    );

    ws.write("Local.lean", "prelude\ninductive Token where\n  | mk\n");
    ws.write("Main.lean", "prelude\nimport Local\n#check Token\n");
    let limited = ws.run(&main, None, &["--max-bytes", "48"]);
    assert!(
        limited
            .refused("resource", 3)
            .contains("\"authority\":false")
    );
    ws.run(&main, None, &[]).complete();

    ws.write(
        "Main.lean",
        format!(
            "prelude\ninductive Token where\n  | mk\n{}",
            "#check Token\n".repeat(4096)
        ),
    );
    let commands = ws.run(&main, None, &[]);
    assert!(commands.refused("resource", 3).contains("source commands"));
    let malformed = b"\xef\xbb\xbfprelude\r\n\r\n#eval (\r\n";
    ws.write("Main.lean", malformed);
    let parsed = ws.run(&main, None, &[]);
    let error = parsed.refused("input", 1);
    let byte = error
        .split_once("byte ")
        .unwrap()
        .1
        .split(|c: char| !c.is_ascii_digit())
        .next()
        .unwrap()
        .parse::<usize>()
        .unwrap();
    let evaluation_at = malformed
        .windows(5)
        .position(|bytes| bytes == b"#eval")
        .unwrap();
    assert!(
        byte >= evaluation_at,
        "diagnostic offset escaped the original header: {error}"
    );

    ws.write(
        "Main.lean",
        "prelude\ninductive Token where\n  | mk\n#check Token\n",
    );
    for (option, name) in [
        ("--emit-flbc", "result.flbc"),
        ("--emit-olean-snapshot", "result.olean"),
    ] {
        let path = ws.0.join(name);
        let emitted = ws.run(&main, None, &[option, path.to_str().unwrap()]);
        assert!(
            emitted
                .refused("capability", 5)
                .contains("artifact publication")
        );
        assert!(!path.exists(), "a refused program must not publish {name}");
    }
    ws.run(&main, None, &[]).complete();
}
