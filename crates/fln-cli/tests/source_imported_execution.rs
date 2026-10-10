//! Installed source execution over actual admitted import bytes.
//! FlN retains its raw result surface; the Lean door selects checked printers.
//! Init.Prelude alone does not supply Repr/ToString for natural-number evaluations.
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
fn caller_execution_ceilings_apply_after_real_import_admission() {
    let Some(lib) = pinned_lib() else { return };
    let ws = Workspace::new("imported-execution-limits");
    let main = ws.write(
        "Main.lean",
        "prelude\nimport Init.Prelude\n#check Nat\n#eval id (42 : Nat)\n",
    );
    let completed = ws.run(
        &main,
        Some(&lib),
        &["--jobs=1", "--fln-max-steps=10000", "--fln-max-frames=128"],
    );
    let text = completed.complete();
    assert!(
        text.contains("\"schema\":\"fln.source-program/1\""),
        "{text}"
    );
    assert!(text.contains("\"value\":42"), "{text}");
    for (flag, reason) in [
        ("--fln-max-steps=0", "ExecutionSteps"),
        ("--fln-max-frames=0", "RecursionDepth"),
    ] {
        let stopped = ws.run(&main, Some(&lib), &["--jobs=1", flag]);
        let stderr = stopped.refused("inconclusive", 3);
        assert!(stderr.contains("\"authority\":false"), "{stopped:?}");
        assert!(stderr.contains(reason), "{stopped:?}");
    }
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

/// The drop-in `lean` on one file, with the search path and the record store
/// both inside the workspace so a run neither reads nor leaves anything else.
fn lean_door(workspace: &Workspace, entry: &Path, lib: &Path) -> Run {
    let output = Command::new(env!("CARGO_BIN_EXE_lean"))
        .arg(entry)
        .env("LEAN_PATH", lib)
        .env("FLN_IMPORT_REUSE_DIR", workspace.0.join("records"))
        .output()
        .expect("run the installed lean");
    Run {
        code: output.status.code().expect("normal process exit"),
        stdout: String::from_utf8(output.stdout).unwrap(),
        stderr: String::from_utf8(output.stderr).unwrap(),
    }
}

/// `lean FILE` used to resolve an import only as a local source file, so a
/// file that imported a compiled module was refused before it was read, while
/// `fln run` ran the same file in its admitted world. The door now takes that
/// route and prints what `lean` prints.
#[test]
fn the_lean_door_runs_a_file_that_imports_a_compiled_module() {
    let Some(lib) = pinned_lib() else { return };
    let workspace = Workspace::new("lean-door-import");
    let entry = workspace.write(
        "Main.lean",
        "import Init.Prelude\n\ndef f (n : Nat) : Nat := n + 1\n\n#eval f 41\n#check f\n",
    );
    let ours = lean_door(&workspace, &entry, &lib);
    assert_eq!(ours.code, 0, "{ours:?}");
    assert!(ours.stderr.is_empty(), "{ours:?}");
    // The entry's own output and nothing else: no module table, no counts.
    assert_eq!(ours.stdout, "42\nf (n : Nat) : Nat\n");

    // The pinned binary beside that library prints the same bytes.
    let pinned = lib
        .parent()
        .and_then(Path::parent)
        .map(|toolchain| toolchain.join("bin/lean"))
        .filter(|lean| lean.is_file());
    match pinned {
        Some(pinned) => {
            let theirs = Command::new(pinned)
                .arg(&entry)
                .output()
                .expect("run the pinned lean");
            assert!(theirs.status.success(), "{theirs:?}");
            assert_eq!(String::from_utf8(theirs.stdout).unwrap(), ours.stdout);
        }
        None => eprintln!("SKIP: no pinned lean beside the library; stdout was not compared"),
    }

    // The same world `fln run` admits: it completes on the same file.
    workspace.run(&entry, Some(&lib), &[]).complete();
    // A second run reuses the verified record and says the same thing.
    let again = lean_door(&workspace, &entry, &lib);
    assert_eq!(
        (again.code, again.stdout.as_str()),
        (0, ours.stdout.as_str()),
        "{again:?}"
    );
}

/// The actual imported Repr class selects a checked user printer. Its result
/// reaches presentation as Format: quoted text is not quoted a second time,
/// line constructors retain trailing newlines, and #guard_msgs sees the text.
/// These expectations follow the explicit text/line constructors in the source;
/// this test does not claim a fresh execution of the Reference compiler.
#[test]
fn the_lean_door_uses_checked_printers_and_keeps_guard_messages_unquoted() {
    let Some(lib) = pinned_lib() else { return };
    let workspace = Workspace::new("lean-door-checked-printers");
    let definitions = r#"prelude
import Init.Data.Repr
inductive Printed where
  | value
instance : Repr Printed where
  reprPrec _ _ := Std.Format.text "\"already rendered λ\""
inductive Terminated where
  | value
instance : Repr Terminated where
  reprPrec _ _ := Std.Format.text "already terminated\n"
inductive Multiline where
  | value
instance : Repr Multiline where
  reprPrec _ _ := Std.Format.append (Std.Format.text "first")
    (Std.Format.append Std.Format.line (Std.Format.append (Std.Format.text "second")
      (Std.Format.append Std.Format.line Std.Format.line)))
"#;
    let entry = workspace.write(
        "Printed.lean",
        format!(
            "{definitions}#eval true\n#eval (42 : Nat)\n#eval Printed.value\n\
             /-- info: \"already rendered λ\" -/\n#guard_msgs in\n#eval Printed.value\n\
             #eval Terminated.value\n#eval Multiline.value\n\
             /--\ninfo: first\nsecond\n\n-/\n#guard_msgs in\n#eval Multiline.value\n"
        ),
    );
    let printed = lean_door(&workspace, &entry, &lib);
    assert_eq!(printed.code, 0, "{printed:?}");
    assert!(printed.stderr.is_empty(), "{printed:?}");
    assert_eq!(
        printed.stdout, "true\n42\n\"already rendered λ\"\nalready terminated\nfirst\nsecond\n\n",
        "{printed:?}"
    );

    // The record store is reused for the same imported closure. A failed
    // guarded message still discards an earlier otherwise successful output.
    let mismatch = workspace.write(
        "Mismatch.lean",
        format!(
            "{definitions}#eval true\n\
             /-- info: a different message -/\n#guard_msgs in\n#eval Printed.value\n"
        ),
    );
    let refused = lean_door(&workspace, &mismatch, &lib);
    assert_eq!(refused.code, 1, "{refused:?}");
    assert!(refused.stdout.is_empty(), "{refused:?}");
    assert!(
        refused
            .stderr
            .contains("Docstring on `#guard_msgs` does not match generated message"),
        "{refused:?}"
    );
    assert!(
        refused.stderr.contains("info: \"already rendered λ\""),
        "{refused:?}"
    );

    // The raw FlN door keeps the original Nat payload even in a world with
    // actual printer instances; it does not serialize the new Format result.
    let raw = workspace.write(
        "Raw.lean",
        "prelude\nimport Init.Data.Repr\n#eval (42 : Nat)\n",
    );
    let raw = workspace.run(&raw, Some(&lib), &["--jobs=1"]);
    assert!(
        raw.complete().contains("\"kind\":\"nat\",\"value\":42"),
        "{raw:?}"
    );
}

/// What did not change, and what a missing import now says. No pin is needed:
/// the search path is an empty directory.
#[test]
fn the_lean_door_keeps_its_local_route_and_names_an_import_that_is_nowhere() {
    let workspace = Workspace::new("lean-door-local");
    let empty = workspace.0.join("lib");
    std::fs::create_dir_all(&empty).unwrap();

    let missing = workspace.write("Missing.lean", "import No.Such.Module\n\n#eval 1\n");
    let refused = lean_door(&workspace, &missing, &empty);
    assert_eq!(refused.code, 1, "{refused:?}");
    assert!(refused.stdout.is_empty(), "{refused:?}");
    assert!(
        refused
            .stderr
            .starts_with("lean: input: import `No.Such.Module` is neither a source file"),
        "{refused:?}"
    );
    assert!(refused.stderr.contains("nor an .olean on the search path"));

    // A headerless file never had imports to resolve.
    let plain = workspace.write(
        "Plain.lean",
        "def g (n : Nat) : Nat := n + 2\n\n#eval g 40\n",
    );
    let ran = lean_door(&workspace, &plain, &empty);
    assert_eq!((ran.code, ran.stdout.as_str()), (0, "42\n"), "{ran:?}");

    // An import that is a local source file is still loaded as source.
    workspace.write("Helper.lean", "def h (n : Nat) : Nat := n + 2\n");
    let local = workspace.write("UsesHelper.lean", "import Helper\n\n#eval h 40\n");
    let ran = lean_door(&workspace, &local, &empty);
    assert_eq!((ran.code, ran.stdout.as_str()), (0, "42\n"), "{ran:?}");
}

/// `prelude` means no imports at all, not even the implicit one. The door used
/// to refuse the keyword itself; it now runs the file in an empty world, where
/// the file's own declarations exist and nothing else does. The pin accepts the
/// first file silently and rejects the second (measured 2026-10-07).
#[test]
fn a_prelude_file_is_an_empty_world_through_the_lean_door() {
    let workspace = Workspace::new("lean-door-prelude");
    let empty = workspace.0.join("lib");
    std::fs::create_dir_all(&empty).unwrap();

    let own = workspace.write(
        "Own.lean",
        "prelude\n\ninductive N where\n  | z : N\n  | s : N → N\n\ndef two : N := N.s (N.s N.z)\n",
    );
    let ran = lean_door(&workspace, &own, &empty);
    assert_eq!(
        (ran.code, ran.stdout.as_str(), ran.stderr.as_str()),
        (0, "", ""),
        "{ran:?}"
    );

    // Nothing is ambient: `Nat` is not there unless the file declares it.
    let borrowed = workspace.write("Borrowed.lean", "prelude\n\ndef f (n : Nat) : Nat := n\n");
    let refused = lean_door(&workspace, &borrowed, &empty);
    assert_eq!(refused.code, 1, "{refused:?}");
    assert!(refused.stdout.is_empty(), "{refused:?}");
    assert!(
        refused.stderr.contains("Unknown identifier `Nat`"),
        "{refused:?}"
    );
}

/// A `prelude` file whose imports do not reach `Init` has none of the `Repr` or `ToString`
/// instances the pin prints an `#eval` through, so there the pin refuses the `#eval` ("could not
/// synthesize a `Repr` or `ToString` instance for type Nat") and the door must not print it. Its
/// `#check` lines and silent declarations are unaffected. Pin verdicts measured 2026-10-07.
#[test]
fn a_prelude_world_without_init_never_prints_an_eval() {
    let Some(lib) = pinned_lib() else { return };
    let workspace = Workspace::new("lean-door-prelude-eval");
    let header = "prelude\nimport Init.Prelude\ndef answer : Nat := id 42\n";
    // Pin: exit 0, silent. Init.Prelude has no `=` notation, hence `Eq`.
    let silent = workspace.write(
        "Silent.lean",
        format!("{header}theorem same : Eq answer answer := rfl\n"),
    );
    let ran = lean_door(&workspace, &silent, &lib);
    assert_eq!(
        (ran.code, ran.stdout.as_str(), ran.stderr.as_str()),
        (0, "", ""),
        "{ran:?}"
    );
    // Pin: `Nat : Type`.
    let check = workspace.write("Check.lean", format!("{header}#check Nat\n"));
    let ran = lean_door(&workspace, &check, &lib);
    assert_eq!(
        (ran.code, ran.stdout.as_str()),
        (0, "Nat : Type\n"),
        "{ran:?}"
    );
    // Pin: refused. Printing `42` would accept what it refuses.
    let eval = workspace.write("Eval.lean", format!("{header}#eval answer\n"));
    let refused = lean_door(&workspace, &eval, &lib);
    assert_eq!(refused.code, 5, "{refused:?}");
    assert!(refused.stdout.is_empty(), "{refused:?}");
    assert!(
        refused.stderr.starts_with("lean: capability: "),
        "{refused:?}"
    );
    assert!(
        refused
            .stderr
            .contains("#eval requires an existing Repr or ToString instance"),
        "{refused:?}"
    );
}
