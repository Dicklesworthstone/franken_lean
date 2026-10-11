//! Installed source execution over actual admitted import bytes.
//! FlN retains its raw result surface; the Lean door selects checked printers.
//! Init.Prelude alone does not supply Repr/ToString for natural-number evaluations.
#![forbid(unsafe_code)]

use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};

#[path = "source_imported_execution/io_printing.rs"]
mod io_printing;
#[path = "source_imported_execution/main_run.rs"]
mod main_run;

static NEXT: AtomicUsize = AtomicUsize::new(0);

struct Workspace(PathBuf);
impl Workspace {
    fn new(case: &str) -> Self {
        let path = std::env::temp_dir().join(format!(
            "fln-program-{case}-{}-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos(),
        ));
        // PIDs can recur across sandboxed invocations. Reusing a fixture root
        // can make a missing-import test accidentally load a previous Init.
        std::fs::create_dir(&path).unwrap();
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
            .args(verb.split_ascii_whitespace())
            .arg("--json")
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

// These two installed IO fixtures use the same Lean binary and actual import
// roots. A serial validation can explicitly share verified admission records;
// ordinary test invocations retain each workspace's private store.
fn full_io_records(workspace: &Workspace) -> PathBuf {
    std::env::var_os("FLN_IMPORT_REUSE_DIR")
        .map(PathBuf::from)
        .filter(|directory| directory.is_absolute())
        .unwrap_or_else(|| workspace.0.join("records"))
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

/// The pin compiles an opaque from its value unless a companion, extern or init
/// attribute selects another implementation (`Compiler/LCNF/ToDecl.lean`, `toDecl`).
/// With `import Init` and `Left.lean` built by the pin, `opaque own : Nat := 5`,
/// `opaque left : Nat := 20` and the value-less `opaque bare : Nat` evaluate to 5, 20
/// and 0 there (measured 2026-10-11). The value runs here only for an opaque admitted
/// from source, in its own file or a sibling source module. The same declaration
/// read from an `.olean` is refused rather than run: an artifact's opaque may carry
/// an `init` attribute the importer does not read, where the pin runs the initializer.
#[test]
fn a_source_opaque_runs_its_value_and_the_same_opaque_read_from_an_olean_is_refused() {
    let Some(lib) = pinned_lib() else { return };
    let ws = Workspace::new("opaque-values");
    ws.write(
        "Left.lean",
        "prelude\nimport Init.Prelude\nopaque left : Nat := 20\nopaque bare : Nat\n",
    );
    let main = ws.write(
        "Main.lean",
        "prelude\nimport Left\nopaque own : Nat := 5\n#eval own\n#eval left\n#eval bare\n",
    );
    let ran = ws.run(&main, Some(&lib), &[]);
    let text = ran.complete();
    for (command, value) in [(1, 5), (2, 20), (3, 0)] {
        assert!(
            text.contains(&format!(
                "\"command\":{command},\"event\":\"evaluation\",\"kind\":\"nat\",\"value\":{value},"
            )),
            "{text}"
        );
    }

    let name = |text: &str| fln::Name::from_components(text.split('.'));
    let left = fln::ConstantInfo::Opaque(fln::OpaqueVal {
        base: fln::ConstantVal {
            name: name("left"),
            level_params: vec![],
            type_: fln::Expr::const_(name("Nat"), vec![]),
        },
        value: fln::Expr::lit(fln::Literal::Nat(fln::NatLit::from_u64(20))),
        is_unsafe: false,
        all: vec![name("left")],
    });
    let bytes = fln::encode_olean_module(
        fln::OleanModuleWriteInput {
            is_module: false,
            imports: &[fln::OleanModuleImport {
                module: name("Init.Prelude"),
                import_all: false,
                is_exported: true,
                is_meta: false,
            }],
            constants: &[left],
            extra_const_names: &[],
        },
        fln::OleanWriteHeader {
            version: fln::OLEAN_ACCEPTED_VERSIONS[0],
            flags: 1,
            lean_version: fln::OLEAN_PIN_TAG.strip_prefix('v').unwrap(),
            githash: fln::OLEAN_PIN_COMMIT,
            base_addr: 2 * fln::OLEAN_REGION_ALIGN as u64,
        },
        fln::OleanWriteBudget::default(),
    )
    .unwrap()
    .bytes;
    let artifact = Workspace::new("opaque-artifact");
    let objects = artifact.0.join("objects");
    std::fs::create_dir(&objects).unwrap();
    std::fs::write(objects.join("Left.olean"), bytes).unwrap();
    let search = PathBuf::from(std::env::join_paths([objects, lib]).unwrap());
    let main = artifact.write(
        "Main.lean",
        "prelude\nimport Left\n#eval (3 : Nat)\n#eval left\n",
    );
    let refused = artifact.run(&main, Some(&search), &[]);
    let stderr = refused.refused("execution", 1);
    // The import was admitted and the first evaluation compiled; only the
    // artifact's opaque value is not taken as its implementation.
    assert!(stderr.contains("command 1, byte"), "{refused:?}");
    assert!(
        stderr.contains("core Expr constant `left`")
            && stderr.contains("is not in the runtime catalogs"),
        "{refused:?}"
    );
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
    for (option, name, class, code, detail) in [
        (
            "--emit-flbc",
            "result.flbc",
            "execution",
            1,
            "entry module has no executed",
        ),
        (
            "--emit-olean-snapshot",
            "result.olean",
            "capability",
            5,
            "snapshot publication",
        ),
    ] {
        let path = ws.0.join(name);
        let emitted = ws.run(&main, None, &[option, path.to_str().unwrap()]);
        assert!(emitted.refused(class, code).contains(detail));
        assert!(!path.exists(), "a refused program must not publish {name}");
    }
    ws.run(&main, None, &[]).complete();
}

/// Build an actual standalone .olean with the installed producer, then import
/// its checked declarations through the ordinary module admission path. No
/// Reference installation or synthetic import receipt is needed for this case.
fn compiled_export_library(workspace: &Workspace) -> PathBuf {
    let source = workspace.write("Producer.lean", "def double (n : Nat) : Nat := Nat.add n n\ndef importedAnswer (n : Nat) : Nat := Nat.add (double n) 2\ndef finalValue : Nat := 0\n");
    let library = workspace.0.join("External.olean");
    workspace
        .run(
            &source,
            None,
            &["--emit-olean-snapshot", library.to_str().unwrap()],
        )
        .complete();
    library
}

#[test]
fn imported_flbc_and_sidecar_survive_without_sources_or_import_artifacts() {
    let workspace = Workspace::new("imported-artifact-closure");
    let library = compiled_export_library(&workspace);
    workspace.write(
        "Left.lean",
        "prelude\nimport External\ndef left (n : Nat) : Nat := importedAnswer n\n",
    );
    let right_source = "prelude\nimport External\ndef right : Nat := 3\n";
    workspace.write("Right.lean", right_source);
    let source = "prelude\nimport Left\nimport Right\n#eval Nat.add (left 20) right\n";
    let entry = workspace.write("Main.lean", source);
    let produce = |label: &str| {
        let product = workspace.0.join(format!("{label}.flbc"));
        let sidecar = workspace.0.join(format!("{label}.sidecar"));
        let run = workspace.run(
            &entry,
            None,
            &[
                "--emit-flbc",
                product.to_str().unwrap(),
                "--emit-sidecar",
                sidecar.to_str().unwrap(),
                "--jobs=1",
            ],
        );
        let output = run.complete();
        assert!(output.contains("\"value\":45"), "{run:?}");
        assert!(
            output.contains("\"emittedFlbc\":{") && output.contains("\"emittedSidecar\":{"),
            "{run:?}"
        );
        assert!(
            output.contains("\"module\":\"Main\",\"command\":0"),
            "{run:?}"
        );
        assert!(output.contains("\"profile\":\"standard\""), "{run:?}");
        (product, sidecar)
    };
    let (product, sidecar) = produce("first");
    let first_product = std::fs::read(&product).unwrap();
    let first_sidecar = std::fs::read(&sidecar).unwrap();
    let (repeat_product, repeat_sidecar) = produce("repeat");
    assert_eq!(std::fs::read(repeat_product).unwrap(), first_product);
    assert_eq!(std::fs::read(repeat_sidecar).unwrap(), first_sidecar);

    // An unchanged answer is not an unchanged source closure. A sibling's
    // comment leaves the compiled code alone but changes the input binding.
    workspace.write(
        "Right.lean",
        format!("{right_source}-- retained sibling input\n"),
    );
    let (changed_product, changed_sidecar) = produce("changed-source");
    assert_eq!(std::fs::read(changed_product).unwrap(), first_product);
    let changed =
        fln::decode_flbc_product_sidecar(&std::fs::read(changed_sidecar).unwrap()).unwrap();
    let original = fln::decode_flbc_product_sidecar(&first_sidecar).unwrap();
    assert_ne!(changed.closure_root(), original.closure_root());
    assert_eq!(changed.product_root(), original.product_root());

    // The consumer gets no usable source or imported artifact. Every called
    // imported definition has to be retained inside the validated bytecode.
    workspace.write("Main.lean", "deliberately malformed source");
    workspace.write("Left.lean", "deliberately malformed source");
    workspace.write("Right.lean", "deliberately malformed source");
    std::fs::write(&library, b"deliberately malformed imported artifact").unwrap();
    let consume = workspace.invoke(
        "flbc run",
        &product,
        None,
        &["--sidecar", sidecar.to_str().unwrap()],
    );
    let output = consume.complete();
    assert!(
        output.contains("\"returnValue\":45") && output.contains("\"verified\":true"),
        "{consume:?}"
    );
    let unbound = workspace.invoke("flbc run", &product, None, &[]);
    assert!(unbound.complete().contains("\"returnValue\":45"));

    let mut corrupt = first_product.clone();
    corrupt[0] ^= 1;
    let corrupted = workspace.write("corrupted.flbc", corrupt);
    let refused = workspace.invoke(
        "flbc run",
        &corrupted,
        None,
        &["--sidecar", sidecar.to_str().unwrap()],
    );
    assert!(refused.refused("sidecar", 1).contains("product"));
    assert!(
        workspace
            .invoke(
                "flbc run",
                &product,
                None,
                &["--sidecar", sidecar.to_str().unwrap()]
            )
            .complete()
            .contains("\"returnValue\":45")
    );
}

#[test]
fn imported_artifact_publication_keeps_failed_sources_and_existing_outputs_atomic() {
    let workspace = Workspace::new("imported-artifact-refusals");
    compiled_export_library(&workspace);
    let source = "prelude\nimport External\n#eval importedAnswer 20\n";
    let entry = workspace.write("Main.lean", source);
    let product = workspace.0.join("result.flbc");
    let sidecar = workspace.0.join("result.sidecar");
    let emit = [
        "--emit-flbc",
        product.to_str().unwrap(),
        "--emit-sidecar",
        sidecar.to_str().unwrap(),
    ];
    workspace.write("Main.lean", format!("{source}def broken : Nat := absent\n"));
    let late = workspace.run(&entry, None, &emit);
    assert_ne!(late.code, 0, "{late:?}");
    assert!(late.stdout.is_empty(), "{late:?}");
    assert!(!product.exists() && !sidecar.exists());

    workspace.write("Main.lean", source);
    let mut limits = emit.to_vec();
    limits.push("--fln-max-steps=0");
    workspace
        .run(&entry, None, &limits)
        .refused("inconclusive", 3);
    assert!(!product.exists() && !sidecar.exists());

    workspace.write(
        "Main.lean",
        "prelude\nimport External\n/-- info: 999 -/\n#guard_msgs in\n#eval (42 : Nat)\n",
    );
    workspace.run(&entry, None, &emit).refused("guard-msgs", 1);
    assert!(!product.exists() && !sidecar.exists());

    workspace.write(
        "Dependency.lean",
        "prelude\nimport External\n#eval (7 : Nat)\n",
    );
    workspace.write("Main.lean", "prelude\nimport Dependency\n#check Nat\n");
    assert!(
        workspace
            .run(&entry, None, &emit)
            .refused("execution", 1)
            .contains("entry module has no executed")
    );
    assert!(
        !product.exists() && !sidecar.exists(),
        "a dependency's execution is not the entry product"
    );

    workspace.write("Main.lean", source);
    workspace.write("result.flbc", b"existing product");
    workspace.run(&entry, None, &emit).refused("output", 1);
    assert_eq!(std::fs::read(&product).unwrap(), b"existing product");
    assert!(
        !sidecar.exists(),
        "known product collision must not publish a sidecar"
    );
    let fresh_product = workspace.0.join("fresh.flbc");
    workspace.write("result.sidecar", b"existing sidecar");
    workspace
        .run(
            &entry,
            None,
            &[
                "--emit-flbc",
                fresh_product.to_str().unwrap(),
                "--emit-sidecar",
                sidecar.to_str().unwrap(),
            ],
        )
        .refused("output", 1);
    assert_eq!(std::fs::read(&sidecar).unwrap(), b"existing sidecar");
    assert!(!fresh_product.exists());
    let fresh_sidecar = workspace.0.join("fresh.sidecar");
    workspace
        .run(
            &entry,
            None,
            &[
                "--emit-flbc",
                fresh_product.to_str().unwrap(),
                "--emit-sidecar",
                fresh_sidecar.to_str().unwrap(),
            ],
        )
        .complete();
    assert!(fresh_product.is_file() && fresh_sidecar.is_file());
}

#[test]
fn pinned_prelude_imports_can_publish_replayable_bytecode_and_a_verified_sidecar() {
    let Some(library) = pinned_lib() else { return };
    let workspace = Workspace::new("pinned-import-artifact");
    let entry = workspace.write(
        "Main.lean",
        "prelude\nimport Init.Prelude\ndef answer : Nat := id 42\n#eval answer\n",
    );
    let product = workspace.0.join("pinned.flbc");
    let sidecar = workspace.0.join("pinned.sidecar");
    let emitted = workspace.run(
        &entry,
        Some(&library),
        &[
            "--emit-flbc",
            product.to_str().unwrap(),
            "--emit-sidecar",
            sidecar.to_str().unwrap(),
            "--jobs=1",
        ],
    );
    assert!(emitted.complete().contains("\"value\":42"));
    let replayed = workspace.invoke(
        "flbc run",
        &product,
        None,
        &["--sidecar", sidecar.to_str().unwrap()],
    );
    assert!(replayed.complete().contains("\"returnValue\":42"));
    assert!(replayed.stdout.contains("\"verified\":true"));
}

/// `sorry` elaborates to the pin's `sorryAx (Lean.Name → T) false tag` and every declaration
/// that uses it is admitted with the pin's warning, positioned at the declared name, or at the
/// keyword for an `example`, an anonymous instance and a structure; `warn.sorry false` silences
/// it. The expected bytes are the pinned v4.32.0's on this file (measured 2026-10-11), and the
/// pinned binary beside the library is compared again when present. `check-source` prints no
/// warnings, so it counts the declarations instead.
#[test]
fn sorry_is_admitted_with_the_pins_warnings() {
    let Some(lib) = pinned_lib() else { return };
    let workspace = Workspace::new("lean-door-sorry");
    let entry = workspace.write(
        "Main.lean",
        "prelude\nimport Init.Prelude\nexample : Eq 1 2 := sorry\nclass C where\n  x : Nat\n\
         instance : C := sorry\n/-- doc -/\nprotected def Foo.bar : Nat := sorry\n\
         set_option warn.sorry false in\ntheorem quiet : Eq 1 2 := sorry\n\
         instance named : C := sorry\ntheorem two : Eq 2 2 := Eq.refl 2\n\
         structure S where\n  x : Nat := sorry\n",
    );
    let file = entry.display();
    let expected: String = ["3:0", "6:0", "8:14", "11:9", "13:0"]
        .iter()
        .map(|at| format!("{file}:{at}: warning: declaration uses `sorry`\n"))
        .collect();
    let ours = lean_door(&workspace, &entry, &lib);
    assert_eq!((ours.code, ours.stderr.as_str()), (0, ""), "{ours:?}");
    assert_eq!(ours.stdout, expected);
    let pinned = lib
        .parent()
        .and_then(Path::parent)
        .map(|toolchain| toolchain.join("bin/lean"))
        .filter(|lean| lean.is_file());
    match pinned {
        Some(pinned) => {
            let theirs = Command::new(pinned)
                .arg(&entry)
                .env("LEAN_PATH", &lib)
                .output()
                .expect("run the pinned lean");
            assert!(theirs.status.success(), "{theirs:?}");
            assert_eq!(String::from_utf8(theirs.stdout).unwrap(), ours.stdout);
        }
        None => eprintln!("SKIP: no pinned lean beside the library; stdout was not compared"),
    }
    // `instC`, `Foo.bar`, `quiet` (silenced, still a use), `named` and `S.x`'s default.
    let checked = workspace.invoke("check-source", &entry, Some(&lib), &[]);
    assert_eq!(checked.code, 0, "{checked:?}");
    assert!(
        checked
            .stdout
            .contains("\"theorems\":2,\"axioms\":0,\"sorryDeclarations\":5,"),
        "{checked:?}"
    );
    // Each `sorry` is its own term: two of them are not definitionally equal, at the pin too.
    let distinct = workspace.write(
        "Distinct.lean",
        "prelude\nimport Init.Prelude\nexample : Eq (sorry : Nat) sorry := Eq.refl _\n",
    );
    let refused = lean_door(&workspace, &distinct, &lib);
    assert_eq!(refused.code, 1, "{refused:?}");
    assert!(refused.stdout.is_empty(), "{refused:?}");
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
        code: output
            .status
            .code()
            .unwrap_or_else(|| panic!("lean terminated: {output:?}")),
        stdout: String::from_utf8(output.stdout).unwrap(),
        stderr: String::from_utf8(output.stderr).unwrap(),
    }
}

fn lean_stdin(workspace: &Workspace, source: &[u8], lib: &Path, extra: &[&str]) -> Run {
    use std::io::Write;
    use std::process::Stdio;
    let mut child = Command::new(env!("CARGO_BIN_EXE_lean"))
        .arg("--stdin")
        .args(extra)
        .current_dir(&workspace.0)
        .env("LEAN_PATH", lib)
        .env("FLN_IMPORT_REUSE_DIR", workspace.0.join("records"))
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("run the installed lean with standard input");
    child.stdin.take().unwrap().write_all(source).unwrap();
    let output = child.wait_with_output().unwrap();
    Run {
        code: output
            .status
            .code()
            .unwrap_or_else(|| panic!("lean terminated: {output:?}")),
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

/// Ordinary Lean source must resolve Init, even without an explicit import.
/// No pin is needed to test a missing dependency or a small source-only world.
#[test]
fn ordinary_lean_requires_init_and_keeps_prelude_local_to_each_module() {
    let workspace = Workspace::new("lean-door-local");
    let empty = workspace.0.join("lib");
    std::fs::create_dir_all(&empty).unwrap();

    let missing = workspace.write(
        "Missing.lean",
        "prelude\nimport No.Such.Module\n\n#eval 1\n",
    );
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

    // These previously ran in a synthetic seed despite the missing Init.
    let plain = workspace.write(
        "Plain.lean",
        "def g (n : Nat) : Nat := n + 2\n\n#eval g 40\n",
    );
    workspace.write("Helper.lean", "def h (n : Nat) : Nat := n + 2\n");
    let local = workspace.write("UsesHelper.lean", "import Helper\n\n#eval h 40\n");
    for entry in [&plain, &local] {
        let refused = lean_door(&workspace, entry, &empty);
        assert_eq!(refused.code, 1, "{refused:?}");
        assert!(refused.stdout.is_empty(), "{refused:?}");
        assert!(
            refused
                .stderr
                .contains("import `Init` is neither a source file"),
            "{refused:?}"
        );
    }

    workspace.write("Init.lean", "prelude\ninductive Marker where\n  | token\n");
    workspace.write("Helper.lean", "def marker : Marker := Marker.token\n");
    for header in ["", "prelude\n"] {
        let entry = workspace.write(
            "UsesHelper.lean",
            format!("{header}import Helper\n#check marker\n"),
        );
        let ran = lean_door(&workspace, &entry, &empty);
        assert_eq!(
            (ran.code, ran.stdout.as_str(), ran.stderr.as_str()),
            (0, "marker : Marker\n", ""),
            "{ran:?}"
        );
    }

    // An entry's own Init cannot leak into a prelude dependency.
    workspace.write(
        "Helper.lean",
        "prelude\ndef marker : Marker := Marker.token\n",
    );
    let entry = workspace.write("UsesHelper.lean", "import Helper\n#check marker\n");
    let refused = lean_door(&workspace, &entry, &empty);
    assert_eq!(refused.code, 1, "{refused:?}");
    assert!(refused.stdout.is_empty(), "{refused:?}");
    assert!(
        refused.stderr.contains("Unknown identifier `Marker`"),
        "{refused:?}"
    );
}

#[test]
fn stdin_is_a_virtual_lean_module_with_real_import_resolution() {
    let workspace = Workspace::new("lean-stdin-imports");
    let empty = workspace.0.join("lib");
    std::fs::create_dir_all(&empty).unwrap();
    let on_disk = workspace.write("stdin.lean", "this file must not be read or overwritten\n");
    let original = std::fs::read(&on_disk).unwrap();
    let refused = lean_stdin(&workspace, b"#check Nat\n", &empty, &[]);
    assert_eq!(refused.code, 1, "{refused:?}");
    assert!(refused.stdout.is_empty(), "{refused:?}");
    assert!(
        refused
            .stderr
            .contains("import `Init` is neither a source file"),
        "{refused:?}"
    );

    let own = lean_stdin(
        &workspace,
        b"prelude\ninductive Local where\n  | value\n#check Local\n",
        &empty,
        &[],
    );
    assert_eq!(
        (own.code, own.stdout.as_str(), own.stderr.as_str()),
        (0, "Local : Type\n", ""),
        "{own:?}"
    );
    workspace.write("Init.lean", "prelude\ninductive Marker where\n  | token\n");
    workspace.write("Helper.lean", "def marker : Marker := Marker.token\n");
    for (source, extra) in [
        (b"#check Marker\n".as_slice(), vec![]),
        (b"import Helper\n#check Marker\n", vec!["--threads=0"]),
        (b"import Helper\n#check Marker\n", vec!["-j2"]),
    ] {
        let ran = lean_stdin(&workspace, source, &empty, &extra);
        assert_eq!(
            (ran.code, ran.stdout.as_str(), ran.stderr.as_str()),
            (0, "Marker : Type\n", ""),
            "{ran:?}"
        );
    }
    let stopped = lean_stdin(
        &workspace,
        b"import Helper\n#check marker\n",
        &empty,
        &["--max-bytes=80"],
    );
    assert_eq!(stopped.code, 3, "{stopped:?}");
    assert!(stopped.stdout.is_empty(), "{stopped:?}");
    assert!(
        stopped.stderr.contains("imported Lean source exceeded")
            && stopped.stderr.contains("input limit"),
        "{stopped:?}"
    );
    let missing = lean_stdin(&workspace, b"prelude\nimport Missing\n", &empty, &[]);
    assert_eq!(missing.code, 1, "{missing:?}");
    assert!(missing.stdout.is_empty(), "{missing:?}");
    assert!(
        missing
            .stderr
            .contains("import `Missing` is neither a source file"),
        "{missing:?}"
    );
    assert_eq!(std::fs::read(on_disk).unwrap(), original);
}

#[test]
fn stdin_uses_the_pinned_virtual_module_identity() {
    let workspace = Workspace::new("stdin-module-identity");
    let empty = workspace.0.join("lib");
    std::fs::create_dir_all(&empty).unwrap();
    workspace.write("stdin.lean", "prelude\ninductive Local where\n  | value\n");
    let imported = lean_stdin(
        &workspace,
        b"prelude\nimport stdin\n#check Local\n",
        &empty,
        &[],
    );
    assert_eq!(
        (
            imported.code,
            imported.stdout.as_str(),
            imported.stderr.as_str()
        ),
        (0, "Local : Type\n", ""),
        "{imported:?}"
    );
    // The pin's anonymous main module is `_stdin`, so an import back to it
    // is a cycle even when an unrelated `_stdin.lean` exists on disk.
    workspace.write("_stdin.lean", "prelude\n");
    workspace.write("Helper.lean", "prelude\nimport _stdin\n");
    let cycle = lean_stdin(&workspace, b"prelude\nimport Helper\n", &empty, &[]);
    assert_eq!(cycle.code, 1, "{cycle:?}");
    assert!(cycle.stdout.is_empty(), "{cycle:?}");
    assert!(
        cycle.stderr.contains("cycle") && cycle.stderr.contains("_stdin"),
        "{cycle:?}"
    );
}

#[test]
fn dependency_message_guards_fail_ordinary_files_and_stdin() {
    let workspace = Workspace::new("ordinary-dependency-guard");
    let empty = workspace.0.join("lib");
    std::fs::create_dir_all(&empty).unwrap();
    workspace.write(
        "Dependency.lean",
        "prelude\ninductive N where\n  | z\n/-- info: unexpected -/\n#guard_msgs in\ndef value : N := N.z\n",
    );
    let source = b"prelude\nimport Dependency\n#check value\n";
    let entry = workspace.write("Main.lean", source);
    for ran in [
        lean_door(&workspace, &entry, &empty),
        lean_stdin(&workspace, source, &empty, &[]),
    ] {
        assert_eq!(ran.code, 1, "{ran:?}");
        assert!(ran.stdout.is_empty(), "{ran:?}");
        assert!(ran.stderr.contains("guard-msgs"), "{ran:?}");
    }
    // This independent entry error would win if dependency guards were only
    // judged after the full module graph had already executed.
    let blocked = lean_stdin(
        &workspace,
        b"prelude\nimport Dependency\n#check missingAfterGuard\n",
        &empty,
        &[],
    );
    assert_eq!(blocked.code, 1, "{blocked:?}");
    assert!(blocked.stdout.is_empty(), "{blocked:?}");
    assert!(blocked.stderr.contains("guard-msgs"), "{blocked:?}");
    assert!(!blocked.stderr.contains("missingAfterGuard"), "{blocked:?}");
    // A matching silent guard completes, with only entry output published.
    workspace.write(
        "Dependency.lean",
        "prelude\ninductive N where\n  | z\n#guard_msgs in\ndef value : N := N.z\n",
    );
    let recovered = lean_stdin(&workspace, source, &empty, &[]);
    assert_eq!(
        (
            recovered.code,
            recovered.stdout.as_str(),
            recovered.stderr.as_str()
        ),
        (0, "value : N\n", ""),
        "{recovered:?}"
    );
}

/// The ordinary path must admit the real Init closure and use its printers.
/// A main declaration is checked but only --run may invoke it.
#[test]
fn ordinary_file_and_stdin_admit_actual_init_without_invoking_main() {
    let Some(library) = pinned_lib() else { return };
    assert!(library.join("Init.olean").is_file());
    let workspace = Workspace::new("ordinary-lean-init");
    let source =
        b"#check Int\n#eval (42 : Nat)\ndef main : IO Unit := IO.println \"main must not run\"\n";
    let entry = workspace.write("Main.lean", source);
    for ran in [
        lean_door(&workspace, &entry, &library),
        lean_stdin(&workspace, source, &library, &[]),
    ] {
        assert_eq!(
            (ran.code, ran.stdout.as_str(), ran.stderr.as_str()),
            (0, "Int : Type\n42\n", ""),
            "{ran:?}"
        );
    }
    // The same admitted closure is available to ordinary local dependencies.
    workspace.write("Helper.lean", "def answer : Int := 42\n");
    let entry = workspace.write(
        "UsesHelper.lean",
        "import Helper\n#check answer\n#eval (42 : Nat)\n",
    );
    let ran = lean_door(&workspace, &entry, &library);
    assert_eq!(
        (ran.code, ran.stdout.as_str(), ran.stderr.as_str()),
        (0, "answer : Int\n42\n", ""),
        "{ran:?}"
    );
    let stopped = lean_stdin(&workspace, source, &library, &["--fln-max-steps=0"]);
    assert_eq!(stopped.code, 3, "{stopped:?}");
    assert!(stopped.stdout.is_empty(), "{stopped:?}");
    let invalid = lean_stdin(
        &workspace,
        b"#check Int\n#eval (42 : Nat)\n#check missing\n",
        &library,
        &[],
    );
    assert_eq!(invalid.code, 1, "{invalid:?}");
    assert!(invalid.stdout.is_empty(), "{invalid:?}");
    assert!(invalid.stderr.contains("missing"), "{invalid:?}");
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
