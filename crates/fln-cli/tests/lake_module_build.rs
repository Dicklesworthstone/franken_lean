//! Installed Lake module builds, real codec inspection and downstream imports.
#![forbid(unsafe_code)]
use std::{
    path::{Path, PathBuf},
    process::{Command, Output},
    sync::atomic::{AtomicUsize, Ordering},
};

static NEXT: AtomicUsize = AtomicUsize::new(0);
struct Package(PathBuf);
impl Package {
    fn new(config: &str) -> Self {
        let path = std::env::temp_dir().join(format!(
            "fln-lake-modules-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        std::fs::create_dir_all(&path).unwrap();
        let package = Self(path);
        package.write("lakefile.toml", config);
        package
    }
    fn write(&self, relative: &str, bytes: impl AsRef<[u8]>) {
        let path = self.0.join(relative);
        std::fs::create_dir_all(path.parent().unwrap()).unwrap();
        std::fs::write(path, bytes).unwrap();
    }
    fn build(&self, targets: &[&str]) -> Output {
        Command::new(env!("CARGO_BIN_EXE_lake"))
            .arg("--dir")
            .arg(&self.0)
            .args(["--json", "build"])
            .args(targets)
            .env("LEAN_PATH", self.0.join("no-imports"))
            // A store of the package's own, never the user's (bead `franken_lean-z8j.1.1`).
            .env("FLN_IMPORT_REUSE_DIR", self.0.join(".records"))
            .output()
            .unwrap()
    }
    fn artifact(&self, module: &str) -> PathBuf {
        self.0
            .join(".lake/build/lib/lean")
            .join(format!("{}.olean", module.replace('.', "/")))
    }
}
impl Drop for Package {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

const CONFIG: &str = "name = \"checked\"\ndefaultTargets = [\"Library\"]\n[[lean_lib]]\nname = \"Library\"\nroots = [\"Lib\"]\n";
const BASE: &str = "prelude\ndef Lib.identity (A : Type) (a : A) : A := a\n";
const TOP: &str = "prelude\nimport Lib.Base\ndef Lib.again (A : Type) (a : A) : A := Lib.identity A a\ntheorem Lib.proof (P : Prop) (h : P) : P := h\n";

fn success(output: &Output) -> String {
    assert!(output.status.success(), "{output:?}");
    assert!(output.stderr.is_empty(), "{output:?}");
    String::from_utf8(output.stdout.clone()).unwrap()
}
fn failure(output: &Output) -> String {
    assert_eq!(output.status.code(), Some(1), "{output:?}");
    assert!(output.stdout.is_empty(), "{output:?}");
    String::from_utf8(output.stderr.clone()).unwrap()
}
fn inspect(path: &Path) -> String {
    success(
        &Command::new(env!("CARGO_BIN_EXE_fln"))
            .args(["olean", "inspect", "--constants"])
            .arg(path)
            .output()
            .unwrap(),
    )
}
fn library() -> Package {
    let package = Package::new(CONFIG);
    package.write("Lib/Base.lean", BASE);
    package.write("Lib/Top.lean", TOP);
    package
}

#[test]
fn builds_real_module_closure_and_downstream_source_imports_it() {
    let package = library();
    let report = success(&package.build(&["+Lib.Top:olean"]));
    assert!(report.contains("\"modules_built\":2"), "{report}");
    assert!(report.contains("\"modules_cached\":0"), "{report}");
    let base = inspect(&package.artifact("Lib.Base"));
    let top = inspect(&package.artifact("Lib.Top"));
    assert!(base.contains("Lib.identity"), "{base}");
    assert!(top.contains("Lib.again"), "{top}");
    assert!(
        !top.contains("Lib.identity"),
        "imported declarations were duplicated: {top}"
    );

    let consumer = Package::new("name = \"consumer\"\n[[lean_lib]]\nname = \"Consumer\"\n");
    consumer.write(
        "Consumer.lean",
        "prelude\nimport Consumer.Helper\ndef downstream (A : Type) (a : A) : A := Consumer.forward A a\n",
    );
    consumer.write(
        "Consumer/Helper.lean",
        "prelude\nimport Lib.Top\ndef Consumer.forward (A : Type) (a : A) : A := Lib.again A a\n",
    );
    let out = Command::new(env!("CARGO_BIN_EXE_lake"))
        .arg("--dir")
        .arg(&consumer.0)
        .args(["--json", "build", "+Consumer:olean"])
        .env("LEAN_PATH", package.0.join(".lake/build/lib/lean"))
        .env("FLN_IMPORT_REUSE_DIR", consumer.0.join(".records"))
        .output()
        .unwrap();
    success(&out);
    assert!(inspect(&consumer.artifact("Consumer")).contains("downstream"));
    assert!(inspect(&consumer.artifact("Consumer.Helper")).contains("Consumer.forward"));

    let client = Package::new("name = \"client\"\n");
    client.write(
        "Use.lean",
        "prelude\nimport Consumer\ntheorem imported (P : Prop) (h : P) : P := Lib.proof P h\n",
    );
    let search = std::env::join_paths([
        consumer.0.join(".lake/build/lib/lean"),
        package.0.join(".lake/build/lib/lean"),
    ])
    .unwrap();
    let out = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["check-source", "--json", "--import-posture", "recheck"])
        .arg(client.0.join("Use.lean"))
        .env("LEAN_PATH", search)
        .output()
        .unwrap();
    let report = success(&out);
    assert!(
        report.contains("\"trust\":\"recheck\",\"admission\":\"council\""),
        "{report}"
    );
}

#[test]
fn rebuilds_changed_bytes_and_never_trusts_forged_or_stale_outputs() {
    let package = library();
    package.write(
        ".lake/build/lib/lean/Lib/Base.olean",
        "fln-olean-artifact:Lib.Base",
    );
    success(&package.build(&["Lib.Top:olean"]));
    let original = std::fs::read(package.artifact("Lib.Base")).unwrap();
    let source_modified = std::fs::metadata(package.0.join("Lib/Base.lean"))
        .unwrap()
        .modified()
        .unwrap();
    success(&package.build(&["Lib.Top:olean"]));
    assert_eq!(
        std::fs::read(package.artifact("Lib.Base")).unwrap(),
        original
    );
    package.write(
        "Lib/Base.lean",
        format!("{BASE}def Lib.second (A : Type) (a : A) : A := a\n"),
    );
    std::fs::File::options()
        .write(true)
        .open(package.0.join("Lib/Base.lean"))
        .unwrap()
        .set_times(std::fs::FileTimes::new().set_modified(source_modified))
        .unwrap();
    success(&package.build(&["Lib.Top:olean"]));
    assert_ne!(
        std::fs::read(package.artifact("Lib.Base")).unwrap(),
        original
    );
    assert!(inspect(&package.artifact("Lib.Base")).contains("Lib.second"));
}

#[test]
fn source_failure_and_multiple_target_failure_preserve_every_previous_artifact() {
    let package = library();
    success(&package.build(&["+Lib.Top:olean"]));
    let base = std::fs::read(package.artifact("Lib.Base")).unwrap();
    let top = std::fs::read(package.artifact("Lib.Top")).unwrap();
    for invalid in [
        "this is not Lean (((",
        "theorem falseProof (P : Prop) : P := by rfl",
    ] {
        package.write("Lib/Base.lean", format!("prelude\n{invalid}\n"));
        let error = failure(&package.build(&["+Lib.Top:olean"]));
        assert!(error.contains("Lib.Base"), "{error}");
        assert_eq!(std::fs::read(package.artifact("Lib.Base")).unwrap(), base);
        assert_eq!(std::fs::read(package.artifact("Lib.Top")).unwrap(), top);
    }
    package.write(
        "Lib/Base.lean",
        format!("{BASE}def Lib.newValue (A : Type) (a : A) : A := a\n"),
    );
    package.write("Lib/Bad.lean", "prelude\ninvalid !!!\n");
    failure(&package.build(&["+Lib.Top:olean", "+Lib.Bad:olean"]));
    assert_eq!(std::fs::read(package.artifact("Lib.Base")).unwrap(), base);
    assert!(!package.artifact("Lib.Bad").exists());
    success(&package.build(&["+Lib.Top:olean"]));
}

#[test]
fn respects_declared_roots_directories_and_does_not_check_unrelated_source() {
    let package = Package::new(
        "name = \"dirs\"\nsrcDir = \"src\"\nbuildDir = \"products\"\n[[lean_lib]]\nname = \"OtherName\"\nroots = [\"Lib\"]\nsrcDir = \"proofs\"\n",
    );
    package.write("src/proofs/Lib/Base.lean", BASE);
    package.write("src/proofs/Lib/Top.lean", TOP);
    package.write("src/proofs/Lib/Unrelated.lean", "garbage !!!");
    success(&package.build(&["+Lib.Top:olean"]));
    assert!(package.0.join("products/lib/lean/Lib/Top.olean").is_file());
    assert!(
        !package
            .0
            .join("products/lib/lean/Lib/Unrelated.olean")
            .exists()
    );
    let error = failure(&package.build(&["+Outside:olean"]));
    assert!(error.contains("declared lean_lib"), "{error}");
}

#[test]
fn refuses_incomplete_facets_unhandled_settings_and_missing_implicit_init() {
    let package = library();
    for args in [
        vec![],
        vec!["Library"],
        vec!["+Lib.Top:c"],
        vec!["+Lib.Top:olean", "--no-build"],
    ] {
        let error = failure(&package.build(&args));
        assert!(error.contains("unavailable"), "{error}");
        assert!(!package.0.join(".lake").exists());
    }
    // TOML defaults name declared targets, not CLI module/facet expressions.
    package.write(
        "lakefile.toml",
        CONFIG.replace("[\"Library\"]", "[\"+Lib.Top:olean\"]"),
    );
    failure(&package.build(&[]));
    assert!(!package.0.join(".lake").exists());
    package.write("lakefile.toml", CONFIG);
    package.write("Lib/Base.lean", "def plain (A : Type) (a : A) : A := a\n");
    let error = failure(&package.build(&["+Lib.Base:olean"]));
    assert!(
        error.contains("Init") && error.contains("search path"),
        "{error}"
    );
    assert!(!package.0.join(".lake").exists());
    for setting in [
        "globs = [\"Lib.*\"]",
        "precompileModules = true",
        "moreLeanArgs = [\"-DautoImplicit=false\"]",
    ] {
        package.write("lakefile.toml", format!("{CONFIG}{setting}\n"));
        let error = failure(&package.build(&["+Lib.Top:olean"]));
        assert!(error.contains("unsupported"), "{error}");
        assert!(!package.0.join(".lake").exists());
    }
}

#[test]
fn cycles_leaked_sibling_declarations_and_resource_overflow_never_publish() {
    let package = library();
    package.write("Lib/Base.lean", "prelude\nimport Lib.Top\n");
    assert!(failure(&package.build(&["+Lib.Top:olean"])).contains("cycle"));
    package.write("Lib/Base.lean", BASE);
    package.write(
        "Lib/Sibling.lean",
        "prelude\ndef leak (A : Type) (a : A) : A := Lib.identity A a\n",
    );
    package.write(
        "Lib/Top.lean",
        "prelude\nimport Lib.Base\nimport Lib.Sibling\n",
    );
    assert!(failure(&package.build(&["+Lib.Top:olean"])).contains("Lib.Sibling"));
    package.write("Lib/Base.lean", vec![b' '; 1024 * 1024 + 1]);
    assert!(failure(&package.build(&["+Lib.Base:olean"])).contains("resource"));
    assert!(!package.0.join(".lake").exists());
}

#[test]
fn output_preflight_refuses_bad_destinations_before_replacing_any_artifact() {
    let package = library();
    package.write(".lake/build/lib/lean/Lib/Base.olean", "previous artifact");
    std::fs::create_dir_all(package.artifact("Lib.Top")).unwrap();
    let error = failure(&package.build(&["+Lib.Top:olean"]));
    assert!(error.contains("not a regular file"), "{error}");
    assert_eq!(
        std::fs::read(package.artifact("Lib.Base")).unwrap(),
        b"previous artifact"
    );
}

#[cfg(unix)]
#[test]
fn symlinked_sources_and_output_directories_are_refused() {
    let package = Package::new(CONFIG);
    let outside = Package::new(CONFIG);
    outside.write("Base.lean", BASE);
    std::fs::create_dir_all(package.0.join("Lib")).unwrap();
    std::os::unix::fs::symlink(outside.0.join("Base.lean"), package.0.join("Lib/Base.lean"))
        .unwrap();
    let error = failure(&package.build(&["+Lib.Base:olean"]));
    assert!(error.contains("symlink"), "{error}");
    assert!(!package.0.join(".lake").exists());

    let package = library();
    std::fs::create_dir_all(package.0.join(".lake/build/lib")).unwrap();
    std::os::unix::fs::symlink(&outside.0, package.0.join(".lake/build/lib/lean")).unwrap();
    assert!(failure(&package.build(&["+Lib.Top:olean"])).contains("symlink"));
    assert!(!outside.0.join("Lib/Top.olean").exists());
}

/// `lake build --jobs N` admits the external `.olean` closure N modules at a time
/// and builds the same report and the same artifact bytes at every N. The
/// consumer's closure holds two siblings that import only `Lib.Base`.
#[test]
fn external_imports_build_identically_at_one_and_several_jobs() {
    let library =
        Package::new("name = \"checked\"\n[[lean_lib]]\nname = \"Library\"\nroots = [\"Lib\"]\n");
    library.write("Lib/Base.lean", BASE);
    library.write(
        "Lib/Left.lean",
        "prelude\nimport Lib.Base\ndef Lib.left (A : Type) (a : A) : A := Lib.identity A a\n",
    );
    library.write(
        "Lib/Right.lean",
        "prelude\nimport Lib.Base\ntheorem Lib.right (P : Prop) (h : P) : P := h\n",
    );
    success(&library.build(&["+Lib.Left:olean", "+Lib.Right:olean"]));
    let built = |jobs: &str| {
        let consumer = Package::new("name = \"consumer\"\n[[lean_lib]]\nname = \"Consumer\"\n");
        consumer.write(
            "Consumer.lean",
            "prelude\nimport Lib.Left\nimport Lib.Right\ndef Consumer.value (A : Type) (a : A) : A := Lib.left A a\ntheorem Consumer.proof (P : Prop) (h : P) : P := Lib.right P h\n",
        );
        let output = Command::new(env!("CARGO_BIN_EXE_lake"))
            .arg("--dir")
            .arg(&consumer.0)
            // The council's job count is this test's subject. Under the default
            // `reuse-verified` posture the second build would reuse the first one's
            // record and report it, so the posture is pinned (bead `fln-uyuz`).
            .args([
                "--json",
                "build",
                "--import-posture",
                "recheck",
                "--jobs",
                jobs,
                "+Consumer:olean",
            ])
            .env("LEAN_PATH", library.0.join(".lake/build/lib/lean"))
            .output()
            .unwrap();
        let report = success(&output).replace(&consumer.0.display().to_string(), "<package>");
        (
            report,
            std::fs::read(consumer.artifact("Consumer")).unwrap(),
        )
    };
    let serial = built("1");
    assert!(serial.0.contains("\"modules_built\":1"), "{}", serial.0);
    for jobs in ["2", "5"] {
        assert_eq!(built(jobs), serial, "--jobs {jobs}");
    }

    let refused = failure(
        &Command::new(env!("CARGO_BIN_EXE_lake"))
            .arg("--dir")
            .arg(&library.0)
            .args(["--json", "build", "--jobs", "0", "+Lib.Left:olean"])
            .output()
            .unwrap(),
    );
    assert!(
        refused.contains("--jobs takes a positive thread count"),
        "{refused}"
    );
}

/// A source module's own `protected` declarations survive into the `.olean` Lake
/// builds (bead `fln-eq4k`): the pin's `protectedExt` block, sorted by
/// `Name.quickLt` as the pin writes it and binary-searches it. Two readers then
/// agree on a consumer: FrankenLean's `check-source` and, when installed, the
/// pinned Reference `lean` itself, which refuses each tag's atomic name under
/// `open` and accepts the qualified name and the unprotected sibling.
#[test]
fn protected_declarations_survive_into_the_olean_for_both_readers() {
    let package = Package::new(CONFIG);
    package.write(
        "Lib/Guard.lean",
        "prelude\nnamespace Lib\nprotected def one (P : Prop) (h : P) : P := h\n\
         protected def two (P : Prop) (h : P) : P := h\n\
         protected theorem three (P : Prop) (h : P) : P := h\n\
         def plain (P : Prop) (h : P) : P := h\nend Lib\n",
    );
    success(&package.build(&["+Lib.Guard:olean"]));
    let bytes = std::fs::read(package.artifact("Lib.Guard")).unwrap();
    let blocks = fln_olean::region::OleanView::parse(&bytes)
        .unwrap()
        .extension_payloads(fln_olean::region::WalkBudget::default(), 1 << 20)
        .unwrap();
    let decoded = fln_olean::source_extensions::decode(
        &blocks,
        fln_olean::source_extensions::DecodeLimits::default(),
    )
    .unwrap();
    let mut expected: Vec<_> = ["Lib.one", "Lib.two", "Lib.three"]
        .map(|name| fln_core::name::Name::from_components(name.split('.')))
        .into();
    expected.sort_by(|left, right| left.quick_cmp(right));
    assert_eq!(decoded.protected, expected, "written in Name.quickLt order");

    let client = Package::new("name = \"client\"\n");
    // Inside `namespace Lib`, not under `open Lib`: the pin's resolution rule is the
    // same at the current namespace, and `open Lib` would test something else. A
    // FrankenLean-written olean records no `namespacesExt` entry, so the pin refuses
    // `open Lib` itself as an "unknown namespace", whatever the tags say.
    let consumer =
        |body: &str| format!("prelude\nimport Lib.Guard\nnamespace Lib\n{body}\nend Lib\n");
    // (program body, the pin's verdict on it)
    let cases = [
        ("theorem u (P : Prop) (h : P) : P := one P h", false),
        ("theorem u (P : Prop) (h : P) : P := two P h", false),
        ("theorem u (P : Prop) (h : P) : P := three P h", false),
        ("theorem u (P : Prop) (h : P) : P := Lib.one P h", true),
        ("theorem u (P : Prop) (h : P) : P := plain P h", true),
    ];
    let lib = package.0.join(".lake/build/lib/lean");
    let pinned = std::env::var_os("HOME")
        .map(|home| PathBuf::from(home).join(".elan/toolchains/leanprover--lean4---v4.32.0"))
        .filter(|root| root.join("bin/lean").is_file());
    assert!(
        pinned.is_some() || std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
        "FLN_REQUIRE_REFERENCE is set but the pinned Reference is absent"
    );
    for (index, (body, accepted)) in cases.iter().enumerate() {
        let file = format!("Use{index}.lean");
        client.write(&file, consumer(body));
        let fln = Command::new(env!("CARGO_BIN_EXE_fln"))
            .args(["check-source", "--json", "--import-posture", "recheck"])
            .arg(client.0.join(&file))
            .env("LEAN_PATH", &lib)
            .env("FLN_IMPORT_REUSE_DIR", client.0.join(".records"))
            .output()
            .unwrap();
        assert_eq!(fln.status.success(), *accepted, "fln on {body}: {fln:?}");
        let Some(root) = &pinned else {
            eprintln!("SKIP: pinned Reference absent; FrankenLean's verdict only");
            continue;
        };
        let search = std::env::join_paths([lib.clone(), root.join("lib/lean")]).unwrap();
        let lean = Command::new(root.join("bin/lean"))
            .arg(client.0.join(&file))
            .env("LEAN_PATH", search)
            .output()
            .unwrap();
        assert_eq!(
            lean.status.success(),
            *accepted,
            "the pinned lean on {body}, reading FrankenLean's olean: {lean:?}"
        );
        if !accepted {
            // Refused because the tag held the atomic name back, nothing else.
            let said = String::from_utf8_lossy(&lean.stdout);
            assert!(
                said.contains("Unknown identifier"),
                "the pinned lean refused {body} for another reason: {said}"
            );
        }
    }
}
