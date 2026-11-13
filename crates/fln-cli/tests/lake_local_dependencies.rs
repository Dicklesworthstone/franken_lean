//! Installed native execution across explicitly declared local Lake packages.
#![forbid(unsafe_code)]

use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::{SystemTime, UNIX_EPOCH};

static NEXT: AtomicUsize = AtomicUsize::new(0);

struct Workspace(PathBuf, Option<PathBuf>);

impl Workspace {
    fn new() -> Self {
        let stamp = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let path = std::env::temp_dir().join(format!(
            "fln-lake-local-{}-{stamp}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed),
        ));
        std::fs::create_dir(&path).unwrap();
        let workspace = Self(path, None);
        workspace.write("root/lakefile.toml", ROOT);
        workspace.write("root/src/app/App/Main.lean", MAIN);
        workspace.write("left/lakefile.toml", LEFT);
        workspace.write("left/code/lib/Feature/Left.lean", LEFT_SOURCE);
        workspace.write("right/lakefile.toml", RIGHT);
        workspace.write("right/Feature/Right.lean", RIGHT_SOURCE);
        workspace.write("right/vendor/shared library/lakefile.toml", SHARED);
        workspace.write(
            "right/vendor/shared library/sources/lib/Shared.lean",
            SHARED_SOURCE,
        );
        workspace
    }

    fn write(&self, relative: &str, bytes: impl AsRef<[u8]>) {
        let path = self.0.join(relative);
        std::fs::create_dir_all(path.parent().unwrap()).unwrap();
        std::fs::write(path, bytes).unwrap();
    }

    fn run(&self, arguments: &[&str], reference: Option<&Path>) -> Output {
        Command::new(
            self.1
                .as_deref()
                .unwrap_or(Path::new(env!("CARGO_BIN_EXE_lake"))),
        )
        .arg("--dir")
        .arg(self.0.join("root"))
        .args(["--jobs", "2"])
        .args(arguments)
        .current_dir(&self.0)
        .env(
            "LEAN_PATH",
            reference.unwrap_or(&self.0.join("absent-imports")),
        )
        .env("FLN_IMPORT_REUSE_DIR", self.0.join("import-records"))
        .output()
        .unwrap()
    }

    fn no_products(&self) {
        for package in ["root", "left", "right", "right/vendor/shared library"] {
            let package = self.0.join(package);
            assert!(!package.join("output").exists(), "{}", package.display());
            assert!(
                !package.join(".lake/build").exists(),
                "{}",
                package.display()
            );
        }
    }

    fn no_manifests(&self) {
        for package in ["root", "left", "right", "right/vendor/shared library"] {
            assert!(!self.0.join(package).join("lake-manifest.json").exists());
        }
    }
}

fn reference() -> Option<(PathBuf, PathBuf)> {
    let lib = std::env::var_os("FLN_REFERENCE_LIB")
        .map(PathBuf::from)
        .or_else(|| {
            std::env::var_os("HOME").map(|home| {
                PathBuf::from(home)
                    .join(".elan/toolchains")
                    .join(format!("leanprover--lean4---{}", fln::OLEAN_PIN_TAG))
                    .join("lib/lean")
            })
        });
    let Some(lib) = lib.filter(|lib| lib.join("Init/System/IO.olean").is_file()) else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "pinned Reference required"
        );
        eprintln!("SKIP: pinned Reference absent; local dependency refusal controls still run");
        return None;
    };
    let lean = lib.join("../../bin/lean");
    let pin = Command::new(&lean).arg("--githash").output().unwrap();
    assert!(pin.status.success(), "{pin:?}");
    assert_eq!(
        String::from_utf8(pin.stdout).unwrap().trim(),
        fln::OLEAN_PIN_COMMIT
    );
    Some((lean.with_file_name("lake"), lib))
}

fn refusal(output: Output, class: &str, detail: &str) {
    assert_eq!(
        output.status.code(),
        Some(if class == "resource" { 3 } else { 1 }),
        "{output:?}"
    );
    assert!(output.stdout.is_empty(), "{output:?}");
    let error = std::str::from_utf8(&output.stderr).unwrap();
    assert!(error.contains(&format!("\"class\":\"{class}\"")), "{error}");
    assert!(error.contains("\"authority\":false"), "{error}");
    if class == "resource" {
        assert!(error.contains("\"status\":\"inconclusive\""), "{error}");
    }
    assert!(error.contains(detail), "{error}");
}

const ROOT: &str = concat!(
    "name = \"program\"\nsrcDir = \"src\"\nbuildDir = \"output\"\n",
    "[[require]]\nname = \"left\"\npath = \"../left\"\n",
    "[[require]]\nname = \"right\"\npath = \"../ignored-direct\"\n",
    "[[require]]\nname = \"right\"\npath = \"../right\"\n",
    "[[lean_exe]]\nname = \"runner\"\nroot = \"App.Main\"\nsrcDir = \"app\"\n",
);
const LEFT: &str = concat!(
    "name = \"left\"\nsrcDir = \"code\"\n",
    "[[require]]\nname = \"shared\"\npath = \"../ignored-transitive\"\n",
    "[[lean_lib]]\nname = \"Left\"\nroots = [\"Feature.Left\"]\nsrcDir = \"lib\"\n",
);
const RIGHT: &str = concat!(
    "name = \"name_overridden_by_requirement\"\n",
    "[[require]]\nname = \"shared\"\npath = \"vendor/shared library\"\n",
    "[[lean_lib]]\nname = \"Right\"\nroots = [\"Feature.Right\"]\n",
);
const SHARED: &str = concat!(
    "name = \"shared\"\nsrcDir = \"sources\"\n",
    "[[lean_lib]]\nname = \"Common\"\nroots = [\"Shared\"]\nsrcDir = \"lib\"\n",
);
const SHARED_SOURCE: &str = concat!(
    "prelude\nimport Init.System.IO\n",
    "def Shared.decorate (value : String) : String := \"chosen:\" ++ value\n",
);
const LEFT_SOURCE: &str = concat!(
    "prelude\nimport Shared\n",
    "def Feature.left (value : String) : String := \"left:\" ++ Shared.decorate value\n",
);
const RIGHT_SOURCE: &str = concat!(
    "prelude\nimport Shared\n",
    "def Feature.right (value : String) : String := \"right:\" ++ Shared.decorate value\n",
);
const MAIN: &str = concat!(
    "prelude\nimport Feature.Left\nimport Feature.Right\n",
    "def main (args : List String) : IO UInt32 := do\n",
    "  for value in args do\n",
    "    IO.println (Feature.left value)\n",
    "    IO.println (Feature.right value)\n",
    "  pure 17\n",
);

#[test]
fn transitive_diamond_and_name_precedence_match_the_pin() {
    let Some((lake, lib)) = reference() else {
        return;
    };
    let native = Workspace::new();
    let oracle = Workspace::new();
    let args = ["exe", "runner", "--help", "", "λ with spaces"];
    let expected = concat!(
        "left:chosen:--help\nright:chosen:--help\n",
        "left:chosen:\nright:chosen:\n",
        "left:chosen:λ with spaces\nright:chosen:λ with spaces\n",
    );
    let pinned = Command::new(&lake)
        .arg("--dir")
        .arg(oracle.0.join("root"))
        .args(args)
        .env("LEAN_PATH", &lib)
        .output()
        .unwrap();
    assert_eq!(pinned.status.code(), Some(17), "{pinned:?}");
    assert_eq!(
        std::str::from_utf8(&pinned.stdout).unwrap(),
        expected,
        "{pinned:?}"
    );

    eprintln!("[lake-local] pinned executable passed; admitting the native import world");
    let output = native.run(&args, Some(&lib));
    assert_eq!(output.status.code(), Some(17), "{output:?}");
    assert_eq!(output.stdout, pinned.stdout, "{output:?}");
    assert!(output.stderr.is_empty(), "{output:?}");
    native.no_products();
    native.no_manifests();

    eprintln!("[lake-local] native executable passed; checking a false dependency theorem");
    native.write(
        "right/vendor/shared library/sources/lib/Shared.lean",
        format!("{SHARED_SOURCE}theorem impossible (P Q : Prop) (h : P) : Q := h\n",),
    );
    let invalid = native.run(&args, Some(&lib));
    assert_eq!(invalid.status.code(), Some(1), "{invalid:?}");
    assert!(invalid.stdout.is_empty(), "{invalid:?}");
    let error = std::str::from_utf8(&invalid.stderr).unwrap();
    assert!(
        error.contains("Shared") && error.contains("NotDefEq"),
        "{error}"
    );
    eprintln!("[lake-local] false theorem refused; checking repaired dependency execution");
    native.write(
        "right/vendor/shared library/sources/lib/Shared.lean",
        SHARED_SOURCE,
    );
    let recovered = native.run(&["exec", "runner", "repaired"], Some(&lib));
    assert_eq!(recovered.status.code(), Some(17), "{recovered:?}");
    assert_eq!(
        std::str::from_utf8(&recovered.stdout).unwrap(),
        "left:chosen:repaired\nright:chosen:repaired\n"
    );
    assert!(recovered.stderr.is_empty(), "{recovered:?}");
    native.no_products();
    native.no_manifests();

    // Consume a real pin-written lock after the declared paths have changed.
    // Both implementations must keep the lock's root-relative package choices.
    let lock = std::fs::read(oracle.0.join("root/lake-manifest.json")).unwrap();
    for workspace in [&native, &oracle] {
        workspace.write(
            "root/lakefile.toml",
            ROOT.replace("path = \"../right\"", "path = \"../missing-after-lock\""),
        );
        workspace.write(
            "right/lakefile.toml",
            RIGHT.replace("vendor/shared library", "missing-after-lock"),
        );
    }
    native.write("root/lake-manifest.json", &lock);
    let pinned_locked = Command::new(&lake)
        .arg("--dir")
        .arg(oracle.0.join("root"))
        .args(args)
        .env("LEAN_PATH", &lib)
        .output()
        .unwrap();
    assert_eq!(pinned_locked.status.code(), Some(17), "{pinned_locked:?}");
    assert_eq!(pinned_locked.stdout, pinned.stdout, "{pinned_locked:?}");
    let native_locked = native.run(&args, Some(&lib));
    assert_eq!(native_locked.status.code(), Some(17), "{native_locked:?}");
    assert_eq!(
        native_locked.stdout, pinned_locked.stdout,
        "{native_locked:?}"
    );
    assert!(native_locked.stderr.is_empty(), "{native_locked:?}");
    assert_eq!(
        std::fs::read(native.0.join("root/lake-manifest.json")).unwrap(),
        lock,
    );
    native.no_products();
}

#[test]
fn package_cycles_are_refused_like_the_pinned_executable_build() {
    let native = Workspace::new();
    let cyclic = format!("{RIGHT}\n[[require]]\nname = \"program\"\npath = \"../root\"\n");
    native.write("right/lakefile.toml", &cyclic);
    refusal(
        native.run(&["--json", "exe", "runner"], None),
        "input",
        "dependency cycle",
    );
    assert!(!native.0.join("import-records").exists());
    native.no_products();
    native.no_manifests();
    if let Some((lake, lib)) = reference() {
        let oracle = Workspace::new();
        oracle.write("right/lakefile.toml", cyclic);
        let output = Command::new(lake)
            .arg("--dir")
            .arg(oracle.0.join("root"))
            .args(["exe", "runner"])
            .env("LEAN_PATH", lib)
            .output()
            .unwrap();
        assert_eq!(output.status.code(), Some(1), "{output:?}");
        assert!(
            std::str::from_utf8(&output.stderr)
                .unwrap()
                .contains("build cycle detected"),
            "{output:?}"
        );
    }
}

#[test]
fn unlocked_dependency_metadata_and_root_overrides_are_never_ignored() {
    for relative in [
        "right/lake-manifest.json",
        "root/.lake/package-overrides.json",
        "right/.lake/package-overrides.json",
    ] {
        let workspace = Workspace::new();
        workspace.write(relative, "pre-existing package selection\n");
        refusal(
            workspace.run(&["--json", "exe", "runner"], None),
            "unsupported",
            relative.split('/').next_back().unwrap(),
        );
        assert_eq!(
            std::fs::read_to_string(workspace.0.join(relative)).unwrap(),
            "pre-existing package selection\n"
        );
        assert!(!workspace.0.join("import-records").exists());
        workspace.no_products();
    }
    // Supported Lean configuration now takes precedence over TOML. A selected
    // unsupported command must still refuse before any imports or products.
    for relative in ["root/lakefile.lean", "right/lakefile.lean"] {
        let workspace = Workspace::new();
        let source = "import Lake\nopen Lake DSL\npackage selected\nscript unsupported := pure 0\n";
        workspace.write(relative, source);
        refusal(
            workspace.run(&["--json", "exe", "runner"], None),
            "unsupported",
            "script",
        );
        assert_eq!(
            std::fs::read_to_string(workspace.0.join(relative)).unwrap(),
            source
        );
        assert!(!workspace.0.join("import-records").exists());
        workspace.no_products();
    }
}

#[test]
fn declared_dependency_sources_remain_contained_and_owned() {
    let workspace = Workspace::new();
    workspace.write(
        "right/lakefile.toml",
        RIGHT.replace(
            "roots = [\"Feature.Right\"]",
            "roots = [\"Feature.Right\"]\nsrcDir = \"../left\"",
        ),
    );
    refusal(
        workspace.run(&["--json", "exe", "runner"], None),
        "unsupported",
        "must stay within the package",
    );
    workspace.write(
        "right/lakefile.toml",
        RIGHT.replace("Feature.Right", "Shared"),
    );
    refusal(
        workspace.run(&["--json", "exe", "runner"], None),
        "unsupported",
        "multiple local packages",
    );
    assert!(!workspace.0.join("import-records").exists());
    workspace.no_products();
    workspace.no_manifests();
}

#[test]
fn missing_dependency_and_unsupported_remote_sources_fail_before_execution() {
    let workspace = Workspace::new();
    workspace.write(
        "root/lakefile.toml",
        ROOT.replace("path = \"../right\"", "path = \"../missing\""),
    );
    refusal(
        workspace.run(&["--json", "exe", "runner"], None),
        "io",
        "missing",
    );
    workspace.write(
        "root/lakefile.toml",
        ROOT.replace(
            "path = \"../right\"",
            "git = \"https://example.invalid/right\"",
        ),
    );
    refusal(
        workspace.run(&["--json", "exe", "runner"], None),
        "unsupported",
        "require.git",
    );
    assert!(!workspace.0.join("import-records").exists());
    workspace.no_products();
    workspace.no_manifests();
}

#[test]
fn package_count_is_bounded_before_build_or_execution() {
    let workspace = Workspace::new();
    let mut config = String::from("name = \"program\"\n");
    for index in 0..64 {
        config.push_str(&format!(
            "[[require]]\nname = \"dep{index}\"\npath = \"../dep{index}\"\n"
        ));
        workspace.write(
            &format!("dep{index}/lakefile.toml"),
            format!("name = \"dep{index}\"\n"),
        );
    }
    config.push_str("[[lean_exe]]\nname = \"runner\"\nroot = \"Main\"\n");
    workspace.write("root/lakefile.toml", config);
    for arguments in [
        ["--json", "exe", "runner"],
        ["--json", "build", "+Feature.Left:olean"],
    ] {
        refusal(
            workspace.run(&arguments, None),
            "resource",
            "package count exceeds 64",
        );
    }
    assert!(!workspace.0.join("import-records").exists());
    workspace.no_products();
    workspace.no_manifests();
}

#[cfg(unix)]
#[test]
fn explicit_dependency_paths_do_not_hide_symlinks_before_parent_components() {
    let workspace = Workspace::new();
    std::os::unix::fs::symlink(workspace.0.join("right"), workspace.0.join("alias")).unwrap();
    workspace.write(
        "root/lakefile.toml",
        ROOT.replace("path = \"../right\"", "path = \"../alias/../right\""),
    );
    refusal(
        workspace.run(&["--json", "exe", "runner"], None),
        "input",
        "refusing symlink",
    );
    assert!(!workspace.0.join("import-records").exists());
    workspace.no_products();
    workspace.no_manifests();
}

const CHECKED_SHARED: &str = "prelude\ndef Shared.identity (A : Type) (a : A) : A := a\n";

fn artifact_workspace() -> Workspace {
    let workspace = Workspace::new();
    workspace.write(
        "root/lakefile.toml",
        format!("{ROOT}[[lean_lib]]\nname = \"Bundle\"\nroots = [\"App\"]\nsrcDir = \"lib\"\n"),
    );
    workspace.write(
        "right/lakefile.toml",
        format!("buildDir = \"products\"\n{RIGHT}"),
    );
    workspace.write(
        "root/src/lib/App/Top.lean",
        concat!(
            "prelude\nimport Feature.Left\nimport Feature.Right\n",
            "def App.combine (A : Type) (a : A) : A := Feature.left A (Feature.right A a)\n",
        ),
    );
    workspace.write(
        "left/code/lib/Feature/Left.lean",
        "prelude\nimport Shared\ndef Feature.left (A : Type) (a : A) : A := Shared.identity A a\n",
    );
    workspace.write(
        "right/Feature/Right.lean",
        "prelude\nimport Shared\ndef Feature.right (A : Type) (a : A) : A := Shared.identity A a\n",
    );
    workspace.write(
        "right/vendor/shared library/sources/lib/Shared.lean",
        CHECKED_SHARED,
    );
    workspace
}

fn artifact_paths(workspace: &Workspace) -> [PathBuf; 4] {
    [
        "root/output/lib/lean/App/Top.olean",
        "left/.lake/build/lib/lean/Feature/Left.olean",
        "right/products/lib/lean/Feature/Right.olean",
        "right/vendor/shared library/.lake/build/lib/lean/Shared.olean",
    ]
    .map(|path| workspace.0.join(path))
}

fn build_success(output: Output) -> String {
    assert!(output.status.success(), "{output:?}");
    assert!(output.stderr.is_empty(), "{output:?}");
    String::from_utf8(output.stdout).unwrap()
}

#[test]
fn artifact_builds_follow_transitive_package_ownership_and_reuse_checked_records() {
    let workspace = artifact_workspace();
    let report = build_success(workspace.run(&["--json", "build", "+App.Top:olean"], None));
    assert!(report.contains("\"modules_built\":4"), "{report}");
    let paths = artifact_paths(&workspace);
    let previous: Vec<_> = paths
        .iter()
        .map(|path| {
            assert!(report.contains(&path.display().to_string()), "{report}");
            let bytes = std::fs::read(path).unwrap();
            fln_olean::region::OleanView::parse(&bytes).unwrap();
            bytes
        })
        .collect();
    // The shared dependency belongs only to the reverse-BFS-selected package.
    assert!(!workspace.0.join("ignored-direct").exists());
    assert!(!workspace.0.join("ignored-transitive").exists());
    assert!(
        !workspace
            .0
            .join("root/output/lib/lean/Shared.olean")
            .exists()
    );
    assert!(
        !workspace
            .0
            .join("root/output/lib/lean/Feature/Left.olean")
            .exists()
    );
    let warm = build_success(workspace.run(&["--json", "build", "+App.Top:olean"], None));
    assert!(warm.contains("\"modules_cached\":4"), "{warm}");
    assert!(warm.contains("\"module_elaborations\":0"), "{warm}");
    for (path, before) in paths.iter().zip(previous) {
        assert_eq!(std::fs::read(path).unwrap(), before);
    }
    // A dependency module is also an explicit workspace target.
    let selected = build_success(workspace.run(&["--json", "build", "+Feature.Left:olean"], None));
    assert!(selected.contains("\"modules_built\":2"), "{selected}");
    workspace.no_manifests();
}

#[test]
fn rejected_dependency_source_cannot_replace_any_previous_package_artifact() {
    let workspace = artifact_workspace();
    build_success(workspace.run(&["--json", "build", "+App.Top:olean"], None));
    let paths = artifact_paths(&workspace);
    let previous: Vec<_> = paths
        .iter()
        .map(|path| std::fs::read(path).unwrap())
        .collect();
    workspace.write(
        "right/vendor/shared library/sources/lib/Shared.lean",
        "prelude\ndef Shared.identity (A : Type) (a : A) : A := A\n",
    );
    let rejected = workspace.run(&["--json", "build", "+App.Top:olean"], None);
    assert_eq!(rejected.status.code(), Some(1), "{rejected:?}");
    assert!(rejected.stdout.is_empty(), "{rejected:?}");
    for (path, before) in paths.iter().zip(&previous) {
        assert_eq!(&std::fs::read(path).unwrap(), before);
        assert!(
            !path
                .ancestors()
                .find(|ancestor| ancestor.ends_with("lib/lean"))
                .unwrap()
                .join(".fln-olean-build.lock")
                .exists()
        );
    }
    workspace.write(
        "right/vendor/shared library/sources/lib/Shared.lean",
        CHECKED_SHARED,
    );
    build_success(workspace.run(&["--json", "build", "+App.Top:olean"], None));
    for (path, before) in paths.iter().zip(previous) {
        assert_eq!(std::fs::read(path).unwrap(), before);
    }
}

#[test]
fn missing_declared_dependency_source_never_falls_back_to_stale_olean() {
    let workspace = artifact_workspace();
    build_success(workspace.run(&["--json", "build", "+App.Top:olean"], None));
    let paths = artifact_paths(&workspace);
    let previous: Vec<_> = paths
        .iter()
        .map(|path| std::fs::read(path).unwrap())
        .collect();
    workspace.write(
        "right/vendor/shared library/lakefile.toml",
        SHARED.replace("srcDir = \"sources\"", "srcDir = \"missing\""),
    );
    let external_shadow = workspace
        .0
        .join("right/vendor/shared library/.lake/build/lib/lean");
    let rejected = workspace.run(
        &["--json", "build", "+App.Top:olean"],
        Some(&external_shadow),
    );
    assert_eq!(rejected.status.code(), Some(1), "{rejected:?}");
    assert!(rejected.stdout.is_empty(), "{rejected:?}");
    assert!(
        std::str::from_utf8(&rejected.stderr)
            .unwrap()
            .contains("missing"),
        "{rejected:?}",
    );
    for (path, before) in paths.iter().zip(previous) {
        assert_eq!(std::fs::read(path).unwrap(), before);
    }
}

#[test]
fn same_source_path_cannot_silently_choose_between_two_package_owners() {
    let workspace = Workspace::new();
    workspace.write(
        "root/lakefile.toml",
        concat!(
            "name = \"root\"\nsrcDir = \"dep\"\n",
            "[[require]]\nname = \"dependency\"\npath = \"dep\"\n",
            "[[lean_lib]]\nname = \"Shared\"\n",
        ),
    );
    workspace.write(
        "root/dep/lakefile.toml",
        "name = \"dependency\"\n[[lean_lib]]\nname = \"Shared\"\n",
    );
    workspace.write("root/dep/Shared.lean", CHECKED_SHARED);
    refusal(
        workspace.run(&["--json", "build", "+Shared:olean"], None),
        "unsupported",
        "multiple local packages",
    );
    assert!(!workspace.0.join("root/.lake/build").exists());
    assert!(!workspace.0.join("root/dep/.lake/build").exists());
    assert!(!workspace.0.join("import-records").exists());
}

#[test]
fn ir_facets_publish_complete_module_families_across_local_packages() {
    let workspace = artifact_workspace();
    for (path, source) in [
        (
            "right/vendor/shared library/sources/lib/Shared.lean",
            "module\nprelude\npublic theorem Shared.keep (P : Prop) (h : P) : P := h\n",
        ),
        (
            "left/code/lib/Feature/Left.lean",
            "module\nprelude\npublic import Shared\npublic theorem Feature.left (P : Prop) (h : P) : P := Shared.keep P h\n",
        ),
        (
            "right/Feature/Right.lean",
            "module\nprelude\npublic import Shared\npublic theorem Feature.right (P : Prop) (h : P) : P := Shared.keep P h\n",
        ),
        (
            "root/src/lib/App/Top.lean",
            "module\nprelude\npublic import Feature.Left\npublic import Feature.Right\npublic theorem App.keep (P : Prop) (h : P) : P := Feature.left P (Feature.right P h)\n",
        ),
    ] {
        workspace.write(path, source);
    }
    let report = build_success(workspace.run(&["--json", "build", "+App.Top:ir"], None));
    assert!(report.contains("\"modules_built\":4"), "{report}");
    assert!(report.contains("\"executable_modules\":4"), "{report}");
    let paths = artifact_paths(&workspace);
    for path in &paths {
        for extension in ["olean", "olean.server", "olean.private", "ir"] {
            let part = path.with_extension(extension);
            assert!(report.contains(&part.display().to_string()), "{report}");
            let bytes = std::fs::read(&part).unwrap();
            fln_olean::region::OleanView::parse(&bytes).unwrap();
        }
    }
    workspace.write(
        "Consumer.lean",
        "prelude\nimport App.Top\ntheorem consumer (P : Prop) (h : P) : P := App.keep P h\n",
    );
    let lean_path = std::env::join_paths([
        workspace.0.join("root/output/lib/lean"),
        workspace.0.join("left/.lake/build/lib/lean"),
        workspace.0.join("right/products/lib/lean"),
        workspace
            .0
            .join("right/vendor/shared library/.lake/build/lib/lean"),
    ])
    .unwrap();
    let checked = Command::new(env!("CARGO_BIN_EXE_lean"))
        .arg(workspace.0.join("Consumer.lean"))
        .env("LEAN_PATH", lean_path)
        .env("FLN_IMPORT_REUSE_DIR", workspace.0.join("consumer-records"))
        .output()
        .unwrap();
    assert!(checked.status.success(), "{checked:?}");
    assert!(checked.stderr.is_empty(), "{checked:?}");
    workspace.no_manifests();
}

#[test]
fn dependency_library_targets_require_explicit_module_selection_for_olean() {
    let workspace = artifact_workspace();
    workspace.write(
        "right/vendor/shared library/lakefile.toml",
        SHARED.replace("name = \"Common\"", "name = \"Shared\""),
    );
    refusal(
        workspace.run(&["--json", "build", "Shared:olean"], None),
        "unsupported",
        "has no library or executable olean facet",
    );
    workspace.no_products();
    let report = build_success(workspace.run(&["--json", "build", "+Shared:olean"], None));
    assert!(report.contains("\"modules_built\":1"), "{report}");
    assert!(artifact_paths(&workspace)[3].is_file());
}

// Handwritten pin-schema data: it is intentionally not serialized by the
// manifest implementation under test. The earlier duplicate and unused remote
// row must not cause filesystem probes or network access.
const LOCKED_MANIFEST: &str = r#"{
  "version":"1.2.0",
  "name":"program",
  "lakeDir":".lake",
  "packagesDir":".lake/packages",
  "fixedToolchain":false,
  "packages":[
    {"type":"path","name":"right","dir":"../unselected-right","inherited":false,"configFile":"lakefile.toml"},
    {"type":"git","name":"unused","url":"https://example.invalid/unused","rev":"deadbeef","inherited":true},
    {"type":"path","name":"left","dir":"../left","inherited":false,"configFile":"lakefile.toml"},
    {"type":"path","name":"right","dir":"../right","inherited":false,"configFile":"lakefile.toml"},
    {"type":"path","name":"shared","dir":"../right/vendor/shared library","inherited":true,"configFile":"lakefile.toml"}
  ]
}
"#;

#[test]
fn root_manifest_locks_transitive_builds_and_checked_record_reuse() {
    let workspace = artifact_workspace();
    workspace.write("root/lake-manifest.json", LOCKED_MANIFEST);
    let configuration = std::fs::read_to_string(workspace.0.join("root/lakefile.toml")).unwrap();
    workspace.write(
        "root/lakefile.toml",
        configuration.replace("path = \"../right\"", "path = \"../missing-config-path\""),
    );
    workspace.write(
        "right/lakefile.toml",
        format!(
            "buildDir = \"products\"\n{}",
            RIGHT.replace("vendor/shared library", "missing-config-path"),
        ),
    );
    // Locked resolution follows the root table, not dependency-local locks or
    // overrides. An explicit configFile also wins over a sibling Lean file.
    for relative in [
        "right/lake-manifest.json",
        "right/.lake/package-overrides.json",
        "right/lakefile.lean",
    ] {
        workspace.write(relative, "unselected metadata\n");
    }
    let report = build_success(workspace.run(&["--json", "build", "+App.Top:olean"], None));
    assert!(report.contains("\"modules_built\":4"), "{report}");
    let paths = artifact_paths(&workspace);
    let original: Vec<_> = paths
        .iter()
        .map(|path| {
            assert!(report.contains(&path.display().to_string()), "{report}");
            let bytes = std::fs::read(path).unwrap();
            fln_olean::region::OleanView::parse(&bytes).unwrap();
            bytes
        })
        .collect();
    let snapshot =
        std::fs::read_to_string(workspace.0.join("root/output/fln-build.snapshot")).unwrap();
    assert!(
        snapshot
            .lines()
            .any(|line| line.starts_with("configuration\tlake-manifest.json\t")),
        "{snapshot}",
    );
    assert!(!snapshot.contains("right/lake-manifest.json"), "{snapshot}",);
    let warm = build_success(workspace.run(&["--json", "build", "+App.Top:olean"], None));
    assert!(warm.contains("\"modules_cached\":4"), "{warm}");
    assert!(warm.contains("\"module_elaborations\":0"), "{warm}");
    for (path, bytes) in paths.iter().zip(original) {
        assert_eq!(std::fs::read(path).unwrap(), bytes);
    }
    assert_eq!(
        std::fs::read_to_string(workspace.0.join("root/lake-manifest.json")).unwrap(),
        LOCKED_MANIFEST,
    );
    assert!(!workspace.0.join("unselected-right").exists());
    assert!(!workspace.0.join("missing-config-path").exists());
}

#[test]
fn locked_resolution_failures_preserve_every_published_artifact() {
    let workspace = artifact_workspace();
    workspace.write("root/lake-manifest.json", LOCKED_MANIFEST);
    build_success(workspace.run(&["--json", "build", "+App.Top:olean"], None));
    let paths = artifact_paths(&workspace);
    let original: Vec<_> = paths
        .iter()
        .map(|path| std::fs::read(path).unwrap())
        .collect();
    let snapshot = workspace.0.join("root/output/fln-build.snapshot");
    let snapshot_bytes = std::fs::read(&snapshot).unwrap();
    for (manifest, class, detail) in [
        ("{invalid".to_owned(), "input", "lake-manifest.json"),
        (
            LOCKED_MANIFEST.replace("\"name\":\"shared\"", "\"name\":\"unselected_shared\""),
            "input",
            "not in lake-manifest.json",
        ),
        (
            LOCKED_MANIFEST.replace(
                "\"dir\":\"../right/vendor/shared library\"",
                "\"dir\":\"../absent-locked-package\"",
            ),
            "io",
            "absent-locked-package",
        ),
        (
            LOCKED_MANIFEST.replace(
                "\"type\":\"path\",\"name\":\"shared\",\"dir\":\"../right/vendor/shared library\"",
                "\"type\":\"git\",\"name\":\"shared\",\"url\":\"https://example.invalid/shared\",\"rev\":\"deadbeef\"",
            ),
            "unsupported",
            "only local path dependencies",
        ),
        (
            LOCKED_MANIFEST.replace(
                "\"configFile\":\"lakefile.toml\"",
                "\"configFile\":\"custom.toml\"",
            ),
            "unsupported",
            "unsupported configuration",
        ),
    ] {
        workspace.write("root/lake-manifest.json", &manifest);
        refusal(
            workspace.run(&["--json", "build", "+App.Top:olean"], None),
            class,
            detail,
        );
        assert_eq!(
            std::fs::read_to_string(workspace.0.join("root/lake-manifest.json")).unwrap(),
            manifest,
        );
        assert_eq!(std::fs::read(&snapshot).unwrap(), snapshot_bytes);
        for (path, bytes) in paths.iter().zip(&original) {
            assert_eq!(&std::fs::read(path).unwrap(), bytes);
            assert!(
                !path
                    .ancestors()
                    .find(|ancestor| ancestor.ends_with("lib/lean"))
                    .unwrap()
                    .join(".fln-olean-build.lock")
                    .exists()
            );
        }
    }
    workspace.write("root/lake-manifest.json", LOCKED_MANIFEST);
    workspace.write(
        "right/vendor/shared library/sources/lib/Shared.lean",
        "prelude\ndef Shared.identity (A : Type) (a : A) : A := A\n",
    );
    let rejected = workspace.run(&["--json", "build", "+App.Top:olean"], None);
    assert_eq!(rejected.status.code(), Some(1), "{rejected:?}");
    assert!(rejected.stdout.is_empty(), "{rejected:?}");
    for (path, bytes) in paths.iter().zip(original) {
        assert_eq!(std::fs::read(path).unwrap(), bytes);
    }
    assert_eq!(std::fs::read(&snapshot).unwrap(), snapshot_bytes);
}

#[test]
fn extensionless_locked_configurations_keep_lean_before_toml_precedence() {
    let workspace = artifact_workspace();
    let manifest = LOCKED_MANIFEST.replace(",\"configFile\":\"lakefile.toml\"", "");
    workspace.write("root/lake-manifest.json", &manifest);
    let report = build_success(workspace.run(&["--json", "build", "+App.Top:olean"], None));
    assert!(report.contains("\"modules_built\":4"), "{report}");
    let paths = artifact_paths(&workspace);
    let original: Vec<_> = paths
        .iter()
        .map(|path| std::fs::read(path).unwrap())
        .collect();
    workspace.write(
        "right/lakefile.lean",
        "import Lake\nopen Lake DSL\npackage right\nscript unsupported := pure 0\n",
    );
    refusal(
        workspace.run(&["--json", "build", "+App.Top:olean"], None),
        "unsupported",
        "lakefile.lean",
    );
    for (path, bytes) in paths.iter().zip(original) {
        assert_eq!(std::fs::read(path).unwrap(), bytes);
    }
    // Selecting TOML explicitly is different from choosing the default.
    workspace.write("root/lake-manifest.json", LOCKED_MANIFEST);
    build_success(workspace.run(&["--json", "build", "+App.Top:olean"], None));
}

#[test]
fn locked_package_cycles_are_refused_before_source_admission() {
    let workspace = artifact_workspace();
    workspace.write("root/lake-manifest.json", LOCKED_MANIFEST);
    workspace.write(
        "right/lakefile.toml",
        format!("{RIGHT}\n[[require]]\nname = \"program\"\npath = \"../ignored\"\n"),
    );
    refusal(
        workspace.run(&["--json", "build", "+App.Top:olean"], None),
        "input",
        "dependency cycle",
    );
    assert!(!workspace.0.join("import-records").exists());
    workspace.no_products();
}

#[cfg(unix)]
#[test]
fn manifest_selected_paths_cannot_hide_symlinks_before_parent_components() {
    let workspace = artifact_workspace();
    std::os::unix::fs::symlink(workspace.0.join("right"), workspace.0.join("alias")).unwrap();
    workspace.write(
        "root/lake-manifest.json",
        LOCKED_MANIFEST.replace("\"dir\":\"../right\"", "\"dir\":\"../alias/../right\""),
    );
    refusal(
        workspace.run(&["--json", "build", "+App.Top:olean"], None),
        "input",
        "refusing symlink",
    );
    assert!(!workspace.0.join("import-records").exists());
    workspace.no_products();
}

#[test]
fn root_manifest_changes_invalidate_build_explanations_without_publishing() {
    let workspace = artifact_workspace();
    workspace.write("root/lake-manifest.json", LOCKED_MANIFEST);
    build_success(workspace.run(&["--json", "build", "+App.Top:olean"], None));
    let original = artifact_paths(&workspace).map(|path| std::fs::read(path).unwrap());
    workspace.write("root/lake-manifest.json", format!("{LOCKED_MANIFEST}\n"));
    let output = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["build", "explain", "--json", "--dir"])
        .arg(workspace.0.join("root"))
        .env("LEAN_PATH", workspace.0.join("absent-imports"))
        .env("FLN_IMPORT_REUSE_DIR", workspace.0.join("import-records"))
        .output()
        .unwrap();
    assert!(output.status.success(), "{output:?}");
    assert!(output.stderr.is_empty(), "{output:?}");
    let report = String::from_utf8(output.stdout).unwrap();
    assert!(
        report.contains("\"reference_decision\":\"rebuild\""),
        "{report}"
    );
    assert!(report.contains("lake-manifest.json"), "{report}");
    assert!(report.contains("configuration"), "{report}");
    for (path, bytes) in artifact_paths(&workspace).into_iter().zip(original) {
        assert_eq!(std::fs::read(path).unwrap(), bytes);
    }
}

#[test]
fn malformed_root_manifest_is_rejected_even_without_requirements() {
    let workspace = artifact_workspace();
    workspace.write(
        "root/lakefile.toml",
        "name = \"root\"\n[[lean_lib]]\nname = \"App\"\n",
    );
    workspace.write("root/lake-manifest.json", "{\"packages\":[]");
    refusal(
        workspace.run(&["--json", "build", "+App.Top:olean"], None),
        "input",
        "lake-manifest.json",
    );
    assert!(!workspace.0.join("import-records").exists());
    workspace.no_products();
}

#[test]
fn manifest_identities_match_hyphenated_toml_names_and_quoted_duplicates() {
    let workspace = artifact_workspace();
    let configuration = std::fs::read_to_string(workspace.0.join("root/lakefile.toml")).unwrap();
    workspace.write(
        "root/lakefile.toml",
        configuration.replace("name = \"left\"", "name = \"left-package\""),
    );
    let manifest = LOCKED_MANIFEST
        .replace("\"name\":\"left\"", "\"name\":\"«left-package»\"")
        .replace(
            "\"name\":\"right\",\"dir\":\"../right\"",
            "\"name\":\"«right»\",\"dir\":\"../right\"",
        );
    workspace.write("root/lake-manifest.json", &manifest);
    let report = build_success(workspace.run(&["--json", "build", "+App.Top:olean"], None));
    assert!(report.contains("\"modules_built\":4"), "{report}");
    for path in artifact_paths(&workspace) {
        fln_olean::region::OleanView::parse(&std::fs::read(path).unwrap()).unwrap();
    }
    assert_eq!(
        std::fs::read_to_string(workspace.0.join("root/lake-manifest.json")).unwrap(),
        manifest,
    );
    assert!(!workspace.0.join("unselected-right").exists());
}

#[test]
fn quoted_self_requirements_share_the_roots_canonical_package_identity() {
    let workspace = artifact_workspace();
    let configuration = std::fs::read_to_string(workspace.0.join("root/lakefile.toml")).unwrap();
    workspace.write(
        "root/lakefile.toml",
        configuration.replace("name = \"program\"", "name = \"root-package\""),
    );
    workspace.write("root/lake-manifest.json", LOCKED_MANIFEST);
    workspace.write(
        "right/lakefile.toml",
        format!("{RIGHT}\n[[require]]\nname = \"«root-package»\"\npath = \"../ignored\"\n",),
    );
    refusal(
        workspace.run(&["--json", "build", "+App.Top:olean"], None),
        "input",
        "dependency cycle",
    );
    assert!(!workspace.0.join("import-records").exists());
    workspace.no_products();
}

#[test]
fn local_update_publishes_a_lock_for_checked_builds_and_preserves_it_on_refusal() {
    let workspace = artifact_workspace();
    let configuration = std::fs::read_to_string(workspace.0.join("root/lakefile.toml")).unwrap();
    let report = build_success(workspace.run(&["--json", "update"], None));
    assert!(
        report.contains("\"schema\":\"fln.lake-update/1\""),
        "{report}"
    );
    assert!(report.contains("\"packages_count\":3"), "{report}");
    let manifest_path = workspace.0.join("root/lake-manifest.json");
    let manifest = std::fs::read(&manifest_path).unwrap();
    for package in ["left", "right", "right/vendor/shared library"] {
        assert!(
            !workspace
                .0
                .join(package)
                .join("lake-manifest.json")
                .exists()
        );
    }
    workspace.no_products();
    let upgraded = build_success(workspace.run(&["--json", "upgrade"], None));
    assert!(upgraded.contains("\"packages_count\":3"), "{upgraded}");
    assert_eq!(std::fs::read(&manifest_path).unwrap(), manifest);

    let built = build_success(workspace.run(&["--json", "build", "+App.Top:olean"], None));
    assert!(built.contains("\"modules_built\":4"), "{built}");
    let paths = artifact_paths(&workspace);
    let original: Vec<_> = paths
        .iter()
        .map(|path| {
            let bytes = std::fs::read(path).unwrap();
            fln_olean::region::OleanView::parse(&bytes).unwrap();
            bytes
        })
        .collect();
    let warm = build_success(workspace.run(&["--json", "build", "+App.Top:olean"], None));
    assert!(warm.contains("\"modules_cached\":4"), "{warm}");
    assert!(warm.contains("\"module_elaborations\":0"), "{warm}");
    let snapshot = workspace.0.join("root/output/fln-build.snapshot");
    let snapshot_bytes = std::fs::read(&snapshot).unwrap();
    let unchanged = || {
        assert_eq!(std::fs::read(&manifest_path).unwrap(), manifest);
        assert_eq!(std::fs::read(&snapshot).unwrap(), snapshot_bytes);
        for (path, before) in paths.iter().zip(&original) {
            assert_eq!(&std::fs::read(path).unwrap(), before);
        }
        for package in ["left", "right", "right/vendor/shared library"] {
            assert!(
                !workspace
                    .0
                    .join(package)
                    .join("lake-manifest.json")
                    .exists()
            );
        }
    };

    // Selective refreshes and unimplemented flags must fail before resolution.
    for arguments in [
        ["--json", "update", "right"],
        ["--json", "upgrade", "--wfail"],
    ] {
        let output = workspace.run(&arguments, None);
        assert_eq!(output.status.code(), Some(5), "{output:?}");
        assert!(output.stdout.is_empty(), "{output:?}");
        let error = std::str::from_utf8(&output.stderr).unwrap();
        assert!(error.contains("\"status\":\"not_implemented\""), "{error}");
        unchanged();
    }

    workspace.write(
        "root/lakefile.toml",
        configuration.replace("path = \"../right\"", "path = \"../missing\\\"dependency\""),
    );
    let missing = workspace.run(&["--json", "update"], None);
    assert_eq!(missing.status.code(), Some(1), "{missing:?}");
    assert!(missing.stdout.is_empty(), "{missing:?}");
    let error = std::str::from_utf8(&missing.stderr).unwrap();
    assert!(error.contains("\"status\":\"error\""), "{error}");
    assert!(error.contains("missing\\\"dependency"), "{error}");
    assert_eq!(error.lines().count(), 1, "{error}");
    unchanged();

    workspace.write(
        "root/lakefile.toml",
        format!("{configuration}#{}\n", "x".repeat(1024 * 1024)),
    );
    refusal(
        workspace.run(&["--json", "update"], None),
        "resource",
        "fln.lake-update/1",
    );
    unchanged();

    workspace.write(
        "root/lakefile.toml",
        configuration.replace(
            "path = \"../right\"",
            "git = \"https://example.invalid/never-fetch.git\"",
        ),
    );
    let remote = workspace.run(&["--json", "update"], None);
    assert_eq!(remote.status.code(), Some(5), "{remote:?}");
    assert!(remote.stdout.is_empty(), "{remote:?}");
    assert!(
        std::str::from_utf8(&remote.stderr)
            .unwrap()
            .contains("\"status\":\"not_implemented\""),
        "{remote:?}",
    );
    unchanged();

    workspace.write("root/lakefile.toml", &configuration);
    workspace.write(
        "root/lakefile.lean",
        "import Lake\nopen Lake DSL\npackage program\nscript unsupported := pure 0\n",
    );
    refusal(
        workspace.run(&["--json", "upgrade"], None),
        "unsupported",
        "script",
    );
    unchanged();
}

#[test]
fn local_update_lock_drives_the_installed_native_executable() {
    let Some((_, lib)) = reference() else {
        return;
    };
    let workspace = Workspace::new();
    let report = build_success(workspace.run(&["--json", "update"], None));
    assert!(report.contains("\"packages_count\":3"), "{report}");
    let manifest_path = workspace.0.join("root/lake-manifest.json");
    let manifest = std::fs::read(&manifest_path).unwrap();
    let output = workspace.run(&["exe", "runner", "updated"], Some(&lib));
    assert_eq!(output.status.code(), Some(17), "{output:?}");
    assert_eq!(
        std::str::from_utf8(&output.stdout).unwrap(),
        "left:chosen:updated\nright:chosen:updated\n",
    );
    assert!(output.stderr.is_empty(), "{output:?}");
    assert_eq!(std::fs::read(manifest_path).unwrap(), manifest);
    workspace.no_products();
}

const MIXED_ROOT: &str = r#"import Lake
open System Lake DSL
def sibling (suffix : String) : FilePath := FilePath.mk ("../" ++ suffix)
package program where
  srcDir := FilePath.mk "src"
  buildDir := FilePath.mk "output"
require left from sibling "left"
lean_lib Bundle where
  roots := #[Lean.Name.str Lean.Name.anonymous "App"]
  srcDir := FilePath.mk "lib"
lean_exe runner where
  root := Lean.Name.str (Lean.Name.str Lean.Name.anonymous "App") "Main"
  srcDir := FilePath.mk "app"
"#;

const MIXED_LEFT: &str = r#"import Lake
open System Lake DSL
def dependency (suffix : String) : FilePath := FilePath.mk ("../right/vendor/" ++ suffix)
package declaredLeftName where
  srcDir := FilePath.mk ("co" ++ "de")
require shared from dependency "shared library"
lean_lib Left where
  roots := #[Lean.Name.str (Lean.Name.str Lean.Name.anonymous "Feature") "Left"]
  srcDir := FilePath.mk "lib"
"#;

fn mixed_configuration_workspace() -> Workspace {
    let mut workspace = artifact_workspace();
    // Reuse records attest the running checker's exact bytes. Keep the
    // installed executable fixed across this multi-command test even when a
    // concurrent development build replaces Cargo's binary in between calls.
    let binary = workspace.0.join("native-bin/lake");
    std::fs::create_dir_all(binary.parent().unwrap()).unwrap();
    std::fs::copy(env!("CARGO_BIN_EXE_lake"), &binary).unwrap();
    workspace.1 = Some(binary);
    // Both formats exist. The Lean files select a three-package graph; the
    // TOML files deliberately describe the different original diamond.
    workspace.write("root/lakefile.lean", MIXED_ROOT);
    workspace.write("left/lakefile.lean", MIXED_LEFT);
    workspace.write(
        "root/src/lib/App/Top.lean",
        "prelude\nimport Feature.Left\ndef App.combine (A : Type) (a : A) : A := Feature.left A a\n",
    );
    workspace
}

#[test]
fn checked_lean_path_dependencies_build_update_and_match_the_pinned_resolver() {
    let Some((lake, lib)) = reference() else {
        return;
    };
    let workspace = mixed_configuration_workspace();
    let report = build_success(workspace.run(&["--json", "build", "+App.Top:olean"], Some(&lib)));
    assert!(report.contains("\"modules_built\":3"), "{report}");
    assert_eq!(
        report.matches("\"trust\":\"reuse-verified\"").count(),
        2,
        "{report}"
    );
    let all_paths = artifact_paths(&workspace);
    let paths = [&all_paths[0], &all_paths[1], &all_paths[3]];
    let original: Vec<_> = paths
        .iter()
        .map(|path| {
            let bytes = std::fs::read(path).unwrap();
            fln_olean::region::OleanView::parse(&bytes).unwrap();
            bytes
        })
        .collect();
    assert!(!all_paths[2].exists());
    workspace.no_manifests();
    let snapshot = workspace.0.join("root/output/fln-build.snapshot");
    let snapshot_text = std::fs::read_to_string(&snapshot).unwrap();
    assert!(snapshot_text.contains("lakefile.lean"), "{snapshot_text}");
    assert!(
        snapshot_text.contains("left/lakefile.lean"),
        "{snapshot_text}"
    );
    assert!(
        snapshot_text.contains("shared library/lakefile.toml"),
        "{snapshot_text}"
    );
    assert_eq!(
        snapshot_text
            .lines()
            .filter(|line| line.starts_with("configuration\t"))
            .count(),
        3
    );

    let warm = build_success(workspace.run(&["--json", "build", "+App.Top:olean"], Some(&lib)));
    assert!(warm.contains("\"modules_cached\":3"), "{warm}");
    assert!(warm.contains("\"module_elaborations\":0"), "{warm}");

    // No configuration is executed by build explain, including transitive
    // Lean configuration. It must not pretend a recorded graph is current.
    let explained = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["build", "explain", "--json", "--dir"])
        .arg(workspace.0.join("root"))
        .env("LEAN_PATH", workspace.0.join("absent-imports"))
        .output()
        .unwrap();
    assert!(!explained.status.success(), "{explained:?}");
    assert!(
        String::from_utf8_lossy(&explained.stderr).contains("does not elaborate or execute"),
        "{explained:?}"
    );

    let updated = build_success(workspace.run(&["--json", "update"], Some(&lib)));
    assert!(updated.contains("\"packages_count\":2"), "{updated}");
    assert_eq!(
        updated.matches("\"admission\":\"reused\"").count(),
        2,
        "{updated}"
    );
    let manifest_path = workspace.0.join("root/lake-manifest.json");
    let native_bytes = std::fs::read(&manifest_path).unwrap();
    let native =
        fln_lake::Manifest::parse_json(std::str::from_utf8(&native_bytes).unwrap()).unwrap();
    assert_eq!(native.packages[0].name, "left");
    assert_eq!(native.packages[0].config_file, "lakefile.lean");
    assert_eq!(native.packages[1].name, "shared");
    assert_eq!(native.packages[1].config_file, "lakefile.toml");

    // The pin evaluates the same computed paths. Compare resolved identities
    // and directories, allowing its textual relative-path normalization.
    let pinned = Command::new(&lake)
        .args(["--dir"])
        .arg(workspace.0.join("root"))
        .arg("update")
        .env_remove("LEAN_PATH")
        .output()
        .unwrap();
    assert!(pinned.status.success(), "{pinned:?}");
    let pinned_manifest =
        fln_lake::Manifest::parse_json(&std::fs::read_to_string(&manifest_path).unwrap()).unwrap();
    assert_eq!(native.name, pinned_manifest.name);
    assert_eq!(native.packages.len(), pinned_manifest.packages.len());
    for (actual, expected) in native.packages.iter().zip(&pinned_manifest.packages) {
        assert_eq!(actual.name, expected.name);
        assert_eq!(actual.entry_type, expected.entry_type);
        assert_eq!(actual.config_file, expected.config_file);
        assert_eq!(actual.inherited, expected.inherited);
        let resolve = |entry: &fln_lake::ManifestPackageEntry| {
            workspace
                .0
                .join("root")
                .join(entry.dir.as_ref().unwrap())
                .canonicalize()
                .unwrap()
        };
        assert_eq!(resolve(actual), resolve(expected));
    }
    std::fs::write(&manifest_path, &native_bytes).unwrap();
    let locked = build_success(workspace.run(&["--json", "build", "+App.Top:olean"], Some(&lib)));
    assert!(locked.contains("\"modules_cached\":3"), "{locked}");

    // Consume the native logical artifacts in the actual pin.
    workspace.write(
        "UseMixed.lean",
        "prelude\nimport App.Top\ndef useMixed (A : Type) (a : A) : A := App.combine A a\n",
    );
    let search = std::env::join_paths(paths.iter().map(|path| {
        path.ancestors()
            .find(|parent| parent.ends_with("lib/lean"))
            .unwrap()
    }))
    .unwrap();
    let consumer = Command::new(lake.with_file_name("lean"))
        .arg(workspace.0.join("UseMixed.lean"))
        .env("LEAN_PATH", search)
        .output()
        .unwrap();
    assert!(consumer.status.success(), "{consumer:?}");

    // Rejected dependency proofs and invalid computed paths cannot replace
    // any previously published family or the last complete root manifest.
    let good_snapshot = std::fs::read(&snapshot).unwrap();
    workspace.write(
        "right/vendor/shared library/sources/lib/Shared.lean",
        "prelude\ntheorem invalid (p q : Prop) (hp : p) : q := hp\n",
    );
    let rejected = workspace.run(&["--json", "build", "+App.Top:olean"], Some(&lib));
    assert_eq!(rejected.status.code(), Some(1), "{rejected:?}");
    assert!(rejected.stdout.is_empty(), "{rejected:?}");
    for (path, bytes) in paths.iter().zip(&original) {
        assert_eq!(std::fs::read(path).unwrap(), *bytes);
    }
    assert_eq!(std::fs::read(&manifest_path).unwrap(), native_bytes);
    assert_eq!(std::fs::read(&snapshot).unwrap(), good_snapshot);
    workspace.write(
        "right/vendor/shared library/sources/lib/Shared.lean",
        CHECKED_SHARED,
    );
    workspace.write(
        "root/lakefile.lean",
        MIXED_ROOT.replace("sibling \"left\"", "sibling \"missing\""),
    );
    // A root lock continues to select its recorded directory for builds.
    build_success(workspace.run(&["--json", "build", "+App.Top:olean"], Some(&lib)));
    // An update resolves the new requirement and refuses its absent directory.
    let missing = workspace.run(&["--json", "update"], Some(&lib));
    assert_eq!(missing.status.code(), Some(1), "{missing:?}");
    assert_eq!(std::fs::read(&manifest_path).unwrap(), native_bytes);
    for (path, bytes) in paths.iter().zip(&original) {
        assert_eq!(std::fs::read(path).unwrap(), *bytes);
    }
}

#[test]
fn checked_lean_path_dependencies_execute_the_selected_program() {
    let Some((_, lib)) = reference() else {
        return;
    };
    let workspace = mixed_configuration_workspace();
    workspace.write(
        "right/vendor/shared library/sources/lib/Shared.lean",
        SHARED_SOURCE,
    );
    workspace.write("left/code/lib/Feature/Left.lean", LEFT_SOURCE);
    workspace.write(
        "root/src/app/App/Main.lean",
        concat!(
            "prelude\nimport Feature.Left\n",
            "def main (args : List String) : IO UInt32 := do\n",
            "  for value in args do\n",
            "    IO.println (Feature.left value)\n",
            "  pure 17\n",
        ),
    );
    let updated = build_success(workspace.run(&["--json", "update"], Some(&lib)));
    assert!(updated.contains("\"packages_count\":2"), "{updated}");
    let output = workspace.run(&["exe", "runner", "mixed"], Some(&lib));
    assert_eq!(output.status.code(), Some(17), "{output:?}");
    assert_eq!(
        std::str::from_utf8(&output.stdout).unwrap(),
        "left:chosen:mixed\n"
    );
    assert!(output.stderr.is_empty(), "{output:?}");
    workspace.no_products();
}
