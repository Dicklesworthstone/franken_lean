//! Installed native execution across explicitly declared local Lake packages.
#![forbid(unsafe_code)]

use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::{SystemTime, UNIX_EPOCH};

static NEXT: AtomicUsize = AtomicUsize::new(0);

struct Workspace(PathBuf);

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
        let workspace = Self(path);
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
        Command::new(env!("CARGO_BIN_EXE_lake"))
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
        format!("{SHARED_SOURCE}theorem impossible : Bool.true = Bool.false := rfl\n",),
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
fn manifests_overrides_and_lean_configurations_are_never_ignored() {
    for relative in [
        "root/lake-manifest.json",
        "right/lake-manifest.json",
        "root/.lake/package-overrides.json",
        "right/.lake/package-overrides.json",
        "root/lakefile.lean",
        "right/lakefile.lean",
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

const CHECKED_SHARED: &str =
    "prelude\ndef Shared.identity (A : Type) (a : A) : A := a\n";

fn artifact_workspace() -> Workspace {
    let workspace = Workspace::new();
    workspace.write(
        "root/lakefile.toml",
        format!(
            "{ROOT}[[lean_lib]]\nname = \"Bundle\"\nroots = [\"App\"]\nsrcDir = \"lib\"\n"
        ),
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
    assert!(!workspace.0.join("root/output/lib/lean/Shared.olean").exists());
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
    let selected = build_success(workspace.run(
        &["--json", "build", "+Feature.Left:olean"],
        None,
    ));
    assert!(selected.contains("\"modules_built\":2"), "{selected}");
    workspace.no_manifests();
}

#[test]
fn rejected_dependency_source_cannot_replace_any_previous_package_artifact() {
    let workspace = artifact_workspace();
    build_success(workspace.run(&["--json", "build", "+App.Top:olean"], None));
    let paths = artifact_paths(&workspace);
    let previous: Vec<_> = paths.iter().map(|path| std::fs::read(path).unwrap()).collect();
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
    let previous: Vec<_> = paths.iter().map(|path| std::fs::read(path).unwrap()).collect();
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
