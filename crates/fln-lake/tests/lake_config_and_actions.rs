//! Unit and integration tests for fln-lake configuration discovery, TOML parsing,
//! package initialization, and clean operations.

#![forbid(unsafe_code)]

use fln_lake::{
    LakeCleanError, LakeConfig, LakeConfigFormat, LakeInitError, LakeParseError, clean,
    init_package, new_package, validate_package_name,
};
use std::path::PathBuf;

fn fresh_temp_dir(label: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!(
        "fln-lake-test-{label}-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos()
    ));
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

#[test]
fn test_parse_valid_lakefile_toml() {
    let toml = r#"
# Lakefile configuration
name = "geometry_suite"
version = "0.1.0"
defaultTargets = ["geometry_suite", "tests"]
srcDir = "src"
buildDir = ".lake/build"

[[lean_lib]]
name = "GeometrySuite"

[[lean_exe]]
name = "geometry_suite"
root = "Main"

[[require]]
name = "batteries"
git = "https://github.com/leanprover-community/batteries.git"
rev = "v4.32.0"

[[require]]
name = "mathlib"
url = "https://github.com/leanprover-community/mathlib4.git"
rev = "v4.32.0"
subdir = "sub"
"#;

    let config = LakeConfig::parse_toml(toml).expect("parse valid toml");
    assert_eq!(config.name, "geometry_suite");
    assert_eq!(config.default_targets, vec!["geometry_suite", "tests"]);
    assert_eq!(config.src_dir, PathBuf::from("src"));
    assert_eq!(config.build_dir, PathBuf::from(".lake/build"));
    assert_eq!(config.format, LakeConfigFormat::Toml);
    assert_eq!(config.requires.len(), 2);

    assert_eq!(config.requires[0].name, "batteries");
    assert_eq!(
        config.requires[0].url.as_deref(),
        Some("https://github.com/leanprover-community/batteries.git")
    );
    assert_eq!(config.requires[0].rev.as_deref(), Some("v4.32.0"));
    assert_eq!(config.requires[0].subdir, None);

    assert_eq!(config.requires[1].name, "mathlib");
    assert_eq!(
        config.requires[1].url.as_deref(),
        Some("https://github.com/leanprover-community/mathlib4.git")
    );
    assert_eq!(config.requires[1].rev.as_deref(), Some("v4.32.0"));
    assert_eq!(config.requires[1].subdir.as_deref(), Some("sub"));
}

#[test]
fn test_parse_toml_missing_name_fails() {
    let toml = r#"
version = "0.1.0"
defaultTargets = ["foo"]
"#;
    let err = LakeConfig::parse_toml(toml).unwrap_err();
    assert_eq!(err, LakeParseError::MissingField("name"));
}

#[test]
fn test_validate_package_names() {
    assert!(validate_package_name("my_project").is_ok());
    assert!(validate_package_name("MyProject").is_ok());
    assert!(validate_package_name("project-1").is_ok());

    assert!(matches!(
        validate_package_name(""),
        Err(LakeInitError::IllegalName(_))
    ));
    assert!(matches!(
        validate_package_name("."),
        Err(LakeInitError::IllegalName(_))
    ));
    assert!(matches!(
        validate_package_name(".."),
        Err(LakeInitError::IllegalName(_))
    ));
    assert!(matches!(
        validate_package_name("foo/bar"),
        Err(LakeInitError::IllegalName(_))
    ));
    assert!(matches!(
        validate_package_name("foo\\bar"),
        Err(LakeInitError::IllegalName(_))
    ));

    // Reserved identifiers
    for reserved in [
        "init", "lean", "lake", "main", "Init", "LEAN", "Lake", "MAIN",
    ] {
        assert!(matches!(
            validate_package_name(reserved),
            Err(LakeInitError::ReservedName(_))
        ));
    }
}

#[test]
fn test_init_and_discover_package() {
    let dir = fresh_temp_dir("init-pkg");
    init_package(&dir, "algebra_lib", None, LakeConfigFormat::Toml).expect("init package");

    // Check files created
    assert!(dir.join("lean-toolchain").exists());
    assert!(dir.join(".gitignore").exists());
    assert!(dir.join("lakefile.toml").exists());
    assert!(dir.join("Main.lean").exists());
    assert!(dir.join("AlgebraLib.lean").exists());
    assert!(dir.join("README.md").exists());

    let toolchain = std::fs::read_to_string(dir.join("lean-toolchain")).unwrap();
    assert!(toolchain.contains("v4.32.0"));

    let gitignore = std::fs::read_to_string(dir.join(".gitignore")).unwrap();
    assert_eq!(gitignore, "/.lake\n");

    let main_lean = std::fs::read_to_string(dir.join("Main.lean")).unwrap();
    assert!(main_lean.contains("import AlgebraLib"));

    // Discover
    let discovered = LakeConfig::discover(&dir).expect("discover config");
    assert_eq!(discovered.name, "algebra_lib");
    assert_eq!(discovered.default_targets, vec!["algebra_lib"]);
    assert_eq!(
        discovered.lean_toolchain.as_deref(),
        Some("leanprover/lean4:v4.32.0")
    );
    assert_eq!(discovered.format, LakeConfigFormat::Toml);
}

#[test]
fn test_new_package_and_clean() {
    let parent = fresh_temp_dir("new-parent");
    let pkg_dir =
        new_package(&parent, "calc_app", None, LakeConfigFormat::Toml).expect("create new package");
    assert_eq!(pkg_dir, parent.join("calc_app"));
    assert!(pkg_dir.join("lakefile.toml").exists());

    // Creating again with same name fails with AlreadyExists
    let err = new_package(&parent, "calc_app", None, LakeConfigFormat::Toml).unwrap_err();
    assert!(matches!(err, LakeInitError::AlreadyExists(_)));

    // Create .lake/build
    let build_dir = pkg_dir.join(".lake").join("build");
    std::fs::create_dir_all(&build_dir).unwrap();
    std::fs::write(build_dir.join("artifact.o"), b"bytes").unwrap();
    assert!(build_dir.exists());

    // Clean
    let report = clean(&pkg_dir).expect("clean package");
    assert!(report.build_dir_removed);
    assert!(!build_dir.exists());

    // Clean when no config file returns NoConfigFile
    let empty_dir = fresh_temp_dir("empty");
    let clean_err = clean(&empty_dir).unwrap_err();
    assert!(matches!(clean_err, LakeCleanError::NoConfigFile(_)));
}

#[test]
fn test_manifest_serialization_and_update() {
    let dir = fresh_temp_dir("manifest-test");
    let toml = r#"
name = "math_project"
version = "0.1.0"
defaultTargets = ["math_project"]

[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4.git"
rev = "v4.32.0"
"#;
    std::fs::write(dir.join("lakefile.toml"), toml).unwrap();

    // A requirement can only be resolved by fetching it. Nothing fetches, so
    // `update_manifest` must refuse and write nothing. It used to copy the
    // requested `rev` ("v4.32.0", a tag) into the resolved `rev` and return Ok
    // (bead fln-front-door-residuals-0f6x); this test asserted that.
    match fln_lake::update_manifest(&dir) {
        Err(fln_lake::LakeUpdateError::DependencyResolutionUnavailable { requirements }) => {
            assert_eq!(requirements, vec!["mathlib".to_owned()]);
        }
        other => panic!("a requirement must be refused, not resolved by copy: {other:?}"),
    }
    assert!(
        !dir.join("lake-manifest.json").exists(),
        "a refused update must not leave a manifest behind"
    );

    // With no requirements there is nothing to resolve, and the manifest is real.
    let bare = fresh_temp_dir("manifest-bare-test");
    std::fs::write(
        bare.join("lakefile.toml"),
        "name = \"math_project\"\nversion = \"0.1.0\"\n",
    )
    .unwrap();
    let manifest = fln_lake::update_manifest(&bare).expect("update with no requirements");
    assert_eq!(manifest.name, "math_project");
    assert_eq!(manifest.version, "1.1.0");
    assert!(manifest.packages.is_empty());
    let loaded = fln_lake::Manifest::load_from_dir(&bare)
        .expect("load manifest")
        .expect("manifest exists");
    assert_eq!(loaded.name, "math_project");
    assert!(loaded.packages.is_empty());

    // Serialization of a resolved entry is still covered, on a manifest built
    // by hand with a real 40-hex commit, which is what a resolution records.
    let mut resolved = fln_lake::Manifest::new("math_project");
    resolved.packages.push(fln_lake::ManifestPackageEntry {
        name: "mathlib".to_owned(),
        scope: String::new(),
        entry_type: "git".to_owned(),
        url: Some("https://github.com/leanprover-community/mathlib4.git".to_owned()),
        rev: Some("81a5d257c8e410db227a6665ed08f64fea08e997".to_owned()),
        input_rev: Some("v4.32.0".to_owned()),
        subdir: None,
        inherited: false,
        config_file: "lakefile.toml".to_owned(),
    });
    let round_trip = fresh_temp_dir("manifest-round-trip-test");
    resolved.save_to_dir(&round_trip).expect("save manifest");
    let loaded = fln_lake::Manifest::load_from_dir(&round_trip)
        .expect("load manifest")
        .expect("manifest exists");
    assert_eq!(loaded.packages.len(), 1);
    assert_eq!(loaded.packages[0].name, "mathlib");
    assert_eq!(
        loaded.packages[0].rev.as_deref(),
        Some("81a5d257c8e410db227a6665ed08f64fea08e997")
    );
    assert_eq!(loaded.packages[0].input_rev.as_deref(), Some("v4.32.0"));

    // Test parse_json with version 7 integer format for backwards compatibility
    let v7_json = r#"{"version": 7, "packagesDir": ".lake/packages", "packages": [], "name": "legacy_pkg", "lakeDir": ".lake"}"#;
    let parsed_v7 = fln_lake::Manifest::parse_json(v7_json).expect("parse v7 manifest");
    assert_eq!(parsed_v7.name, "legacy_pkg");
    assert_eq!(parsed_v7.version, "7");
    assert_eq!(parsed_v7.packages.len(), 0);
}

#[test]
fn artifact_builds_refuse_without_creating_or_replacing_outputs() {
    let dir = fresh_temp_dir("build-test");
    init_package(&dir, "tensor_lib", None, LakeConfigFormat::Toml).expect("init package");

    for target in ["tensor_lib", "absent", "../../escaped", "/tmp/escaped"] {
        assert!(matches!(
            fln_lake::build_package(&dir, &[target.to_owned()]),
            Err(fln_lake::LakeBuildError::Unavailable)
        ));
        assert!(!dir.join(".lake").exists());
    }
    let artifact = dir.join(".lake/build/lib/tensor_lib.olean");
    std::fs::create_dir_all(artifact.parent().unwrap()).unwrap();
    std::fs::write(&artifact, b"old artifact").unwrap();
    std::fs::write(dir.join("Main.lean"), "invalid source").unwrap();
    assert!(fln_lake::build_package(&dir, &[]).is_err());
    assert_eq!(std::fs::read(&artifact).unwrap(), b"old artifact");
}

#[test]
fn build_explanations_cannot_invent_provenance() {
    let dir = fresh_temp_dir("explain-test");
    init_package(&dir, "algebra_geom", None, LakeConfigFormat::Toml).expect("init package");

    for faithful in [false, true] {
        assert!(matches!(
            fln_lake::explain_build(&dir, Some("algebra_geom"), faithful),
            Err(fln_lake::LakeExplainError::Unavailable)
        ));
    }
    assert!(!dir.join(".lake").exists());
}

#[test]
fn default_targets_are_not_synthesized_and_bad_arrays_are_not_filtered() {
    for config in ["name = 'p'", "name = 'p'\ndefaultTargets = []"] {
        assert!(
            LakeConfig::parse_toml(config)
                .unwrap()
                .default_targets
                .is_empty()
        );
    }
    for array in ["[42]", "['real', 42]", "['real',,]", "['unfinished]"] {
        assert!(
            LakeConfig::parse_toml(&format!("name = 'p'\ndefaultTargets = {array}")).is_err(),
            "{array}"
        );
    }
    assert_eq!(
        LakeConfig::parse_toml("name = 'p'\ndefaultTargets = ['a', 'b',]")
            .unwrap()
            .default_targets,
        ["a", "b"]
    );
}

/// Every file of the tree under `root`, by relative path, with its bytes.
fn tree(root: &std::path::Path) -> std::collections::BTreeMap<String, String> {
    let mut out = std::collections::BTreeMap::new();
    let mut pending = vec![root.to_path_buf()];
    while let Some(dir) = pending.pop() {
        for entry in std::fs::read_dir(&dir).unwrap() {
            let path = entry.unwrap().path();
            if path.is_dir() {
                pending.push(path);
            } else {
                let relative = path.strip_prefix(root).unwrap().display().to_string();
                out.insert(relative, std::fs::read_to_string(&path).unwrap());
            }
        }
    }
    out
}

/// The expected bytes are the pin's `std` template (`Lake.initPkg`, vendored
/// `src/lake/Lake/CLI/Init.lean`), as the pinned `lake new demo` writes them;
/// fln-cli's `lake_new_writes_the_tree_the_pinned_lake_writes` compares against
/// the pin itself where it is installed.
#[test]
fn the_std_scaffold_is_the_pins_template_byte_for_byte() {
    let parent = fresh_temp_dir("std-scaffold");
    let dir = new_package(&parent, "demo", None, LakeConfigFormat::Toml).expect("lake new demo");
    let expected: std::collections::BTreeMap<String, String> = [
        (
            ".github/workflows/lean_action_ci.yml",
            "name: Lean Action CI\n\non:\n  push:\n  pull_request:\n  workflow_dispatch:\n\njobs:\n  build:\n    runs-on: ubuntu-latest\n\n    steps:\n      - uses: actions/checkout@v5\n      - uses: leanprover/lean-action@v1\n",
        ),
        (".gitignore", "/.lake\n"),
        (
            "Demo.lean",
            "-- This module serves as the root of the `Demo` library.\n-- Import modules here that should be built as part of the library.\nimport Demo.Basic\n",
        ),
        ("Demo/Basic.lean", "def hello := \"world\"\n"),
        (
            "Main.lean",
            "import Demo\n\ndef main : IO Unit :=\n  IO.println s!\"Hello, {hello}!\"\n",
        ),
        ("README.md", "# demo"),
        (
            "lakefile.toml",
            "name = \"demo\"\nversion = \"0.1.0\"\ndefaultTargets = [\"demo\"]\n\n[[lean_lib]]\nname = \"Demo\"\n\n[[lean_exe]]\nname = \"demo\"\nroot = \"Main\"\n",
        ),
        ("lean-toolchain", "leanprover/lean4:v4.32.0\n"),
    ]
    .into_iter()
    .map(|(path, bytes)| (path.to_owned(), bytes.to_owned()))
    .collect();
    assert_eq!(tree(&dir), expected);

    // The explicit spelling of the default, in any case, is the same request.
    let again = new_package(&parent, "demo2", Some("STD.Toml"), LakeConfigFormat::Toml).unwrap();
    assert_eq!(
        tree(&again)["Main.lean"],
        "import Demo2\n\ndef main : IO Unit :=\n  IO.println s!\"Hello, {hello}!\"\n"
    );

    // A second init in the same directory is the pin's refusal and changes nothing.
    let before = tree(&dir);
    let err = init_package(&dir, "demo", None, LakeConfigFormat::Toml).unwrap_err();
    assert!(matches!(err, LakeInitError::AlreadyInitialized));
    assert_eq!(err.to_string(), "error: package already initialized");
    assert_eq!(tree(&dir), before);
}

#[test]
fn a_template_this_does_not_write_creates_nothing() {
    let parent = fresh_temp_dir("templates");
    // The pin has these; only `std` with a TOML configuration is written here.
    for spec in [
        "math",
        "math-lax",
        "lib",
        "exe",
        "std.lean",
        ".lean",
        "MATH.toml",
    ] {
        let err = new_package(&parent, "pkg", Some(spec), LakeConfigFormat::Toml).unwrap_err();
        assert!(
            matches!(err, LakeInitError::TemplateUnavailable { .. }) && err.is_unavailable(),
            "{spec}: {err}"
        );
        assert!(
            !parent.join("pkg").exists(),
            "{spec} left a directory behind"
        );
    }
    // The pin does not have these: its own errors, template before language.
    let unknown = |spec: &str| {
        let err = new_package(&parent, "pkg", Some(spec), LakeConfigFormat::Toml).unwrap_err();
        assert!(!err.is_unavailable());
        assert!(
            !parent.join("pkg").exists(),
            "{spec} left a directory behind"
        );
        err.to_string()
    };
    assert_eq!(unknown("zzz"), "error: unknown package template `zzz`");
    assert_eq!(
        unknown("std.zzz"),
        "error: unknown configuration language `zzz`"
    );
    assert_eq!(unknown("zzz.yyy"), "error: unknown package template `zzz`");
    // Three parts is not a specification at all, and the pin takes its defaults.
    assert!(new_package(&parent, "three", Some("a.b.c"), LakeConfigFormat::Toml).is_ok());
    // The caller's language is the default one when the argument names none.
    let err = new_package(&parent, "pkg", None, LakeConfigFormat::Lean).unwrap_err();
    assert!(matches!(
        err,
        LakeInitError::TemplateUnavailable { ref template, ref language }
            if template == "std" && language == "lean"
    ));
}

#[test]
fn clean_removes_the_configured_build_directory_and_nothing_else() {
    let parent = fresh_temp_dir("clean-build-dir");
    let dir = new_package(&parent, "demo", None, LakeConfigFormat::Toml).unwrap();
    let set_build_dir = |value: Option<&str>| {
        let base = "name = \"demo\"\nversion = \"0.1.0\"\n";
        let line = value.map_or(String::new(), |v| format!("buildDir = \"{v}\"\n"));
        std::fs::write(
            dir.join("lakefile.toml"),
            format!("{base}{line}\n[[lean_lib]]\nname = \"Demo\"\n"),
        )
        .unwrap();
    };
    let plant = |relative: &str| {
        let path = dir.join(relative);
        std::fs::create_dir_all(&path).unwrap();
        std::fs::write(path.join("marker"), b"x").unwrap();
        path
    };

    // A configured directory is the one removed; the default one is not touched.
    set_build_dir(Some("out"));
    let (custom, default) = (plant("out"), plant(".lake/build"));
    let report = clean(&dir).expect("clean with buildDir");
    assert!(report.build_dir_removed);
    assert!(!custom.exists(), "the configured build directory survived");
    assert!(
        default.exists(),
        "a directory the package does not build into was removed"
    );

    // With none configured, the default is.
    set_build_dir(None);
    assert!(clean(&dir).unwrap().build_dir_removed);
    assert!(!default.exists());
    // Nothing there to remove is an answer, not an error.
    assert!(!clean(&dir).unwrap().build_dir_removed);

    // A build directory that is not inside the package is refused, and nothing goes.
    let outside = parent.join("outside");
    std::fs::create_dir_all(&outside).unwrap();
    std::fs::write(outside.join("precious"), b"x").unwrap();
    for escape in ["../outside", "..", ".", "", outside.to_str().unwrap()] {
        set_build_dir(Some(escape));
        let err = clean(&dir).unwrap_err();
        assert!(
            matches!(err, LakeCleanError::BuildDirOutsidePackage(_)),
            "{escape:?}: {err}"
        );
        assert!(
            outside.join("precious").exists(),
            "{escape:?} removed outside the package"
        );
        assert!(
            dir.join("Main.lean").exists(),
            "{escape:?} removed the package"
        );
    }

    // A `lakefile.lean` is not evaluated, so its build directory is not known.
    let lean_only = fresh_temp_dir("clean-lean-config");
    std::fs::write(lean_only.join("lakefile.lean"), "import Lake\n").unwrap();
    let kept = lean_only.join(".lake").join("build");
    std::fs::create_dir_all(&kept).unwrap();
    let err = clean(&lean_only).unwrap_err();
    assert!(matches!(err, LakeCleanError::BuildDirUnknown(_)) && err.is_unavailable());
    assert!(kept.exists());
}
