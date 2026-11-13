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
fn local_requirements_are_retained_for_checked_execution_and_artifact_builds() {
    let source = concat!(
        "name = \"program\"\n",
        "[[require]]\nname = \"shared\"\npath = \"../first\"\n",
        "[[require]]\nname = \"shared\"\npath = \"../second\"\n",
        "[[lean_exe]]\nname = \"runner\"\nroot = \"Main\"\n",
    );
    let executable = LakeConfig::parse_toml_for_execution(source).unwrap();
    assert_eq!(executable.requires.len(), 2);
    assert_eq!(executable.requires[0].name, "shared");
    assert_eq!(executable.requires[1].name, "shared");
    assert_eq!(
        executable.requires[0].path.as_deref(),
        Some(std::path::Path::new("../first")),
    );
    assert_eq!(
        executable.requires[1].path.as_deref(),
        Some(std::path::Path::new("../second")),
    );
    assert_eq!(
        LakeConfig::parse_toml(source).unwrap().requires,
        executable.requires,
    );
    assert_eq!(
        LakeConfig::parse_toml_for_build(source).unwrap().requires,
        executable.requires,
    );
}

#[test]
fn checked_requirements_do_not_ignore_remote_or_custom_settings() {
    for fields in [
        "name = \"dep\"\n",
        "name = \"dep\"\ngit = \"https://example.invalid/dep\"\n",
        "name = \"dep\"\npath = \"../dep\"\nrev = \"branch\"\n",
        "name = \"dep\"\npath = \"../dep\"\nscope = \"owner\"\n",
        "name = \"dep\"\npath = \"../dep\"\noptions = []\n",
    ] {
        let source = format!("name = \"program\"\n[[require]]\n{fields}");
        for parse in [
            LakeConfig::parse_toml_for_execution,
            LakeConfig::parse_toml_for_build,
        ] {
            assert!(
                matches!(
                    parse(&source),
                    Err(LakeParseError::UnsupportedBuildSetting(_))
                ),
                "{source}"
            );
        }
    }
    assert!(matches!(
        LakeConfig::parse_toml_for_execution(
            "name = \"program\"\n[[require]]\npath = \"../dep\"\n",
        ),
        Err(LakeParseError::MissingField("require name")),
    ));
    assert!(matches!(
        LakeConfig::parse_toml_for_execution(
            "name = \"program\"\n[[require]]\nname = \"dep\"\npath = 1\n",
        ),
        Err(LakeParseError::InvalidSyntax(_)),
    ));
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
    assert_eq!(manifest.version, "1.2.0");
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
        dir: None,
        url: Some("https://github.com/leanprover-community/mathlib4.git".to_owned()),
        rev: Some("81a5d257c8e410db227a6665ed08f64fea08e997".to_owned()),
        input_rev: Some("v4.32.0".to_owned()),
        subdir: None,
        inherited: false,
        config_file: "lakefile.toml".to_owned(),
        manifest_file: Some(PathBuf::from("lake-manifest.json")),
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

#[test]
fn manifests_preserve_local_paths_and_every_json_string_field() {
    let input = r#"{
        "packages": [
            {"name":"local","type":"path","dir":"../quoted\"\\dir/\ud83e\udd80",
             "scope":"owner\\name","inherited":false,
             "configFile":"config\".toml","manifestFile":"locks\\manifest.json"},
            {"name":"remote","type":"git","url":"https://example.invalid/\"repo\\name",
             "rev":"actual\\revision","inputRev":"release\nbranch","subDir":"sub\tpath",
             "inherited":true,"configFile":"lakefile.toml"}
        ],
        "name":"«workspace\"name»","version":"1.2.0",
        "lakeDir":"build\\cache","packagesDir":null,"fixedToolchain":true
    }"#;
    let manifest = fln_lake::Manifest::parse_json(input).unwrap();
    assert_eq!(manifest.name, "«workspace\"name»");
    assert_eq!(manifest.packages_dir, None);
    assert!(manifest.fixed_toolchain);
    assert_eq!(
        manifest.packages[0].dir,
        Some(PathBuf::from("../quoted\"\\dir/🦀")),
    );
    assert_eq!(
        manifest.packages[1].input_rev.as_deref(),
        Some("release\nbranch")
    );
    assert_eq!(manifest.packages[1].subdir.as_deref(), Some("sub\tpath"));
    assert_eq!(
        fln_lake::Manifest::parse_json(&manifest.to_json()).unwrap(),
        manifest,
    );
}

#[test]
fn manifest_fields_are_scoped_and_duplicate_keys_follow_the_pin() {
    let manifest = fln_lake::Manifest::parse_json(
        r#"{"packages":[{"name":"dependency","type":"path","dir":"../dep","inherited":false}],
            "metadata":{"name":"not-the-workspace","version":99},
            "name":"first","na\u006de":"selected","version":7}"#,
    )
    .unwrap();
    assert_eq!(manifest.name, "selected");
    assert_eq!(manifest.packages[0].name, "dependency");
    assert_eq!(manifest.version, "7");
    assert_eq!(
        fln_lake::Manifest::parse_json(&manifest.to_json()).unwrap(),
        manifest,
    );

    let anonymous = fln_lake::Manifest::parse_json(
        r#"{"version":7,"packages":[{"name":"dependency","type":"path","dir":".","inherited":false}]}"#,
    )
    .unwrap();
    assert_eq!(anonymous.name, "[anonymous]");
}

#[test]
fn manifest_defaults_match_the_pins_null_and_missing_fields() {
    let manifest = fln_lake::Manifest::parse_json(
        r#"{"schemaVersion":"1.2.0-custom","name":null,"lakeDir":null,
            "fixedToolchain":null,"packagesDir":null,
            "packages":[{"name":"dep","type":"path","dir":"../dep","inherited":false,
                         "scope":null,"configFile":null,"manifestFile":null}]}"#,
    )
    .unwrap();
    assert_eq!(manifest.name, "[anonymous]");
    assert_eq!(manifest.lake_dir, PathBuf::from(".lake"));
    assert!(!manifest.fixed_toolchain);
    assert_eq!(manifest.packages_dir, None);
    let package = &manifest.packages[0];
    assert_eq!(package.scope, "");
    assert_eq!(package.config_file, "lakefile");
    assert_eq!(
        package.manifest_file,
        Some(PathBuf::from("lake-manifest.json"))
    );
    assert!(
        fln_lake::Manifest::parse_json(r#"{"version":"1.99.0","packages":null}"#)
            .unwrap()
            .packages
            .is_empty()
    );
    assert!(
        fln_lake::Manifest::parse_json(r#"{"version":null,"schemaVersion":7}"#).is_err(),
        "a present invalid version must not fall back to schemaVersion",
    );
}

#[test]
fn malformed_manifests_cannot_become_partial_or_empty_dependency_locks() {
    for input in [
        r#""name":"not-an-object""#,
        r#"{"version":7,"name":"p"} trailing"#,
        r#"{"version":7,"packages":[}"#,
        r#"{"version":7,"packages":[{"name":"dep"}]}"#,
        r#"{"version":7,"packages":[{"name":"dep","type":"path","inherited":false}]}"#,
        r#"{"version":7,"packages":[{"name":"dep","type":"path","dir":4,"inherited":false}]}"#,
        r#"{"version":7,"packages":[{"name":"dep","type":"path","dir":".","inherited":null}]}"#,
        r#"{"version":7,"packages":[{"name":"dep","type":"path","dir":"."}]}"#,
        r#"{"version":7,"packages":[{"name":"dep","type":"git","url":"remote","inherited":false}]}"#,
        r#"{"version":7,"packages":[null]}"#,
        r#"{"version":7,"packages":{}}"#,
        r#"{"version":7,"fixedToolchain":"false"}"#,
        r#"{"version":7,"name":"\ud800"}"#,
        r#"{"version":7,"name":"\udc00"}"#,
        r#"{"version":7,"name":"\ud800\u0041"}"#,
        r#"{"version":7,"name":"\q"}"#,
        r#"{"version":7,}"#,
        r#"{"version":7,"extension":[1,]}"#,
        r#"{"version":7,"extension":01}"#,
        r#"{"version":7,"extension":1e}"#,
        r#"{"version":7,"extension":true false}"#,
    ] {
        assert!(
            matches!(
                fln_lake::Manifest::parse_json(input),
                Err(fln_lake::ManifestParseError::Invalid(_))
            ),
            "{input}",
        );
    }
    for version in [
        "true",
        "null",
        "-1",
        "7.5",
        "\"2.0.0\"",
        "\"1.2\"",
        "\"1.2.0-\"",
        "\"1.2.0-bad suffix\"",
        "\"1.2.0+metadata\"",
        "4",
        "5",
        "6",
    ] {
        assert!(
            fln_lake::Manifest::parse_json(&format!("{{\"version\":{version}}}")).is_err(),
            "{version}",
        );
    }
}

#[test]
fn manifest_budget_exhaustion_is_distinct_from_invalid_json() {
    let deep = format!(
        "{{\"version\":7,\"extension\":{}null{}}}",
        "[".repeat(70),
        "]".repeat(70),
    );
    let many = format!(
        "{{\"version\":7,\"extension\":[{}]}}",
        vec!["null"; 100_001].join(","),
    );
    for input in [deep, many, " ".repeat(1024 * 1024 + 1)] {
        assert!(matches!(
            fln_lake::Manifest::parse_json(&input),
            Err(fln_lake::ManifestParseError::Resource(_))
        ),);
    }
    let directory = fresh_temp_dir("manifest-budget");
    std::fs::write(
        directory.join("lake-manifest.json"),
        " ".repeat(1024 * 1024 + 1),
    )
    .unwrap();
    assert!(matches!(
        fln_lake::Manifest::load_from_dir(&directory),
        Err(fln_lake::LakeUpdateError::Resource(_)),
    ));
}

#[test]
fn manifest_publication_preserves_old_data_and_unowned_temporary_files() {
    let directory = fresh_temp_dir("manifest-publication");
    let mut manifest = fln_lake::Manifest::new("original");
    manifest.save_to_dir(&directory).unwrap();
    let destination = directory.join("lake-manifest.json");
    let original = std::fs::read(&destination).unwrap();
    let old_temporary = directory.join(".lake-manifest.json.tmp");
    std::fs::write(&old_temporary, b"another writer's data").unwrap();

    manifest.packages.push(fln_lake::ManifestPackageEntry {
        name: "invalid".to_owned(),
        scope: String::new(),
        entry_type: "path".to_owned(),
        dir: None,
        url: None,
        rev: None,
        input_rev: None,
        subdir: None,
        inherited: false,
        config_file: "lakefile.toml".to_owned(),
        manifest_file: Some(PathBuf::from("lake-manifest.json")),
    });
    assert!(manifest.save_to_dir(&directory).is_err());
    assert_eq!(std::fs::read(&destination).unwrap(), original);
    assert_eq!(
        std::fs::read(&old_temporary).unwrap(),
        b"another writer's data",
    );

    manifest.packages.clear();
    manifest.name = "replacement".to_owned();
    manifest.save_to_dir(&directory).unwrap();
    assert_eq!(
        fln_lake::Manifest::load_from_dir(&directory)
            .unwrap()
            .unwrap()
            .name,
        "replacement",
    );
    assert_eq!(
        std::fs::read(&old_temporary).unwrap(),
        b"another writer's data",
    );

    let blocked = fresh_temp_dir("manifest-directory-destination");
    std::fs::create_dir(blocked.join("lake-manifest.json")).unwrap();
    std::fs::write(blocked.join("lake-manifest.json/retained"), b"keep").unwrap();
    assert!(manifest.save_to_dir(&blocked).is_err());
    assert_eq!(
        std::fs::read(blocked.join("lake-manifest.json/retained")).unwrap(),
        b"keep",
    );
}

#[cfg(unix)]
#[test]
fn manifest_publication_does_not_follow_old_temporary_or_destination_symlinks() {
    let directory = fresh_temp_dir("manifest-symlinks");
    let outside = fresh_temp_dir("manifest-outside").join("sentinel");
    std::fs::write(&outside, b"outside data").unwrap();
    std::os::unix::fs::symlink(&outside, directory.join(".lake-manifest.json.tmp")).unwrap();
    fln_lake::Manifest::new("safe")
        .save_to_dir(&directory)
        .unwrap();
    assert_eq!(std::fs::read(&outside).unwrap(), b"outside data");

    let blocked = fresh_temp_dir("manifest-destination-symlink");
    std::os::unix::fs::symlink(&outside, blocked.join("lake-manifest.json")).unwrap();
    assert!(
        fln_lake::Manifest::new("refused")
            .save_to_dir(&blocked)
            .is_err()
    );
    assert_eq!(std::fs::read(&outside).unwrap(), b"outside data");
}

#[test]
fn manifest_package_names_follow_the_pinned_identifier_grammar() {
    for (input, expected) in [
        ("Pkg.Sub", "Pkg.Sub"),
        ("«with spaces»", "«with spaces»"),
        ("«a.b»", "«a.b»"),
        ("Pkg.000", "Pkg.0"),
        ("Pkg.«»", "Pkg.«»"),
        ("«plain»", "plain"),
        ("café", "café"),
        ("α", "α"),
        ("Pkg.184467440737095516160", "Pkg.184467440737095516160"),
    ] {
        let text = format!("{{\"version\":7,\"name\":\"{input}\"}}");
        assert_eq!(
            fln_lake::Manifest::parse_json(&text).unwrap().name,
            expected
        );
    }
    for name in [
        "",
        ".",
        "a.",
        ".a",
        "a..b",
        "a-b",
        "123abc",
        "«unfinished",
        "λ",
    ] {
        let text = format!("{{\"version\":7,\"name\":\"{name}\"}}");
        assert!(fln_lake::Manifest::parse_json(&text).is_err(), "{name}");
    }
}

#[test]
fn toml_package_identities_remain_distinct_from_json_name_spellings() {
    for (source, expected) in [
        ("plain", "plain"),
        ("foo-bar", "«foo-bar»"),
        ("with spaces", "«with spaces»"),
        ("Pkg.000", "Pkg.0"),
        ("Pkg.«»", "Pkg.«»"),
        ("[anonymous]", "«[anonymous]»"),
        ("", "«»"),
        ("a..b", "«a..b»"),
    ] {
        assert_eq!(fln_lake::canonical_package_name(source), expected);
        let manifest = fln_lake::Manifest::new(source);
        assert_eq!(manifest.name, expected);
        assert_eq!(
            fln_lake::Manifest::parse_json(&manifest.to_json())
                .unwrap()
                .name,
            expected,
        );
    }
}

fn update_write_package(base: &std::path::Path, relative: &str, source: &str) {
    let dir = base.join(relative);
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(dir.join("lakefile.toml"), source).unwrap();
}

fn update_path_entry(
    name: &str,
    directory: &str,
    inherited: bool,
) -> fln_lake::ManifestPackageEntry {
    fln_lake::ManifestPackageEntry {
        name: name.to_owned(),
        scope: String::new(),
        entry_type: "path".to_owned(),
        dir: Some(PathBuf::from(directory)),
        url: None,
        rev: None,
        input_rev: None,
        subdir: None,
        inherited,
        config_file: "lakefile.toml".to_owned(),
        manifest_file: Some(PathBuf::from("lake-manifest.json")),
    }
}

#[test]
fn local_update_resolves_the_reverse_breadth_first_diamond_without_child_writes() {
    let base = fresh_temp_dir("update-diamond");
    update_write_package(
        &base,
        "root",
        concat!(
            "name = \"root\"\n",
            "[[require]]\nname = \"left\"\npath = \"../left\"\n",
            "[[require]]\nname = \"right\"\npath = \"../missing-direct\"\n",
            "[[require]]\nname = \"right\"\npath = \"../right\"\n",
        ),
    );
    update_write_package(
        &base,
        "left",
        concat!(
            "name = \"left\"\n",
            "[[require]]\nname = \"shared\"\npath = \"../missing-transitive\"\n",
        ),
    );
    update_write_package(
        &base,
        "right",
        concat!(
            "name = \"different-from-required-identity\"\n",
            "[[require]]\nname = \"shared\"\npath = \"vendor/shared library\"\n",
        ),
    );
    update_write_package(&base, "right/vendor/shared library", "name = \"shared\"\n");
    let root = base.join("root");
    std::fs::write(root.join("lake-manifest.json"), "{stale malformed lock}").unwrap();
    let before = tree(&base);
    let manifest = fln_lake::update_manifest(&root).unwrap();
    assert_eq!(manifest.name, "root");
    assert_eq!(manifest.version, "1.2.0");
    assert!(!manifest.fixed_toolchain);
    assert_eq!(manifest.packages_dir, Some(PathBuf::from(".lake/packages")));
    assert_eq!(
        manifest.packages,
        [
            update_path_entry("right", "../right", false),
            update_path_entry("left", "../left", false),
            update_path_entry("shared", "../right/vendor/shared library", true),
        ],
    );
    let bytes = std::fs::read_to_string(root.join("lake-manifest.json")).unwrap();
    let loaded = fln_lake::Manifest::load_from_dir(&root).unwrap().unwrap();
    assert_eq!(loaded, manifest);
    let mut expected = before;
    expected.insert(
        std::path::Path::new("root/lake-manifest.json")
            .display()
            .to_string(),
        bytes.clone(),
    );
    assert_eq!(tree(&base), expected);
    assert_eq!(fln_lake::update_manifest(&root).unwrap(), manifest);
    assert_eq!(
        std::fs::read_to_string(root.join("lake-manifest.json")).unwrap(),
        bytes,
    );
    assert_eq!(tree(&base), expected);
}

#[test]
fn local_update_inherits_child_locks_after_reserving_every_direct_name() {
    let base = fresh_temp_dir("update-inherited");
    update_write_package(
        &base,
        "root",
        concat!(
            "name = \"root\"\n",
            "[[require]]\nname = \"leaf\"\npath = \"../direct\"\n",
            "[[require]]\nname = \"parent\"\npath = \"../parent\"\n",
        ),
    );
    update_write_package(
        &base,
        "parent",
        concat!(
            "name = \"parent\"\n",
            "[[require]]\nname = \"leaf\"\npath = \"missing-unlocked-leaf\"\n",
            "[[require]]\nname = \"transitive\"\npath = \"missing-unlocked-transitive\"\n",
        ),
    );
    update_write_package(&base, "direct", "name = \"leaf-own-name\"\n");
    update_write_package(&base, "parent/vendor/locked", "name = \"transitive\"\n");
    let mut child = fln_lake::Manifest::new("parent");
    child.packages = vec![
        update_path_entry("leaf", "missing-shadow", false),
        update_path_entry("transitive", "vendor/locked", false),
        // The first imported lock for a name wins, unlike reading a root lock.
        update_path_entry("transitive", "missing-later-duplicate", false),
    ];
    child.save_to_dir(&base.join("parent")).unwrap();
    let root = base.join("root");
    let mut stale = fln_lake::Manifest::new("root");
    stale.packages = vec![update_path_entry("leaf", "../missing-stale-root", false)];
    stale.save_to_dir(&root).unwrap();
    let before = tree(&base);
    let manifest = fln_lake::update_manifest(&root).unwrap();
    assert_eq!(
        manifest.packages,
        [
            update_path_entry("parent", "../parent", false),
            update_path_entry("leaf", "../direct", false),
            update_path_entry("transitive", "../parent/vendor/locked", true),
        ],
    );
    let mut expected = before;
    expected.insert(
        std::path::Path::new("root/lake-manifest.json")
            .display()
            .to_string(),
        std::fs::read_to_string(root.join("lake-manifest.json")).unwrap(),
    );
    assert_eq!(tree(&base), expected);
    assert_eq!(
        fln_lake::Manifest::load_from_dir(&base.join("parent"))
            .unwrap()
            .unwrap(),
        child,
    );
}

#[test]
fn local_update_discovery_failures_preserve_every_existing_file() {
    for (label, root_source, child_source, detail) in [
        (
            "missing",
            concat!(
                "name = \"root\"\n",
                "[[require]]\nname = \"absent\"\npath = \"../absent\"\n",
                "[[require]]\nname = \"good\"\npath = \"../good\"\n",
            ),
            "name = \"good\"\n",
            "absent",
        ),
        (
            "remote",
            concat!(
                "name = \"root\"\n",
                "[[require]]\nname = \"remote\"\ngit = \"https://example.invalid/repo\"\n",
                "[[require]]\nname = \"good\"\npath = \"../good\"\n",
            ),
            "name = \"good\"\n",
            "remote",
        ),
        (
            "cycle",
            "name = \"root\"\n[[require]]\nname = \"good\"\npath = \"../good\"\n",
            "name = \"good\"\n[[require]]\nname = \"root\"\npath = \"../root\"\n",
            "cycle",
        ),
        (
            "options",
            "name = \"root\"\n[[require]]\nname = \"good\"\npath = \"../good\"\n",
            "name = \"good\"\n[[require]]\nname = \"leaf\"\npath = \"../leaf\"\noptions = []\n",
            "options",
        ),
    ] {
        let base = fresh_temp_dir(&format!("update-{label}"));
        update_write_package(&base, "root", root_source);
        update_write_package(&base, "good", child_source);
        let root = base.join("root");
        fln_lake::Manifest::new("old-selection")
            .save_to_dir(&root)
            .unwrap();
        let before = tree(&base);
        let error = fln_lake::update_manifest(&root).unwrap_err();
        assert!(error.to_string().contains(detail), "{label}: {error}");
        assert_eq!(tree(&base), before, "{label}");
    }
}

#[test]
fn local_update_does_not_ignore_child_manifests_or_toolchain_changes() {
    for (label, extra_path, contents, expected) in [
        (
            "child-manifest",
            "good/lake-manifest.json",
            "{not valid json}",
            "manifest",
        ),
        (
            "toolchain",
            "good/lean-toolchain",
            "leanprover/lean4:v4.33.0\n",
            "toolchain",
        ),
        (
            "overrides",
            "good/.lake/package-overrides.json",
            "{}",
            "package-overrides.json",
        ),
        (
            "lean-config",
            "good/lakefile.lean",
            "import Lake\n",
            "lakefile.lean",
        ),
    ] {
        let base = fresh_temp_dir(&format!("update-{label}"));
        update_write_package(
            &base,
            "root",
            "name = \"root\"\n[[require]]\nname = \"good\"\npath = \"../good\"\n",
        );
        update_write_package(&base, "good", "name = \"good\"\n");
        let root = base.join("root");
        std::fs::write(root.join("lean-toolchain"), "leanprover/lean4:v4.32.0\n").unwrap();
        let extra = base.join(extra_path);
        std::fs::create_dir_all(extra.parent().unwrap()).unwrap();
        std::fs::write(extra, contents).unwrap();
        fln_lake::Manifest::new("old-selection")
            .save_to_dir(&root)
            .unwrap();
        let before = tree(&base);
        let error = fln_lake::update_manifest(&root).unwrap_err();
        assert!(error.to_string().contains(expected), "{label}: {error}");
        assert_eq!(tree(&base), before, "{label}");
    }
}

#[test]
fn local_update_budget_stops_do_not_publish_partial_dependency_sets() {
    let base = fresh_temp_dir("update-package-bound");
    let mut source = String::from("name = \"root\"\n");
    for index in 0..64 {
        let name = format!("dep{index}");
        source.push_str(&format!(
            "[[require]]\nname = \"{name}\"\npath = \"../{name}\"\n",
        ));
        update_write_package(&base, &name, &format!("name = \"{name}\"\n"));
    }
    update_write_package(&base, "root", &source);
    let root = base.join("root");
    fln_lake::Manifest::new("previous")
        .save_to_dir(&root)
        .unwrap();
    let before = tree(&base);
    assert!(matches!(
        fln_lake::update_manifest(&root),
        Err(fln_lake::LakeUpdateError::Resource(detail))
            if detail.contains("package count exceeds 64")
    ));
    assert_eq!(tree(&base), before);

    std::fs::write(root.join("lakefile.toml"), " ".repeat(64 * 1024 + 1)).unwrap();
    let before = tree(&base);
    assert!(matches!(
        fln_lake::update_manifest(&root),
        Err(fln_lake::LakeUpdateError::Resource(detail))
            if detail.contains("65536 bytes")
    ));
    assert_eq!(tree(&base), before);
}

#[cfg(unix)]
#[test]
fn local_update_checks_symlinks_before_erasing_parent_components() {
    let base = fresh_temp_dir("update-symlink-parent");
    update_write_package(
        &base,
        "root",
        "name = \"root\"\n[[require]]\nname = \"good\"\npath = \"../alias/../good\"\n",
    );
    update_write_package(&base, "good", "name = \"good\"\n");
    std::os::unix::fs::symlink(base.join("good"), base.join("alias")).unwrap();
    let root = base.join("root");
    fln_lake::Manifest::new("previous")
        .save_to_dir(&root)
        .unwrap();
    let before = std::fs::read(root.join("lake-manifest.json")).unwrap();
    let error = fln_lake::update_manifest(&root).unwrap_err();
    assert!(error.to_string().contains("symlink"), "{error}");
    assert_eq!(
        std::fs::read(root.join("lake-manifest.json")).unwrap(),
        before
    );
    assert_eq!(
        std::fs::read_to_string(base.join("good/lakefile.toml")).unwrap(),
        "name = \"good\"\n",
    );
    assert!(!base.join("good/lake-manifest.json").exists());
}

#[test]
fn local_update_uses_canonical_names_and_an_inherited_explicit_toml_selector() {
    let base = fresh_temp_dir("update-canonical-names");
    update_write_package(
        &base,
        "root",
        "name = \"root-project\"\n[[require]]\nname = \"parent-lib\"\npath = \"../parent\"\n",
    );
    update_write_package(
        &base,
        "parent",
        concat!(
            "name = \"parent-lib\"\n",
            "[[require]]\nname = \"shared-lib\"\npath = \"missing-unlocked-shared\"\n",
        ),
    );
    update_write_package(&base, "parent/vendor/shared", "name = \"shared-lib\"\n");
    // The inherited entry explicitly selects TOML, so a sibling Lean file
    // does not take precedence as it would for a fresh default selector.
    std::fs::write(
        base.join("parent/vendor/shared/lakefile.lean"),
        "import Lake\npackage ignored\n",
    )
    .unwrap();
    let mut inherited = fln_lake::Manifest::new("parent-lib");
    inherited.packages = vec![update_path_entry("«shared-lib»", "vendor/shared", false)];
    inherited.save_to_dir(&base.join("parent")).unwrap();
    let before = tree(&base);
    let root = base.join("root");
    let manifest = fln_lake::update_manifest(&root).unwrap();
    assert_eq!(manifest.name, "«root-project»");
    assert_eq!(
        manifest.packages,
        [
            update_path_entry("«parent-lib»", "../parent", false),
            update_path_entry("«shared-lib»", "../parent/vendor/shared", true),
        ],
    );
    assert_eq!(
        fln_lake::Manifest::load_from_dir(&root).unwrap().unwrap(),
        manifest,
    );
    let mut expected = before;
    expected.insert(
        std::path::Path::new("root/lake-manifest.json")
            .display()
            .to_string(),
        std::fs::read_to_string(root.join("lake-manifest.json")).unwrap(),
    );
    assert_eq!(tree(&base), expected);
}

// These core resolver tests inject already checked configurations. The CLI's
// installed tests exercise the actual source loader and Golem evaluation.
fn update_checked_lean(name: &str, requirements: &[(&str, &str)]) -> LakeConfig {
    LakeConfig {
        name: name.to_owned(),
        default_targets: Vec::new(),
        lean_toolchain: None,
        src_dir: PathBuf::from("."),
        build_dir: PathBuf::from(".lake/build"),
        requires: requirements
            .iter()
            .map(|(name, path)| fln_lake::LakeRequire {
                name: (*name).to_owned(),
                path: Some(PathBuf::from(path)),
                url: None,
                rev: None,
                subdir: None,
            })
            .collect(),
        targets: Vec::new(),
        format: LakeConfigFormat::Lean,
    }
}

#[test]
fn local_update_lean_loader_resolves_mixed_packages_and_inherited_locks() {
    let base = fresh_temp_dir("update-lean-mixed");
    update_write_package(&base, "root", "this TOML must not be selected\n");
    std::fs::write(
        base.join("root/lakefile.lean"),
        "package «root-project»\r\n",
    )
    .unwrap();
    update_write_package(
        &base,
        "parent",
        concat!(
            "name = \"parent-lib\"\n",
            "[[require]]\nname = \"leaf-lib\"\npath = \"missing-unlocked-leaf\"\n",
            "[[require]]\nname = \"transitive-lib\"\npath = \"missing-unlocked-transitive\"\n",
        ),
    );
    for (directory, source) in [
        ("direct", "package leafOwnName\n"),
        ("parent/vendor/locked", "package transitiveOwnName\n"),
    ] {
        std::fs::create_dir_all(base.join(directory)).unwrap();
        std::fs::write(base.join(directory).join("lakefile.lean"), source).unwrap();
    }
    let mut inherited = fln_lake::Manifest::new("parent-lib");
    let mut transitive = update_path_entry("«transitive-lib»", "vendor/locked", false);
    transitive.config_file = "lakefile.lean".to_owned();
    inherited.packages = vec![
        update_path_entry("«leaf-lib»", "missing-shadowed-by-root", false),
        transitive,
    ];
    inherited.save_to_dir(&base.join("parent")).unwrap();
    let before = tree(&base);
    let canonical_base = std::fs::canonicalize(&base).unwrap();
    let mut loaded = Vec::new();
    let manifest = fln_lake::update_manifest_with_lean::<fln_lake::LakeUpdateError>(
        &base.join("root"),
        |directory, bytes| {
            let relative = directory.strip_prefix(&canonical_base).unwrap();
            loaded.push(relative.to_path_buf());
            let config = if relative == std::path::Path::new("root") {
                assert_eq!(bytes, "package «root-project»\r\n".as_bytes());
                update_checked_lean(
                    "root-project",
                    &[("leaf-lib", "../direct"), ("parent-lib", "../parent")],
                )
            } else if relative == std::path::Path::new("direct") {
                assert_eq!(bytes, b"package leafOwnName\n");
                update_checked_lean("leafOwnName", &[])
            } else {
                assert_eq!(relative, std::path::Path::new("parent/vendor/locked"));
                assert_eq!(bytes, b"package transitiveOwnName\n");
                update_checked_lean("transitiveOwnName", &[])
            };
            Ok(config)
        },
    )
    .unwrap();
    assert_eq!(manifest.name, "«root-project»");
    let mut leaf = update_path_entry("«leaf-lib»", "../direct", false);
    leaf.config_file = "lakefile.lean".to_owned();
    let mut transitive = update_path_entry("«transitive-lib»", "../parent/vendor/locked", true);
    transitive.config_file = "lakefile.lean".to_owned();
    assert_eq!(
        manifest.packages,
        [
            update_path_entry("«parent-lib»", "../parent", false),
            leaf,
            transitive
        ],
    );
    assert_eq!(
        loaded,
        [
            PathBuf::from("root"),
            PathBuf::from("direct"),
            PathBuf::from("parent/vendor/locked")
        ],
    );
    let mut expected = before;
    expected.insert(
        std::path::Path::new("root/lake-manifest.json")
            .display()
            .to_string(),
        manifest.to_json(),
    );
    assert_eq!(tree(&base), expected);
}

#[test]
fn local_update_lean_and_toml_selectors_do_not_override_or_fall_back() {
    for (selector, lean_exists, toml_exists, selected) in [
        ("lakefile", true, true, Some("lakefile.lean")),
        ("lakefile", false, true, Some("lakefile.toml")),
        ("lakefile.toml", true, true, Some("lakefile.toml")),
        ("lakefile.lean", true, true, Some("lakefile.lean")),
        ("lakefile.toml", true, false, None),
        ("lakefile.lean", false, true, None),
    ] {
        let base = fresh_temp_dir("update-lean-selector");
        update_write_package(
            &base,
            "root",
            "name = \"root\"\n[[require]]\nname = \"parent\"\npath = \"../parent\"\n",
        );
        update_write_package(
            &base,
            "parent",
            "name = \"parent\"\n[[require]]\nname = \"leaf\"\npath = \"missing\"\n",
        );
        std::fs::create_dir_all(base.join("leaf")).unwrap();
        if toml_exists {
            update_write_package(&base, "leaf", "name = \"tomlLeaf\"\n");
        }
        if lean_exists {
            std::fs::write(base.join("leaf/lakefile.lean"), "package leanLeaf\n").unwrap();
        }
        let mut child = fln_lake::Manifest::new("parent");
        let mut entry = update_path_entry("leaf", "../leaf", false);
        entry.config_file = selector.to_owned();
        child.packages = vec![entry];
        child.save_to_dir(&base.join("parent")).unwrap();
        fln_lake::Manifest::new("previous")
            .save_to_dir(&base.join("root"))
            .unwrap();
        let before = tree(&base);
        let leaf = std::fs::canonicalize(base.join("leaf")).unwrap();
        let mut calls = 0;
        let result = fln_lake::update_manifest_with_lean::<fln_lake::LakeUpdateError>(
            &base.join("root"),
            |directory, bytes| {
                assert_eq!(directory, leaf);
                assert_eq!(bytes, b"package leanLeaf\n");
                calls += 1;
                Ok(update_checked_lean("leanLeaf", &[]))
            },
        );
        if let Some(selected) = selected {
            let manifest = result.unwrap();
            assert_eq!(manifest.packages[1].name, "leaf");
            assert_eq!(manifest.packages[1].config_file, selected);
            assert_eq!(calls, usize::from(selected == "lakefile.lean"));
        } else {
            assert!(matches!(
                result,
                Err(fln_lake::LakeUpdateError::Discovery(_))
            ));
            assert_eq!(calls, 0);
            assert_eq!(tree(&base), before);
        }
    }
}

#[test]
fn local_update_rechecks_captured_lean_bytes_and_side_inputs_after_loading() {
    for (relative, replacement) in [
        ("lakefile.lean", "package changed\n"),
        ("lean-toolchain", "leanprover/lean4:v4.33.0\n"),
        (".lake/package-overrides.json", "{}"),
    ] {
        let root = fresh_temp_dir("update-lean-input-change");
        std::fs::write(root.join("lakefile.lean"), "package original\n").unwrap();
        fln_lake::Manifest::new("previous")
            .save_to_dir(&root)
            .unwrap();
        let previous = std::fs::read(root.join("lake-manifest.json")).unwrap();
        let result = fln_lake::update_manifest_with_lean::<fln_lake::LakeUpdateError>(
            &root,
            |directory, bytes| {
                let changed = directory.join(relative);
                std::fs::create_dir_all(changed.parent().unwrap()).unwrap();
                std::fs::write(changed, replacement).unwrap();
                // The loader still sees the captured source, even after its path changes.
                assert_eq!(bytes, b"package original\n");
                Ok(update_checked_lean("original", &[]))
            },
        );
        let filename = std::path::Path::new(relative)
            .file_name()
            .unwrap()
            .to_str()
            .unwrap();
        assert!(
            matches!(result, Err(fln_lake::LakeUpdateError::Parse(detail))
            if detail.contains("changed during dependency resolution") && detail.contains(filename)),
            "{relative}"
        );
        assert_eq!(
            std::fs::read(root.join("lake-manifest.json")).unwrap(),
            previous
        );
    }
}

#[test]
fn local_update_detects_a_new_preferred_lean_file_while_loading_a_dependency() {
    let base = fresh_temp_dir("update-lean-precedence-change");
    update_write_package(
        &base,
        "root",
        "name = \"root\"\n[[require]]\nname = \"leaf\"\npath = \"../leaf\"\n",
    );
    std::fs::create_dir_all(base.join("leaf")).unwrap();
    std::fs::write(base.join("leaf/lakefile.lean"), "package leaf\n").unwrap();
    let root = base.join("root");
    fln_lake::Manifest::new("previous")
        .save_to_dir(&root)
        .unwrap();
    let previous = std::fs::read(root.join("lake-manifest.json")).unwrap();
    let result =
        fln_lake::update_manifest_with_lean::<fln_lake::LakeUpdateError>(&root, |_, bytes| {
            assert_eq!(bytes, b"package leaf\n");
            std::fs::write(root.join("lakefile.lean"), "package newlyPreferred\n").unwrap();
            Ok(update_checked_lean("leaf", &[]))
        });
    assert!(
        matches!(result, Err(fln_lake::LakeUpdateError::Parse(detail))
        if detail.contains("changed during dependency resolution") && detail.contains("lakefile.lean"))
    );
    assert_eq!(
        std::fs::read(root.join("lake-manifest.json")).unwrap(),
        previous
    );
}

#[derive(Debug)]
enum UpdateLoaderError {
    Resolution(fln_lake::LakeUpdateError),
    Source {
        class: &'static str,
        declaration: &'static str,
    },
}

impl From<fln_lake::LakeUpdateError> for UpdateLoaderError {
    fn from(error: fln_lake::LakeUpdateError) -> Self {
        Self::Resolution(error)
    }
}

#[test]
fn local_update_preserves_loader_errors_and_bounds_source_and_returned_requirements() {
    let root = fresh_temp_dir("update-lean-errors");
    std::fs::write(root.join("lakefile.lean"), "package example\n").unwrap();
    fln_lake::Manifest::new("previous")
        .save_to_dir(&root)
        .unwrap();
    let previous = std::fs::read(root.join("lake-manifest.json")).unwrap();
    let failed = fln_lake::update_manifest_with_lean(&root, |_, bytes| {
        assert_eq!(bytes, b"package example\n");
        Err(UpdateLoaderError::Source {
            class: "resource",
            declaration: "choosePackage",
        })
    });
    assert!(matches!(
        failed,
        Err(UpdateLoaderError::Source {
            class: "resource",
            declaration: "choosePackage"
        })
    ));
    let oversized = fln_lake::update_manifest_with_lean::<UpdateLoaderError>(&root, |_, _| {
        let mut config = update_checked_lean("example", &[("leaf", "../leaf")]);
        config.requires = vec![config.requires[0].clone(); 4097];
        Ok(config)
    });
    assert!(
        matches!(oversized, Err(UpdateLoaderError::Resolution(fln_lake::LakeUpdateError::Resource(detail)))
        if detail.contains("requirement count exceeds 4096"))
    );
    let remote = fln_lake::update_manifest_with_lean::<UpdateLoaderError>(&root, |_, _| {
        let mut config = update_checked_lean("example", &[("remote", "../unused")]);
        config.requires[0].url = Some("https://example.invalid/repository".to_owned());
        Ok(config)
    });
    assert!(
        matches!(remote, Err(UpdateLoaderError::Resolution(fln_lake::LakeUpdateError::DependencyResolutionUnavailable { requirements }))
        if requirements == ["remote"])
    );
    std::fs::write(root.join("lakefile.lean"), " ".repeat(64 * 1024 + 1)).unwrap();
    let bounded = fln_lake::update_manifest_with_lean::<UpdateLoaderError>(&root, |_, _| {
        panic!("oversized source must not reach the loader")
    });
    assert!(
        matches!(bounded, Err(UpdateLoaderError::Resolution(fln_lake::LakeUpdateError::Resource(detail)))
        if detail.contains("65536 bytes"))
    );
    assert_eq!(
        std::fs::read(root.join("lake-manifest.json")).unwrap(),
        previous
    );
}
