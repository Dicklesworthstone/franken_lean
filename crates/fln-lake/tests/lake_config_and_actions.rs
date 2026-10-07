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
