//! Unit and integration tests for fln-lake configuration discovery, TOML parsing,
//! package initialization, and clean operations.

#![forbid(unsafe_code)]

use std::path::PathBuf;
use fln_lake::{
    clean, init_package, new_package, validate_package_name, LakeCleanError, LakeConfig,
    LakeConfigFormat, LakeInitError, LakeParseError,
};

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
    for reserved in ["init", "lean", "lake", "main", "Init", "LEAN", "Lake", "MAIN"] {
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
    let pkg_dir = new_package(&parent, "calc_app", None, LakeConfigFormat::Toml)
        .expect("create new package");
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

    let manifest = fln_lake::update_manifest(&dir).expect("update manifest");
    assert_eq!(manifest.name, "math_project");
    assert_eq!(manifest.version, "1.1.0");
    assert_eq!(manifest.packages.len(), 1);
    assert_eq!(manifest.packages[0].name, "mathlib");
    assert_eq!(
        manifest.packages[0].url.as_deref(),
        Some("https://github.com/leanprover-community/mathlib4.git")
    );
    assert_eq!(manifest.packages[0].rev.as_deref(), Some("v4.32.0"));

    // Verify written lake-manifest.json
    let loaded = fln_lake::Manifest::load_from_dir(&dir)
        .expect("load manifest")
        .expect("manifest exists");
    assert_eq!(loaded.name, "math_project");
    assert_eq!(loaded.packages.len(), 1);
    assert_eq!(loaded.packages[0].name, "mathlib");

    // Test parse_json with version 7 integer format for backwards compatibility
    let v7_json = r#"{"version": 7, "packagesDir": ".lake/packages", "packages": [], "name": "legacy_pkg", "lakeDir": ".lake"}"#;
    let parsed_v7 = fln_lake::Manifest::parse_json(v7_json).expect("parse v7 manifest");
    assert_eq!(parsed_v7.name, "legacy_pkg");
    assert_eq!(parsed_v7.version, "7");
    assert_eq!(parsed_v7.packages.len(), 0);
}

