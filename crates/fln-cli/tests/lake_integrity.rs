//! Installed-command controls: configuration is not compilation or provenance.
#![forbid(unsafe_code)]
use std::{
    path::PathBuf,
    process::Command,
    sync::atomic::{AtomicUsize, Ordering},
};
static NEXT: AtomicUsize = AtomicUsize::new(0);

/// A package root removed on drop, so the passing path leaves nothing behind.
struct Package(PathBuf);

impl std::ops::Deref for Package {
    type Target = PathBuf;
    fn deref(&self) -> &PathBuf {
        &self.0
    }
}

impl Drop for Package {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

fn package(config: &str) -> Package {
    let dir = std::env::temp_dir().join(format!(
        "fln-lake-integrity-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::create_dir(&dir).unwrap();
    std::fs::write(dir.join("lakefile.toml"), config).unwrap();
    Package(dir)
}

#[test]
fn lake_build_never_reports_success_without_a_compiler() {
    let dir = package("name = \"honest\"\ndefaultTargets = [\"Honest\"]\n");
    for source in [
        "def answer : Nat := 42\n",
        "this is not Lean\n",
        "theorem bad : False := by rfl\n",
    ] {
        std::fs::write(dir.join("Honest.lean"), source).unwrap();
        for json in [false, true] {
            let mut cmd = Command::new(env!("CARGO_BIN_EXE_lake"));
            cmd.arg("--dir").arg(&*dir);
            if json {
                cmd.arg("--json");
            }
            let out = cmd.arg("build").output().unwrap();
            assert_eq!(out.status.code(), Some(1), "{out:?}");
            assert!(out.stdout.is_empty(), "{out:?}");
            let err = String::from_utf8(out.stderr).unwrap();
            assert!(err.contains("unavailable"), "{err}");
            if json {
                assert!(err.contains("\"status\":\"unsupported\""), "{err}");
                assert!(!err.contains("targets_cached"), "{err}");
            }
            assert!(!dir.join(".lake").exists());
        }
    }
}

#[test]
fn stale_or_forged_artifacts_cannot_authorize_builds_or_cache_reports() {
    let dir = package("name = \"honest\"\ndefaultTargets = [\"Honest\"]\n");
    std::fs::create_dir_all(dir.join(".lake/build/lib")).unwrap();
    let artifact = dir.join(".lake/build/lib/Honest.olean");
    for bytes in [
        b"fln-olean-artifact:Honest".as_slice(),
        b"previous output must survive",
    ] {
        std::fs::write(&artifact, bytes).unwrap();
        for source in [
            "def answer : Nat := 2\n",
            "-- fln-interface-change\naxiom a : Nat\n",
            "def answer : Nat := 1\n",
        ] {
            std::fs::write(dir.join("Honest.lean"), source).unwrap();
            let build = Command::new(env!("CARGO_BIN_EXE_lake"))
                .arg("--dir")
                .arg(&*dir)
                .args(["--json", "build", "Honest"])
                .output()
                .unwrap();
            assert_eq!(build.status.code(), Some(1), "{build:?}");
            assert!(build.stdout.is_empty());
            for faithful in [false, true] {
                let mut cmd = Command::new(env!("CARGO_BIN_EXE_fln"));
                cmd.args(["build", "explain", "--json", "--dir"]).arg(&*dir);
                if faithful {
                    cmd.arg("--faithful-invalidation");
                }
                let out = cmd.output().unwrap();
                assert_eq!(out.status.code(), Some(1), "{out:?}");
                assert!(out.stdout.is_empty());
                let err = String::from_utf8(out.stderr).unwrap();
                assert!(err.contains("\"status\":\"unsupported\""), "{err}");
                for invented in [
                    "\"cache_outcome\"",
                    "\"reference_decision\"",
                    "\"native_decision\"",
                ] {
                    assert!(!err.contains(invented), "{err}");
                }
            }
            assert_eq!(std::fs::read(&artifact).unwrap(), bytes);
        }
    }
}

#[test]
fn check_build_only_tests_explicit_default_target_presence() {
    // Pinned Lake/CLI/Help.lean: no target-name or source validation is promised.
    for (config, code) in [
        ("name = \"p\"\n", 1),
        ("name = \"p\"\ndefaultTargets = []\n", 1),
        ("name = \"p\"\ndefaultTargets = [\"absent\"]\n", 0),
    ] {
        let dir = package(config);
        let out = Command::new(env!("CARGO_BIN_EXE_lake"))
            .arg("--dir")
            .arg(&*dir)
            .arg("check-build")
            .output()
            .unwrap();
        assert_eq!(out.status.code(), Some(code), "{config}: {out:?}");
        assert!(out.stdout.is_empty(), "{out:?}");
        assert!(!dir.join(".lake").exists());
        let extra = Command::new(env!("CARGO_BIN_EXE_lake"))
            .arg("--dir")
            .arg(&*dir)
            .args(["check-build", "extra"])
            .output()
            .unwrap();
        assert_eq!(extra.status.code(), Some(1), "{extra:?}");
    }
}

#[test]
fn lean_configuration_is_not_invented_from_directory_name() {
    let root = package("name = \"holder\"\n");
    let dir = root.join("lean_config");
    std::fs::create_dir(&dir).unwrap();
    std::fs::write(dir.join("lakefile.lean"), "not a valid lakefile\n").unwrap();
    for command in ["check-build", "build"] {
        let out = Command::new(env!("CARGO_BIN_EXE_lake"))
            .arg("--dir")
            .arg(&*dir)
            .arg(command)
            .output()
            .unwrap();
        assert_eq!(out.status.code(), Some(1), "{out:?}");
        assert!(out.stdout.is_empty());
        assert!(
            String::from_utf8_lossy(&out.stderr).contains("unavailable"),
            "{out:?}"
        );
        assert!(!dir.join(".lake").exists());
    }
}
