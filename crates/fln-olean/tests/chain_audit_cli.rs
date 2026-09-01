#![forbid(unsafe_code)]

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::atomic::{AtomicU64, Ordering};

static NEXT_TEMP: AtomicU64 = AtomicU64::new(0);

struct TempDir {
    path: PathBuf,
}

impl TempDir {
    fn new() -> Self {
        let serial = NEXT_TEMP.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir().join(format!(
            "fln-olean-chain-audit-{}-{serial}",
            std::process::id()
        ));
        let _ = fs::remove_dir_all(&path);
        fs::create_dir_all(&path).expect("create temporary directory");
        Self { path }
    }

    fn write(&self, name: &str, bytes: &[u8]) -> PathBuf {
        let path = self.path.join(name);
        fs::write(&path, bytes).expect("write artifact fixture");
        path
    }
}

impl Drop for TempDir {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
}

fn audit(exported: &Path, server: &Path, private: &Path, extra: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_fln-olean-chain-audit"))
        .args(extra)
        .arg(exported)
        .arg(server)
        .arg(private)
        .output()
        .expect("launch fln-olean-chain-audit")
}

#[test]
fn byte_ceiling_refuses_the_triplet_before_format_parsing() {
    let temp = TempDir::new();
    let exported = temp.write("Demo.olean", &[0; 8]);
    let server = temp.write("Demo.olean.server", &[1; 8]);
    let private = temp.write("Demo.olean.private", &[2; 8]);

    let output = audit(
        &exported,
        &server,
        &private,
        &["--json", "--max-bytes", "23"],
    );
    assert_eq!(output.status.code(), Some(3));
    assert!(output.stdout.is_empty(), "errors belong on stderr");
    let stderr = String::from_utf8(output.stderr).expect("stderr is UTF-8");
    assert!(stderr.contains("\"schema\":\"fln.olean-chain-audit/1\""));
    assert!(stderr.contains("\"status\":\"error\""));
    assert!(stderr.contains("over the 23-byte ceiling"));
    assert!(stderr.contains("no artifact bytes were read"));
}

#[test]
fn malformed_artifacts_are_not_misreported_as_a_resource_stop() {
    let temp = TempDir::new();
    let exported = temp.write("Demo.olean", b"not an olean");
    let server = temp.write("Demo.olean.server", b"still not an olean");
    let private = temp.write("Demo.olean.private", b"also not an olean");

    let output = audit(&exported, &server, &private, &["--json"]);
    assert_eq!(output.status.code(), Some(3));
    let stderr = String::from_utf8(output.stderr).expect("stderr is UTF-8");
    assert!(stderr.contains("\"status\":\"error\""));
    assert!(stderr.contains("decode chain"));
    assert!(!stderr.contains("over the"));
}

#[test]
fn usage_errors_are_distinct_from_audited_artifact_errors() {
    let output = Command::new(env!("CARGO_BIN_EXE_fln-olean-chain-audit"))
        .arg("only-one-path.olean")
        .output()
        .expect("launch fln-olean-chain-audit");
    assert_eq!(output.status.code(), Some(2));
    assert!(
        String::from_utf8_lossy(&output.stderr).contains("expected exactly three artifact paths")
    );
}
