#![forbid(unsafe_code)]

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::atomic::{AtomicU64, Ordering};

static NEXT_TEMP: AtomicU64 = AtomicU64::new(0);

struct TempRepo {
    path: PathBuf,
}

impl TempRepo {
    fn new() -> Self {
        let serial = NEXT_TEMP.fetch_add(1, Ordering::Relaxed);
        let path =
            std::env::temp_dir().join(format!("fln-agent-anchor-{}-{serial}", std::process::id()));
        let _ = fs::remove_dir_all(&path);
        fs::create_dir_all(&path).expect("create temporary repository");
        git(&path, ["init", "--quiet"]);
        git(&path, ["config", "user.name", "FrankenLean test"]);
        git(&path, ["config", "user.email", "test@frankenlean.invalid"]);
        Self { path }
    }

    fn write(&self, relative: &str, contents: &str) {
        let path = self.path.join(relative);
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent).expect("create fixture directory");
        }
        fs::write(path, contents).expect("write fixture");
    }

    fn commit_all(&self, message: &str) {
        git(&self.path, ["add", "."]);
        git(&self.path, ["commit", "--quiet", "-m", message]);
    }
}

impl Drop for TempRepo {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
}

fn git<const N: usize>(repo: &Path, args: [&str; N]) -> String {
    let output = Command::new("git")
        .arg("-C")
        .arg(repo)
        .args(args)
        .output()
        .expect("launch git");
    assert!(
        output.status.success(),
        "git failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8(output.stdout)
        .expect("git output is UTF-8")
        .trim()
        .to_owned()
}

fn anchor(repo: &Path, extra: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_fln-agent-anchor"))
        .arg("--repo")
        .arg(repo)
        .args(["--bead", "fln-test", "--owner", "integration-test"])
        .args(extra)
        .output()
        .expect("launch fln-agent-anchor")
}

#[test]
fn clean_and_dirty_git_identities_are_reported_without_ambiguity() {
    let repo = TempRepo::new();
    repo.write("crates/demo/src/lib.rs", "pub const VALUE: u8 = 1;\n");
    repo.commit_all("fixture");

    let head = git(&repo.path, ["rev-parse", "HEAD"]);
    let tree = git(&repo.path, ["rev-parse", "HEAD^{tree}"]);
    let blob = git(&repo.path, ["rev-parse", "HEAD:crates/demo/src/lib.rs"]);
    let clean = anchor(&repo.path, &["--path", "crates/demo/src/lib.rs"]);
    assert!(
        clean.status.success(),
        "clean anchor failed: {}",
        String::from_utf8_lossy(&clean.stderr)
    );
    let clean = String::from_utf8(clean.stdout).expect("anchor output is UTF-8");
    assert!(clean.contains("\"schema\":\"fln.agent-anchor/1\""));
    assert!(clean.contains(&format!("\"head\":\"{head}\"")));
    assert!(clean.contains(&format!("\"tree\":\"{tree}\"")));
    assert!(clean.contains(&format!("\"head_blob\":\"{blob}\"")));
    assert!(clean.contains(&format!("\"worktree_blob\":\"{blob}\"")));
    assert!(clean.contains("\"dirty\":false"));

    repo.write("crates/demo/src/lib.rs", "pub const VALUE: u8 = 2;\n");
    let refused = anchor(&repo.path, &["--path", "crates/demo/src/lib.rs"]);
    assert_eq!(refused.status.code(), Some(2));
    assert!(
        String::from_utf8_lossy(&refused.stderr).contains("working tree is dirty"),
        "unexpected refusal: {}",
        String::from_utf8_lossy(&refused.stderr)
    );

    let dirty = anchor(
        &repo.path,
        &["--allow-dirty", "--path", "./crates/demo/src/lib.rs"],
    );
    assert!(
        dirty.status.success(),
        "dirty anchor failed: {}",
        String::from_utf8_lossy(&dirty.stderr)
    );
    let dirty = String::from_utf8(dirty.stdout).expect("anchor output is UTF-8");
    let worktree_blob = git(&repo.path, ["hash-object", "--", "crates/demo/src/lib.rs"]);
    assert_ne!(blob, worktree_blob, "the fixture must actually be dirty");
    assert!(dirty.contains(&format!("\"head_blob\":\"{blob}\"")));
    assert!(dirty.contains(&format!("\"worktree_blob\":\"{worktree_blob}\"")));
    assert!(dirty.contains("\"dirty\":true"));
}

#[test]
fn untracked_and_escaping_paths_are_refused() {
    let repo = TempRepo::new();
    repo.write("tracked.txt", "tracked\n");
    repo.commit_all("fixture");
    repo.write("untracked.txt", "untracked\n");

    let dirty = anchor(&repo.path, &["--allow-dirty", "--path", "untracked.txt"]);
    assert_eq!(dirty.status.code(), Some(2));
    assert!(String::from_utf8_lossy(&dirty.stderr).contains("ls-files"));

    let escaping = anchor(&repo.path, &["--allow-dirty", "--path", "../outside"]);
    assert_eq!(escaping.status.code(), Some(2));
    assert!(String::from_utf8_lossy(&escaping.stderr).contains("escapes the repository"));
}
