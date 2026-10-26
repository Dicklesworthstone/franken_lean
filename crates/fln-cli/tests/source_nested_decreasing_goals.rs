//! A nested recursive call (`ack x (ack (x+1) y)`) is its own decreasing goal, and its proof is an
//! argument in the outer call's goal: at the pin that argument is the nested goal's metavariable
//! (`mkDecreasingProof`, vendored `Lean/Elab/PreDefinition/WF/Fix.lean`), so a proof script that
//! proves the nested call first works on the outer goal with that proof in place, not over an open
//! hole. Through `fln check-source` over `prelude`, `Init.WFTactics` and `Init.Omega`. Every
//! program is compared with the pinned `lean` v4.32.0 whenever it is present. The definition is
//! `noncomputable`: its termination proof is elaborated as for a compiled one, and under this
//! header this engine does not yet compile a well-founded definition the pin compiles.
#![forbid(unsafe_code)]

use std::path::{Path, PathBuf};
use std::process::Command;

const HEADER: &str = "prelude\nimport Init.WFTactics\nimport Init.Omega\n";

const ACKERMANN: &str = "noncomputable def ack : Nat → Nat → Nat\n  | 0,   y   => y+1\n  | x+1, 0   => ack x 1\n  \
     | x+1, y+1 => ack x (ack (x+1) y)\n";

/// Accepted at the pin and here: `ACKERMANN` followed by each suffix.
const ACCEPTED: &[(&str, &str)] = &[
    ("inferred_measure", ""),
    ("default_tactic", "termination_by x y => (x, y)\n"),
    (
        "tactic_per_goal",
        "termination_by x y => (x, y)\ndecreasing_by\n  · decreasing_tactic\n  \
         · decreasing_tactic\n  · decreasing_tactic\n",
    ),
    (
        "tactic_on_all_goals",
        "termination_by x y => (x, y)\ndecreasing_by\n  all_goals decreasing_tactic\n",
    ),
    (
        "simp_on_each_goal",
        "termination_by x y => (x, y)\ndecreasing_by\n  · (try simp)\n    sorry\n  \
         · (try simp)\n    sorry\n  · (try simp)\n    sorry\n",
    ),
];

fn pinned_lib() -> Option<PathBuf> {
    let lib = std::env::var_os("FLN_REFERENCE_LIB")
        .map(PathBuf::from)
        .or_else(|| {
            std::env::var_os("HOME").map(|home| {
                PathBuf::from(home)
                    .join(".elan/toolchains")
                    .join(format!("leanprover--lean4---{}", fln::OLEAN_PIN_TAG))
                    .join("lib/lean")
            })
        })
        .filter(|lib| lib.join("Init/Omega.olean").is_file());
    assert!(
        lib.is_some() || std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
        "the pinned Reference library is required"
    );
    if lib.is_none() {
        eprintln!("SKIP: pinned Reference lib/lean absent");
    }
    lib
}

fn workspace() -> PathBuf {
    let path = std::env::temp_dir().join(format!(
        "fln-nested-decreasing-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos(),
    ));
    std::fs::create_dir(&path).unwrap();
    path
}

/// `fln check-source` on `HEADER` + `program`, and the pinned binary's exit code when present.
fn check(lib: &Path, root: &Path, name: &str, program: &str) -> (i32, String, Option<i32>) {
    let entry = root.join(format!("{name}.lean"));
    std::fs::write(&entry, format!("{HEADER}{program}")).unwrap();
    let theirs = lib
        .parent()
        .and_then(Path::parent)
        .map(|toolchain| toolchain.join("bin/lean"))
        .filter(|lean| lean.is_file())
        .map(|pinned| {
            Command::new(pinned)
                .arg(&entry)
                .env("LEAN_PATH", lib)
                .output()
                .expect("run the pinned lean")
                .status
                .code()
                .expect("normal pinned exit")
        });
    let ours = Command::new(env!("CARGO_BIN_EXE_fln"))
        .arg("check-source")
        .arg(&entry)
        .env("LEAN_PATH", lib)
        .env("FLN_IMPORT_REUSE_DIR", root.join("records"))
        .output()
        .expect("run the installed CLI");
    (
        ours.status.code().expect("normal process exit"),
        String::from_utf8_lossy(&ours.stderr).into_owned(),
        theirs,
    )
}

#[test]
fn a_nested_call_proof_is_its_own_goal_in_the_outer_goal() {
    let Some(lib) = pinned_lib() else {
        return;
    };
    // One workspace, so the import closure is admitted once for every program.
    let root = workspace();
    for (name, suffix) in ACCEPTED {
        let program = format!("{ACKERMANN}{suffix}");
        let (code, stderr, pinned) = check(&lib, &root, name, &program);
        assert_eq!(code, 0, "{name}: {program}\n{stderr}");
        assert_eq!(pinned.unwrap_or(0), 0, "{name}: the pinned lean rejects it");
    }
}
