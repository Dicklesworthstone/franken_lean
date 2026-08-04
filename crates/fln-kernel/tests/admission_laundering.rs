//! `admission_laundering` — the KR-986 fixtures (bead `franken_lean-79k`, §12):
//! every forbidden path into kernel acceptance carries a mechanical proof, not
//! an argument. Compile-fail probes (a capability forge outside the kernel
//! crate does not compile), source censuses (no serialization path exists), and
//! runtime controls (a forged verdict is data with no transition).
//!
//! The compile-fail harness drives the pinned rustc directly on a tiny probe
//! crate, so the refusal is the compiler's own error text, never a comment
//! claiming the refusal exists.

#![forbid(unsafe_code)]

use std::path::{Path, PathBuf};
use std::process::Command;

use fln_core::expr::{Expr, Literal, NatLit};
use fln_core::level::Level;
use fln_core::name::Name;
use fln_core::outcome::Outcome;
use fln_core::scratch::{ADMISSION_PROBE_PREFIX, ScratchRoot};
use fln_env::constants::{AxiomVal, ConstantVal};
use fln_env::environment::Environment;
use fln_kernel::Declaration;
use fln_kernel::capability::{Admitted, admit};
use fln_kernel::verdict::Budget;

fn rustc() -> PathBuf {
    std::env::var_os("RUSTC")
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from("rustc"))
}

fn deps_dir() -> PathBuf {
    std::env::var_os("CARGO_TARGET_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from("target"))
        .join("debug/deps")
}

fn newest_rlib(crate_name: &str) -> PathBuf {
    let deps = deps_dir();
    let prefix = format!("lib{crate_name}-");
    let mut candidates: Vec<PathBuf> = std::fs::read_dir(&deps)
        .unwrap_or_else(|error| panic!("deps dir {} must be readable: {error}", deps.display()))
        .filter_map(|entry| {
            let path = entry.ok()?.path();
            let name = path.file_name()?.to_str()?.to_string();
            (name.starts_with(&prefix) && name.ends_with(".rlib")).then_some(path)
        })
        .collect();
    candidates.sort();
    candidates
        .pop()
        .unwrap_or_else(|| panic!("{crate_name} rlib must exist in {}", deps.display()))
}

/// Compile `source` as a library crate against the kernel's rlib and return the
/// compiler's (status, stderr). The refusal must be the compiler's own words.
fn try_compile(root: &Path, name: &str, source: &str) -> (bool, String) {
    let probe = root.join(format!("{name}.rs"));
    std::fs::write(&probe, source).expect("write the probe crate");
    let kernel_rlib = newest_rlib("fln_kernel");
    let env_rlib = newest_rlib("fln_env");
    let output = Command::new(rustc())
        .arg("--edition")
        .arg("2024")
        .arg("--crate-type")
        .arg("lib")
        .arg("--extern")
        .arg(format!("fln_kernel={}", kernel_rlib.display()))
        .arg("--extern")
        .arg(format!("fln_env={}", env_rlib.display()))
        .arg("-L")
        .arg(format!("dependency={}", deps_dir().display()))
        .arg(&probe)
        .arg("-o")
        .arg(root.join("probe.rlib"))
        .output()
        .expect("the pinned rustc must run");
    let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
    (output.status.success(), stderr)
}

#[test]
fn an_external_forge_of_the_capability_does_not_compile() {
    let root = ScratchRoot::create(ADMISSION_PROBE_PREFIX, "admission-probe", "forge")
        .expect("create probe root");
    let (success, stderr) = try_compile(
        &root,
        "forge",
        r#"
extern crate fln_kernel;
extern crate fln_env;

pub fn forge(base: &fln_env::environment::Environment, decl: fln_kernel::Declaration) {
    let _ = fln_kernel::capability::CheckedDecl { base, decl, consumption: todo!(), budget: todo!(), _seal: todo!() };
}
"#,
    );
    assert!(
        !success,
        "the capability forge compiled — the seal is broken"
    );
    assert!(
        stderr.contains("private") || stderr.contains("cannot construct"),
        "the refusal must be about inexpressibility, got: {stderr}"
    );
}

#[test]
fn an_external_clone_of_the_capability_does_not_compile() {
    let root = ScratchRoot::create(ADMISSION_PROBE_PREFIX, "admission-probe", "clone")
        .expect("create probe root");
    let (success, stderr) = try_compile(
        &root,
        "clone",
        r#"
extern crate fln_kernel;

pub fn clone_it(capability: fln_kernel::capability::CheckedDecl<'_>) {
    let _ = capability.clone();
}
"#,
    );
    assert!(
        !success,
        "cloning the capability compiled — replay is expressible"
    );
    assert!(
        stderr.contains("no method named `clone`"),
        "the refusal must name the missing method, got: {stderr}"
    );
}

#[test]
fn no_serialization_path_exists_for_the_capability() {
    // A capability that cannot be serialized cannot arrive by mail. This is a
    // census, not an argument: no serde derive anywhere in the capability's
    // module, and no serde anywhere in the kernel crate's manifest.
    let manifest_dir = std::env::var_os("CARGO_MANIFEST_DIR")
        .map(PathBuf::from)
        .expect("cargo identifies the invoking crate directory");
    let capability = std::fs::read_to_string(manifest_dir.join("src/capability.rs"))
        .expect("capability.rs must be readable");
    assert!(
        !capability.contains("Serialize") && !capability.contains("Deserialize"),
        "a serialization path appeared in the capability module"
    );
    let manifest = std::fs::read_to_string(manifest_dir.join("Cargo.toml"))
        .expect("Cargo.toml must be readable");
    assert!(
        !manifest.contains("serde"),
        "a serde dependency appeared in the kernel crate's manifest"
    );
}

#[test]
fn a_forged_verdict_carries_no_authority() {
    // A `Verdict::Accepted` value is just data: it cannot be turned into a
    // capability by any path — the only mint is `admit` on a declaration the
    // kernel actually checked. The control: a malformed declaration never
    // yields the capability, so even the real mint cannot be laundered with
    // false premises.
    let env = Environment::new();
    let wrong = Declaration::Axiom(AxiomVal {
        base: ConstantVal {
            name: Name::str(Name::anonymous(), "Forged"),
            level_params: vec![],
            // Not a sort: an axiom whose "type" is a Nat literal fails the
            // preamble that the type itself checks to a sort.
            type_: Expr::lit(Literal::Nat(NatLit::from_u64(42))),
        },
        is_unsafe: false,
    });
    match admit(&env, wrong, Budget::DEFAULT) {
        Outcome::Complete(Admitted::Rejected { class, message, .. }) => {
            assert!(
                !message.is_empty(),
                "the rejection must carry its reason; class {class:?}"
            );
        }
        other => match other {
            Outcome::Complete(Admitted::Accepted(_)) => {
                panic!("a malformed declaration was admitted with a capability")
            }
            Outcome::Inconclusive(reason) => {
                panic!(
                    "a malformed declaration returned inconclusive instead of rejected: {reason:?}"
                )
            }
            Outcome::InternalFault(fault) => {
                panic!("a malformed declaration faulted instead of rejected: {fault:?}")
            }
            Outcome::Complete(Admitted::Rejected { .. }) => {
                unreachable!("the match above already handled the rejected arm")
            }
        },
    }
}

#[test]
fn starvation_mints_no_capability() {
    // The non-promotion half (KR-987): a starved budget is a non-answer and
    // mints nothing — the arm is Inconclusive-shaped, never Accepted.
    let env = Environment::new();
    let starved = Budget::DEFAULT.narrowed(0, Budget::DEFAULT.depth);
    let decl = Declaration::Axiom(AxiomVal {
        base: ConstantVal {
            name: Name::str(Name::anonymous(), "Starved"),
            level_params: vec![],
            type_: Expr::sort(Level::one()),
        },
        is_unsafe: false,
    });
    if let Outcome::Complete(Admitted::Accepted(_)) = admit(&env, decl, starved) {
        panic!("an exhausted check minted a publication capability");
    }
}
