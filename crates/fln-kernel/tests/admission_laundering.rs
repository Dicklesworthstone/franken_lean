//! `admission_laundering` — the KR-986 fixtures (bead `franken_lean-79k`, §12):
//! every forbidden path into kernel acceptance carries a mechanical proof, not
//! an argument. Compile-fail probes (a capability forge outside the kernel
//! crate does not compile), source censuses (no serialization path exists), and
//! runtime controls (a forged verdict is data with no transition).
//!
//! The compile-fail harness builds a fresh external crate against this checkout
//! with Cargo and its pinned compiler. Refusals must be the compiler's own
//! error text, and a compiling public-API control prevents hollow passes.

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

/// Compile a fresh external crate against this checkout. Cargo owns artifact
/// discovery: neither its output layout nor a stale sibling rlib may choose
/// which version of the capability surface the probe actually checks.
fn try_compile(root: &Path, name: &str, source: &str) -> (bool, String) {
    let kernel = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let environment = kernel.parent().expect("workspace crates").join("fln-env");
    let quote_path = |path: &Path| {
        path.to_str()
            .expect("Cargo manifest paths must be UTF-8")
            .replace('\\', "\\\\")
            .replace('"', "\\\"")
            .replace('\n', "\\n")
            .replace('\r', "\\r")
    };
    let manifest = format!(
        "[package]\nname = \"admission_probe_{name}\"\nversion = \"0.0.0\"\nedition = \"2024\"\n\n\
         [workspace]\n\n[lib]\npath = \"probe.rs\"\n\n\
         [dependencies]\nfln-kernel = {{ path = \"{}\" }}\nfln-env = {{ path = \"{}\" }}\n",
        quote_path(&kernel),
        quote_path(&environment),
    );
    std::fs::write(root.join("probe.rs"), source).expect("write the probe crate");
    std::fs::write(root.join("Cargo.toml"), manifest).expect("write probe manifest");
    let cargo = std::env::var_os("CARGO").expect("Cargo identifies the pinned driver");
    let output = Command::new(cargo)
        .current_dir(&kernel)
        .args(["check", "--offline", "--quiet", "--manifest-path"])
        .arg(root.join("Cargo.toml"))
        .arg("--target-dir")
        .arg(root.join("target"))
        .output()
        .expect("the pinned compiler driver must run");
    let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
    (output.status.success(), stderr)
}

#[test]
fn an_external_public_capability_consumer_compiles() {
    let root = ScratchRoot::create(ADMISSION_PROBE_PREFIX, "admission-probe", "public")
        .expect("create probe root");
    let (success, stderr) = try_compile(
        &root,
        "public",
        "pub fn consume(_: fln_kernel::capability::CheckedDecl<'_>) {}",
    );
    assert!(success, "the public control must compile: {stderr}");
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
    // The control must be rejected by the real admission authority.
    let env = Environment::new();
    let wrong = Declaration::Axiom(AxiomVal {
        base: ConstantVal {
            name: Name::str(Name::anonymous(), "Forged"),
            level_params: vec![],
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
