//! Shared fixture harness for the structure-guard integration suites.
//!
//! Both `seeded.rs` (one seeded violation per check) and `authority.rs` (the
//! `structure_authority_model` escape matrix) need a materialised workspace carrying the
//! COMPLETE plan crate map: `validate_constitutional_baseline` emits `FLN-STRUCT-024` for
//! every plan-defined crate a reviewed graph omits, so a trimmed-down fixture cannot be
//! used to test anything else.

#![forbid(unsafe_code)]
// Each suite uses a subset of the harness, and Cargo compiles this module separately into
// every test binary, so an item only `authority.rs` needs reads as dead code while
// building `seeded.rs` and vice versa.
#![allow(dead_code)]

use std::cell::RefCell;
use std::collections::BTreeMap;
use std::fs::{self, OpenOptions};
use std::io::Write;
use std::path::PathBuf;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{SystemTime, UNIX_EPOCH};

use structure_guard::checks::{self, RunOutcome};
use structure_guard::contract_inventory::{SCHEMA_DEFINITION, canonical_inventory_text};
use structure_guard::{
    ABI_TARGET_LAYOUT_FILE, CONTRACT_INVENTORY_FILE, CONTRACT_INVENTORY_POLICY_FILE,
    CONTRACT_INVENTORY_SCHEMA_FILE, EXTERN_BUILTIN_ENVIRONMENT_FILE, OLEAN_ILEAN_FORMAT_FILE,
    SUITE_LOCK_FILE,
};

/// An immutable workspace recipe. Every execution materializes a fresh, uniquely named
/// root and retains it for inspection, as required by the repository's no-deletion rule.
pub struct TempWs {
    tag: String,
    files: RefCell<BTreeMap<String, Vec<u8>>>,
}

impl TempWs {
    pub fn new(tag: &str) -> TempWs {
        TempWs {
            tag: tag.to_string(),
            files: RefCell::new(BTreeMap::new()),
        }
    }

    pub fn write(&self, rel: &str, content: &str) {
        self.write_bytes(rel, content.as_bytes());
    }

    /// Plant exact bytes. Needed for inputs that are deliberately not valid UTF-8: the
    /// guard's behaviour on an undecodable governed file is itself a contract.
    pub fn write_bytes(&self, rel: &str, content: &[u8]) {
        self.files
            .borrow_mut()
            .insert(rel.to_string(), content.to_vec());
    }

    /// Drop recipe entries whose workspace-relative path fails `keep`. Used to model a
    /// crate or a primary target that is absent rather than malformed.
    pub fn retain_paths(&self, keep: impl Fn(&str) -> bool) {
        self.files.borrow_mut().retain(|path, _| keep(path));
    }

    pub fn materialize(&self) -> Result<PathBuf, String> {
        static NEXT_ROOT: AtomicU64 = AtomicU64::new(0);
        let stamp = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map_err(|error| format!("system clock precedes Unix epoch: {error}"))?
            .as_nanos();
        let root = loop {
            let sequence = NEXT_ROOT.fetch_add(1, Ordering::Relaxed);
            let candidate = std::env::temp_dir().join(format!(
                "structure-guard-test-{}-{stamp}-{sequence}-{}",
                std::process::id(),
                self.tag
            ));
            match fs::create_dir(&candidate) {
                Ok(()) => break candidate,
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(error) => return Err(format!("create retained fixture root: {error}")),
            }
        };

        let mut files = self.files.borrow().clone();
        if !files.contains_key(CONTRACT_INVENTORY_FILE)
            && let (
                Some(suite_lock),
                Some(schema),
                Some(policy),
                Some(abi_target_layout),
                Some(olean_ilean_format),
                Some(extern_builtin_environment),
            ) = (
                files.get(SUITE_LOCK_FILE),
                files.get(CONTRACT_INVENTORY_SCHEMA_FILE),
                files.get(CONTRACT_INVENTORY_POLICY_FILE),
                files.get(ABI_TARGET_LAYOUT_FILE),
                files.get(OLEAN_ILEAN_FORMAT_FILE),
                files.get(EXTERN_BUILTIN_ENVIRONMENT_FILE),
            )
            && let (
                Ok(suite_lock),
                Ok(schema),
                Ok(policy),
                Ok(abi_target_layout),
                Ok(olean_ilean_format),
                Ok(extern_builtin_environment),
            ) = (
                std::str::from_utf8(suite_lock),
                std::str::from_utf8(schema),
                std::str::from_utf8(policy),
                std::str::from_utf8(abi_target_layout),
                std::str::from_utf8(olean_ilean_format),
                std::str::from_utf8(extern_builtin_environment),
            )
            && let Ok(inventory) = canonical_inventory_text(
                suite_lock,
                schema,
                policy,
                abi_target_layout,
                olean_ilean_format,
                extern_builtin_environment,
            )
        {
            files.insert(CONTRACT_INVENTORY_FILE.to_string(), inventory.into_bytes());
        }

        for (rel, content) in &files {
            let path = root.join(rel);
            let parent = path
                .parent()
                .ok_or_else(|| format!("fixture path has no parent: {rel}"))?;
            fs::create_dir_all(parent)
                .map_err(|error| format!("create fixture directories for {rel}: {error}"))?;
            let mut file = OpenOptions::new()
                .write(true)
                .create_new(true)
                .open(&path)
                .map_err(|error| format!("create fixture file {rel} without overwrite: {error}"))?;
            file.write_all(content)
                .map_err(|error| format!("write fixture file {rel}: {error}"))?;
        }
        eprintln!("retained structure-guard fixture: {}", root.display());
        Ok(root)
    }

    pub fn run(&self) -> RunOutcome {
        let root = self.materialize().expect("materialize retained fixture");
        checks::run(&root).expect("guard runs")
    }
}

pub const BASE_GRAPH: &str = "\
schema fln-workspace-graph/1
crate fln-core       rank=0  kind=ordinary
crate fln-hash       rank=1  kind=ordinary
crate fln-bignum     rank=1  kind=ordinary
crate fln-libm       rank=1  kind=ordinary
crate fln-unsafe-abi rank=2  kind=unsafe-boundary
crate fln-unsafe-region rank=2 kind=unsafe-boundary
crate fln-rt         rank=3  kind=ordinary
crate fln-env        rank=4  kind=ordinary
crate fln-olean      rank=5  kind=ordinary
crate fln-kernel     rank=6  kind=ordinary
crate fln-checker    rank=6  kind=ordinary
crate fln-syntax     rank=7  kind=ordinary
crate fln-parse      rank=8  kind=ordinary
crate fln-mid        rank=8  kind=ordinary
crate fln-elab       rank=9  kind=ordinary
crate fln-comp       rank=10 kind=ordinary
crate fln-vm         rank=11 kind=ordinary
crate fln-unsafe-jit rank=12 kind=unsafe-boundary
crate fln-verdict    rank=13 kind=ordinary
crate fln-anvil      rank=14 kind=ordinary
crate fln-ledger     rank=15 kind=ordinary
crate fln-lake       rank=16 kind=ordinary
crate fln-server     rank=17 kind=ordinary
crate fln-trace      rank=18 kind=ordinary
crate fln            rank=19 kind=ordinary
crate fln-hound      rank=20 kind=ordinary
crate fln-doc        rank=20 kind=ordinary
crate fln-mcp        rank=20 kind=ordinary
crate fln-tui        rank=20 kind=ordinary
crate fln-cli        rank=21 kind=ordinary
crate fln-wasm       rank=21 kind=ordinary
crate fln-conformance rank=22 kind=ordinary
prohibit fln-unsafe-* ->* fln-kernel
prohibit fln-unsafe-* ->* fln-checker
prohibit fln-kernel ->* fln-checker
prohibit fln-checker ->* fln-kernel
prohibit fln-checker ->* fln-olean
prohibit fln-checker ->* fln-rt
prohibit fln-checker ->* fln-unsafe-*
allow-direct fln-kernel = fln-core, fln-hash, fln-bignum, fln-env
allow-direct fln-checker = fln-core, fln-hash, fln-bignum
covenant fln-kernel max-loc=100
suite-dep asupersync
";

pub const EMPTY_LEDGER: &str = "schema fln-unsafe-ledger/1\n";

pub const TOOLCHAIN_PIN: &str = "[toolchain]\nchannel = \"nightly-2026-07-13\"\n";

pub const SUITE_LOCK_FIXTURE: &str = "\
schema fln-suite-lock/1
rust-nightly nightly-2026-07-13
rust-release 1.99.0-nightly
rust-commit 77cf889bc178ddb44d6a1c78e5a820b5abb31d8d
target x86_64-unknown-linux-gnu
suite asupersync commit=e464a484cb65c1a55be0d9c925e6e9c20318edcb path=/dp/asupersync
crate asupersync repo=asupersync
reference leanprover/lean4 tag=v4.32.0 commit=8c9756b28d64dab099da31a4c09229a9e6a2ef35 tree=ba16913719a2f6a15a826918fbe6ba9dd5413e91
corpus leanprover-community/mathlib4 tag=v4.32.0 commit=81a5d257c8e410db227a6665ed08f64fea08e997
";

pub const CONTRACT_INVENTORY_POLICY_FIXTURE: &str = "\
schema fln-contract-inventory-policy/1
row abi-layout:target:0001 kind=abi-layout support=required target-class=certified abi-class=lp64-le
row artifact-format:ilean kind=artifact-format support=required target-class=none abi-class=none
row artifact-format:olean:target:0001 kind=artifact-format support=required target-class=certified abi-class=lp64-le
row corpus kind=corpus support=required target-class=none abi-class=none
row environment-census:builtin kind=environment-census support=required target-class=none abi-class=none
row environment-census:extern kind=environment-census support=required target-class=none abi-class=none
row reference kind=reference support=required target-class=none abi-class=none
row suite:asupersync kind=suite support=required target-class=none abi-class=none
row target:0001 kind=target support=required target-class=certified abi-class=none
row toolchain kind=toolchain support=required target-class=none abi-class=none
";

pub const ABI_TARGET_LAYOUT_FIXTURE: &str =
    include_str!("../../../../contracts/ABI_TARGET_LAYOUT.txt");
pub const OLEAN_ILEAN_FORMAT_FIXTURE: &str =
    include_str!("../../../../contracts/OLEAN_ILEAN_FORMAT.txt");
pub const EXTERN_BUILTIN_ENVIRONMENT_FIXTURE: &str =
    include_str!("../../../../contracts/EXTERN_BUILTIN_ENVIRONMENT.txt");

fn fixture_hash_fields(domain: &str, fields: &[&[u8]]) -> u64 {
    let mut state = 0xcbf2_9ce4_8422_2325_u64;
    for byte in domain.as_bytes().iter().copied().chain(std::iter::once(0)) {
        state ^= u64::from(byte);
        state = state.wrapping_mul(0x0000_0100_0000_01b3);
    }
    for field in fields {
        for byte in (field.len() as u64)
            .to_le_bytes()
            .iter()
            .copied()
            .chain(field.iter().copied())
        {
            state ^= u64::from(byte);
            state = state.wrapping_mul(0x0000_0100_0000_01b3);
        }
    }
    state
}

/// Test-only mechanical expansion of the checked-in one-target ABI observation. Both
/// fixture targets use the same LP64 little-endian layout; target identities remain
/// opaque and are bound positionally by the production parser.
pub fn abi_target_layout_fixture(target_count: usize) -> String {
    assert!(target_count > 0, "fixture needs at least one target");
    let lines: Vec<_> = ABI_TARGET_LAYOUT_FIXTURE.lines().collect();
    let root_index = lines
        .iter()
        .position(|line| line.starts_with("target-root target:0001 "))
        .expect("fixture target root");
    let block_template = lines[4..root_index].join("\n") + "\n";
    let mut output = format!(
        "{}\n{}\n{}\ntarget-count {target_count}\n",
        lines[0], lines[1], lines[2]
    );
    for index in 1..=target_count {
        let key = format!("target:{index:04}");
        let block = block_template.replace("target:0001", &key);
        output.push_str(&block);
        let root = fixture_hash_fields("fln.abi-target-layout.target-root/1", &[block.as_bytes()]);
        output.push_str(&format!("target-root {key} fnv1a64:{root:016x}\n"));
    }
    let root = fixture_hash_fields(
        "fln.abi-target-layout.inventory-root/1",
        &[output.as_bytes()],
    );
    output.push_str(&format!("inventory-root fnv1a64:{root:016x}\n"));
    output
}

/// Test-only mechanical expansion of the checked-in exact-format observation. Each
/// synthetic OLEAN target reuses the pinned LP64 little-endian format facts while
/// receiving its own target identity and recomputed section/inventory roots.
pub fn olean_ilean_format_fixture(target_count: usize) -> String {
    assert!(target_count > 0, "fixture needs at least one target");
    let lines: Vec<_> = OLEAN_ILEAN_FORMAT_FIXTURE.lines().collect();
    let count_index = lines
        .iter()
        .position(|line| line.starts_with("target-count "))
        .expect("fixture target count");
    let olean_start = lines
        .iter()
        .position(|line| line.starts_with("section olean:target:0001 "))
        .expect("fixture OLEAN section");
    let olean_root = lines
        .iter()
        .position(|line| line.starts_with("section-root olean:target:0001 "))
        .expect("fixture OLEAN section root");
    assert_eq!(
        olean_root + 1,
        lines.len() - 1,
        "one-target fixture must end with its OLEAN root and inventory root"
    );

    let mut output = format!(
        "{}\ntarget-count {target_count}\n{}\n",
        lines[..count_index].join("\n"),
        lines[count_index + 1..olean_start].join("\n")
    );
    let block_template = format!("{}\n", lines[olean_start..olean_root].join("\n"));
    for index in 1..=target_count {
        let key = format!("target:{index:04}");
        let block = block_template.replace("target:0001", &key);
        output.push_str(&block);
        let root =
            fixture_hash_fields("fln.olean-ilean-format.section-root/1", &[block.as_bytes()]);
        output.push_str(&format!("section-root olean:{key} fnv1a64:{root:016x}\n"));
    }
    let root = fixture_hash_fields(
        "fln.olean-ilean-format.inventory-root/1",
        &[output.as_bytes()],
    );
    output.push_str(&format!("inventory-root fnv1a64:{root:016x}\n"));
    output
}

/// The crates every base fixture materializes (name, is-boundary) — must stay in
/// lockstep with BASE_GRAPH and base().
pub const FIXTURE_CRATES: [(&str, bool); 32] = [
    ("fln-core", false),
    ("fln-hash", false),
    ("fln-bignum", false),
    ("fln-libm", false),
    ("fln-unsafe-abi", true),
    ("fln-unsafe-region", true),
    ("fln-rt", false),
    ("fln-env", false),
    ("fln-olean", false),
    ("fln-kernel", false),
    ("fln-checker", false),
    ("fln-syntax", false),
    ("fln-parse", false),
    ("fln-mid", false),
    ("fln-elab", false),
    ("fln-comp", false),
    ("fln-vm", false),
    ("fln-unsafe-jit", true),
    ("fln-verdict", false),
    ("fln-anvil", false),
    ("fln-ledger", false),
    ("fln-lake", false),
    ("fln-server", false),
    ("fln-trace", false),
    ("fln", false),
    ("fln-hound", false),
    ("fln-doc", false),
    ("fln-mcp", false),
    ("fln-tui", false),
    ("fln-cli", false),
    ("fln-wasm", false),
    ("fln-conformance", false),
];

pub fn fixture_cargo_lock() -> String {
    fixture_cargo_lock_with_dependencies(&[])
}

pub fn fixture_cargo_lock_with_dependencies(dependencies: &[(&str, &[&str])]) -> String {
    let mut lock = String::from("version = 4\n");
    for (name, _) in FIXTURE_CRATES {
        lock.push_str(&format!(
            "\n[[package]]\nname = \"{name}\"\nversion = \"0.0.0\"\n"
        ));
        if let Some((_, package_dependencies)) =
            dependencies.iter().find(|(package, _)| *package == name)
            && !package_dependencies.is_empty()
        {
            lock.push_str("dependencies = [\n");
            for dependency in *package_dependencies {
                lock.push_str(&format!(" \"{dependency}\",\n"));
            }
            lock.push_str("]\n");
        }
    }
    lock
}

pub fn fixture_allowlist() -> String {
    let mut rows = String::from("schema fln-closure-allowlist/1\n");
    for (name, boundary) in FIXTURE_CRATES {
        let audit = if boundary { "deny-ledgered" } else { "forbid" };
        rows.push_str(&format!(
            "package {name} version=0.0.0 source=workspace checksum=- license=MIT build-script=no proc-macro=no native-link=no unsafe-audit={audit} policy=runtime owner=franken_lean upgrade=workspace reason=fixture\n"
        ));
    }
    rows
}

pub fn manifest(name: &str, deps: &[&str]) -> String {
    let mut m = format!(
        "[package]\nname = \"{name}\"\nversion = \"0.0.0\"\nedition = \"2024\"\nlicense = \"MIT\"\npublish = false\n\n[dependencies]\n"
    );
    for dep in deps {
        m.push_str(&format!("{dep} = {{ path = \"../{dep}\" }}\n"));
    }
    m
}

pub fn lib_rs(boundary: bool) -> &'static str {
    if boundary {
        "//! boundary stub\n#![deny(unsafe_code)]\n"
    } else {
        "//! stub\n#![forbid(unsafe_code)]\n"
    }
}

/// Baseline clean fixture: the complete plan crate map plus one synthetic middle
/// crate used by transitive-path tests, no edges, plus the
/// closure-governance files (Cargo.lock ⇄ allowlist ⇄ SUITE.lock ⇄ toolchain pin)
/// the D1 audit requires on every root.
pub fn base(ws: &TempWs) {
    ws.write(
        "Cargo.toml",
        "[workspace]\nresolver = \"3\"\nmembers = [\"crates/*\", \"tools/*\"]\n",
    );
    ws.write("rust-toolchain.toml", TOOLCHAIN_PIN);
    ws.write("SUITE.lock", SUITE_LOCK_FIXTURE);
    ws.write(CONTRACT_INVENTORY_SCHEMA_FILE, SCHEMA_DEFINITION);
    ws.write(
        CONTRACT_INVENTORY_POLICY_FILE,
        CONTRACT_INVENTORY_POLICY_FIXTURE,
    );
    ws.write(ABI_TARGET_LAYOUT_FILE, ABI_TARGET_LAYOUT_FIXTURE);
    ws.write(OLEAN_ILEAN_FORMAT_FILE, OLEAN_ILEAN_FORMAT_FIXTURE);
    ws.write(
        EXTERN_BUILTIN_ENVIRONMENT_FILE,
        EXTERN_BUILTIN_ENVIRONMENT_FIXTURE,
    );
    ws.write("Cargo.lock", &fixture_cargo_lock());
    ws.write("ci/CLOSURE_ALLOWLIST.txt", &fixture_allowlist());
    ws.write("ci/WORKSPACE_GRAPH.txt", BASE_GRAPH);
    ws.write("ci/UNSAFE_LEDGER.txt", EMPTY_LEDGER);
    for (name, boundary) in FIXTURE_CRATES {
        ws.write(&format!("crates/{name}/Cargo.toml"), &manifest(name, &[]));
        ws.write(&format!("crates/{name}/src/lib.rs"), lib_rs(boundary));
    }
}

pub fn codes(outcome: &RunOutcome) -> Vec<&'static str> {
    outcome.findings.iter().map(|f| f.code).collect()
}

pub fn graph_with_edges(edges: &[&str]) -> String {
    let mut g = String::from(BASE_GRAPH);
    for e in edges {
        g.push_str(&format!("edge {e}\n"));
    }
    g
}
