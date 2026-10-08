//! Verify that the real command takes the typed path by default.
#![forbid(unsafe_code)]

use fln_core::name::Name;
use fln_olean::ir::{IrDecodeLimits, decode_ir};
use fln_olean::ir_files::{IrFileLimits, check_ir_files, check_ir_files_with_types};
use fln_olean::region::{OleanView, WalkBudget};
use fln_olean::write::{ModuleWriteInput, OleanWriteHeader, WriteBudget};
use fln_olean::{ModuleExtensionInput, encode_module_with_extensions};
use fln_rt::region::materialize;
use std::collections::BTreeMap;
use std::path::PathBuf;
use std::process::{Command, Output};
use std::sync::atomic::{AtomicU64, Ordering};

static NEXT: AtomicU64 = AtomicU64::new(0);

struct Fixture {
    dir: PathBuf,
    file: PathBuf,
}

impl Fixture {
    fn new() -> Self {
        let dir = loop {
            let candidate = std::env::temp_dir().join(format!(
                "fln-ir-type-cli-{}-{}", std::process::id(), NEXT.fetch_add(1, Ordering::Relaxed),
            ));
            match std::fs::create_dir(&candidate) {
                Ok(()) => break candidate,
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(error) => panic!(/* ubs:ignore -- test-only diagnostic. */ "scratch: {error}"),
            }
        };
        let file = dir.join("closed.ir");
        let view = OleanView::parse(include_bytes!("../fixtures/ir/Init.Data.Nat.Basic.ir")).unwrap();
        let blocks = view.extension_payloads(WalkBudget::default(), 1 << 30).unwrap();
        let decoded = decode_ir(&blocks, IrDecodeLimits::default()).unwrap();
        let wanted = Name::from_components(["Nat", "instTransLe"]);
        let index = decoded.decls.iter().position(|decl| decl.name() == &wanted).unwrap();
        let extension = Name::from_components(["Lean", "IR", "declMapExt"]);
        let block = blocks.iter().find(|block| block.name == extension).unwrap();
        let entry = materialize(&block.entries[index], 0).unwrap();
        // The declaration is unchanged pinned data; its wrapper is synthetic.
        let encoded = encode_module_with_extensions(
            ModuleWriteInput { is_module: false, imports: &[], constants: &[], extra_const_names: &[] },
            &[ModuleExtensionInput { name: &extension, entries: &[entry] }],
            OleanWriteHeader {
                version: 2, flags: 1, lean_version: "4.32.0",
                githash: "0123456789abcdef0123456789abcdef01234567", base_addr: 0x20_000,
            },
            WriteBudget::default(),
        ).unwrap();
        std::fs::write(&file, encoded.bytes).unwrap();
        Self { dir, file }
    }

    fn run(&self, args: &[&str]) -> Output {
        Command::new(env!("CARGO_BIN_EXE_fln-ir-check"))
            .args(args).arg(&self.file).output().unwrap()
    }
}

impl Drop for Fixture {
    fn drop(&mut self) {
        // Only the private directory this helper created exclusively.
        let _ = std::fs::remove_dir_all(&self.dir);
    }
}

#[test]
fn default_command_checks_representations_and_opt_out_is_explicit() {
    let fixture = Fixture::new();
    let before = std::fs::read(&fixture.file).unwrap();
    let output = fixture.run(&[]);
    assert!(output.status.success(), "{output:?}");
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.contains("IR expression representations checked:"));
    assert!(!stdout.contains("NOT CHECKED"));
    let diagnostic = fixture.run(&["--structural-only"]);
    assert!(diagnostic.status.success(), "{diagnostic:?}");
    let stdout = String::from_utf8(diagnostic.stdout).unwrap();
    assert!(stdout.contains("NOT CHECKED (structural-only)"));
    assert!(!stdout.contains("IR expression representations checked:"));
    assert_eq!(std::fs::read(&fixture.file).unwrap(), before);
}

#[test]
fn default_command_cannot_reset_the_work_budget_between_passes() {
    let fixture = Fixture::new();
    let paths = [fixture.file.clone()];
    let structural = check_ir_files(&paths, &BTreeMap::new(), IrFileLimits::default()).unwrap();
    let typed = check_ir_files_with_types(&paths, &BTreeMap::new(), IrFileLimits::default()).unwrap();
    let partial_cap = structural.checked.summary().work.to_string();
    let total_cap = typed.representation.unwrap().work.to_string();
    assert_ne!(partial_cap, total_cap);
    let refused = fixture.run(&["--dot", "--max-work", &partial_cap]);
    assert_eq!(refused.status.code(), Some(5));
    assert!(refused.stdout.is_empty(), "resource exhaustion must publish no graph");
    let diagnostic = fixture.run(&["--structural-only", "--dot", "--max-work", &partial_cap]);
    assert!(diagnostic.status.success(), "{diagnostic:?}");
    let exact = fixture.run(&["--dot", "--max-work", &total_cap]);
    assert!(exact.status.success(), "{exact:?}");
    assert!(String::from_utf8(exact.stderr).unwrap().contains("IR expression representations checked:"));
    assert_eq!(exact.stdout, diagnostic.stdout, "type checking does not change graph identity");
}
