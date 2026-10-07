//! File -> real IR decoder -> structural validator -> native command tests.
#![forbid(unsafe_code)]

use fln_core::name::Name;
use fln_olean::ir::{IrDecodeLimits, decode_ir};
use fln_olean::ir_files::{IrFileError, IrFileLimits, check_ir_files, ir_graph_dot};
use fln_olean::region::{OleanView, WalkBudget};
use fln_olean::write::{ModuleWriteInput, OleanWriteHeader, WriteBudget};
use fln_olean::{ModuleExtensionInput, encode_module_with_extensions};
use fln_rt::region::materialize;
use std::collections::BTreeMap;
use std::path::PathBuf;
use std::process::{Command, Output};
use std::sync::atomic::{AtomicU64, Ordering};

const NAT: &[u8] = include_bytes!("../fixtures/ir/Init.Data.Nat.Basic.ir");
static NEXT: AtomicU64 = AtomicU64::new(0);

fn name(text: &str) -> Name {
    Name::from_components(text.split('.'))
}

struct Scratch(PathBuf);

impl Scratch {
    fn new() -> Self {
        loop {
            let path = std::env::temp_dir().join(format!(
                "fln-ir-files-{}-{}", std::process::id(), NEXT.fetch_add(1, Ordering::Relaxed),
            ));
            match std::fs::create_dir(&path) {
                Ok(()) => return Self(path),
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(error) => panic!(/* ubs:ignore -- test-only diagnostic. */ "scratch: {error}"),
            }
        }
    }

    fn write(&self, filename: &str, bytes: &[u8]) -> PathBuf {
        let path = self.0.join(filename);
        std::fs::write(&path, bytes).unwrap();
        path
    }
}

impl Drop for Scratch {
    fn drop(&mut self) {
        // This directory was exclusively created by this helper, never supplied
        // by a caller and never reused when create_dir reported AlreadyExists.
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

/// Re-envelope an UNCHANGED declaration payload from the real pinned fixture.
/// The wrapper header is synthetic: this is not a Reference byte-identity test.
fn isolated(declaration: Option<&str>) -> Vec<u8> {
    let view = OleanView::parse(NAT).unwrap();
    let blocks = view.extension_payloads(WalkBudget::default(), 1 << 30).unwrap();
    let decoded = decode_ir(&blocks, IrDecodeLimits::default()).unwrap();
    let extension = name("Lean.IR.declMapExt");
    let block = blocks.iter().find(|block| block.name == extension).unwrap();
    let entries = declaration.map(|wanted| {
        let index = decoded.decls.iter().position(|d| d.name() == &name(wanted)).unwrap();
        materialize(&block.entries[index], 0).unwrap()
    }).into_iter().collect::<Vec<_>>();
    let extensions = if declaration.is_some() {
        vec![ModuleExtensionInput { name: &extension, entries: &entries }]
    } else {
        vec![]
    };
    encode_module_with_extensions(
        ModuleWriteInput { is_module: false, imports: &[], constants: &[], extra_const_names: &[] },
        &extensions,
        OleanWriteHeader {
            version: 2, flags: 1, lean_version: "4.32.0",
            githash: "0123456789abcdef0123456789abcdef01234567", base_addr: 0x20_000,
        },
        WriteBudget::default(),
    ).unwrap().bytes
}

fn command(args: &[&str], paths: &[PathBuf]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_fln-ir-check"))
        .args(args).args(paths).output().unwrap()
}

#[test]
fn real_declaration_passes_file_validation_and_the_native_command() {
    let dir = Scratch::new();
    let bytes = isolated(Some("Nat.instTransLe"));
    let paths = [dir.write("closed.ir", &bytes)];
    let result = check_ir_files(&paths, &BTreeMap::new(), IrFileLimits::default()).unwrap();
    assert_eq!(result.checked.summary().declarations, 1);
    assert_eq!(result.input_bytes, bytes.len() as u64);
    assert!(result.captured_payload_bytes > 0);
    let output = command(&["--dot"], &paths);
    assert!(output.status.success(), "{:?}", output);
    let dot = String::from_utf8(output.stdout).unwrap();
    assert!(dot.starts_with("digraph IR {\n"));
    assert!(dot.contains("Nat.instTransLe"));
    assert!(String::from_utf8(output.stderr).unwrap().contains("1 declarations"));
    assert_eq!(std::fs::read(&paths[0]).unwrap(), bytes);
}

#[test]
fn missing_real_import_is_refused_before_any_dot_output() {
    let dir = Scratch::new();
    let paths = [dir.write("unclosed.ir", &isolated(Some("Nat.blt")))];
    let output = command(&["--dot"], &paths);
    assert_eq!(output.status.code(), Some(1));
    assert!(output.stdout.is_empty());
    let error = String::from_utf8(output.stderr).unwrap();
    assert!(error.contains("UnknownCallee"));
    assert!(error.contains("Nat"));
    assert!(error.contains("add"));
}

#[test]
fn reviewed_signatures_are_explicit_and_do_not_invent_ir_bodies() {
    let dir = Scratch::new();
    let paths = [dir.write("Nat.blt.ir", &isolated(Some("Nat.blt")))];
    // Signatures explicitly supplied by this test, not inferred by the loader.
    let signatures = BTreeMap::from([(name("Nat.add"), 2), (name("Nat.ble"), 2)]);
    let result = check_ir_files(&paths, &signatures, IrFileLimits::default()).unwrap();
    assert_eq!(result.checked.summary().declarations, 1);
    assert_eq!(result.checked.summary().census_signatures, 2);
    assert_eq!(result.checked.graph().edge_count(), 2);
    let dot = ir_graph_dot(&result.checked, 100_000).unwrap();
    assert_eq!(dot.matches("signature-only").count(), 2);
}

#[test]
fn a_container_without_an_ir_block_is_not_a_successful_empty_ir_check() {
    let dir = Scratch::new();
    let paths = [dir.write("not-ir.olean", &isolated(None))];
    assert!(matches!(
        check_ir_files(&paths, &BTreeMap::new(), IrFileLimits::default()),
        Err(IrFileError::MissingIrBlock(_)),
    ));
    let output = command(&["--dot"], &paths);
    assert_eq!(output.status.code(), Some(1));
    assert!(output.stdout.is_empty());
}

#[test]
fn duplicate_paths_and_empty_input_do_not_manufacture_a_closure() {
    let dir = Scratch::new();
    let path = dir.write("closed.ir", &isolated(Some("Nat.instTransLe")));
    assert!(matches!(
        check_ir_files(&[path.clone(), path], &BTreeMap::new(), IrFileLimits::default()),
        Err(IrFileError::DuplicateInput(_)),
    ));
    assert!(matches!(
        check_ir_files(&[], &BTreeMap::new(), IrFileLimits::default()),
        Err(IrFileError::EmptyInput),
    ));
}

#[test]
fn cumulative_input_byte_limit_accepts_the_exact_boundary() {
    let dir = Scratch::new();
    let a = isolated(Some("Nat.instTransLe"));
    let b = isolated(Some("Nat.instTransLt"));
    let paths = [dir.write("a.ir", &a), dir.write("b.ir", &b)];
    let exact = IrFileLimits {
        max_total_bytes: (a.len() + b.len()) as u64, ..IrFileLimits::default()
    };
    let result = check_ir_files(&paths, &BTreeMap::new(), exact).unwrap();
    assert_eq!(result.checked.summary().declarations, 2);
    let below = IrFileLimits { max_total_bytes: exact.max_total_bytes - 1, ..exact };
    let failure = check_ir_files(&paths, &BTreeMap::new(), below).unwrap_err();
    assert!(failure.is_inconclusive());
    assert!(matches!(failure, IrFileError::Limit { .. }));
}

#[test]
fn expanded_payload_budget_is_shared_across_files() {
    let dir = Scratch::new();
    let paths = [
        dir.write("a.ir", &isolated(Some("Nat.instTransLe"))),
        dir.write("b.ir", &isolated(Some("Nat.instTransLt"))),
    ];
    let measured = check_ir_files(&paths, &BTreeMap::new(), IrFileLimits::default()).unwrap();
    let exact = IrFileLimits {
        max_payload_bytes: measured.captured_payload_bytes, ..IrFileLimits::default()
    };
    check_ir_files(&paths, &BTreeMap::new(), exact).unwrap();
    let below = IrFileLimits { max_payload_bytes: exact.max_payload_bytes - 1, ..exact };
    assert!(check_ir_files(&paths, &BTreeMap::new(), below).unwrap_err().is_inconclusive());
}

#[test]
fn file_declaration_and_work_limits_remain_inconclusive() {
    let dir = Scratch::new();
    let paths = [dir.write("closed.ir", &isolated(Some("Nat.instTransLe")))];
    let mut declarations = IrFileLimits::default();
    declarations.validation.max_declarations = 0;
    let mut work = IrFileLimits::default();
    work.validation.max_work = 0;
    for limits in [
        IrFileLimits { max_files: 0, ..IrFileLimits::default() },
        IrFileLimits { max_file_bytes: 0, ..IrFileLimits::default() },
        declarations, work,
    ] {
        assert!(check_ir_files(&paths, &BTreeMap::new(), limits).unwrap_err().is_inconclusive());
    }
}

#[test]
fn dot_is_independent_of_file_enumeration_and_obeys_exact_output_limit() {
    let dir = Scratch::new();
    let a = dir.write("a.ir", &isolated(Some("Nat.instTransLe")));
    let b = dir.write("b.ir", &isolated(Some("Nat.instTransLt")));
    let first = check_ir_files(&[a.clone(), b.clone()], &BTreeMap::new(), IrFileLimits::default()).unwrap();
    let second = check_ir_files(&[b, a], &BTreeMap::new(), IrFileLimits::default()).unwrap();
    let dot = ir_graph_dot(&first.checked, 100_000).unwrap();
    assert_eq!(dot, ir_graph_dot(&second.checked, dot.len()).unwrap());
    assert!(ir_graph_dot(&first.checked, dot.len() - 1).unwrap_err().is_inconclusive());
}

#[test]
fn dot_ids_do_not_merge_distinct_names_with_the_same_display_text() {
    use fln_olean::ir::{IrArg, IrBody, IrDecl, IrModule, IrTerminal, IrType};
    use fln_olean::ir_validate::{IrValidationLimits, build_validated_ir_call_graph};
    let names = [Name::str(Name::anonymous(), "A.B"), name("A.B"), name("Quote\"\\\n")];
    let module = IrModule {
        decls: names.into_iter().map(|name| IrDecl::Function {
            name, params: vec![], result: IrType::Erased,
            body: IrBody { stmts: vec![], terminal: Box::new(IrTerminal::Ret(IrArg::Erased)) },
            sorry_dep: None,
        }).collect(),
        uninterpreted: vec![],
    };
    let checked = build_validated_ir_call_graph(
        &[("unused-path", &module)], &BTreeMap::new(), IrValidationLimits::default(),
    ).unwrap();
    let dot = ir_graph_dot(&checked, 100_000).unwrap();
    assert_eq!(dot.matches("fln_kind=\"function\"").count(), 3);
    for index in 0..3 {
        assert!(dot.contains(&format!("n{index} [label=")));
    }
    assert!(dot.contains("\\\""));
    assert!(!dot.contains("unused-path"));
}

#[test]
fn command_reports_usage_and_does_not_publish_on_output_exhaustion() {
    assert!(command(&["--help"], &[]).status.success());
    for args in [vec![], vec!["--unknown"], vec!["--max-work"], vec!["--max-work", "-1"]] {
        assert_eq!(command(&args, &[]).status.code(), Some(2));
    }
    let dir = Scratch::new();
    let paths = [dir.write("closed.ir", &isolated(Some("Nat.instTransLe")))];
    let output = command(&["--dot", "--max-output-bytes", "0"], &paths);
    assert_eq!(output.status.code(), Some(5));
    assert!(output.stdout.is_empty());
}

#[test]
fn missing_input_directory_and_corrupt_container_have_distinct_outcomes() {
    let dir = Scratch::new();
    assert_eq!(command(&[], &[dir.0.join("absent.ir")]).status.code(), Some(5));
    assert_eq!(command(&[], &[dir.0.clone()]).status.code(), Some(5));
    let bad = dir.write("bad.ir", b"not an IR container");
    let output = command(&["--dot"], &[bad]);
    assert_eq!(output.status.code(), Some(1));
    assert!(output.stdout.is_empty());
}
