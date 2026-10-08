//! Whole-container controls for the typed file entry point.
use super::*;
use crate::ir_format as f;
use crate::write::{ModuleWriteInput, OleanWriteHeader, WriteBudget};
use crate::{ModuleExtensionInput, encode_module_with_extensions};
use fln_rt::convert::inject_name;
use fln_rt::obj::Obj;
use std::sync::atomic::{AtomicU64, Ordering};

static NEXT: AtomicU64 = AtomicU64::new(0);

struct Scratch(PathBuf);

impl Scratch {
    fn new() -> Self {
        loop {
            let path = std::env::temp_dir().join(format!(
                "fln-ir-type-files-{}-{}",
                std::process::id(), NEXT.fetch_add(1, Ordering::Relaxed),
            ));
            match std::fs::create_dir(&path) {
                Ok(()) => return Self(path),
                Err(error) if error.kind() == io::ErrorKind::AlreadyExists => continue,
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
        // Only this helper's exclusively created temporary test directory.
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

fn slots(tag: u8, count: usize, values: Vec<(usize, Obj)>, scalars: &[u8]) -> Obj {
    let mut fields: Vec<_> = (0..count).map(|_| Obj::mk_nat(0)).collect();
    assert_eq!(count, values.len());
    for (index, value) in values { fields[index] = value; }
    Obj::mk_ctor(tag, fields, scalars)
}

/// Synthetic wrapper and program, built from the generated contract slots:
/// `f (x0 : source) : uint8 := let x1 : uint8 := unbox x0; ret x1`.
fn program(text: &str, source: u8) -> Vec<u8> {
    let parameter = slots(0, f::PARAM_POINTERS, vec![
        (f::PARAM_X, Obj::mk_nat(0)),
        (f::PARAM_TY, Obj::mk_nat(source.into())),
    ], &[0]);
    let expr = slots(f::EXPR_UNBOX, f::EXPR_UNBOX_POINTERS,
        vec![(f::EXPR_UNBOX_X, Obj::mk_nat(0))], &[]);
    let arg = slots(f::ARG_VAR, f::ARG_VAR_POINTERS,
        vec![(f::ARG_VAR_ID, Obj::mk_nat(1))], &[]);
    let ret = slots(f::BODY_RET, f::BODY_RET_POINTERS,
        vec![(f::BODY_RET_X, arg)], &[]);
    let body = slots(f::BODY_VDECL, f::BODY_VDECL_POINTERS, vec![
        (f::BODY_VDECL_X, Obj::mk_nat(1)),
        (f::BODY_VDECL_TY, Obj::mk_nat(f::IR_TYPE_UINT8.into())),
        (f::BODY_VDECL_E, expr),
        (f::BODY_VDECL_B, ret),
    ], &[]);
    let declaration = slots(f::DECL_FDECL, f::DECL_FDECL_POINTERS, vec![
        (f::DECL_FDECL_F, inject_name(&Name::from_components(text.split('.')))),
        (f::DECL_FDECL_XS, Obj::mk_array(vec![parameter])),
        (f::DECL_FDECL_TYPE, Obj::mk_nat(f::IR_TYPE_UINT8.into())),
        (f::DECL_FDECL_BODY, body),
        (f::DECL_FDECL_INFO, Obj::mk_nat(0)),
    ], &[]);
    let extension = Name::from_components(f::DECL_MAP_EXTENSION.split('.'));
    encode_module_with_extensions(
        ModuleWriteInput { is_module: false, imports: &[], constants: &[], extra_const_names: &[] },
        &[ModuleExtensionInput { name: &extension, entries: &[declaration] }],
        OleanWriteHeader {
            version: 2, flags: 1, lean_version: "4.32.0",
            githash: "0123456789abcdef0123456789abcdef01234567", base_addr: 0x20_000,
        },
        WriteBudget::default(),
    ).unwrap().bytes
}

#[test]
fn structurally_valid_scalar_unbox_file_is_rejected_by_the_typed_entry() {
    let scratch = Scratch::new();
    let bytes = program("Bad", f::IR_TYPE_UINT64);
    let paths = [scratch.write("bad.ir", &bytes)];
    let untyped = check_ir_files(&paths, &BTreeMap::new(), IrFileLimits::default()).unwrap();
    assert!(untyped.representation.is_none());
    let failure = check_ir_files_with_types(&paths, &BTreeMap::new(), IrFileLimits::default()).unwrap_err();
    assert!(!failure.is_inconclusive(), "a type violation is not exhaustion");
    assert!(matches!(failure, IrFileError::Representation(IrTypeValidationError::Rule {
        operation: "unbox source", binding: 1, ..
    })));
    assert_eq!(std::fs::read(&paths[0]).unwrap(), bytes);
}

#[test]
fn typed_file_checks_share_the_structural_budget_without_changing_the_graph() {
    let scratch = Scratch::new();
    let paths = [scratch.write("good.ir", &program("Good", f::IR_TYPE_OBJECT))];
    let plain = check_ir_files(&paths, &BTreeMap::new(), IrFileLimits::default()).unwrap();
    let typed = check_ir_files_with_types(&paths, &BTreeMap::new(), IrFileLimits::default()).unwrap();
    let summary = typed.representation.unwrap();
    assert_eq!(summary.expressions, 1);
    assert_eq!(summary.structural, *plain.checked.summary());
    assert!(summary.work > summary.structural.work);
    assert_eq!(ir_graph_dot(&plain.checked, 10_000).unwrap(), ir_graph_dot(&typed.checked, 10_000).unwrap());
    let exact = IrFileLimits {
        validation: IrValidationLimits { max_work: summary.work, ..IrValidationLimits::default() },
        ..IrFileLimits::default()
    };
    check_ir_files_with_types(&paths, &BTreeMap::new(), exact).unwrap();
    let below = IrFileLimits {
        validation: IrValidationLimits { max_work: summary.work - 1, ..exact.validation },
        ..exact
    };
    let failure = check_ir_files_with_types(&paths, &BTreeMap::new(), below).unwrap_err();
    assert!(failure.is_inconclusive());
    assert!(matches!(failure, IrFileError::Representation(IrTypeValidationError::Limit { resource: "work", .. })));
}

#[test]
fn one_bad_unreachable_declaration_refuses_the_entire_file_set() {
    let scratch = Scratch::new();
    let paths = [
        scratch.write("good.ir", &program("Good", f::IR_TYPE_OBJECT)),
        scratch.write("bad.ir", &program("UnusedBad", f::IR_TYPE_UINT64)),
    ];
    assert!(check_ir_files(&paths, &BTreeMap::new(), IrFileLimits::default()).is_ok());
    let failure = check_ir_files_with_types(&paths, &BTreeMap::new(), IrFileLimits::default()).unwrap_err();
    match failure {
        IrFileError::Representation(IrTypeValidationError::Rule { declaration, .. }) => {
            assert_eq!(declaration, Name::from_components(["UnusedBad"]));
        }
        other => panic!(/* ubs:ignore -- test-only diagnostic. */ "unexpected: {other:?}"),
    }
}
