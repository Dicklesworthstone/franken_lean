//! Metadata and terminal observations over live files and canonical FLBC.
#![forbid(unsafe_code)]

use fln_comp::flbc::{
    self, ArgumentOwnership as A, CallableResultOwnership as C, CodecLimits, Function, FunctionId,
    Instruction as I, Program, Register, ResultOwnership as R, ValidatedProgram,
};
use fln_core::outcome::{InconclusiveCause, Outcome};
use fln_rt::obj::{FileIoError, Obj};
use fln_vm::interpreter::{ExecutionLimits, VmExit, VmRefusal, execute};
use std::os::unix::fs::{MetadataExt, symlink};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicUsize, Ordering};

static SERIAL: AtomicUsize = AtomicUsize::new(0);
const METADATA: &str = "extern:System.FilePath.metadata";
const SYMLINK: &str = "extern:System.FilePath.symlinkMetadata";
const IS_TTY: &str = "extern:IO.FS.Handle.isTty";

fn directory() -> PathBuf {
    let path = std::env::temp_dir().join(format!(
        "fln-vm-metadata-{}-{}-λ",
        std::process::id(),
        SERIAL.fetch_add(1, Ordering::Relaxed),
    ));
    std::fs::create_dir(&path).unwrap();
    path
}

fn r(index: u16) -> Register {
    Register::new(index)
}

fn call(dst: u16, row: &str, args: Vec<Register>) -> I {
    I::Intrinsic {
        dst: r(dst),
        row: row.to_owned(),
        argument_ownership: vec![A::Borrowed; args.len()],
        args,
        result_ownership: R::Owned,
    }
}

fn program(row: &str, path: Option<&Path>, tty_handle: bool) -> Program {
    let mut code = vec![match path {
        Some(path) => I::String {
            dst: r(0),
            value: path.to_str().unwrap().to_owned(),
        },
        None => I::Nat {
            dst: r(0),
            value: 0,
        },
    }];
    if tty_handle {
        code.extend([
            I::Nat {
                dst: r(1),
                value: 0,
            },
            call(2, "extern:IO.FS.Handle.mk", vec![r(0), r(1)]),
            I::CtorField {
                dst: r(3),
                src: r(2),
                expected_tag: 0,
                expected_fields: 7,
                field: 0,
            },
        ]);
    }
    code.push(call(4, row, vec![r(if tty_handle { 3 } else { 0 })]));
    code.push(I::Return { src: r(4) });
    Program::new(
        FunctionId::new(0),
        vec![Function {
            id: FunctionId::new(0),
            arity: 0,
            parameter_ownership: vec![],
            result_ownership: if row == IS_TTY { C::Scalar } else { C::Owned },
            register_count: 5,
            code,
        }],
    )
}

fn replay(program: Program) -> ValidatedProgram {
    let checked = flbc::validate(program).unwrap();
    let bytes = flbc::encode_canonical(&checked, CodecLimits::default()).unwrap();
    let decoded = flbc::decode_canonical(&bytes, CodecLimits::default()).unwrap();
    assert_eq!(
        bytes,
        flbc::encode_canonical(&decoded, CodecLimits::default()).unwrap()
    );
    decoded
}

fn returned(program: &ValidatedProgram) -> Obj {
    let outcome = execute(program, ExecutionLimits::default(), None);
    let Outcome::Complete(VmExit::Returned(result)) = outcome else {
        panic!("live filesystem observation: {outcome:?}");
    };
    result.value
}

fn child(value: &Obj, index: usize) -> Obj {
    value.try_ctor_child(index).unwrap()
}

fn number(value: &Obj) -> u64 {
    if value.is_scalar() {
        value.unbox() as u64
    } else {
        let (_, sign, limbs) = value.try_mpz_view().unwrap();
        assert_eq!(sign, 1);
        assert_eq!(limbs.len(), 1);
        limbs[0]
    }
}

fn payload(packet: &Obj) -> Obj {
    assert_eq!(packet.header().tag, 0);
    assert_eq!(packet.header().other, 7);
    assert_eq!(child(packet, 1).unbox(), 1);
    let payload = child(packet, 0);
    assert_eq!(payload.header().tag, 0);
    assert_eq!(payload.header().other, 9);
    payload
}

#[test]
fn metadata_rows_replay_live_files_links_and_directories_without_stale_values() {
    let root = directory();
    let file = root.join("file");
    let linked = root.join("symbolic");
    let hard = root.join("hard");
    std::fs::write(&file, b"first").unwrap();
    symlink(&file, &linked).unwrap();
    std::fs::hard_link(&file, &hard).unwrap();
    let followed = replay(program(METADATA, Some(&linked), false));
    let unlinked = replay(program(SYMLINK, Some(&linked), false));
    for content in [b"first".as_slice(), b"a different size".as_slice()] {
        std::fs::write(&file, content).unwrap();
        let observed = payload(&returned(&followed));
        assert_eq!(number(&child(&observed, 6)), content.len() as u64);
        assert_eq!(number(&child(&observed, 7)), 1);
        assert_eq!(number(&child(&observed, 8)), 2);
        let link = payload(&returned(&unlinked));
        assert_eq!(
            number(&child(&link, 6)),
            std::fs::symlink_metadata(&linked).unwrap().size()
        );
        assert_eq!(number(&child(&link, 7)), 2);
    }
    let observed = payload(&returned(&replay(program(METADATA, Some(&root), false))));
    assert_eq!(number(&child(&observed, 7)), 0);
    let tty = returned(&replay(program(IS_TTY, Some(&file), true)));
    assert!(tty.is_scalar());
    assert_eq!(tty.unbox(), 0);
}

#[test]
fn metadata_errors_preserve_native_code_filename_and_symlink_behavior() {
    let root = directory();
    let missing = root.join("missing");
    let dangling = root.join("dangling");
    symlink(&missing, &dangling).unwrap();
    for row in [METADATA, SYMLINK] {
        // The pin's stat/lstat leaves use libuv's negative errno, stored in
        // UInt32. Embedded NUL is the separate positive-errno input error.
        for (path, tag, code) in [
            (missing.as_path(), 11, (-2_i32) as u32 as usize),
            (Path::new("bad\0path"), 12, 22),
        ] {
            let packet = returned(&replay(program(row, Some(path), false)));
            assert_eq!(child(&packet, 0).unbox(), 0);
            assert_eq!(child(&packet, 1).unbox(), 0);
            assert_eq!(child(&packet, 2).unbox(), tag);
            assert_eq!(child(&packet, 3).unbox(), code);
            let filename = child(&packet, 5);
            let (size, _, _, bytes) = filename.try_string_view().unwrap();
            assert_eq!(&bytes[..size - 1], path.to_str().unwrap().as_bytes());
        }
    }
    let followed = returned(&replay(program(METADATA, Some(&dangling), false)));
    assert_eq!(child(&followed, 1).unbox(), 0);
    let symlink = payload(&returned(&replay(program(SYMLINK, Some(&dangling), false))));
    assert_eq!(number(&child(&symlink, 7)), 2);
}

#[test]
fn observations_refuse_bad_values_and_census_ownership_and_respect_resource_stops() {
    let root = directory();
    let file = root.join("file");
    std::fs::write(&file, b"preserved").unwrap();
    for row in [METADATA, SYMLINK, IS_TTY] {
        let invalid = execute(
            &replay(program(row, None, false)),
            ExecutionLimits::default(),
            None,
        );
        let Outcome::Complete(VmExit::Refused {
            refusal: VmRefusal::NativeFileIo { error },
            ..
        }) = invalid
        else {
            panic!("bad argument for {row}: {invalid:?}");
        };
        assert_eq!(
            error,
            if row == IS_TTY {
                FileIoError::InvalidHandle
            } else {
                FileIoError::InvalidFilename
            }
        );
        for mutation in 0..4 {
            let mut invalid = program(row, Some(&file), row == IS_TTY);
            let last_call = invalid.functions[0].code.len() - 2;
            let I::Intrinsic {
                args,
                argument_ownership,
                result_ownership,
                ..
            } = &mut invalid.functions[0].code[last_call]
            else {
                unreachable!()
            };
            match mutation {
                0 => argument_ownership[0] = A::Owned,
                1 => *result_ownership = R::Scalar,
                2 => {
                    args.clear();
                    argument_ownership.clear();
                }
                3 => {
                    args.push(r(0));
                    argument_ownership.push(A::Borrowed);
                }
                _ => unreachable!(),
            }
            assert!(matches!(
                execute(&replay(invalid), ExecutionLimits::default(), None),
                Outcome::Complete(VmExit::Refused { .. })
            ));
        }
        let program = replay(program(row, Some(&file), row == IS_TTY));
        assert!(matches!(
            execute(
                &program,
                ExecutionLimits {
                    max_steps: 1,
                    ..ExecutionLimits::default()
                },
                None
            ),
            Outcome::Inconclusive(_)
        ));
        assert!(matches!(
            execute(&program, ExecutionLimits::default(), Some(&|| true)),
            Outcome::Inconclusive(stop) if matches!(stop.cause, InconclusiveCause::Cancelled { .. })
        ));
    }
    assert_eq!(std::fs::read(file).unwrap(), b"preserved");
}
