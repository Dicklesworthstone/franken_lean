//! Actual filesystem reads through genuine rows and canonical FLBC replay.
//! These are runtime fixtures, not source or imported-module admission.
#![forbid(unsafe_code)]

use fln_comp::flbc::{
    self, ArgumentOwnership as A, CallableResultOwnership as C, CodecLimits, Function, FunctionId,
    Instruction as I, Program, Register, ResultOwnership as R, ValidatedProgram,
};
use fln_core::diag::ResourceReason;
use fln_core::outcome::{InconclusiveCause, Outcome};
use fln_rt::obj::Obj;
use fln_vm::interpreter::{ExecutionLimits, VmExit, execute};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicUsize, Ordering};

const CEILING: usize = 16 * 1024 * 1024;
static SERIAL: AtomicUsize = AtomicUsize::new(0);
fn path(label: &str) -> PathBuf {
    std::env::temp_dir().join(format!(
        "fln-vm-line-{}-{}-{label}",
        std::process::id(),
        SERIAL.fetch_add(1, Ordering::Relaxed)
    ))
}
fn r(n: u16) -> Register {
    Register::new(n)
}
fn f(n: u32) -> FunctionId {
    FunctionId::new(n)
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
fn field(dst: u16, src: u16, index: u16) -> I {
    I::CtorField {
        dst: r(dst),
        src: r(src),
        expected_tag: 0,
        expected_fields: 7,
        field: index,
    }
}
fn replay(program: Program) -> ValidatedProgram {
    let validated = flbc::validate(program).unwrap();
    let encoded = flbc::encode_canonical(&validated, CodecLimits::default()).unwrap();
    let decoded = flbc::decode_canonical(&encoded, CodecLimits::default()).unwrap();
    assert_eq!(
        encoded,
        flbc::encode_canonical(&decoded, CodecLimits::default()).unwrap()
    );
    decoded
}

fn fixture(path: &Path, mode: u64, kind: usize, return_packet: bool) -> ValidatedProgram {
    let mut entry = vec![
        I::String {
            dst: r(0),
            value: path.to_str().unwrap().to_owned(),
        },
        I::Nat {
            dst: r(1),
            value: mode,
        },
        call(2, "extern:IO.FS.Handle.mk", vec![r(0), r(1)]),
        field(3, 2, 0),
    ];
    let mut extra = Vec::new();
    if kind == 0 {
        entry.push(call(4, "extern:IO.FS.Handle.getLine", vec![r(3)]));
        if return_packet {
            entry.push(I::Return { src: r(4) });
        } else {
            entry.extend([field(5, 4, 0), I::Return { src: r(5) }]);
        }
    } else {
        entry.extend([
            I::Closure {
                dst: r(4),
                function: f(1),
                captures: vec![r(3)],
                capture_ownership: vec![A::Borrowed],
            },
            I::Nat {
                dst: r(5),
                value: 0,
            },
        ]);
        let action = Function {
            id: f(1),
            arity: 2,
            parameter_ownership: vec![A::Borrowed; 2],
            result_ownership: C::Owned,
            register_count: 4,
            code: vec![
                call(2, "extern:IO.FS.Handle.getLine", vec![r(0)]),
                field(3, 2, 0),
                I::Return { src: r(3) },
            ],
        };
        extra.push(action);
        match kind {
            1 => entry.extend([
                I::Apply {
                    dst: r(6),
                    closure: r(4),
                    args: vec![r(5)],
                    argument_ownership: vec![A::Borrowed],
                    result_ownership: C::Owned,
                },
                I::Return { src: r(6) },
            ]),
            2 => entry.push(I::TailApply {
                closure: r(4),
                args: vec![r(5)],
                argument_ownership: vec![A::Borrowed],
                result_ownership: C::Owned,
            }),
            3 => {
                extra.push(Function {
                    id: f(2),
                    arity: 1,
                    parameter_ownership: vec![A::Borrowed],
                    result_ownership: C::Owned,
                    register_count: 1,
                    code: vec![I::Return { src: r(0) }],
                });
                entry.extend([
                    I::Closure {
                        dst: r(7),
                        function: f(2),
                        captures: vec![],
                        capture_ownership: vec![],
                    },
                    I::Apply {
                        dst: r(6),
                        closure: r(7),
                        args: vec![r(4), r(5)],
                        argument_ownership: vec![A::Borrowed; 2],
                        result_ownership: C::Owned,
                    },
                    I::Return { src: r(6) },
                ]);
            }
            4 => entry.push(I::Return { src: r(4) }),
            _ => unreachable!(),
        }
    }
    let mut functions = vec![Function {
        id: f(0),
        arity: 0,
        parameter_ownership: vec![],
        result_ownership: C::Owned,
        register_count: 8,
        code: entry,
    }];
    functions.extend(extra);
    replay(Program::new(f(0), functions))
}

fn returned(program: &ValidatedProgram) -> Obj {
    match execute(program, ExecutionLimits::default(), None) {
        Outcome::Complete(VmExit::Returned(result)) => result.value,
        other => panic!("expected real read result: {other:?}"),
    }
}
fn text(value: &Obj) -> String {
    let (n, _, chars, bytes) = value.try_string_view().expect("native String");
    let s = std::str::from_utf8(&bytes[..n - 1]).unwrap();
    assert_eq!(chars, s.chars().count());
    s.to_owned()
}

#[test]
fn get_line_executes_direct_apply_tail_and_returned_continuations_and_keeps_actions_deferred() {
    let path = path("calls");
    std::fs::write(&path, "λ🙂\0\r\nsecond\n").unwrap();
    for kind in 0..4 {
        assert_eq!(
            text(&returned(&fixture(&path, 0, kind, false))),
            "λ🙂\0\r\n"
        );
    }
    let closure = returned(&fixture(&path, 0, 4, false));
    let (_, captures) = closure.closure_shell_parts().expect("Golem closure shell");
    let handle = captures
        .iter()
        .find(|o| o.is_file_handle())
        .expect("retained native Handle");
    let first = handle.try_file_get_line(&Obj::mk_nat(0), 100, 100).unwrap();
    assert_eq!(
        text(&first.try_ctor_child(0).unwrap()),
        "λ🙂\0\r\n",
        "returning the action must not advance its captured cursor"
    );
    retain_fixtures();
}

#[test]
fn get_line_reads_are_real_io_errors_and_recovery_is_the_pinned_variant() {
    let path = path("errors-and-utf8");
    std::fs::write(&path, [0xff, 0x80, 0x80, b'X', b'\n']).unwrap();
    assert_eq!(text(&returned(&fixture(&path, 0, 0, false))), "�X\n");
    let result = returned(&fixture(&path, 4, 0, true));
    assert_eq!(result.try_ctor_child(1).unwrap().unbox(), 0);
    assert_eq!(result.try_ctor_child(2).unwrap().unbox(), 12);
    assert_eq!(result.try_ctor_child(3).unwrap().unbox(), 9);
    assert_eq!(result.try_ctor_child(4).unwrap().unbox(), 0);
    assert!(!text(&result.try_ctor_child(6).unwrap()).is_empty());
}

#[test]
fn get_line_input_resources_stay_inconclusive_through_all_callable_routes() {
    let path = path("input-limit");
    std::fs::write(&path, vec![b'A'; CEILING + 1]).unwrap();
    for kind in 0..4 {
        let result = execute(
            &fixture(&path, 0, kind, false),
            ExecutionLimits::default(),
            None,
        );
        let Outcome::Inconclusive(limit) = result else {
            panic!("resource is a nonanswer: {result:?}");
        };
        match limit.cause {
            InconclusiveCause::ResourceExhausted { usage } => {
                assert_eq!(
                    usage.reason,
                    ResourceReason::Memory {
                        limit_bytes: CEILING as u64
                    }
                );
                assert_eq!(usage.allowed, CEILING as u64);
                assert_eq!(usage.observed, CEILING as u64 + 1);
            }
            other => panic!("expected read resource: {other:?}"),
        }
        assert!(
            format!("{:?}", limit.progress).contains("16777217"),
            "consumed lookahead must remain diagnostic"
        );
    }
}

#[test]
fn get_line_output_expansion_is_bounded_independently_of_consumed_file_bytes() {
    let path = path("output-limit");
    let consumed = CEILING / 3 + 1;
    std::fs::write(&path, vec![0xff; consumed]).unwrap();
    let result = execute(
        &fixture(&path, 0, 0, false),
        ExecutionLimits::default(),
        None,
    );
    let Outcome::Inconclusive(limit) = result else {
        panic!("output expansion resource: {result:?}");
    };
    match limit.cause {
        InconclusiveCause::ResourceExhausted { usage } => {
            assert_eq!(usage.allowed, CEILING as u64);
            assert_eq!(usage.observed, (3 * consumed) as u64);
        }
        other => panic!("expected read resource: {other:?}"),
    }
    assert!(format!("{:?}", limit.progress).contains(&consumed.to_string()));
}

fn retain_fixtures() {
    let Some(directory) = std::env::var_os("FLN_FS_READ_LINE_FIXTURE_DIR") else {
        return;
    };
    let directory = PathBuf::from(directory);
    std::fs::create_dir_all(&directory).unwrap();
    let directory = directory.canonicalize().unwrap();
    let cases = [
        ("FsReadLineUnicode", "λ🙂\0\r\nsecond\n".as_bytes().to_vec()),
        ("FsReadLineRecovery", vec![0xff, 0x80, 0x80, b'X', b'\n']),
        ("FsReadLineInputLimit", vec![b'A'; CEILING + 1]),
        ("FsReadLineOutputLimit", vec![0xff; CEILING / 3 + 1]),
    ];
    for (name, bytes) in cases {
        let input = directory.join(format!("{name}.input"));
        write_new(&input, &bytes);
        let program = fixture(&input, 0, 0, false);
        write_new(
            &directory.join(format!("{name}.flbc")),
            &flbc::encode_canonical(&program, CodecLimits::default()).unwrap(),
        );
    }
    write_new(&directory.join("PROVENANCE.txt"), b"Actual native getLine runtime fixtures via canonical FLBC and genuine census row. No source/module admission claim. Unicode and pinned recovery succeed; input/output limits are explicit16MiB VM resource nonanswers. Input fixtures and read artifacts are retained without deletion.\n");
}
fn write_new(path: &Path, bytes: &[u8]) {
    use std::io::Write;
    let mut file = std::fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(path)
        .unwrap();
    file.write_all(bytes).unwrap();
}
