//! Generated filesystem rows through canonical, validated FLBC and native IO packets.
#![forbid(unsafe_code)]

use fln_comp::flbc::{
    self, ArgumentOwnership as A, CallableResultOwnership as C, CodecLimits, Function, FunctionId,
    Instruction as I, Program, Register, ResultOwnership as R, ValidatedProgram,
};
use fln_core::diag::ResourceReason;
use fln_core::outcome::{InconclusiveCause, Outcome};
use fln_rt::obj::{FileIoError, Obj};
use fln_vm::interpreter::{ExecutionLimits, VmExit, VmRefusal, execute};
use std::cell::Cell;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicUsize, Ordering};

static SERIAL: AtomicUsize = AtomicUsize::new(0);

fn directory(label: &str) -> PathBuf {
    let path = std::env::temp_dir().join(format!(
        "fln-vm-path-mutations-{}-{}-{label}",
        std::process::id(),
        SERIAL.fetch_add(1, Ordering::Relaxed),
    ));
    std::fs::create_dir(&path).unwrap();
    path
}

fn program(row: &str, paths: &[Option<&Path>], owned: bool) -> ValidatedProgram {
    let mut code: Vec<_> = paths
        .iter()
        .enumerate()
        .map(|(index, path)| {
            let dst = Register::new(index as u16);
            match path {
                Some(path) => I::String {
                    dst,
                    value: path.to_str().unwrap().to_owned(),
                },
                None => I::Nat { dst, value: 0 },
            }
        })
        .collect();
    let result = Register::new(paths.len() as u16);
    code.push(I::Intrinsic {
        dst: result,
        row: row.to_owned(),
        args: (0..paths.len())
            .map(|index| Register::new(index as u16))
            .collect(),
        argument_ownership: vec![if owned { A::Owned } else { A::Borrowed }; paths.len()],
        result_ownership: R::Owned,
    });
    code.push(I::Return { src: result });
    let checked = flbc::validate(Program::new(
        FunctionId::new(0),
        vec![Function {
            id: FunctionId::new(0),
            arity: 0,
            parameter_ownership: vec![],
            result_ownership: C::Owned,
            register_count: paths.len() as u16 + 1,
            code,
        }],
    ))
    .unwrap();
    let bytes = flbc::encode_canonical(&checked, CodecLimits::default()).unwrap();
    let decoded = flbc::decode_canonical(&bytes, CodecLimits::default()).unwrap();
    assert_eq!(
        bytes,
        flbc::encode_canonical(&decoded, CodecLimits::default()).unwrap()
    );
    decoded
}

fn call(row: &str, paths: &[&Path], success: bool) -> Obj {
    let program = program(
        row,
        &paths.iter().map(|path| Some(*path)).collect::<Vec<_>>(),
        false,
    );
    let outcome = execute(&program, ExecutionLimits::default(), None);
    let Outcome::Complete(VmExit::Returned(result)) = outcome else {
        panic!("filesystem row {row}: {outcome:?}");
    };
    let packet = result.value;
    assert_eq!(packet.header().tag, 0);
    assert_eq!(packet.header().other, 7);
    assert_eq!(
        packet.try_ctor_child(1).unwrap().unbox(),
        usize::from(success)
    );
    assert_eq!(packet.try_ctor_child(0).unwrap().unbox(), 0);
    packet
}

#[test]
fn path_rows_execute_creation_links_rename_and_nonrecursive_removal() {
    let root = directory("native-λ🙂");
    let child = root.join("child");
    let from = child.join("original");
    let link = child.join("linked");
    let to = child.join("renamed");
    call("extern:IO.FS.createDir", &[&child], true);
    call("extern:IO.FS.createDir", &[&child], false);
    std::fs::write(&from, b"one").unwrap();
    call("extern:IO.FS.hardLink", &[&from, &link], true);
    std::fs::write(&from, b"shared update").unwrap();
    assert_eq!(std::fs::read(&link).unwrap(), b"shared update");
    std::fs::write(&to, b"replaced destination").unwrap();
    call("extern:IO.FS.rename", &[&link, &to], true);
    assert!(!link.exists());
    call("extern:IO.FS.removeDir", &[&child], false);
    assert!(from.exists() && to.exists());
    call("extern:IO.FS.removeFile", &[&from], true);
    assert_eq!(std::fs::read(&to).unwrap(), b"shared update");
    call("extern:IO.FS.removeFile", &[&to], true);
    call("extern:IO.FS.removeDir", &[&child], true);
    assert!(!child.exists());
    call("extern:IO.FS.removeFile", &[&from], false);
    call("extern:IO.FS.rename", &[&from, &to], false);
    call("extern:IO.FS.hardLink", &[&from, &to], false);
}

#[test]
fn path_rows_refuse_bad_arguments_and_census_ownership_before_mutation() {
    let root = directory("preconditions");
    let from = root.join("original");
    let to = root.join("destination");
    std::fs::write(&from, b"preserved").unwrap();
    for (row, arity) in [
        ("extern:IO.FS.createDir", 1),
        ("extern:IO.FS.removeDir", 1),
        ("extern:IO.FS.removeFile", 1),
        ("extern:IO.FS.rename", 2),
        ("extern:IO.FS.hardLink", 2),
    ] {
        for invalid in 0..arity {
            let mut paths = vec![Some(from.as_path()), Some(to.as_path())];
            paths.truncate(arity);
            paths[invalid] = None;
            assert!(matches!(
                execute(
                    &program(row, &paths, false),
                    ExecutionLimits::default(),
                    None
                ),
                Outcome::Complete(VmExit::Refused {
                    refusal: VmRefusal::NativeFileIo {
                        error: FileIoError::InvalidFilename
                    },
                    ..
                })
            ));
        }
        let paths = [Some(from.as_path()), Some(to.as_path())];
        assert!(matches!(
            execute(
                &program(row, &paths[..arity], true),
                ExecutionLimits::default(),
                None
            ),
            Outcome::Complete(VmExit::Refused { .. })
        ));
        assert!(matches!(
            execute(&program(row, &[], false), ExecutionLimits::default(), None),
            Outcome::Complete(VmExit::Refused { .. })
        ));
        assert_eq!(std::fs::read(&from).unwrap(), b"preserved");
        assert!(!to.exists());
    }
}

#[test]
fn path_rows_stop_before_effects_when_fuel_or_cancellation_interrupts() {
    let root = directory("interrupted");
    let from = root.join("original");
    let to = root.join("destination");
    let empty = root.join("empty");
    std::fs::write(&from, b"preserved").unwrap();
    std::fs::create_dir(&empty).unwrap();
    let unchanged = || {
        assert_eq!(std::fs::read(&from).unwrap(), b"preserved");
        assert!(empty.is_dir());
        assert_eq!(std::fs::read_dir(&empty).unwrap().count(), 0);
        assert!(!to.exists());
    };
    for (row, paths) in [
        ("extern:IO.FS.createDir", vec![Some(to.as_path())]),
        ("extern:IO.FS.removeDir", vec![Some(empty.as_path())]),
        ("extern:IO.FS.removeFile", vec![Some(from.as_path())]),
        (
            "extern:IO.FS.rename",
            vec![Some(from.as_path()), Some(to.as_path())],
        ),
        (
            "extern:IO.FS.hardLink",
            vec![Some(from.as_path()), Some(to.as_path())],
        ),
    ] {
        let program = program(row, &paths, false);
        // Exactly the String argument instructions may run; the next step is
        // the effectful intrinsic, whose operands are all valid native paths.
        let allowed = paths.len() as u64;
        assert!(matches!(
            execute(
                &program,
                ExecutionLimits {
                    max_steps: allowed,
                    ..ExecutionLimits::default()
                },
                None
            ),
            Outcome::Inconclusive(stopped)
                if matches!(&stopped.cause, InconclusiveCause::ResourceExhausted { usage }
                    if usage.reason == ResourceReason::ExecutionSteps
                        && usage.allowed == allowed
                        && usage.observed == allowed + 1)
        ));
        unchanged();

        let already_cancelled = || true;
        assert!(matches!(
            execute(&program, ExecutionLimits::default(), Some(&already_cancelled)),
            Outcome::Inconclusive(stopped)
                if matches!(stopped.cause, InconclusiveCause::Cancelled { .. })
        ));
        unchanged();

        let polls = Cell::new(0);
        let cancel_before_intrinsic = || {
            polls.set(polls.get() + 1);
            polls.get() > allowed
        };
        assert!(matches!(
            execute(&program, ExecutionLimits::default(), Some(&cancel_before_intrinsic)),
            Outcome::Inconclusive(stopped)
                if matches!(stopped.cause, InconclusiveCause::Cancelled { .. })
        ));
        unchanged();
    }
}
