//! The captured Reference convention is checked again at every native apply.
use super::*;
use fln_rt::obj::StdoutCapture;
use fln_vm::interpreter::{
    CommandExecutionContext, execute_cached_with_context, execute_with_context,
};

fn context() -> CommandExecutionContext {
    CommandExecutionContext::UNLIMITED.with_captured_reference_output()
}

fn program(tail: bool, continuation: bool, read: bool) -> ValidatedProgram {
    let mut code = callback_prefix(if read { 3 } else { 4 });
    code[2] = I::String {
        dst: r(2),
        value: "λ\0🙂\n".to_owned(),
    };
    // A denied getLine must stop before even checking its invalid world, so a
    // mutant missing the capability check refuses for a different reason
    // rather than attempting a host read in the test runner.
    if read {
        code[3] = I::Nat {
            dst: r(3),
            value: 1,
        };
    }
    let mut args = if read { vec![r(3)] } else { vec![r(2), r(3)] };
    let closure = if continuation {
        code.push(I::Closure {
            dst: r(4),
            function: f(1),
            captures: vec![],
            capture_ownership: vec![],
        });
        args.insert(0, r(1));
        r(4)
    } else {
        r(1)
    };
    let ownership = vec![A::Borrowed; args.len()];
    if tail {
        code.push(I::TailApply {
            closure,
            args,
            argument_ownership: ownership,
            result_ownership: R::Erased,
        });
    } else {
        code.push(I::Apply {
            dst: r(5),
            closure,
            args,
            argument_ownership: ownership,
            result_ownership: R::Erased,
        });
        code.push(I::Return { src: r(5) });
    }
    let mut functions = vec![function(0, vec![], R::Erased, 6, code)];
    if continuation {
        functions.push(function(
            1,
            vec![A::Borrowed],
            R::Owned,
            1,
            vec![I::Return { src: r(0) }],
        ));
    }
    raw_program(functions)
}

fn assert_native_result(value: &Obj) {
    assert_eq!((value.header().tag, value.header().other), (0, 1));
    let unit = value.try_ctor_child(0).unwrap();
    assert!(unit.is_scalar());
    assert_eq!(unit.unbox(), 0);
}

#[test]
fn captured_native_apply_and_continuations_require_scope_and_preserve_context_on_warm_caches() {
    let _lock = LOCK.lock().unwrap_or_else(|error| error.into_inner());
    for tail in [false, true] {
        for continuation in [false, true] {
            let raw = program(tail, continuation, false);
            let owned = owned_program(&raw);
            for program in [&raw, &owned] {
                let uncaptured =
                    execute_with_context(program, ExecutionLimits::default(), context(), None);
                assert!(
                    matches!(uncaptured, Outcome::InternalFault(_)),
                    "missing capture cannot fall back to fwrite; tail={tail} continuation={continuation}: {uncaptured:?}"
                );
                let mut caches = InlineCaches::try_new(1024).unwrap();
                let cache_context = ExecutionCacheContext::new(
                    ContentRoot::new([19; 32]),
                    BuildProfileId::new(7),
                    Mode::Sound,
                );
                for _ in 0..2 {
                    let capture = StdoutCapture::begin_isolated(8, true).unwrap();
                    let value = returned(execute_cached_with_context(
                        program,
                        ExecutionLimits::default(),
                        context(),
                        None,
                        cache_context,
                        &mut caches,
                    ));
                    assert_native_result(&value.value);
                    assert_eq!(capture.finish().bytes, "λ\0🙂\n".as_bytes());

                    // Plans and projection values can be warm, but native ABI
                    // validation must still observe the current command.
                    let capture = StdoutCapture::begin_isolated(8, true).unwrap();
                    assert!(matches!(
                        refused(execute_cached_with_context(
                            program,
                            ExecutionLimits::default(),
                            CommandExecutionContext::UNLIMITED,
                            None,
                            cache_context,
                            &mut caches
                        )),
                        VmRefusal::NativeStdoutContract { .. }
                    ));
                    assert!(capture.finish().bytes.is_empty());
                }
                assert!(caches.stats().hits > 0);
            }
        }
    }
}

#[test]
fn captured_native_reads_are_denied_before_apply_tail_apply_and_returned_continuations() {
    let _lock = LOCK.lock().unwrap_or_else(|error| error.into_inner());
    for tail in [false, true] {
        for continuation in [false, true] {
            let raw = program(tail, continuation, true);
            let owned = owned_program(&raw);
            for program in [&raw, &owned] {
                let refusal = refused(execute_with_context(
                    program,
                    ExecutionLimits::default(),
                    context(),
                    None,
                ));
                assert!(
                    matches!(
                        refusal,
                        VmRefusal::NativeStdoutContract {
                            reason: "captured Reference output does not authorize stream reads"
                        }
                    ),
                    "tail={tail} continuation={continuation}: {refusal:?}"
                );
            }
        }
    }
}
