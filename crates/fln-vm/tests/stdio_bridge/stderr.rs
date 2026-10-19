//! stderr uses the existing guarded native callback protocol, not stdout capture.
#![forbid(unsafe_code)]
use super::*;

fn getter(dst: u16) -> I {
    let mut call = get_stdout(dst);
    let I::Intrinsic { row, .. } = &mut call else {
        unreachable!()
    };
    let stderr = EXTERN_ROWS
        .iter()
        .find(|row| row.id == "extern:IO.getStderr")
        .unwrap();
    assert_eq!(stderr.symbol, "lean_get_stderr");
    assert_eq!(stderr.arity, 0);
    assert_eq!(stderr.ownership, "rule(borrowed-args,owned-result)");
    *row = stderr.id.to_owned();
    call
}

fn write_program(tail: bool, message: &str) -> ValidatedProgram {
    let mut code = callback_prefix(4);
    code[0] = getter(0);
    code[2] = I::String {
        dst: r(2),
        value: message.to_owned(),
    };
    if tail {
        code.push(I::TailApply {
            closure: r(1),
            args: vec![r(2), r(3)],
            argument_ownership: vec![A::Borrowed; 2],
            result_ownership: R::Owned,
        });
    } else {
        code.push(I::Apply {
            dst: r(4),
            closure: r(1),
            args: vec![r(2), r(3)],
            argument_ownership: vec![A::Borrowed; 2],
            result_ownership: R::Owned,
        });
        code.push(I::Return { src: r(4) });
    }
    raw_program(vec![function(0, vec![], R::Owned, 5, code)])
}

#[test]
fn stderr_writes_real_bytes_outside_stdout_capture_and_replays_warm_calls() {
    const CASE: &str =
        "stderr::stderr_writes_real_bytes_outside_stdout_capture_and_replays_warm_calls";
    const CHILD: &str = "FLN_STDERR_EXECUTION_CHILD";
    const MESSAGE: &str = "stderr λ🙂\0tail\n";
    if std::env::var(CHILD).as_deref() != Ok(CASE) {
        let output = std::process::Command::new(std::env::current_exe().unwrap())
            .args(["--exact", CASE, "--nocapture", "--test-threads=1"])
            .env(CHILD, CASE)
            .output()
            .unwrap();
        assert!(output.status.success(), "{output:?}");
        assert_eq!(output.stderr, MESSAGE.repeat(12).as_bytes());
        assert!(!String::from_utf8_lossy(&output.stdout).contains(MESSAGE));
        assert!(String::from_utf8_lossy(&output.stdout).contains("1 passed; 0 failed; 0 ignored"));
        return;
    }
    shadow::enable();
    drop(Obj::stdio_stderr().unwrap());
    {
        let capture = fln_rt::obj::StdoutCapture::begin(1).unwrap();
        for tail in [false, true] {
            let raw = write_program(tail, MESSAGE);
            let owned = owned_program(&raw);
            for program in [&raw, &owned] {
                let mut cache = InlineCaches::try_new(1024).unwrap();
                let context = ExecutionCacheContext::new(
                    ContentRoot::new([63; 32]),
                    BuildProfileId::new(73),
                    Mode::Faithful,
                );
                for _ in 0..3 {
                    let result = returned(execute_cached(
                        program,
                        ExecutionLimits::default(),
                        None,
                        context,
                        &mut cache,
                    ));
                    assert_success_packet(&result.value);
                }
                assert!(cache.stats().hits > 0);
            }
        }
        let output = capture.finish();
        assert!(output.bytes.is_empty());
        assert_eq!(output.error, None);
    }
    no_leaks();
}

#[test]
fn stderr_getter_returns_only_the_checked_six_method_native_stream() {
    let program = raw_program(vec![function(
        0,
        vec![],
        R::Owned,
        1,
        vec![getter(0), I::Return { src: r(0) }],
    )]);
    for program in [&program, &owned_program(&program)] {
        let value = returned(execute(program, ExecutionLimits::default(), None)).value;
        assert_eq!(value.header().other, 6);
        for field in 0..6 {
            let callback = value.try_ctor_child(field).unwrap();
            assert_eq!(callback.is_stdio_put_str_closure(), field == 4);
            assert_eq!(callback.is_stdio_get_line_closure(), field == 3);
        }
    }
}
