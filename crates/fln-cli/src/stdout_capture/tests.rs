use super::{MAX_DOCUMENT_BYTES, attach, json};
use crate::MultiplexerOutput;
use fln_rt::obj::Obj;

fn write(text: &str) {
    let callback = Obj::stdio_stdout().unwrap().try_ctor_child(4).unwrap();
    callback
        .try_stdio_put_str(&Obj::mk_string(text), &Obj::mk_nat(0))
        .unwrap();
}

#[test]
fn json_capture_preserves_silent_success_and_error_bytes() {
    for output in [
        MultiplexerOutput::success("{\"value\":42}\n".to_owned()),
        MultiplexerOutput::failure(
            "{\"class\":\"io-exception\",\"authority\":true}\n".to_owned(),
            1,
        ),
    ] {
        let expected = (
            output.exit_code,
            output.stdout.clone(),
            output.stderr.clone(),
        );
        let actual = json(true, "test", || output);
        assert_eq!((actual.exit_code, actual.stdout, actual.stderr), expected);
    }
}

#[test]
fn json_capture_preserves_success_failure_and_panic_prefixes() {
    let success = json(true, "test", || {
        write("λ🙂\0\"\n");
        MultiplexerOutput::success("{\"value\":42}\n".to_owned())
    });
    assert_eq!(
        success.stdout,
        "{\"value\":42,\"stdout\":\"λ🙂\\u0000\\\"\\n\"}\n"
    );
    assert!(success.stderr.is_empty());
    let failure = json(true, "test", || {
        write("before error\n");
        MultiplexerOutput::failure("{\"class\":\"io-error\"}\n".to_owned(), 1)
    });
    assert_eq!(failure.exit_code, 1);
    assert!(failure.stdout.is_empty());
    assert_eq!(
        failure.stderr,
        "{\"class\":\"io-error\",\"stdout\":\"before error\\n\"}\n"
    );
    let panic = json(true, "test", || {
        write("before fault");
        panic!("intentional worker failure")
    });
    assert_eq!(panic.exit_code, 4);
    assert!(panic.stderr.contains("\"stdout\":\"before fault\""));
    let restored = json(true, "test", || {
        write("next request");
        MultiplexerOutput::success("{}\n".to_owned())
    });
    assert_eq!(restored.stdout, "{\"stdout\":\"next request\"}\n");
}

#[test]
fn json_capture_document_limit_retains_complete_stdout_in_resource_error() {
    let oversized = MultiplexerOutput::success(format!(
        "{{\"metadata\":\"{}\"}}\n",
        "x".repeat(MAX_DOCUMENT_BYTES)
    ));
    let result = attach("test", oversized, b"accepted prefix");
    assert_eq!(result.exit_code, 3);
    assert!(result.stdout.is_empty());
    assert!(result.stderr.contains("\"authority\":false"));
    assert!(result.stderr.contains("\"stdout\":\"accepted prefix\""));
    assert!(result.stderr.len() < MAX_DOCUMENT_BYTES);
}

#[test]
fn json_import_probe_fallback_does_not_install_a_lingering_capture() {
    assert!(super::optional_json(true, "test", || None).is_none());
    let result = json(true, "test", || {
        write("after fallback");
        MultiplexerOutput::success("{\"value\":1}\n".to_owned())
    });
    assert!(result.stdout.contains("\"stdout\":\"after fallback\""));
}

#[test]
fn json_panic_router_is_thread_local_and_keeps_process_error_json_clean() {
    const TEST: &str = "stdout_capture::tests::json_panic_router_is_thread_local_and_keeps_process_error_json_clean";
    const CHILD: &str = "FLN_JSON_PANIC_ROUTER_CASE";
    if std::env::var(CHILD).as_deref() != Ok("child") {
        let output = std::process::Command::new(std::env::current_exe().unwrap())
            .args(["--exact", TEST, "--nocapture", "--test-threads=1"])
            .env(CHILD, "child")
            .output()
            .unwrap();
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(
            output.status.success() && stdout.contains("1 passed; 0 failed;"),
            "{stdout}\n{stderr}"
        );
        assert!(stdout.contains("\"stdout\":\"before worker fault\""));
        assert!(stderr.contains("OTHER_THREAD_PANIC"));
        assert!(!stderr.contains("JSON_WORKER_PANIC"));
        return;
    }
    crate::install_json_execution_panic_hook();
    let output = std::thread::spawn(|| {
        json(true, "test", || {
            write("before worker fault");
            let other = std::thread::spawn(|| panic!("OTHER_THREAD_PANIC"));
            assert!(other.join().is_err());
            panic!("JSON_WORKER_PANIC")
        })
    })
    .join()
    .unwrap();
    assert_eq!(output.exit_code, 4);
    print!("{}", output.stderr);
}
