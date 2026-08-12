//! Real-process producer-to-consumer evidence for the bounded FLBC product seam.
//!
//! This is deliberately narrower than D18: it proves one supported Nat source
//! reaches the filesystem only after batch success and that the exact bytes are
//! consumed by Golem. It does not claim a certified build, general Lean source
//! support, closure-complete reproducibility, or thread-matrix determinism.

#![forbid(unsafe_code)]

use std::path::{Path, PathBuf};
use std::process::{Command, Output};

fn run_fln(arguments: &[&Path]) -> Output {
    let mut command = Command::new(env!("CARGO_BIN_EXE_fln"));
    for argument in arguments {
        command.arg(argument);
    }
    command.output().expect("run the real fln binary")
}

fn utf8(bytes: &[u8]) -> &str {
    std::str::from_utf8(bytes).expect("CLI output is UTF-8")
}

#[test]
fn source_product_crosses_the_filesystem_and_real_golem_consumer() {
    // ubs:ignore — test-only retained scratch discriminator, not a security token.
    let root = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join(format!(
        "flbc-product-e2e-{}-{:?}",
        std::process::id(),
        std::thread::current().id()
    ));
    std::fs::create_dir(&root).expect("create fresh retained integration-test directory");
    let source = root.join("Answer.lean");
    let bad_source = root.join("Open.lean");
    let product = root.join("Answer.flbc");
    let failed_product = root.join("Failed.flbc");
    let collision = root.join("Collision.flbc");
    std::fs::write(
        &source,
        b"def first (x y : Nat) : Nat := x\ndef answer : Nat := first 42 9\n",
    )
    .expect("write supported dependent source batch");
    std::fs::write(&bad_source, b"def open (x : Nat) : Nat := x\n")
        .expect("write non-closed source");

    let failed = run_fln(&[
        Path::new("run"),
        Path::new("--json"),
        Path::new("--emit-flbc"),
        &failed_product,
        &bad_source,
    ]);
    assert!(!failed.status.success());
    assert!(failed.stdout.is_empty());
    assert!(utf8(&failed.stderr).contains("\"schema\":\"fln.source-run/4\""));
    assert!(matches!(
        std::fs::symlink_metadata(&failed_product),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound
    ));

    let produced = run_fln(&[
        Path::new("run"),
        Path::new("--json"),
        Path::new("--emit-flbc"),
        &product,
        &source,
    ]);
    assert!(
        produced.status.success(),
        "producer stderr: {}",
        utf8(&produced.stderr)
    );
    assert!(produced.stderr.is_empty());
    let producer_stdout = utf8(&produced.stdout);
    assert!(producer_stdout.contains("\"schema\":\"fln.source-run/4\""));
    assert!(producer_stdout.contains("\"definitions\":2"));
    assert!(producer_stdout.contains("\"finalValue\":42"));
    assert!(producer_stdout.contains("\"emittedFlbc\":{"));
    let original = std::fs::read(&product).expect("read emitted FLBC product");
    assert!(!original.is_empty());

    let sentinel = b"retained collision sentinel";
    fln::publish_file_atomic(sentinel, &collision).expect("seed existing output");
    let collided = run_fln(&[
        Path::new("run"),
        Path::new("--json"),
        Path::new("--emit-flbc"),
        &collision,
        &source,
    ]);
    assert!(!collided.status.success());
    assert!(collided.stdout.is_empty());
    let collision_stderr = utf8(&collided.stderr);
    assert!(collision_stderr.contains("\"class\":\"output\""));
    assert!(collision_stderr.contains("create target link"));
    assert!(collision_stderr.contains("target not created"));
    assert!(collision_stderr.contains("File exists"));
    assert_eq!(
        std::fs::read(&collision).expect("read retained collision"),
        sentinel,
        "default product publication must never clobber an existing entry"
    );

    let source_before = std::fs::read(&source).expect("read source before alias attempt");
    let aliased = run_fln(&[
        Path::new("run"),
        Path::new("--json"),
        Path::new("--emit-flbc"),
        &source,
        &source,
    ]);
    assert!(!aliased.status.success());
    assert!(aliased.stdout.is_empty());
    assert!(utf8(&aliased.stderr).contains("aliases source input"));
    assert_eq!(
        std::fs::read(&source).expect("read source after alias refusal"),
        source_before
    );

    let consumed = run_fln(&[
        Path::new("flbc"),
        Path::new("run"),
        Path::new("--json"),
        &product,
    ]);
    assert!(
        consumed.status.success(),
        "consumer stderr: {}",
        utf8(&consumed.stderr)
    );
    assert!(consumed.stderr.is_empty());
    let consumer_stdout = utf8(&consumed.stdout);
    assert!(consumer_stdout.contains("\"schema\":\"fln.flbc-run/2\""));
    assert!(consumer_stdout.contains("\"scalarValue\":42"));

    let mut corrupt = original.clone();
    corrupt[0] ^= 0xff;
    fln::publish_file_atomic(&corrupt, &product).expect("publish planted corruption");
    let rejected = run_fln(&[
        Path::new("flbc"),
        Path::new("run"),
        Path::new("--json"),
        &product,
    ]);
    assert!(!rejected.status.success());
    assert!(rejected.stdout.is_empty());
    let rejected_stderr = utf8(&rejected.stderr);
    assert!(rejected_stderr.contains("\"schema\":\"fln.flbc-run/2\""));
    assert!(rejected_stderr.contains("\"class\":\"codec\""));
    assert!(rejected_stderr.contains("FLBC artifact magic mismatch"));

    fln::publish_file_atomic(&original, &product).expect("restore exact product bytes");
    assert_eq!(
        std::fs::read(&product).expect("read restored product"),
        original
    );
    let recovered = run_fln(&[
        Path::new("flbc"),
        Path::new("run"),
        Path::new("--json"),
        &product,
    ]);
    assert!(
        recovered.status.success(),
        "recovery stderr: {}",
        utf8(&recovered.stderr)
    );
    assert!(recovered.stderr.is_empty());
    assert!(utf8(&recovered.stdout).contains("\"scalarValue\":42"));
}
