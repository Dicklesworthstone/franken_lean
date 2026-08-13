//! Real-process producer-to-consumer evidence for the bounded FLBC product seam.
//!
//! This is deliberately narrower than D18: it proves supported checked Nat
//! arithmetic and String sources reach the filesystem only after batch success
//! and that their exact bytes are consumed by Golem. It does not claim a
//! certified build, general Lean source support, closure-complete
//! reproducibility, or thread-matrix determinism.

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
    let string_source = root.join("Message.lean");
    let bad_source = root.join("Open.lean");
    let product = root.join("Answer.flbc");
    let string_product = root.join("Message.flbc");
    let failed_product = root.join("Failed.flbc");
    let collision = root.join("Collision.flbc");
    std::fs::write(
        &source,
        b"def product : Nat := Nat.mul 6 7\ndef incremented : Nat := Nat.add product 1\ndef answer : Nat := Nat.sub incremented 1\n",
    )
    .expect("write supported dependent source batch");
    std::fs::write(
        &string_source,
        "def copy (value : String) := value\ndef message := let output : String := copy \"artifact\\nβ\"; output\n"
            .as_bytes(),
    )
    .expect("write supported String source");
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
    assert!(utf8(&failed.stderr).contains("\"schema\":\"fln.source-run/5\""));
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
    assert!(producer_stdout.contains("\"schema\":\"fln.source-run/5\""));
    assert!(producer_stdout.contains("\"definitions\":3"));
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
    assert!(consumer_stdout.contains("\"schema\":\"fln.flbc-run/3\""));
    assert!(consumer_stdout.contains("\"returnValue\":42"));

    let string_produced = run_fln(&[
        Path::new("run"),
        Path::new("--json"),
        Path::new("--emit-flbc"),
        &string_product,
        &string_source,
    ]);
    assert!(
        string_produced.status.success(),
        "String producer stderr: {}",
        utf8(&string_produced.stderr)
    );
    assert!(string_produced.stderr.is_empty());
    let string_producer_stdout = utf8(&string_produced.stdout);
    assert!(string_producer_stdout.contains("\"definitions\":2"));
    assert!(string_producer_stdout.contains("\"finalKind\":\"string\""));
    assert!(string_producer_stdout.contains("\"finalValue\":\"artifact\\nβ\""));
    assert!(string_producer_stdout.contains("\"emittedFlbc\":{"));
    let original_string = std::fs::read(&string_product).expect("read emitted String FLBC product");
    assert!(!original_string.is_empty());

    let string_consumed = run_fln(&[
        Path::new("flbc"),
        Path::new("run"),
        Path::new("--json"),
        &string_product,
    ]);
    assert!(
        string_consumed.status.success(),
        "String consumer stderr: {}",
        utf8(&string_consumed.stderr)
    );
    assert!(string_consumed.stderr.is_empty());
    let string_consumer_stdout = utf8(&string_consumed.stdout).to_owned();
    assert!(string_consumer_stdout.contains("\"schema\":\"fln.flbc-run/3\""));
    assert!(string_consumer_stdout.contains("\"returnKind\":\"string\""));
    assert!(string_consumer_stdout.contains("\"returnValue\":\"artifact\\nβ\""));

    let mut corrupt_string = original_string.clone();
    corrupt_string[0] ^= 0xff;
    fln::publish_file_atomic(&corrupt_string, &string_product)
        .expect("publish planted String corruption");
    let string_rejected = run_fln(&[
        Path::new("flbc"),
        Path::new("run"),
        Path::new("--json"),
        &string_product,
    ]);
    assert!(!string_rejected.status.success());
    assert!(string_rejected.stdout.is_empty());
    let string_rejected_stderr = utf8(&string_rejected.stderr);
    assert!(string_rejected_stderr.contains("\"schema\":\"fln.flbc-run/3\""));
    assert!(string_rejected_stderr.contains("\"class\":\"codec\""));
    assert!(string_rejected_stderr.contains("FLBC artifact magic mismatch"));

    fln::publish_file_atomic(&original_string, &string_product)
        .expect("restore exact String product bytes");
    assert_eq!(
        std::fs::read(&string_product).expect("read restored String product"),
        original_string
    );
    let string_recovered = run_fln(&[
        Path::new("flbc"),
        Path::new("run"),
        Path::new("--json"),
        &string_product,
    ]);
    assert!(
        string_recovered.status.success(),
        "String recovery stderr: {}",
        utf8(&string_recovered.stderr)
    );
    assert!(string_recovered.stderr.is_empty());
    assert_eq!(utf8(&string_recovered.stdout), string_consumer_stdout);

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
    assert!(rejected_stderr.contains("\"schema\":\"fln.flbc-run/3\""));
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
    assert!(utf8(&recovered.stdout).contains("\"returnValue\":42"));
}

/// Real-process D18 increment for the live `fln-cli` product root.
///
/// This proves the sidecar that the CLI actually emits: two isolated producer
/// invocations are byte-identical, the sound consumer binds that pair, a
/// frontier-tagged sidecar and a 12-component (omitted-closure) sidecar are
/// both refused before Golem runs, and restoring the original pair recovers.
/// Concurrent consumers of the restored pair return identical JSON.
///
/// It does not claim a certified profile, mode-separated cache reuse, 1/8/32
/// engine scheduling, or general Lean. Those remain open on
/// `fln-d18-product-half-rgsg`.
#[test]
fn d18_sidecar_isolated_rebuilds_refuse_plants_and_recover() {
    // ubs:ignore — test-only retained scratch discriminator, not a security token.
    let root = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join(format!(
        "d18-sidecar-e2e-{}-{:?}",
        std::process::id(),
        std::thread::current().id()
    ));
    std::fs::create_dir(&root).expect("create retained D18 integration-test directory");
    let source = root.join("Answer.lean");
    std::fs::write(
        &source,
        b"def product : Nat := Nat.mul 6 7\ndef incremented : Nat := Nat.add product 1\ndef answer : Nat := Nat.sub incremented 1\n",
    )
    .expect("write supported dependent source batch");

    let first_product = root.join("first.flbc");
    let first_sidecar = root.join("first.sidecar");
    let second_product = root.join("second.flbc");
    let second_sidecar = root.join("second.sidecar");

    let first = run_fln(&[
        Path::new("run"),
        Path::new("--json"),
        Path::new("--emit-flbc"),
        &first_product,
        Path::new("--emit-sidecar"),
        &first_sidecar,
        &source,
    ]);
    assert!(
        first.status.success(),
        "first isolated producer stderr: {}",
        utf8(&first.stderr)
    );
    assert!(first.stderr.is_empty());
    let first_stdout = utf8(&first.stdout);
    assert!(first_stdout.contains("\"schema\":\"fln.source-run/5\""));
    assert!(first_stdout.contains("\"finalValue\":42"));
    assert!(first_stdout.contains("\"emittedSidecar\":{"));
    assert!(first_stdout.contains("\"profile\":\"standard\""));

    let second = run_fln(&[
        Path::new("run"),
        Path::new("--json"),
        Path::new("--emit-flbc"),
        &second_product,
        Path::new("--emit-sidecar"),
        &second_sidecar,
        &source,
    ]);
    assert!(
        second.status.success(),
        "second isolated producer stderr: {}",
        utf8(&second.stderr)
    );
    assert!(second.stderr.is_empty());
    let product = std::fs::read(&first_product).expect("read first product");
    let sidecar = std::fs::read(&first_sidecar).expect("read first sidecar");
    assert_eq!(
        product,
        std::fs::read(&second_product).expect("read second product"),
        "two isolated standard-profile builds must emit byte-identical FLBC"
    );
    assert_eq!(
        sidecar,
        std::fs::read(&second_sidecar).expect("read second sidecar"),
        "two isolated standard-profile builds must emit byte-identical sidecars"
    );
    assert!(!product.is_empty());
    assert!(!sidecar.is_empty());
    fln::decode_flbc_product_sidecar(&sidecar).expect("emitted sidecar decodes");

    let bound = run_fln(&[
        Path::new("flbc"),
        Path::new("run"),
        Path::new("--json"),
        Path::new("--sidecar"),
        &first_sidecar,
        &first_product,
    ]);
    assert!(
        bound.status.success(),
        "bound consumer stderr: {}",
        utf8(&bound.stderr)
    );
    assert!(bound.stderr.is_empty());
    let bound_stdout = utf8(&bound.stdout).to_owned();
    assert!(bound_stdout.contains("\"schema\":\"fln.flbc-run/3\""));
    assert!(bound_stdout.contains("\"returnValue\":42"));
    assert!(bound_stdout.contains("\"sidecar\":{\"verified\":true"));

    let mode_at = sidecar_mode_offset(&sidecar);
    assert_eq!(sidecar[mode_at], 2, "producer emits the sound mode tag");
    let mut frontier = sidecar.clone();
    frontier[mode_at] = 3;
    fln::publish_file_atomic(&frontier, &first_sidecar).expect("plant frontier-tagged sidecar");
    let contaminated = run_fln(&[
        Path::new("flbc"),
        Path::new("run"),
        Path::new("--json"),
        Path::new("--sidecar"),
        &first_sidecar,
        &first_product,
    ]);
    assert!(!contaminated.status.success());
    assert!(contaminated.stdout.is_empty());
    let contaminated_stderr = utf8(&contaminated.stderr);
    assert!(contaminated_stderr.contains("\"schema\":\"fln.flbc-run/3\""));
    assert!(contaminated_stderr.contains("\"class\":\"sidecar\""));
    assert!(contaminated_stderr.contains("product coordinate mode"));

    fln::publish_file_atomic(&sidecar, &first_sidecar).expect("restore exact sidecar");
    let after_frontier = run_fln(&[
        Path::new("flbc"),
        Path::new("run"),
        Path::new("--json"),
        Path::new("--sidecar"),
        &first_sidecar,
        &first_product,
    ]);
    assert!(
        after_frontier.status.success(),
        "post-frontier recovery stderr: {}",
        utf8(&after_frontier.stderr)
    );
    assert_eq!(utf8(&after_frontier.stdout), bound_stdout);

    let count_at = sidecar_component_count_offset(&sidecar);
    let mut omitted = sidecar.clone();
    omitted[count_at..count_at + 8].copy_from_slice(&12_u64.to_le_bytes());
    let planted = fln::decode_flbc_product_sidecar(&omitted)
        .expect_err("a 12-component sidecar must not decode");
    let planted_text = planted.to_string();
    assert!(
        planted_text.contains("all 13 closure components"),
        "component-count plant must be the omission refusal, not a nearby field: {planted_text}"
    );
    fln::publish_file_atomic(&omitted, &first_sidecar).expect("plant omitted-closure sidecar");
    let omitted_run = run_fln(&[
        Path::new("flbc"),
        Path::new("run"),
        Path::new("--json"),
        Path::new("--sidecar"),
        &first_sidecar,
        &first_product,
    ]);
    assert!(!omitted_run.status.success());
    assert!(omitted_run.stdout.is_empty());
    let omitted_stderr = utf8(&omitted_run.stderr);
    assert!(
        omitted_stderr.contains("\"class\":\"sidecar\""),
        "omitted-closure consumer stderr: {omitted_stderr}"
    );
    assert!(
        omitted_stderr.contains("all 13 closure components"),
        "omitted-closure consumer must quote the planted decode refusal: {omitted_stderr}"
    );

    fln::publish_file_atomic(&sidecar, &first_sidecar)
        .expect("restore exact sidecar after omission");
    let recovered = run_fln(&[
        Path::new("flbc"),
        Path::new("run"),
        Path::new("--json"),
        Path::new("--sidecar"),
        &first_sidecar,
        &first_product,
    ]);
    assert!(
        recovered.status.success(),
        "post-omission recovery stderr: {}",
        utf8(&recovered.stderr)
    );
    assert_eq!(utf8(&recovered.stdout), bound_stdout);

    let product_path = first_product.clone();
    let sidecar_path = first_sidecar.clone();
    let expected = bound_stdout.clone();
    std::thread::scope(|scope| {
        let handles: Vec<_> = (0..3)
            .map(|_| {
                let product_path = product_path.clone();
                let sidecar_path = sidecar_path.clone();
                let expected = expected.clone();
                scope.spawn(move || {
                    let output = run_fln(&[
                        Path::new("flbc"),
                        Path::new("run"),
                        Path::new("--json"),
                        Path::new("--sidecar"),
                        &sidecar_path,
                        &product_path,
                    ]);
                    assert!(
                        output.status.success(),
                        "concurrent consumer stderr: {}",
                        utf8(&output.stderr)
                    );
                    assert_eq!(utf8(&output.stdout), expected);
                })
            })
            .collect();
        for handle in handles {
            handle.join().expect("concurrent consumer thread");
        }
    });
}

fn sidecar_schema_body_offset(bytes: &[u8]) -> usize {
    const NAME: &[u8] = b"fln.canon.flbc-product-sidecar";
    assert!(
        bytes.len() >= 10,
        "sidecar is too small to carry a schema header"
    );
    let name_len = usize::try_from(u64::from_le_bytes(
        bytes[0..8].try_into().expect("schema name length"),
    ))
    .expect("schema name length fits this host");
    let name_end = 8 + name_len;
    assert_eq!(
        &bytes[8..name_end],
        NAME,
        "plant offsets are only valid for the live sidecar schema"
    );
    name_end + 2
}

fn sidecar_mode_offset(bytes: &[u8]) -> usize {
    sidecar_schema_body_offset(bytes)
}

fn sidecar_component_count_offset(bytes: &[u8]) -> usize {
    // write_u128 is length-prefixed (`u64` length + 16 payload bytes), not a
    // bare 16-byte integer. After the mode tag: epoch, CGSE, determinism u8,
    // profile u8, target, build profile, then the component count.
    const PREFIXED_U128: usize = 8 + 16;
    sidecar_schema_body_offset(bytes)
        + 1
        + PREFIXED_U128
        + PREFIXED_U128
        + 1
        + 1
        + PREFIXED_U128
        + PREFIXED_U128
}
