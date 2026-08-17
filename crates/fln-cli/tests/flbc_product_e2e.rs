//! Real-process producer-to-consumer evidence for the bounded FLBC product seam.
//!
//! This is deliberately narrower than D18: it proves supported checked Nat
//! arithmetic, String, and Bool sources reach the filesystem only after batch success
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

fn fresh_test_root(label: &str) -> PathBuf {
    let parent = PathBuf::from(env!("CARGO_TARGET_TMPDIR"));
    for attempt in 0..1_024_u32 {
        let candidate = parent.join(format!(
            "{label}-{}-{:?}-{attempt}",
            std::process::id(),
            std::thread::current().id()
        ));
        match std::fs::create_dir(&candidate) {
            Ok(()) => return candidate,
            Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => {}
            Err(error) => panic!("create retained integration-test directory: {error}"),
        }
    }
    panic!("could not allocate a retained integration-test directory");
}

#[test]
fn source_import_closure_reaches_the_real_binary_and_refuses_open_graphs() {
    let root = fresh_test_root("source-import-closure-e2e");
    let project = root.join("Project");
    std::fs::create_dir(&project).expect("create module namespace directory");
    let base = project.join("Base.lean");
    let middle = project.join("Middle.lean");
    let main = root.join("Main.lean");
    let product = root.join("Main.flbc");
    std::fs::write(&base, b"def base : Nat := 20\n").expect("write base module");
    std::fs::write(
        &middle,
        b"import Project.Base\ndef middle : Nat := Nat.mul base 2\n",
    )
    .expect("write middle module");
    std::fs::write(&main, b"import Project.Middle\n#eval middle + 2\n")
        .expect("write evaluating entry module");

    let produced = run_fln(&[
        Path::new("run"),
        Path::new("--json"),
        Path::new("--emit-flbc"),
        &product,
        &middle,
        &base,
        &main,
    ]);
    assert!(
        produced.status.success(),
        "module producer stderr: {}",
        utf8(&produced.stderr)
    );
    assert!(produced.stderr.is_empty());
    let stdout = utf8(&produced.stdout);
    assert!(stdout.contains("\"schema\":\"fln.source-run/8\""));
    assert!(stdout.contains("\"commands\":3"));
    assert!(stdout.contains("\"definitions\":2"));
    assert!(stdout.contains("\"evaluations\":1"));
    assert!(stdout.contains("\"finalValue\":42"));

    let consumed = run_fln(&[
        Path::new("flbc"),
        Path::new("run"),
        Path::new("--json"),
        &product,
    ]);
    assert!(
        consumed.status.success(),
        "module consumer stderr: {}",
        utf8(&consumed.stderr)
    );
    assert!(consumed.stderr.is_empty());
    assert!(utf8(&consumed.stdout).contains("\"returnValue\":42"));

    let interleaved_eval = root.join("InterleavedEval.lean");
    let interleaved_product = root.join("InterleavedEval.flbc");
    std::fs::write(
        &interleaved_eval,
        b"#eval Nat.add 40 2\ndef later : Nat := 7\n",
    )
    .expect("write an evaluation followed by a definition");
    let interleaved = run_fln(&[
        Path::new("run"),
        Path::new("--json"),
        Path::new("--emit-flbc"),
        &interleaved_product,
        &interleaved_eval,
    ]);
    assert!(
        interleaved.status.success(),
        "interleaved #eval stderr: {}",
        utf8(&interleaved.stderr)
    );
    assert!(interleaved.stderr.is_empty());
    let interleaved_stdout = utf8(&interleaved.stdout);
    assert!(interleaved_stdout.contains("\"commands\":2"));
    assert!(interleaved_stdout.contains("\"definitions\":1"));
    assert!(interleaved_stdout.contains("\"evaluations\":1"));
    assert!(
        interleaved_stdout
            .contains("\"evaluationResults\":[{\"command\":0,\"kind\":\"nat\",\"value\":42}]")
    );
    assert!(interleaved_stdout.contains("\"finalValue\":7"));
    let pristine_product =
        std::fs::read(&interleaved_product).expect("read the interleaved final product");
    let consumed_interleaved = run_fln(&[
        Path::new("flbc"),
        Path::new("run"),
        Path::new("--json"),
        &interleaved_product,
    ]);
    assert!(
        consumed_interleaved.status.success(),
        "interleaved consumer stderr: {}",
        utf8(&consumed_interleaved.stderr)
    );
    assert!(consumed_interleaved.stderr.is_empty());
    assert!(utf8(&consumed_interleaved.stdout).contains("\"returnValue\":7"));

    let failed_product = root.join("FailedInterleavedEval.flbc");
    std::fs::write(
        &interleaved_eval,
        b"#eval Nat.add 40 2\ndef later : Nat := missing\n",
    )
    .expect("plant a later checked-definition failure");
    let failed_interleaved = run_fln(&[
        Path::new("run"),
        Path::new("--json"),
        Path::new("--emit-flbc"),
        &failed_product,
        &interleaved_eval,
    ]);
    assert!(!failed_interleaved.status.success());
    assert!(failed_interleaved.stdout.is_empty());
    assert!(utf8(&failed_interleaved.stderr).contains("\"class\":\"execution\""));
    assert!(matches!(
        std::fs::symlink_metadata(&failed_product),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound
    ));

    let recovered_product = root.join("RecoveredInterleavedEval.flbc");
    std::fs::write(
        &interleaved_eval,
        b"#eval Nat.add 40 2\ndef later : Nat := 7\n",
    )
    .expect("restore the interleaved source bytes");
    let recovered_eval = run_fln(&[
        Path::new("run"),
        Path::new("--json"),
        Path::new("--emit-flbc"),
        &recovered_product,
        &interleaved_eval,
    ]);
    assert!(
        recovered_eval.status.success(),
        "recovered #eval stderr: {}",
        utf8(&recovered_eval.stderr)
    );
    assert!(recovered_eval.stderr.is_empty());
    let recovered_stdout = utf8(&recovered_eval.stdout);
    assert!(recovered_stdout.contains("\"commands\":2"));
    assert!(recovered_stdout.contains("\"definitions\":1"));
    assert!(recovered_stdout.contains("\"evaluations\":1"));
    assert!(recovered_stdout.contains("\"finalValue\":7"));
    assert_eq!(
        std::fs::read(&recovered_product).expect("read the recovered final product"),
        pristine_product
    );

    let empty_entry = root.join("EmptyEntry.lean");
    let empty_entry_product = root.join("EmptyEntry.flbc");
    std::fs::write(&empty_entry, b"import Project.Base\n")
        .expect("write imports-only entry module");
    let empty_entry_run = run_fln(&[
        Path::new("run"),
        Path::new("--json"),
        Path::new("--emit-flbc"),
        &empty_entry_product,
        &base,
        &empty_entry,
    ]);
    assert!(!empty_entry_run.status.success());
    assert!(empty_entry_run.stdout.is_empty());
    let empty_entry_stderr = utf8(&empty_entry_run.stderr);
    assert!(empty_entry_stderr.contains("\"class\":\"module-graph\""));
    assert!(empty_entry_stderr.contains("\"authority\":false"));
    assert!(empty_entry_stderr.contains("contains no supported command to execute"));
    assert!(matches!(
        std::fs::symlink_metadata(&empty_entry_product),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound
    ));

    std::fs::write(
        &empty_entry,
        b"import Project.Base\ndef answer : Nat := Nat.add base 22\n",
    )
    .expect("repair entry module with an exact final definition");
    let repaired_entry = run_fln(&[
        Path::new("run"),
        Path::new("--json"),
        Path::new("--emit-flbc"),
        &empty_entry_product,
        &base,
        &empty_entry,
    ]);
    assert!(
        repaired_entry.status.success(),
        "repaired entry stderr: {}",
        utf8(&repaired_entry.stderr)
    );
    assert!(repaired_entry.stderr.is_empty());
    assert!(utf8(&repaired_entry.stdout).contains("\"finalValue\":42"));
    assert!(
        !std::fs::read(&empty_entry_product)
            .expect("read repaired entry product")
            .is_empty()
    );

    let missing = root.join("MissingMain.lean");
    std::fs::write(&missing, b"import Project.Absent\ndef answer : Nat := 1\n")
        .expect("write open import graph");
    let refused = run_fln(&[Path::new("run"), Path::new("--json"), &missing]);
    assert!(!refused.status.success());
    assert!(refused.stdout.is_empty());
    let stderr = utf8(&refused.stderr);
    assert!(stderr.contains("\"class\":\"module-graph\""));
    assert!(stderr.contains("\"authority\":false"));
    assert!(stderr.contains("Project.Absent"));

    let cycle_dir = root.join("Cycle");
    std::fs::create_dir(&cycle_dir).expect("create cyclic module namespace");
    let cycle_a = cycle_dir.join("A.lean");
    let cycle_b = cycle_dir.join("B.lean");
    std::fs::write(&cycle_a, b"import Cycle.B\ndef a : Nat := 1\n")
        .expect("write first cyclic module");
    std::fs::write(&cycle_b, b"import Cycle.A\ndef b : Nat := 2\n")
        .expect("write second cyclic module");
    let cycled = run_fln(&[Path::new("run"), Path::new("--json"), &cycle_b, &cycle_a]);
    assert!(!cycled.status.success());
    assert!(cycled.stdout.is_empty());
    let stderr = utf8(&cycled.stderr);
    assert!(stderr.contains("\"class\":\"module-graph\""));
    assert!(stderr.contains("source import graph contains a cycle"));

    let provider = root.join("A.lean");
    let consumer = root.join("B.lean");
    let sibling_main = root.join("SiblingMain.lean");
    let sibling_product = root.join("SiblingMain.flbc");
    std::fs::write(&provider, b"def leaked : Nat := 40\n").expect("write sibling provider");
    std::fs::write(&consumer, b"def borrowed : Nat := Nat.add leaked 1\n")
        .expect("write sibling consumer without its import");
    std::fs::write(
        &sibling_main,
        b"import A\nimport B\ndef answer : Nat := Nat.add borrowed 1\n",
    )
    .expect("write sibling entry");
    let leaked = run_fln(&[
        Path::new("run"),
        Path::new("--json"),
        Path::new("--emit-flbc"),
        &sibling_product,
        &consumer,
        &provider,
        &sibling_main,
    ]);
    assert!(!leaked.status.success());
    assert!(leaked.stdout.is_empty());
    let stderr = utf8(&leaked.stderr);
    assert!(stderr.contains("\"class\":\"module-graph\""));
    assert!(stderr.contains("declaration `borrowed` in module `B`"));
    assert!(stderr.contains("references `leaked` from module `A`"));
    assert!(matches!(
        std::fs::symlink_metadata(&sibling_product),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound
    ));

    std::fs::write(
        &consumer,
        b"import A\ndef borrowed : Nat := Nat.add leaked 1\n",
    )
    .expect("repair sibling consumer with an exact import");
    std::fs::write(
        &sibling_main,
        b"import B\ndef answer : Nat := Nat.add leaked 2\n",
    )
    .expect("exercise visibility through the repaired transitive import chain");
    let recovered = run_fln(&[
        Path::new("run"),
        Path::new("--json"),
        Path::new("--emit-flbc"),
        &sibling_product,
        &provider,
        &consumer,
        &sibling_main,
    ]);
    assert!(
        recovered.status.success(),
        "repaired sibling graph stderr: {}",
        utf8(&recovered.stderr)
    );
    assert!(recovered.stderr.is_empty());
    assert!(utf8(&recovered.stdout).contains("\"finalValue\":42"));
    assert!(
        !std::fs::read(&sibling_product)
            .expect("read repaired sibling product")
            .is_empty()
    );
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
    let string_metric_source = root.join("StringMetric.lean");
    let bounded_nat_source = root.join("BoundedNat.lean");
    let comparison_source = root.join("Comparison.lean");
    let bad_source = root.join("Open.lean");
    let product = root.join("Answer.flbc");
    let string_product = root.join("Message.flbc");
    let string_metric_product = root.join("StringMetric.flbc");
    let bounded_nat_product = root.join("BoundedNat.flbc");
    let comparison_product = root.join("Comparison.flbc");
    let failed_product = root.join("Failed.flbc");
    let collision = root.join("Collision.flbc");
    std::fs::write(
        &source,
        b"def product : Nat := 6 * 7\ndef incremented : Nat := product + 1\ndef answer : Nat := (incremented + 0) - 1\n",
    )
    .expect("write supported dependent source batch");
    std::fs::write(
        &string_source,
        "def copy (value : String) := value\ndef prefix := copy \"artifact\\n\"\ndef message := let output : String := copy prefix ++ \"β\"; output\n"
            .as_bytes(),
    )
    .expect("write supported String source");
    std::fs::write(
        &string_metric_source,
        "def answer := Nat.add (String.length \"βeta\") (String.utf8ByteSize \"βeta\")\n"
            .as_bytes(),
    )
    .expect("write supported String metric source");
    std::fs::write(
        &bounded_nat_source,
        b"def legacy := Nat.add (Nat.pred 9) (Nat.add (Nat.div 20 6) (Nat.add (Nat.mod 20 6) (Nat.add (Nat.gcd 48 18) (Nat.add (Nat.land 12 10) (Nat.add (Nat.lor 12 10) (Nat.xor 12 10))))))\ndef power := Nat.pow 3 4\ndef shifted := Nat.add (Nat.shiftLeft 7 3) (Nat.shiftRight 56 3)\ndef subtotal := Nat.add legacy (Nat.add power (Nat.add (Nat.log2 8) shifted))\ndef huge := 1208925819614629174706176\ndef answer := Nat.add huge subtotal\n",
    )
    .expect("write supported bounded Nat source");
    std::fs::write(
        &comparison_source,
        "def choose (left right : Bool) : Bool := left\n#eval false\ndef natEq : Bool := Nat.beq 42 42\ndef natLe : Bool := Nat.ble 41 42\ndef stringEq : Bool := String.decEq \"βeta\" \"βeta\"\ndef literal := true\ndef answer : Bool := choose (choose natEq natLe) (choose stringEq literal)\n"
            .as_bytes(),
    )
    .expect("write supported Bool comparison source");
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
    assert!(utf8(&failed.stderr).contains("\"schema\":\"fln.source-run/8\""));
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
    assert!(producer_stdout.contains("\"schema\":\"fln.source-run/8\""));
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
    assert!(string_producer_stdout.contains("\"definitions\":3"));
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

    let string_metric_produced = run_fln(&[
        Path::new("run"),
        Path::new("--json"),
        Path::new("--emit-flbc"),
        &string_metric_product,
        &string_metric_source,
    ]);
    assert!(
        string_metric_produced.status.success(),
        "String metric producer stderr: {}",
        utf8(&string_metric_produced.stderr)
    );
    assert!(string_metric_produced.stderr.is_empty());
    let string_metric_stdout = utf8(&string_metric_produced.stdout);
    assert!(string_metric_stdout.contains("\"definitions\":1"));
    assert!(string_metric_stdout.contains("\"finalValue\":9"));
    let string_metric_consumed = run_fln(&[
        Path::new("flbc"),
        Path::new("run"),
        Path::new("--json"),
        &string_metric_product,
    ]);
    assert!(
        string_metric_consumed.status.success(),
        "String metric consumer stderr: {}",
        utf8(&string_metric_consumed.stderr)
    );
    assert!(string_metric_consumed.stderr.is_empty());
    assert!(utf8(&string_metric_consumed.stdout).contains("\"returnValue\":9"));

    let bounded_nat_produced = run_fln(&[
        Path::new("run"),
        Path::new("--json"),
        Path::new("--emit-flbc"),
        &bounded_nat_product,
        &bounded_nat_source,
    ]);
    assert!(
        bounded_nat_produced.status.success(),
        "bounded Nat producer stderr: {}",
        utf8(&bounded_nat_produced.stderr)
    );
    assert!(bounded_nat_produced.stderr.is_empty());
    let bounded_nat_stdout = utf8(&bounded_nat_produced.stdout);
    assert!(bounded_nat_stdout.contains("\"definitions\":6"));
    assert!(bounded_nat_stdout.contains("\"finalValue\":1208925819614629174706370"));
    let bounded_nat_consumed = run_fln(&[
        Path::new("flbc"),
        Path::new("run"),
        Path::new("--json"),
        &bounded_nat_product,
    ]);
    assert!(
        bounded_nat_consumed.status.success(),
        "bounded Nat consumer stderr: {}",
        utf8(&bounded_nat_consumed.stderr)
    );
    assert!(bounded_nat_consumed.stderr.is_empty());
    assert!(
        utf8(&bounded_nat_consumed.stdout).contains("\"returnValue\":1208925819614629174706370")
    );

    let comparison_produced = run_fln(&[
        Path::new("run"),
        Path::new("--json"),
        Path::new("--emit-flbc"),
        &comparison_product,
        &comparison_source,
    ]);
    assert!(
        comparison_produced.status.success(),
        "comparison producer stderr: {}",
        utf8(&comparison_produced.stderr)
    );
    assert!(comparison_produced.stderr.is_empty());
    let comparison_stdout = utf8(&comparison_produced.stdout);
    assert!(comparison_stdout.contains("\"definitions\":6"));
    assert!(comparison_stdout.contains("\"evaluations\":1"));
    assert!(
        comparison_stdout
            .contains("\"evaluationResults\":[{\"command\":1,\"kind\":\"bool\",\"value\":false}]")
    );
    assert!(comparison_stdout.contains("\"finalKind\":\"bool\""));
    assert!(comparison_stdout.contains("\"finalValue\":true"));
    let comparison_consumed = run_fln(&[
        Path::new("flbc"),
        Path::new("run"),
        Path::new("--json"),
        &comparison_product,
    ]);
    assert!(
        comparison_consumed.status.success(),
        "comparison consumer stderr: {}",
        utf8(&comparison_consumed.stderr)
    );
    assert!(comparison_consumed.stderr.is_empty());
    assert!(utf8(&comparison_consumed.stdout).contains("\"returnValue\":1"));

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
        b"def product : Nat := Nat.mul 6 7\ndef incremented : Nat := Nat.add product 1\ndef answer : Nat := Nat.sub (Nat.add incremented 0) 1\n",
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
    assert!(first_stdout.contains("\"schema\":\"fln.source-run/8\""));
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
