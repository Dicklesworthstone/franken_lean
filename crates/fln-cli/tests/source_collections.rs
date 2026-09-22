//! Installed collection proofs use the actual source checker, not a model.
#![forbid(unsafe_code)]
use std::{
    path::{Path, PathBuf},
    process::Command,
    sync::atomic::{AtomicUsize, Ordering},
};

static NEXT: AtomicUsize = AtomicUsize::new(0);
fn file(source: &str) -> PathBuf {
    let directory = std::env::temp_dir().join(format!(
        "fln-collection-check-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::create_dir(&directory).unwrap();
    let path = directory.join("collections.lean");
    std::fs::write(&path, source).unwrap();
    path
}
fn run(paths: &[&Path]) -> std::process::Output {
    Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["check-source", "--json"])
        .args(paths)
        .output()
        .expect("installed fln collection checker")
}

#[test]
fn installed_checker_accepts_collection_computation_and_generic_induction() {
    let path = file(include_str!("../../../examples/native_collections.lean"));
    let before = std::fs::read(&path).unwrap();
    let output = run(&[&path]);
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(output.stderr.is_empty());
    let text = String::from_utf8(output.stdout).unwrap();
    for field in [
        "\"schema\":\"fln.source-check/1\"",
        "\"outcome\":\"complete\"",
        "\"authority\":true",
        "\"commands\":9",
        "\"theorems\":8",
        "\"executed\":false",
    ] {
        assert!(text.contains(field), "{text}");
    }
    assert_eq!(std::fs::read(&path).unwrap(), before);
    assert_eq!(
        std::fs::read_dir(path.parent().unwrap()).unwrap().count(),
        1
    );
}

#[test]
fn false_collection_suffixes_emit_no_partial_success_and_allow_recovery() {
    let prefix = file("def values : List Nat := List.cons 5 (List.cons 2 List.nil)");
    let good = file("theorem good : List.foldl Nat.sub 10 values = 3 := by rfl");
    let bad = file("theorem bad : List.foldl Nat.sub 10 values = 5 := by rfl");
    for successful in [true, false, true] {
        let suffix = if successful { &good } else { &bad };
        let output = run(&[&prefix, suffix]);
        assert_eq!(output.status.success(), successful);
        if successful {
            assert!(output.stderr.is_empty());
            let text = String::from_utf8(output.stdout).unwrap();
            for field in ["\"files\":2", "\"theorems\":1", "\"executed\":false"] {
                assert!(text.contains(field), "{text}");
            }
        } else {
            assert!(
                output.stdout.is_empty(),
                "no partial success for the prefix"
            );
            let text = String::from_utf8(output.stderr).unwrap();
            assert!(text.contains("\"outcome\":\"kernel-rejection\""), "{text}");
            assert!(!text.contains("\"outcome\":\"complete\""), "{text}");
        }
    }
}

#[test]
fn installed_collection_execution_exports_and_replays_native_bytecode() {
    let program = include_str!("../../../examples/native_collection_runtime.lean");
    let path = file(program);
    let artifact = path.with_extension("flbc");
    let output = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["run", "--json", "--emit-flbc"])
        .arg(&artifact)
        .arg(&path)
        .output()
        .unwrap();
    assert!(output.status.success(), "{:?}", output);
    assert!(output.stderr.is_empty());
    let report = String::from_utf8(output.stdout).unwrap();
    assert!(report.contains("\"finalValue\":42"), "{report}");
    let retained = std::fs::read(&artifact).unwrap();
    let replay = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["flbc", "run", "--json"])
        .arg(&artifact)
        .output()
        .unwrap();
    assert!(replay.status.success(), "{:?}", replay);
    assert!(replay.stderr.is_empty());
    let report = String::from_utf8(replay.stdout).unwrap();
    assert!(report.contains("\"returnValue\":42"), "{report}");

    let failed = path.with_extension("failed.flbc");
    std::fs::write(
        &path,
        format!("{program}\ntheorem falseSuffix : 0 = 1 := by rfl"),
    )
    .unwrap();
    let refused = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["run", "--json", "--emit-flbc"])
        .arg(&failed)
        .arg(&path)
        .output()
        .unwrap();
    assert!(!refused.status.success());
    assert!(refused.stdout.is_empty());
    assert!(!refused.stderr.is_empty());
    assert!(!failed.exists());
    assert_eq!(std::fs::read(&artifact).unwrap(), retained);
    std::fs::write(&path, program).unwrap();
    let recovered = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["run", "--json"])
        .arg(&path)
        .output()
        .unwrap();
    assert!(recovered.status.success(), "{:?}", recovered);
    assert!(recovered.stderr.is_empty());
    assert_eq!(std::fs::read_to_string(path).unwrap(), program);
}

#[test]
fn lean_personality_executes_owned_collection_payloads() {
    let program = "#eval List.foldl (fun (acc s : String) => acc ++ s) \"\" [\"hello\", \" world\"]\n#eval List.length [true, false]\n";
    let path = file(program);
    let output = Command::new(env!("CARGO_BIN_EXE_lean"))
        .arg(&path)
        .output()
        .unwrap();
    assert!(output.status.success(), "{:?}", output);
    assert!(output.stderr.is_empty());
    assert_eq!(output.stdout, b"\"hello world\"\n2\n");
    assert_eq!(std::fs::read_to_string(path).unwrap(), program);
}
