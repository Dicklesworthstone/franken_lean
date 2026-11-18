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
            // A false `by rfl` is refused while elaborating, as at the pin ("Tactic `rfl`
            // failed: The left-hand side … is not definitionally equal to the right-hand side").
            let text = String::from_utf8(output.stderr).unwrap();
            for expected in [
                "\"outcome\":\"elaboration\"",
                "file 1, command 1, byte 0:",
                "not definitionally equal",
            ] {
                assert!(text.contains(expected), "{text}");
            }
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

fn pinned_lib() -> Option<PathBuf> {
    let lib = std::env::var_os("FLN_REFERENCE_LIB")
        .map(PathBuf::from)
        .or_else(|| {
            std::env::var_os("HOME").map(|home| {
                PathBuf::from(home)
                    .join(".elan/toolchains")
                    .join(format!("leanprover--lean4---{}", fln::OLEAN_PIN_TAG))
                    .join("lib/lean")
            })
        })
        .filter(|lib| lib.join("Init.olean").is_file());
    assert!(
        lib.is_some() || std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
        "the pinned Reference library is required"
    );
    if lib.is_none() {
        eprintln!(
            "SKIP: pinned Reference lib/lean absent for implicit-Init lean personality check"
        );
    }
    lib
}

#[test]
fn lean_personality_executes_owned_collection_payloads() {
    // Unconditional import-free check so hosts without `~/.elan` still exercise
    // owned String/Bool collection payloads end-to-end through the native engine.
    let seed_program = "#eval List.foldl String.append \"\" (List.cons \"hello\" (List.cons \" world\" List.nil))\n";
    let seed_path = file(seed_program);
    let seed_out = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["run", "--json"])
        .arg(&seed_path)
        .output()
        .unwrap();
    assert!(seed_out.status.success(), "{seed_out:?}");
    assert!(seed_out.stderr.is_empty());
    assert!(
        String::from_utf8_lossy(&seed_out.stdout).contains("\"finalValue\":\"hello world\""),
        "{seed_out:?}"
    );
    assert_eq!(std::fs::read_to_string(&seed_path).unwrap(), seed_program);

    let Some(lib) = pinned_lib() else {
        return;
    };
    let program = "prelude\nimport Init.Data.Repr\nimport Init.Data.List.Basic\nimport Init.Data.String.Basic\n#eval List.foldl (fun (acc s : String) => acc ++ s) \"\" [\"hello\", \" world\"]\n#eval List.length [true, false]\n";
    let path = file(program);
    let records = path.parent().unwrap().join("records");
    let output = Command::new(env!("CARGO_BIN_EXE_lean"))
        .arg(&path)
        .env("LEAN_PATH", &lib)
        .env("FLN_IMPORT_REUSE_DIR", &records)
        .output()
        .unwrap();
    assert!(output.status.success(), "{:?}", output);
    assert!(output.stderr.is_empty());
    assert_eq!(output.stdout, b"\"hello world\"\n2\n");
    if let Some(pinned_lean) = lib
        .parent()
        .and_then(Path::parent)
        .map(|toolchain| toolchain.join("bin/lean"))
        .filter(|exe| exe.is_file())
    {
        let ref_out = Command::new(pinned_lean)
            .arg(&path)
            .env("LEAN_PATH", &lib)
            .output()
            .unwrap();
        assert!(ref_out.status.success(), "{ref_out:?}");
        assert_eq!(output.stdout, ref_out.stdout);
    }
    assert_eq!(std::fs::read_to_string(path).unwrap(), program);
}

#[test]
fn named_callbacks_and_constructor_closures_survive_bytecode_roundtrip() {
    let source = "#eval Option.getD (Option.bind (Option.some (List.foldl Nat.add 37 (List.map String.length [\"ab\", \"cde\"]))) Option.some) 0";
    let path = file(source);
    let artifact = path.with_extension("flbc");
    let output = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["run", "--json", "--emit-flbc"])
        .arg(&artifact)
        .arg(&path)
        .output()
        .unwrap();
    assert!(output.status.success(), "{:?}", output);
    assert!(output.stderr.is_empty());
    assert!(String::from_utf8_lossy(&output.stdout).contains("\"finalValue\":42"));
    let retained = std::fs::read(&artifact).unwrap();
    let replay = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["flbc", "run", "--json"])
        .arg(&artifact)
        .output()
        .unwrap();
    assert!(replay.status.success(), "{:?}", replay);
    assert!(replay.stderr.is_empty());
    assert!(String::from_utf8_lossy(&replay.stdout).contains("\"returnValue\":42"));
    assert_eq!(std::fs::read(&artifact).unwrap(), retained);
    assert_eq!(std::fs::read_to_string(path).unwrap(), source);
}
