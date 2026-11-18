//! Installed monadic source compilation, canonical artifact replay and refusal.
#![forbid(unsafe_code)]
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

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
        .filter(|lib| lib.join("Init/Data/Repr.olean").is_file());
    assert!(
        lib.is_some() || std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
        "the pinned Reference library is required"
    );
    if lib.is_none() {
        eprintln!("SKIP: pinned Reference lib/lean absent for Init.Data.Repr import checks");
    }
    lib
}

fn success(output: Output) -> String {
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(output.stderr.is_empty());
    String::from_utf8(output.stdout).unwrap()
}

const SEED_DO_PROGRAM: &str = r#"class Pure (f : Type -> Type) where
  pure : {A : Type} -> A -> f A

class Bind (m : Type -> Type) where
  bind : {A B : Type} -> m A -> (A -> m B) -> m B

abbrev Id (A : Type) : Type := A
instance idPure : Pure Id := { pure := fun a => a }
instance idBind : Bind Id := { bind := fun a k => k a }

def mapping {M : Type -> Type} [Pure M] [Bind M]
    {A B : Type} (f : A -> B) (action : M A) : M B := do
  let x ← action
  return (f x)

def answer : Id Nat := do
  let n ← mapping (M := Id) (fun (x : Nat) => x + 1) (Pure.pure (f := Id) 40)
  return (n + 1)

theorem answerValue : answer = 42 := by rfl
"#;

#[test]
fn native_do_checks_executes_exports_and_replays_through_installed_commands() {
    let dir = std::env::temp_dir().join(format!("fln-native-do-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();

    // Import-free seed-world exercise runs unconditionally on every worker.
    let seed_source = dir.join("SeedExample.lean");
    let seed_artifact = dir.join("SeedExample.flbc");
    std::fs::write(&seed_source, SEED_DO_PROGRAM).unwrap();
    let seed_checked = success(
        Command::new(env!("CARGO_BIN_EXE_fln"))
            .args(["check-source", "--json"])
            .arg(&seed_source)
            .output()
            .unwrap(),
    );
    assert!(
        seed_checked.contains("\"authority\":true"),
        "{seed_checked}"
    );
    assert!(seed_checked.contains("\"theorems\":1"), "{seed_checked}");
    std::fs::write(&seed_source, format!("{SEED_DO_PROGRAM}\n#eval answer\n")).unwrap();
    let seed_run = success(
        Command::new(env!("CARGO_BIN_EXE_fln"))
            .args(["run", "--json", "--emit-flbc"])
            .arg(&seed_artifact)
            .arg(&seed_source)
            .output()
            .unwrap(),
    );
    assert!(seed_run.contains("\"authority\":true"), "{seed_run}");
    assert!(seed_run.contains("\"finalValue\":42"), "{seed_run}");
    let seed_replay = success(
        Command::new(env!("CARGO_BIN_EXE_fln"))
            .args(["flbc", "run", "--json"])
            .arg(&seed_artifact)
            .output()
            .unwrap(),
    );
    assert!(seed_replay.contains("\"returnValue\":42"), "{seed_replay}");

    let Some(lib) = pinned_lib() else {
        return;
    };
    let records = dir.join("records");
    let source = dir.join("Example.lean");
    let artifact = dir.join("Example.flbc");
    let proof = include_str!("../../../examples/native_do.lean");
    std::fs::write(&source, proof).unwrap();
    let checked = success(
        Command::new(env!("CARGO_BIN_EXE_fln"))
            .args(["check-source", "--json"])
            .arg(&source)
            .env("LEAN_PATH", &lib)
            .env("FLN_IMPORT_REUSE_DIR", &records)
            .output()
            .unwrap(),
    );
    assert!(checked.contains("\"authority\":true"), "{checked}");
    assert!(checked.contains("\"theorems\":1"), "{checked}");
    let program = format!("{proof}\n#eval answer\n");
    std::fs::write(&source, &program).unwrap();
    assert_eq!(
        success(
            Command::new(env!("CARGO_BIN_EXE_lean"))
                .arg(&source)
                .env("LEAN_PATH", &lib)
                .env("FLN_IMPORT_REUSE_DIR", &records)
                .output()
                .unwrap()
        ),
        "42\n"
    );
    let run = success(
        Command::new(env!("CARGO_BIN_EXE_fln"))
            .args(["run", "--json", "--emit-flbc"])
            .arg(&artifact)
            .arg(&source)
            .env("LEAN_PATH", &lib)
            .env("FLN_IMPORT_REUSE_DIR", &records)
            .output()
            .unwrap(),
    );
    assert!(run.contains("\"authority\":true"), "{run}");
    assert!(run.contains("\"evaluations\":1"), "{run}");
    assert!(run.contains("\"kind\":\"nat\",\"value\":42"), "{run}");
    let replay = success(
        Command::new(env!("CARGO_BIN_EXE_fln"))
            .args(["flbc", "run", "--json"])
            .arg(&artifact)
            .output()
            .unwrap(),
    );
    assert!(replay.contains("\"returnValue\":42"), "{replay}");
    let retained = std::fs::read(&artifact).unwrap();
    let failed_path = dir.join("Failed.flbc");
    std::fs::write(
        &source,
        format!("{program}\ndef invalid.{{u}} {{A : Type u}} (a : A) : A := 7"),
    )
    .unwrap();
    let failure = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["run", "--json", "--emit-flbc"])
        .arg(&failed_path)
        .arg(&source)
        .env("LEAN_PATH", &lib)
        .env("FLN_IMPORT_REUSE_DIR", &records)
        .output()
        .unwrap();
    assert!(!failure.status.success());
    assert!(failure.stdout.is_empty());
    assert!(!failure.stderr.is_empty());
    assert!(!failed_path.exists());
    assert_eq!(std::fs::read(&artifact).unwrap(), retained);
}

#[test]
fn alias_results_keep_bool_nat_and_string_distinct_in_both_presentations() {
    let dir = std::env::temp_dir().join(format!("fln-native-do-kinds-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();

    // Unconditional import-free kind check.
    for (ty, expr, expected) in [
        ("Bool", "true", "\"finalValue\":true"),
        ("String", "\"hello\"", "\"finalValue\":\"hello\""),
        ("Nat", "1", "\"finalValue\":1"),
    ] {
        let seed_source = dir.join("SeedKinds.lean");
        std::fs::write(
            &seed_source,
            format!("{SEED_DO_PROGRAM}\ndef v : Id {ty} := do return {expr}\n#eval v\n"),
        )
        .unwrap();
        let out = success(
            Command::new(env!("CARGO_BIN_EXE_fln"))
                .args(["run", "--json"])
                .arg(&seed_source)
                .output()
                .unwrap(),
        );
        assert!(out.contains(expected), "{out}");
    }

    let Some(lib) = pinned_lib() else {
        return;
    };
    let records = dir.join("records");
    let source = dir.join("Kinds.lean");
    let proof = include_str!("../../../examples/native_do.lean");
    std::fs::write(&source, format!("{proof}\ndef boolAnswer : Id Bool := do return true\ndef stringAnswer : Id String := do return \"hello\"\ndef natAnswer : Id Nat := do return 1\n#eval boolAnswer\n#eval stringAnswer\n#eval natAnswer\n")).unwrap();
    assert_eq!(
        success(
            Command::new(env!("CARGO_BIN_EXE_lean"))
                .arg(&source)
                .env("LEAN_PATH", &lib)
                .env("FLN_IMPORT_REUSE_DIR", &records)
                .output()
                .unwrap()
        ),
        "true\n\"hello\"\n1\n"
    );
    if let Some(pinned_lean) = lib
        .parent()
        .and_then(Path::parent)
        .map(|toolchain| toolchain.join("bin/lean"))
        .filter(|exe| exe.is_file())
    {
        let ref_out = Command::new(pinned_lean)
            .arg(&source)
            .env("LEAN_PATH", &lib)
            .output()
            .unwrap();
        assert!(ref_out.status.success(), "{ref_out:?}");
        assert_eq!(ref_out.stdout, b"true\n\"hello\"\n1\n");
    }
    let output = success(
        Command::new(env!("CARGO_BIN_EXE_fln"))
            .args(["run", "--json"])
            .arg(&source)
            .env("LEAN_PATH", &lib)
            .env("FLN_IMPORT_REUSE_DIR", &records)
            .output()
            .unwrap(),
    );
    for expected in [
        "\"kind\":\"bool\",\"value\":true",
        "\"kind\":\"string\",\"value\":\"hello\"",
        "\"kind\":\"nat\",\"value\":1",
    ] {
        assert!(output.contains(expected), "{output}");
    }
}
