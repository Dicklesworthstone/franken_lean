//! Unsafe source is executable through the CLI, not usable as safe proof evidence.
#![forbid(unsafe_code)]

use std::process::{Command, Output};

fn successful(output: Output) -> String {
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(output.stderr.is_empty());
    String::from_utf8(output.stdout).unwrap()
}

#[test]
fn installed_unsafe_recursion_executes_replays_and_cannot_publish_a_safe_proof() {
    let root = std::env::temp_dir().join(format!("fln-source-unsafe-{}", std::process::id()));
    std::fs::create_dir(&root).unwrap();
    let source = root.join("Unsafe.lean");
    let artifact = root.join("Unsafe.flbc");
    let definition = "unsafe def gcd' (a b : Nat) : Nat := if b == 0 then a else gcd' b (a % b)\n";
    std::fs::write(&source, definition).unwrap();
    let check = successful(
        Command::new(env!("CARGO_BIN_EXE_fln"))
            .args(["check-source", "--json"])
            .arg(&source)
            .output()
            .unwrap(),
    );
    assert!(check.contains("\"executed\":false"), "{check}");
    let good = format!("{definition}#eval gcd' 48 18\n");
    std::fs::write(&source, &good).unwrap();
    let output = successful(
        Command::new(env!("CARGO_BIN_EXE_fln"))
            .args(["run", "--json", "--emit-flbc"])
            .arg(&artifact)
            .arg(&source)
            .output()
            .unwrap(),
    );
    assert!(output.contains("\"finalValue\":6"), "{output}");
    let retained = std::fs::read(&artifact).unwrap();
    let replay = successful(
        Command::new(env!("CARGO_BIN_EXE_fln"))
            .args(["flbc", "run", "--json"])
            .arg(&artifact)
            .output()
            .unwrap(),
    );
    assert!(replay.contains("\"returnValue\":6"), "{replay}");

    // Even reflexivity cannot smuggle an unsafe constant into a safe theorem's
    // type. A late failure also cannot publish earlier output or bytecode.
    let refused_artifact = root.join("Refused.flbc");
    std::fs::write(
        &source,
        format!("{good}theorem leak : gcd' 48 18 = gcd' 48 18 := by rfl\n"),
    )
    .unwrap();
    let refused = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["run", "--json", "--emit-flbc"])
        .arg(&refused_artifact)
        .arg(&source)
        .output()
        .unwrap();
    assert!(!refused.status.success());
    assert!(refused.stdout.is_empty());
    assert!(!refused_artifact.exists());
    assert_eq!(std::fs::read(&artifact).unwrap(), retained);
    std::fs::write(&source, &good).unwrap();
    let recovered = successful(
        Command::new(env!("CARGO_BIN_EXE_fln"))
            .args(["run", "--json"])
            .arg(&source)
            .output()
            .unwrap(),
    );
    assert!(recovered.contains("\"finalValue\":6"), "{recovered}");
    assert_eq!(std::fs::read(&source).unwrap(), good.as_bytes());
}

#[test]
fn installed_mutual_unsafe_group_replays_its_real_bodies() {
    let root = std::env::temp_dir().join(format!("fln-mutual-unsafe-{}", std::process::id()));
    std::fs::create_dir(&root).unwrap();
    let source = root.join("Mutual.lean");
    let artifact = root.join("Mutual.flbc");
    let group = "mutual\nunsafe def ping (n : Nat) : Nat := if n == 0 then 7 else pong (n - 1)\nunsafe def pong (n : Nat) : Nat := if n == 0 then 13 else ping (n - 1)\nend\n";
    let good = format!("{group}#eval ping 5\n");
    std::fs::write(&source, &good).unwrap();
    let output = successful(
        Command::new(env!("CARGO_BIN_EXE_fln"))
            .args(["run", "--json", "--emit-flbc"])
            .arg(&artifact)
            .arg(&source)
            .output()
            .unwrap(),
    );
    assert!(output.contains("\"finalValue\":13"), "{output}");
    let replay = successful(
        Command::new(env!("CARGO_BIN_EXE_fln"))
            .args(["flbc", "run", "--json"])
            .arg(&artifact)
            .output()
            .unwrap(),
    );
    assert!(replay.contains("\"returnValue\":13"), "{replay}");
    std::fs::write(
        &source,
        format!("{good}theorem leak : ping 0 = ping 0 := by rfl\n"),
    )
    .unwrap();
    let refusal = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["run", "--json"])
        .arg(&source)
        .output()
        .unwrap();
    assert!(!refusal.status.success());
    assert!(refusal.stdout.is_empty());
    std::fs::write(&source, &good).unwrap();
    let recovered = successful(
        Command::new(env!("CARGO_BIN_EXE_fln"))
            .args(["run", "--json"])
            .arg(&source)
            .output()
            .unwrap(),
    );
    assert!(recovered.contains("\"finalValue\":13"), "{recovered}");
}

#[test]
fn installed_unsafe_instances_execute_and_replay_but_cannot_publish_safe_consumers() {
    let root = std::env::temp_dir().join(format!("fln-unsafe-instances-{}", std::process::id()));
    std::fs::create_dir(&root).unwrap();
    let source = root.join("Instances.lean");
    let artifact = root.join("Instances.flbc");
    let rejected_artifact = root.join("Rejected.flbc");
    let declarations = "class Pick where\n  value : Nat\ndef selected [p : Pick] : Nat := p.value\nunsafe instance chosen : Pick := ⟨42⟩\nunsafe def answer : Nat := selected\n";
    std::fs::write(&source, declarations).unwrap();
    let check = successful(
        Command::new(env!("CARGO_BIN_EXE_fln"))
            .args(["check-source", "--json"])
            .arg(&source)
            .output()
            .unwrap(),
    );
    assert!(check.contains("\"executed\":false"), "{check}");
    let good = format!("{declarations}#eval answer\n");
    std::fs::write(&source, &good).unwrap();
    let output = successful(
        Command::new(env!("CARGO_BIN_EXE_fln"))
            .args(["run", "--json", "--emit-flbc"])
            .arg(&artifact)
            .arg(&source)
            .output()
            .unwrap(),
    );
    assert!(output.contains("\"finalValue\":42"), "{output}");
    let retained = std::fs::read(&artifact).unwrap();
    let replay = successful(
        Command::new(env!("CARGO_BIN_EXE_fln"))
            .args(["flbc", "run", "--json"])
            .arg(&artifact)
            .output()
            .unwrap(),
    );
    assert!(replay.contains("\"returnValue\":42"), "{replay}");
    let bad = format!("{good}def leak : Nat := selected\n");
    std::fs::write(&source, &bad).unwrap();
    for destination in [&rejected_artifact, &artifact] {
        let refused = Command::new(env!("CARGO_BIN_EXE_fln"))
            .args(["run", "--json", "--emit-flbc"])
            .arg(destination)
            .arg(&source)
            .output()
            .unwrap();
        assert_eq!(
            refused.status.code(),
            Some(1),
            "{}",
            String::from_utf8_lossy(&refused.stderr)
        );
        assert!(refused.stdout.is_empty());
        // An authoritative rejection is not an accepted program. The run
        // schema distinguishes an actual safety verdict from a nonanswer.
        let diagnostic = String::from_utf8_lossy(&refused.stderr);
        for field in ["\"outcome\":\"error\"", "SafetyViolation", "chosen"] {
            assert!(diagnostic.contains(field), "{diagnostic}");
        }
        assert!(!rejected_artifact.exists());
        assert_eq!(std::fs::read(&artifact).unwrap(), retained);
        assert_eq!(std::fs::read_to_string(&source).unwrap(), bad);
    }
    std::fs::write(&source, &good).unwrap();
    let recovered = successful(
        Command::new(env!("CARGO_BIN_EXE_fln"))
            .args(["run", "--json"])
            .arg(&source)
            .output()
            .unwrap(),
    );
    assert!(recovered.contains("\"finalValue\":42"), "{recovered}");
}
