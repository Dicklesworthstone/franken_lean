//! Installed and library CLI source-proof checking. No fake compiler or checker.
#![forbid(unsafe_code)]
use std::{
    ffi::OsString,
    path::PathBuf,
    process::Command,
    sync::atomic::{AtomicUsize, Ordering},
};
static NEXT: AtomicUsize = AtomicUsize::new(0);
fn file(text: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!(
        "fln-proof-check-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::create_dir(&dir).unwrap();
    let path = dir.join("proof.lean");
    std::fs::write(&path, text).unwrap();
    path
}
fn run(args: Vec<OsString>) -> fln_cli::MultiplexerOutput {
    fln_cli::run(args)
}
#[test]
fn installed_binary_checks_a_real_source_proof_file() {
    let path = file(
        "def identity (x : Nat) : Nat := x\ntheorem self (x : Nat) : identity x = x := by rfl\ntheorem symm (x y : Nat) (h : x = y) : y = x := by rw [h]\n",
    );
    let before = std::fs::read(&path).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["check-source", "--json"])
        .arg(&path)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let text = String::from_utf8(output.stdout).unwrap();
    for required in [
        "\"schema\":\"fln.source-check/1\"",
        "\"outcome\":\"complete\"",
        "\"authority\":true",
        "\"commands\":3",
        "\"theorems\":2",
        "\"executed\":false",
    ] {
        assert!(text.contains(required), "{text}");
    }
    assert!(output.stderr.is_empty());
    assert_eq!(std::fs::read(&path).unwrap(), before);
    assert_eq!(
        std::fs::read_dir(path.parent().unwrap()).unwrap().count(),
        1
    );
}
#[test]
fn later_files_can_use_prior_theorems_and_failure_emits_no_partial_success() {
    let one = file("theorem self (x : Nat) : x = x := by rfl");
    let two = file("theorem reuse (x : Nat) : x = x := by apply self");
    let args = vec![
        "check-source".into(),
        "--json".into(),
        one.clone().into_os_string(),
        two.clone().into_os_string(),
    ];
    let output = run(args.clone());
    assert_eq!(output.exit_code, 0, "{}", output.stderr);
    assert!(output.stdout.contains("\"files\":2"));
    std::fs::write(two, "theorem bad : 1 = 2 := by rfl").unwrap();
    let output = run(args);
    assert_eq!(output.exit_code, 1);
    assert!(output.stdout.is_empty());
    assert!(output.stderr.contains("\"outcome\":\"kernel-rejection\""));
    assert!(!output.stderr.contains("\"outcome\":\"complete\""));
}
#[test]
fn byte_budget_is_aggregate_and_duplicate_options_are_refused() {
    let path = file("def x : Nat := 1");
    let output = run(vec![
        "check-source".into(),
        "--json".into(),
        "--max-bytes=20".into(),
        path.clone().into_os_string(),
        path.clone().into_os_string(),
    ]);
    assert_eq!(output.exit_code, 3);
    assert!(output.stdout.is_empty());
    assert!(output.stderr.contains("\"authority\":false"));
    for flags in [
        vec!["--json", "--json"],
        vec!["--max-bytes=20", "--max-bytes=30"],
    ] {
        let args = std::iter::once(OsString::from("check-source"))
            .chain(flags.into_iter().map(OsString::from))
            .chain(std::iter::once(path.clone().into_os_string()))
            .collect();
        assert_ne!(run(args).exit_code, 0);
    }
}
#[test]
fn unsupported_commands_never_execute_and_end_of_options_preserves_dash_paths() {
    let path = file("#eval 1");
    let output = run(vec![
        "check-source".into(),
        "--json".into(),
        "--".into(),
        path.clone().into_os_string(),
    ]);
    assert_ne!(output.exit_code, 0);
    assert!(output.stdout.is_empty());
    assert!(output.stderr.contains("\"authority\":false"));
    let dir = path.parent().unwrap();
    std::fs::write(dir.join("-proof.lean"), "theorem same : 7 = 7 := by rfl").unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_fln"))
        .current_dir(dir)
        .args(["check-source", "--", "-proof.lean"])
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn installed_binary_checks_quantified_simp_and_selected_definition_proofs() {
    let example = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../examples/native_simplification.lean");
    let output = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["check-source", "--json"])
        .arg(example)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let text = String::from_utf8(output.stdout).unwrap();
    for field in [
        "\"commands\":7",
        "\"theorems\":6",
        "\"executed\":false",
        "\"outcome\":\"complete\"",
    ] {
        assert!(text.contains(field), "{text}");
    }
    assert!(output.stderr.is_empty());
}

#[test]
fn a_late_simp_failure_does_not_emit_partial_success_for_prior_files() {
    let one =
        file("theorem contract (f : Nat -> Nat) (x : Nat) (h : f x = x) : f x = x := by exact h");
    let two = file(
        "theorem use (f : Nat -> Nat) (x : Nat) (h : f x = x) : f (f x) = x := by simp only [contract f, h]",
    );
    let args = vec![
        "check-source".into(),
        "--json".into(),
        one.into_os_string(),
        two.clone().into_os_string(),
    ];
    let complete = run(args.clone());
    assert_eq!(complete.exit_code, 0, "{}", complete.stderr);
    std::fs::write(two, "theorem bad : 1 = 2 := by simp only []").unwrap();
    let refused = run(args);
    assert_ne!(refused.exit_code, 0);
    assert!(refused.stdout.is_empty());
    assert!(!refused.stderr.contains("\"outcome\":\"complete\""));
}

#[test]
fn installed_binary_resolves_source_instances_across_files_without_execution() {
    let one = file(
        "instance (priority := 2000) seven : Inhabited Nat := Inhabited.mk 7\ninstance constantFunction {A : Type} [Inhabited A] : Inhabited (Nat -> A) := Inhabited.mk (fun x => default)",
    );
    let two = file(
        "def dictionary : Inhabited Nat := inferInstance\ndef nested : Nat -> Nat -> Nat := default\ntheorem computes : nested 1 2 = 7 := by rfl",
    );
    let output = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["check-source", "--json"])
        .arg(&one)
        .arg(&two)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(output.stderr.is_empty());
    let text = String::from_utf8(output.stdout).unwrap();
    for required in [
        "\"files\":2",
        "\"commands\":5",
        "\"theorems\":1",
        "\"executed\":false",
    ] {
        assert!(text.contains(required), "{text}");
    }
    std::fs::write(&two, "theorem falseDefault : default = 8 := by rfl").unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["check-source", "--json"])
        .arg(one)
        .arg(two)
        .output()
        .unwrap();
    assert!(!output.status.success());
    assert!(
        output.stdout.is_empty(),
        "late failure must not expose successful prefix"
    );
    assert!(String::from_utf8_lossy(&output.stderr).contains("kernel-rejection"));
}

#[test]
fn installed_binary_checks_local_dictionaries_and_conditional_instance_rewrites() {
    let one = file(
        "def consume (i : Inhabited Nat) : Nat := 0\ntheorem rule (P : Prop) [i : Inhabited Nat] (hp : P) : consume i = 0 := by rfl",
    );
    let two = file(
        "def dictionary (i : Inhabited Nat) : Inhabited Nat := inferInstance\ntheorem selected (i : Inhabited Nat) : dictionary i = i := by rfl\ntheorem use (P : Prop) (hp : P) : consume instInhabitedNat = 0 := by simp only [rule P, hp]",
    );
    let args = vec![
        "check-source".into(),
        "--json".into(),
        one.into_os_string(),
        two.clone().into_os_string(),
    ];
    let complete = run(args.clone());
    assert_eq!(complete.exit_code, 0, "{}", complete.stderr);
    for required in [
        "\"files\":2",
        "\"commands\":5",
        "\"theorems\":3",
        "\"executed\":false",
    ] {
        assert!(complete.stdout.contains(required), "{}", complete.stdout);
    }
    std::fs::write(
        two,
        "theorem wrong (i : Inhabited Nat) : default = 0 := by rfl",
    )
    .unwrap();
    let refused = run(args);
    assert_ne!(refused.exit_code, 0);
    assert!(refused.stdout.is_empty());
    assert!(refused.stderr.contains("kernel-rejection"));
}

#[test]
fn installed_binary_checks_source_defined_records_and_recursive_classes() {
    let example =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples/native_records.lean");
    let output = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["check-source", "--json"])
        .arg(example)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let text = String::from_utf8(output.stdout).unwrap();
    for required in [
        "\"commands\":8",
        "\"theorems\":2",
        "\"executed\":false",
        "\"authority\":true",
    ] {
        assert!(text.contains(required), "{text}");
    }
    assert!(output.stderr.is_empty());
}

#[test]
fn later_record_file_failure_emits_no_successful_prefix_or_class_registration() {
    let one = file("class Choice (A : Type) where\n  value : A");
    let two = file(
        "instance natChoice : Choice Nat := Choice.mk 13\ntheorem bad : Choice.value = 14 := by rfl",
    );
    let output = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["check-source", "--json"])
        .arg(one)
        .arg(two)
        .output()
        .unwrap();
    assert!(!output.status.success());
    assert!(output.stdout.is_empty());
    let error = String::from_utf8_lossy(&output.stderr);
    assert!(error.contains("kernel-rejection"), "{error}");
    assert!(!error.contains("\"outcome\":\"complete\""));
}

#[test]
fn installed_binary_checks_named_fields_and_dependent_projection_chains() {
    let path = file(include_str!("../../../examples/native_record_values.lean"));
    let before = std::fs::read(&path).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["check-source", "--json"])
        .arg(&path)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let text = String::from_utf8(output.stdout).unwrap();
    assert!(text.contains("\"commands\":10"), "{text}");
    assert!(text.contains("\"theorems\":4"), "{text}");
    assert!(text.contains("\"executed\":false"), "{text}");
    assert_eq!(std::fs::read(&path).unwrap(), before);
}

#[test]
fn late_record_field_failure_emits_no_success_or_output_artifacts() {
    let prefix = file("structure Point where\n  x : Nat\ndef point : Point := { x := 7 }");
    let suffix = file("def failure : Nat := point.unknown");
    let output = run(vec![
        "check-source".into(),
        "--json".into(),
        prefix.into_os_string(),
        suffix.into_os_string(),
    ]);
    assert_ne!(output.exit_code, 0);
    assert!(output.stdout.is_empty());
    assert!(
        output.stderr.contains("unknown record field"),
        "{}",
        output.stderr
    );
}

#[test]
fn installed_binary_checks_function_dictionaries_and_refuses_late_false_proofs() {
    let one = file(
        "class Choice (A : Type) where\n  value : A\n\
         instance natChoice : Choice Nat := Choice.mk 11\n\
         def dictionary : Nat -> Choice Nat := inferInstance",
    );
    let two = file("theorem result : dictionary 7 = natChoice := by rfl");
    let bad = file("theorem wrong : dictionary 7 = Choice.mk 12 := by rfl");
    for (last, success) in [(&two, true), (&bad, false), (&two, true)] {
        let output = Command::new(env!("CARGO_BIN_EXE_fln"))
            .args(["check-source", "--json"])
            .arg(&one)
            .arg(last)
            .output()
            .unwrap();
        assert_eq!(
            output.status.success(),
            success,
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        if success {
            let text = String::from_utf8(output.stdout).unwrap();
            for required in [
                "\"commands\":4",
                "\"theorems\":1",
                "\"files\":2",
                "\"authority\":true",
                "\"executed\":false",
            ] {
                assert!(text.contains(required), "{text}");
            }
            assert!(output.stderr.is_empty());
        } else {
            assert!(output.stdout.is_empty());
            assert!(String::from_utf8_lossy(&output.stderr).contains("kernel-rejection"));
        }
    }
}

#[test]
fn installed_binary_checks_instance_dependent_field_receivers_atomically() {
    let prefix = file(
        "structure Point where\n  x : Nat\n\
         def point [Inhabited Nat] : Point := { x := default }",
    );
    let good = file(
        "theorem dotted : point.x = 0 := by rfl\n\
         theorem postfix : (point).x = 0 := by rfl",
    );
    let bad = file("theorem wrong : point.x = 1 := by rfl");
    for (suffix, success) in [(&good, true), (&bad, false), (&good, true)] {
        let output = Command::new(env!("CARGO_BIN_EXE_fln"))
            .args(["check-source", "--json"])
            .arg(&prefix)
            .arg(suffix)
            .output()
            .unwrap();
        assert_eq!(
            output.status.success(),
            success,
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        if success {
            let text = String::from_utf8(output.stdout).unwrap();
            for required in [
                "\"commands\":4",
                "\"theorems\":2",
                "\"files\":2",
                "\"authority\":true",
                "\"executed\":false",
            ] {
                assert!(text.contains(required), "{text}");
            }
            assert!(output.stderr.is_empty());
        } else {
            assert!(output.stdout.is_empty());
            assert!(String::from_utf8_lossy(&output.stderr).contains("kernel-rejection"));
        }
    }
}

#[test]
fn installed_binary_checks_type_position_instances_and_header_refusal_with_recovery() {
    let prefix = file(
        "class Factory where\n  carrier : Type\n  produce : carrier\n\
         instance natFactory : Factory := { carrier := Nat, produce := 7 }",
    );
    let good = file(
        "def keep [Factory] (x : Factory.carrier) : Factory.carrier := x\n\
         def answer : Nat := keep (Factory.produce : Factory.carrier)\n\
         theorem result : answer = 7 := by rfl",
    );
    let bad = file(
        "def inferred {A : Type} [Inhabited A] : Type := A\n\
         def bad (n : Nat) : inferred := n",
    );
    let wrong = file("theorem wrong : Factory.produce = (8 : Nat) := by rfl");
    for (suffix, success) in [(&good, true), (&bad, false), (&wrong, false), (&good, true)] {
        let before = std::fs::read(suffix).unwrap();
        let output = Command::new(env!("CARGO_BIN_EXE_fln"))
            .args(["check-source", "--json"])
            .arg(&prefix)
            .arg(suffix)
            .output()
            .unwrap();
        assert_eq!(
            output.status.success(),
            success,
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        if success {
            let text = String::from_utf8(output.stdout).unwrap();
            for required in [
                "\"commands\":5",
                "\"theorems\":1",
                "\"files\":2",
                "\"authority\":true",
                "\"executed\":false",
            ] {
                assert!(text.contains(required), "{text}");
            }
            assert!(output.stderr.is_empty());
        } else {
            assert!(output.stdout.is_empty());
            assert!(!output.stderr.is_empty());
            assert!(!String::from_utf8_lossy(&output.stderr).contains("\"outcome\":\"complete\""));
        }
        assert_eq!(std::fs::read(suffix).unwrap(), before);
        assert_eq!(
            std::fs::read_dir(suffix.parent().unwrap()).unwrap().count(),
            1
        );
    }
}

#[test]
fn installed_binary_checks_defaults_updates_and_late_failure_without_partial_success() {
    let prefix = file(
        "structure Config where\n  base : Nat := 3\n  twice : Nat := base + base\ndef custom : Config := { base := 7 }\ndef copied := { custom with base := 20 }",
    );
    let good = file(
        "theorem ok : custom.twice = 14 := by rfl\ntheorem retained : copied.twice = 14 := by rfl",
    );
    let bad = file("theorem wrong : copied.twice = 40 := by rfl");
    for (suffix, success) in [(&good, true), (&bad, false), (&good, true)] {
        let output = Command::new(env!("CARGO_BIN_EXE_fln"))
            .args(["check-source", "--json"])
            .arg(&prefix)
            .arg(suffix)
            .output()
            .unwrap();
        assert_eq!(
            output.status.success(),
            success,
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        if success {
            let text = String::from_utf8(output.stdout).unwrap();
            for expected in [
                "\"commands\":5",
                "\"theorems\":2",
                "\"files\":2",
                "\"authority\":true",
                "\"executed\":false",
            ] {
                assert!(text.contains(expected), "{text}");
            }
            assert!(output.stderr.is_empty());
        } else {
            assert!(output.stdout.is_empty());
            assert!(String::from_utf8_lossy(&output.stderr).contains("kernel-rejection"));
        }
    }
}

#[test]
fn installed_binary_checks_constructor_matches_and_refuses_an_invalid_unused_branch() {
    let prefix = file(
        "inductive Item (A : Type) where | none | some (value : A)\n\
         def get (item : Item Nat) : Nat := match item with | .none => 0 | .some n => n\n\
         def predecessor (n : Nat) : Nat := match n with | .zero => 0 | .succ k => k",
    );
    let good = file(
        "theorem payload : get (Item.some 12) = 12 := by rfl\ntheorem pred : predecessor 6 = 5 := by rfl",
    );
    let bad = file("def invalid : Nat := match true with | true => 0 | false => (0 : String)");
    for (suffix, success) in [(&good, true), (&bad, false), (&good, true)] {
        let output = Command::new(env!("CARGO_BIN_EXE_fln"))
            .args(["check-source", "--json"])
            .arg(&prefix)
            .arg(suffix)
            .output()
            .unwrap();
        assert_eq!(
            output.status.success(),
            success,
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        if success {
            let text = String::from_utf8(output.stdout).unwrap();
            for expected in [
                "\"commands\":5",
                "\"theorems\":2",
                "\"files\":2",
                "\"authority\":true",
                "\"executed\":false",
            ] {
                assert!(text.contains(expected), "{text}");
            }
            assert!(output.stderr.is_empty());
        } else {
            assert!(output.stdout.is_empty());
            assert!(String::from_utf8_lossy(&output.stderr).contains("kernel-rejection"));
        }
    }
}

#[test]
fn installed_binary_checks_recursive_functions_and_never_publishes_a_bad_suffix() {
    let prefix = file(
        "def sumAcc (n : Nat) (acc : Nat) : Nat := match n with | .zero => acc | .succ k => sumAcc k (acc + n)\ndef add (n : Nat) (m : Nat) : Nat := match n with | .zero => m | .succ k => let smaller := add k; smaller (m + 1)",
    );
    let good =
        file("theorem sum_ok : sumAcc 4 7 = 17 := by rfl\ntheorem add_ok : add 3 5 = 8 := by rfl");
    let bad = file(
        "def loop (n : Nat) (acc : Nat) : Nat := match n with | .zero => acc | .succ k => let unused := loop n acc; 0",
    );
    let false_proof = file("theorem bad_sum : sumAcc 4 7 = 18 := by rfl");
    for (suffix, success) in [
        (&good, true),
        (&bad, false),
        (&false_proof, false),
        (&good, true),
    ] {
        let output = Command::new(env!("CARGO_BIN_EXE_fln"))
            .args(["check-source", "--json"])
            .arg(&prefix)
            .arg(suffix)
            .output()
            .unwrap();
        assert_eq!(
            output.status.success(),
            success,
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        if success {
            let text = String::from_utf8(output.stdout).unwrap();
            for expected in [
                "\"commands\":4",
                "\"theorems\":2",
                "\"files\":2",
                "\"authority\":true",
                "\"executed\":false",
            ] {
                assert!(text.contains(expected), "{text}");
            }
            assert!(output.stderr.is_empty());
        } else {
            assert!(output.stdout.is_empty());
            assert!(!output.stderr.is_empty());
        }
    }
}

#[test]
fn installed_binary_uses_recursive_computed_types_without_guessing_stuck_majors() {
    let prefix = file(
        "def Tower (n : Nat) : Type := match n with | .zero => Nat | .succ k => Tower k -> Tower k",
    );
    let good = file("def identity : Tower 1 := fun x => x\ntheorem ok : identity 9 = 9 := by rfl");
    let bad = file("def ambiguous (n : Nat) : Tower n := fun x => x");
    for (suffix, success) in [(&good, true), (&bad, false), (&good, true)] {
        let output = Command::new(env!("CARGO_BIN_EXE_fln"))
            .args(["check-source", "--json"])
            .arg(&prefix)
            .arg(suffix)
            .output()
            .unwrap();
        assert_eq!(
            output.status.success(),
            success,
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        if success {
            let text = String::from_utf8(output.stdout).unwrap();
            for expected in ["\"commands\":3", "\"theorems\":1", "\"executed\":false"] {
                assert!(text.contains(expected), "{text}");
            }
            assert!(output.stderr.is_empty());
        } else {
            assert!(output.stdout.is_empty());
            assert!(!output.stderr.is_empty());
        }
    }
}
