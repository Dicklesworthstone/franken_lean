//! Installed and library CLI source-proof checking. No fake compiler or checker.
#![forbid(unsafe_code)]

#[test]
fn indexed_recursive_functions_are_checked_without_publishing_a_bad_suffix() {
    let prefix = file(include_str!(
        "../../../examples/native_indexed_recursion.lean"
    ));
    let bad = file("theorem bad : indexSum 2 two = 4 := by rfl");
    for success in [true, false, true] {
        let mut command = Command::new(env!("CARGO_BIN_EXE_fln"));
        command.args(["check-source", "--json"]).arg(&prefix);
        if !success {
            command.arg(&bad);
        }
        let output = command.output().unwrap();
        assert_eq!(
            output.status.success(),
            success,
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        if success {
            let json = String::from_utf8(output.stdout).unwrap();
            for expected in ["\"commands\":12", "\"theorems\":6", "\"executed\":false"] {
                assert!(json.contains(expected), "{json}");
            }
            assert!(output.stderr.is_empty());
        } else {
            assert!(output.stdout.is_empty());
            assert!(!output.stderr.is_empty());
        }
    }
}
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
fn installed_binary_checks_inductive_constructors_and_recursor_computation_atomically() {
    let prefix = file("inductive Chain where | nil | cons (head : Nat) (tail : Chain)");
    let good = file(
        "def chain : Chain := Chain.cons 3 Chain.nil\n\
                     theorem count : Chain.rec 0 (fun n tail ih => ih + 1) chain = 1 := by rfl",
    );
    let bad = file(
        "theorem wrong : Chain.rec 0 (fun n tail ih => ih + 1) (Chain.cons 3 Chain.nil) = 2 := by rfl",
    );
    for (suffix, success) in [(&good, true), (&bad, false), (&good, true)] {
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
                "\"commands\":3",
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

#[test]
fn installed_binary_checks_real_induction_and_dependent_case_proofs() {
    let path = file(include_str!("../../../examples/native_induction.lean"));
    let output = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["check-source", "--json"])
        .arg(path)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let text = String::from_utf8(output.stdout).unwrap();
    for expected in [
        "\"commands\":12",
        "\"theorems\":5",
        "\"authority\":true",
        "\"executed\":false",
    ] {
        assert!(text.contains(expected), "{text}");
    }
    assert!(output.stderr.is_empty());
}

#[test]
fn failed_induction_branches_never_publish_a_multi_file_success_prefix() {
    let prefix = file("def zero (n : Nat) : Nat := match n with | .zero => 0 | .succ k => zero k");
    let good = file(
        "theorem zero_ok (n : Nat) : zero n = 0 := by induction n with | zero => rfl | succ k ih => exact ih",
    );
    let unfinished = file(
        "theorem zero_ok (n : Nat) : zero n = 0 := by cases n with | zero => rfl | succ k => assumption",
    );
    let false_proof = file(
        "theorem false_proof (n : Nat) : 0 = 1 := by cases n with | zero => rfl | succ k => rfl",
    );
    for (suffix, success) in [
        (&good, true),
        (&unfinished, false),
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
                "\"commands\":2",
                "\"theorems\":1",
                "\"files\":2",
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
fn installed_binary_checks_generic_collection_laws_through_both_checkers() {
    let path = file(include_str!(
        "../../../examples/native_parameterized_recursion.lean"
    ));
    let output = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["check-source", "--json"])
        .arg(path)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let text = String::from_utf8(output.stdout).unwrap();
    for expected in [
        "\"commands\":14",
        "\"theorems\":7",
        "\"authority\":true",
        "\"executed\":false",
    ] {
        assert!(text.contains(expected), "{text}");
    }
    assert!(output.stderr.is_empty());
}

#[test]
fn failed_generic_collection_proofs_do_not_publish_a_multi_file_prefix() {
    let prefix = file("inductive Seq (A : Type) where | nil | cons (head : A) (tail : Seq A)");
    let good = file("theorem valid : (Seq.nil : Seq Nat) = Seq.nil := by rfl");
    let bad = file("theorem invalid : Seq.cons 1 Seq.nil = Seq.cons 2 Seq.nil := by rfl");
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
                "\"commands\":2",
                "\"theorems\":1",
                "\"files\":2",
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
fn installed_binary_checks_indexed_declarations_and_refuses_wrong_lengths() {
    let prefix = file(include_str!("../../../examples/native_indexed.lean"));
    let bad = file("def wrong : Vec Nat 0 := two");
    for success in [true, false, true] {
        let mut command = Command::new(env!("CARGO_BIN_EXE_fln"));
        command.args(["check-source", "--json"]).arg(&prefix);
        if !success {
            command.arg(&bad);
        }
        let output = command.output().unwrap();
        assert_eq!(
            output.status.success(),
            success,
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        if success {
            let json = String::from_utf8(output.stdout).unwrap();
            for required in ["\"commands\":8", "\"theorems\":3", "\"executed\":false"] {
                assert!(json.contains(required), "{json}");
            }
            assert!(output.stderr.is_empty());
        } else {
            assert!(output.stdout.is_empty());
            assert!(!output.stderr.is_empty());
        }
    }
}

#[test]
fn installed_binary_checks_indexed_induction_and_dependent_cases() {
    let path = file(include_str!(
        "../../../examples/native_indexed_elimination.lean"
    ));
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
    for field in ["\"commands\":11", "\"theorems\":5", "\"executed\":false"] {
        assert!(text.contains(field), "{text}");
    }
    assert!(output.stderr.is_empty());
    assert_eq!(std::fs::read(&path).unwrap(), before);
}

#[test]
fn indexed_proof_failure_emits_no_success_and_does_not_poison_the_next_check() {
    let prefix = file(
        "inductive Vec (A : Type) : Nat -> Type where | nil : Vec A 0 | cons (n : Nat) (head : A) (tail : Vec A n) : Vec A (Nat.succ n)",
    );
    let good = file(
        "theorem same {A : Type} (n : Nat) (xs : Vec A n) : n = n := by cases xs with | nil => rfl | cons k x tail => rfl",
    );
    let bad = file(
        "theorem false (n : Nat) (xs : Vec Nat n) : n = 0 := by cases xs with | nil => rfl | cons k x tail => rfl",
    );
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
            assert!(output.stderr.is_empty());
        } else {
            assert!(output.stdout.is_empty());
            assert!(
                String::from_utf8_lossy(&output.stderr)
                    .contains("\"outcome\":\"kernel-rejection\"")
            );
        }
    }
}

#[test]
fn installed_binary_checks_indexed_matches_without_publishing_failed_prefixes() {
    let prefix = file(
        "inductive Vec (A : Type) : Nat -> Type where | nil : Vec A 0 | cons (n : Nat) (head : A) (tail : Vec A n) : Vec A (Nat.succ n)\ndef rebuild {A : Type} (n : Nat) (xs : Vec A n) : Vec A n := match xs with | .nil => Vec.nil | .cons k x tail => Vec.cons k x tail",
    );
    let good =
        file("theorem checked : rebuild 1 (Vec.cons 0 7 Vec.nil) = Vec.cons 0 7 Vec.nil := by rfl");
    let bad =
        file("theorem wrong : rebuild 1 (Vec.cons 0 7 Vec.nil) = Vec.cons 0 9 Vec.nil := by rfl");
    let before = std::fs::read(&prefix).unwrap();
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
            assert!(output.stderr.is_empty());
            let json = String::from_utf8(output.stdout).unwrap();
            for required in [
                "\"commands\":3",
                "\"theorems\":1",
                "\"files\":2",
                "\"executed\":false",
            ] {
                assert!(json.contains(required), "{json}");
            }
        } else {
            assert!(output.stdout.is_empty());
            assert_eq!(output.status.code(), Some(1));
            assert!(
                String::from_utf8_lossy(&output.stderr)
                    .contains("\"outcome\":\"kernel-rejection\"")
            );
        }
        assert_eq!(std::fs::read(&prefix).unwrap(), before);
        assert_eq!(
            std::fs::read_dir(prefix.parent().unwrap()).unwrap().count(),
            1
        );
    }
}

#[test]
fn installed_binary_refuses_hidden_match_hypotheses_and_checks_real_assumptions() {
    for (source, success) in [
        (
            "theorem hidden (n : Nat) : 0 = 0 := match n with | .zero => rfl | .succ k => by assumption",
            false,
        ),
        (
            "theorem real (n : Nat) (h : 0 = 0) : 0 = 0 := match n with | .zero => rfl | .succ k => by assumption",
            true,
        ),
    ] {
        let path = file(source);
        let output = Command::new(env!("CARGO_BIN_EXE_fln"))
            .args(["check-source", "--json"])
            .arg(&path)
            .output()
            .unwrap();
        assert_eq!(
            output.status.success(),
            success,
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        if success {
            assert!(output.stderr.is_empty());
        } else {
            assert!(output.stdout.is_empty());
            assert!(!output.stderr.is_empty());
        }
    }
}

#[test]
fn installed_binary_checks_dependent_index_recursion_and_retains_failure_isolation() {
    let prefix = file(include_str!(
        "../../../examples/native_dependent_indices.lean"
    ));
    let bad = file("theorem bad : depth 2 false trace = 0 := by rfl");
    for success in [true, false, true] {
        let mut command = Command::new(env!("CARGO_BIN_EXE_fln"));
        command.args(["check-source", "--json"]).arg(&prefix);
        if !success {
            command.arg(&bad);
        }
        let output = command.output().unwrap();
        assert_eq!(
            output.status.success(),
            success,
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        if success {
            let json = String::from_utf8(output.stdout).unwrap();
            for required in ["\"commands\":9", "\"theorems\":4", "\"executed\":false"] {
                assert!(json.contains(required), "{json}");
            }
            assert!(output.stderr.is_empty());
        } else {
            assert!(output.stdout.is_empty());
            assert!(!output.stderr.is_empty());
        }
    }
}

#[test]
fn installed_binary_checks_inductive_propositions_and_atomic_refusals() {
    let prefix = file(include_str!("../../../examples/native_propositions.lean"));
    let before = std::fs::read(&prefix).unwrap();
    let bad = file("theorem impossible : Below 3 0 := Below.refl");
    let extract = file(
        "def witness (A : Type) (P : A -> Prop) (h : HasWitness A P) : A := by cases h with | intro a hp => exact a",
    );
    for suffix in [None, Some(&bad), Some(&extract), None] {
        let mut command = Command::new(env!("CARGO_BIN_EXE_fln"));
        command.args(["check-source", "--json"]).arg(&prefix);
        if let Some(path) = suffix {
            command.arg(path);
        }
        let output = command.output().unwrap();
        assert_eq!(
            output.status.success(),
            suffix.is_none(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        if suffix.is_none() {
            let json = String::from_utf8(output.stdout).unwrap();
            for expected in [
                "\"commands\":15",
                "\"theorems\":7",
                "\"authority\":true",
                "\"executed\":false",
            ] {
                assert!(json.contains(expected), "{json}");
            }
            assert!(output.stderr.is_empty());
        } else {
            assert!(output.stdout.is_empty());
            assert!(!output.stderr.is_empty());
        }
        assert_eq!(std::fs::read(&prefix).unwrap(), before);
    }
}

#[test]
fn installed_constructor_equality_checks_real_proofs_and_failure_isolation() {
    let prefix = file(include_str!(
        "../../../examples/native_constructor_equality.lean"
    ));
    let invalid = file("theorem bad (h : 7 = 7) : 0 = 1 := by contradiction");
    for success in [true, false, true] {
        let mut command = Command::new(env!("CARGO_BIN_EXE_fln"));
        command.args(["check-source", "--json"]).arg(&prefix);
        if !success {
            command.arg(&invalid);
        }
        let output = command.output().unwrap();
        assert_eq!(
            output.status.success(),
            success,
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        if success {
            let json = String::from_utf8(output.stdout).unwrap();
            for required in ["\"commands\":11", "\"theorems\":7", "\"executed\":false"] {
                assert!(json.contains(required), "{json}");
            }
        } else {
            assert!(output.stdout.is_empty());
            assert!(!output.stderr.is_empty());
        }
    }
}

#[test]
fn constructor_equality_example_crosses_the_installed_checker() {
    let source = include_str!("../../../examples/native_constructor_equalities.lean");
    let input = file(source);
    let bytes = std::fs::read(&input).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["check-source", "--json"])
        .arg(&input)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let json = String::from_utf8(output.stdout).unwrap();
    for expected in [
        "\"commands\":9",
        "\"theorems\":7",
        "\"authority\":true",
        "\"executed\":false",
    ] {
        assert!(json.contains(expected), "{json}");
    }
    assert!(output.stderr.is_empty());
    assert_eq!(std::fs::read(&input).unwrap(), bytes);
    assert_eq!(
        std::fs::read_dir(input.parent().unwrap()).unwrap().count(),
        1
    );
}

#[test]
fn failed_constructor_proofs_do_not_publish_or_poison_an_earlier_file() {
    let prefix = file(include_str!(
        "../../../examples/native_constructor_equalities.lean"
    ));
    let suffix = file(
        "theorem falseProof (a b : Nat) (h : Nat.succ a = Nat.succ b) : 0 = 1 := by\n  injection h with field\n  rfl",
    );
    for good in [true, false, true] {
        let mut command = Command::new(env!("CARGO_BIN_EXE_fln"));
        command.args(["check-source", "--json"]).arg(&prefix);
        if !good {
            command.arg(&suffix);
        }
        let output = command.output().unwrap();
        assert_eq!(
            output.status.success(),
            good,
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        if good {
            assert!(output.stderr.is_empty());
            assert!(
                String::from_utf8(output.stdout)
                    .unwrap()
                    .contains("\"commands\":9")
            );
        } else {
            assert!(output.stdout.is_empty());
            assert!(!output.stderr.is_empty());
        }
    }
}

#[test]
fn installed_heterogeneous_equality_checks_bridges_substitution_and_failure_isolation() {
    let prefix = file(include_str!(
        "../../../examples/native_heterogeneous_equality.lean"
    ));
    let bad = file("theorem invalid : HEq 0 1 := by rfl");
    for valid in [true, false, true] {
        let mut command = Command::new(env!("CARGO_BIN_EXE_fln"));
        command.args(["check-source", "--json"]).arg(&prefix);
        if !valid {
            command.arg(&bad);
        }
        let output = command.output().unwrap();
        assert_eq!(
            output.status.success(),
            valid,
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        if valid {
            let result = String::from_utf8(output.stdout).unwrap();
            for field in ["\"commands\":10", "\"theorems\":8", "\"executed\":false"] {
                assert!(result.contains(field), "{result}");
            }
            assert!(output.stderr.is_empty());
        } else {
            assert!(output.stdout.is_empty());
            assert!(!output.stderr.is_empty());
        }
    }
}

#[test]
fn installed_fixed_index_cases_preserve_checked_computation_and_batch_isolation() {
    let prefix = file(include_str!(
        "../../../examples/native_index_refinement.lean"
    ));
    let bad =
        file("theorem invalid (xs : Vec Nat 1) : 0 = 1 := by cases xs with | cons k x tail => rfl");
    let before = std::fs::read(&prefix).unwrap();
    for valid in [true, false, true] {
        let mut command = Command::new(env!("CARGO_BIN_EXE_fln"));
        command.args(["check-source", "--json"]).arg(&prefix);
        if !valid {
            command.arg(&bad);
        }
        let output = command.output().unwrap();
        assert_eq!(
            output.status.success(),
            valid,
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        if valid {
            let result = String::from_utf8(output.stdout).unwrap();
            for field in [
                "\"commands\":15",
                "\"theorems\":5",
                "\"executed\":false",
                "\"authority\":true",
            ] {
                assert!(result.contains(field), "{result}");
            }
            assert!(output.stderr.is_empty());
        } else {
            assert!(output.stdout.is_empty());
            assert!(!output.stderr.is_empty());
        }
        assert_eq!(std::fs::read(&prefix).unwrap(), before);
    }
}

#[test]
fn installed_fixed_index_matches_check_real_terms_and_recover_after_failure() {
    let prefix = file(include_str!(
        "../../../examples/native_constrained_matching.lean"
    ));
    let invalid =
        file("theorem bad (xs : Vec Nat 1) : 0 = 1 := match xs with | .cons k x rest => rfl");
    let bytes = std::fs::read(&prefix).unwrap();
    for success in [true, false, true] {
        let mut command = Command::new(env!("CARGO_BIN_EXE_fln"));
        command.args(["check-source", "--json"]).arg(&prefix);
        if !success {
            command.arg(&invalid);
        }
        let output = command.output().unwrap();
        assert_eq!(
            output.status.success(),
            success,
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        if success {
            let json = String::from_utf8(output.stdout).unwrap();
            for expected in ["\"commands\":20", "\"theorems\":8", "\"executed\":false"] {
                assert!(json.contains(expected), "{json}");
            }
        } else {
            assert!(output.stdout.is_empty());
            assert!(!output.stderr.is_empty());
        }
        assert_eq!(std::fs::read(&prefix).unwrap(), bytes);
    }
}

#[test]
fn installed_constrained_induction_checks_both_engines_without_partial_success() {
    let prefix = file(include_str!(
        "../../../examples/native_induction_specialization.lean"
    ));
    let invalid = file(
        "theorem bad (w : Walk 3) : 0 = 1 := by induction w with | done k => rfl | step k child ih => exact ih",
    );
    let original = std::fs::read(&prefix).unwrap();
    for valid in [true, false, true] {
        let mut command = Command::new(env!("CARGO_BIN_EXE_fln"));
        command.args(["check-source", "--json"]).arg(&prefix);
        if !valid {
            command.arg(&invalid);
        }
        let output = command.output().unwrap();
        assert_eq!(
            output.status.success(),
            valid,
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        if valid {
            let json = String::from_utf8(output.stdout).unwrap();
            for expected in [
                "\"commands\":16",
                "\"theorems\":6",
                "\"executed\":false",
                "\"authority\":true",
            ] {
                assert!(json.contains(expected), "{json}");
            }
        } else {
            assert!(output.stdout.is_empty());
            assert!(!output.stderr.is_empty());
        }
        assert_eq!(std::fs::read(&prefix).unwrap(), original);
    }
}

#[test]
fn installed_constrained_induction_checks_proofs_and_rejects_a_false_suffix() {
    let prefix = file(include_str!(
        "../../../examples/native_constrained_induction.lean"
    ));
    let invalid = file(
        "theorem bad (xs : Vec Nat 1) : 0 = 1 := by\n  induction xs with\n  | cons k x tail ih => exact ih tail (HEq.refl 1) (HEq.refl tail)",
    );
    let bytes = std::fs::read(&prefix).unwrap();
    for valid in [true, false, true] {
        let mut command = Command::new(env!("CARGO_BIN_EXE_fln"));
        command.args(["check-source", "--json"]).arg(&prefix);
        if !valid {
            command.arg(&invalid);
        }
        let output = command.output().unwrap();
        assert_eq!(
            output.status.success(),
            valid,
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        if valid {
            let json = String::from_utf8(output.stdout).unwrap();
            for expected in [
                "\"commands\":12",
                "\"theorems\":6",
                "\"authority\":true",
                "\"executed\":false",
            ] {
                assert!(json.contains(expected), "{json}");
            }
        } else {
            assert!(output.stdout.is_empty());
            assert!(!output.stderr.is_empty());
        }
        assert_eq!(std::fs::read(&prefix).unwrap(), bytes);
    }
}

#[test]
fn installed_constrained_recursion_checks_computations_proofs_and_failure_recovery() {
    let prefix = file(include_str!(
        "../../../examples/native_constrained_recursion.lean"
    ));
    let invalid = file(
        "def bad (w : Walk 7) : Nat := match w with | .done n => 0 | .step n child => let ignored := bad w; 0",
    );
    let original = std::fs::read(&prefix).unwrap();
    for valid in [true, false, true] {
        let mut command = Command::new(env!("CARGO_BIN_EXE_fln"));
        command.args(["check-source", "--json"]).arg(&prefix);
        if !valid {
            command.arg(&invalid);
        }
        let output = command.output().unwrap();
        assert_eq!(
            output.status.success(),
            valid,
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        if valid {
            let json = String::from_utf8(output.stdout).unwrap();
            for expected in [
                "\"commands\":16",
                "\"theorems\":6",
                "\"authority\":true",
                "\"executed\":false",
            ] {
                assert!(json.contains(expected), "{json}");
            }
        } else {
            assert!(output.stdout.is_empty());
            assert!(!output.stderr.is_empty());
        }
        assert_eq!(std::fs::read(&prefix).unwrap(), original);
    }
}

#[test]
fn installed_local_proofs_are_checked_and_never_publish_a_false_suffix() {
    let prefix = file(include_str!("../../../examples/native_local_proofs.lean"));
    let false_suffix = file("theorem bad : 0 = 0 := by\n  have unused : String := 1\n  rfl");
    let original = std::fs::read(&prefix).unwrap();
    for valid in [true, false, true] {
        let mut command = Command::new(env!("CARGO_BIN_EXE_fln"));
        command.args(["check-source", "--json"]).arg(&prefix);
        if !valid {
            command.arg(&false_suffix);
        }
        let output = command.output().unwrap();
        assert_eq!(
            output.status.success(),
            valid,
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        if valid {
            let json = String::from_utf8(output.stdout).unwrap();
            for expected in [
                "\"commands\":12",
                "\"theorems\":8",
                "\"executed\":false",
                "\"authority\":true",
            ] {
                assert!(json.contains(expected), "{json}");
            }
        } else {
            assert!(output.stdout.is_empty());
            assert!(!output.stderr.is_empty());
        }
        assert_eq!(std::fs::read(&prefix).unwrap(), original);
    }
}

#[test]
fn installed_pattern_matrices_check_all_files_and_preserve_failure_isolation() {
    let prefix = file(include_str!(
        "../../../examples/native_pattern_matrices.lean"
    ));
    let bad = file("theorem invalid : swapped 3 7 = 3 := by rfl");
    let original = std::fs::read(&prefix).unwrap();
    for valid in [true, false, true] {
        let mut command = Command::new(env!("CARGO_BIN_EXE_fln"));
        command.args(["check-source", "--json"]).arg(&prefix);
        if !valid {
            command.arg(&bad);
        }
        let output = command.output().unwrap();
        assert_eq!(
            output.status.success(),
            valid,
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        if valid {
            let json = String::from_utf8(output.stdout).unwrap();
            for field in [
                "\"commands\":15",
                "\"theorems\":8",
                "\"executed\":false",
                "\"authority\":true",
            ] {
                assert!(json.contains(field), "{json}");
            }
        } else {
            assert!(output.stdout.is_empty());
            assert!(!output.stderr.is_empty());
        }
        assert_eq!(std::fs::read(&prefix).unwrap(), original);
    }
}

#[test]
fn installed_recursive_matrices_compute_check_proofs_and_isolate_failed_suffixes() {
    let prefix = file(include_str!(
        "../../../examples/native_matrix_recursion.lean"
    ));
    let invalid = file("theorem invalid : copyMatrix 2 true = 3 := by rfl");
    let before = std::fs::read(&prefix).unwrap();
    for valid in [true, false, true] {
        let mut command = Command::new(env!("CARGO_BIN_EXE_fln"));
        command.args(["check-source", "--json"]).arg(&prefix);
        if !valid {
            command.arg(&invalid);
        }
        let result = command.output().unwrap();
        assert_eq!(
            result.status.success(),
            valid,
            "{}",
            String::from_utf8_lossy(&result.stderr)
        );
        if valid {
            let json = String::from_utf8(result.stdout).unwrap();
            for field in [
                "\"commands\":17",
                "\"theorems\":7",
                "\"authority\":true",
                "\"executed\":false",
            ] {
                assert!(json.contains(field), "{json}");
            }
        } else {
            assert!(result.stdout.is_empty());
            assert!(!result.stderr.is_empty());
        }
        assert_eq!(std::fs::read(&prefix).unwrap(), before);
    }
}

#[test]
fn installed_equation_definitions_check_real_terms_and_reject_late_failures() {
    let prefix = file(include_str!("../../../examples/native_equations.lean"));
    let bad = file("def invalid : Bool -> Nat | true => 0 | false => let unused : String := 1; 0");
    let original = std::fs::read(&prefix).unwrap();
    for valid in [true, false, true] {
        let mut command = Command::new(env!("CARGO_BIN_EXE_fln"));
        command.args(["check-source", "--json"]).arg(&prefix);
        if !valid {
            command.arg(&bad);
        }
        let result = command.output().unwrap();
        assert_eq!(
            result.status.success(),
            valid,
            "{}",
            String::from_utf8_lossy(&result.stderr)
        );
        if valid {
            let json = String::from_utf8(result.stdout).unwrap();
            for expected in [
                "\"commands\":15",
                "\"theorems\":7",
                "\"authority\":true",
                "\"executed\":false",
            ] {
                assert!(json.contains(expected), "{json}");
            }
        } else {
            assert!(result.stdout.is_empty());
            assert!(!result.stderr.is_empty());
        }
        assert_eq!(std::fs::read(&prefix).unwrap(), original);
    }
}

#[test]
fn installed_pattern_functions_check_callbacks_and_isolate_invalid_branches() {
    let prefix = file(include_str!(
        "../../../examples/native_pattern_functions.lean"
    ));
    let invalid = file(
        "theorem bad : 0 = 0 := by\n  have ignored : Bool -> Nat := fun | true => 1 | false => (1 : String)\n  rfl",
    );
    let before = std::fs::read(&prefix).unwrap();
    for valid in [true, false, true] {
        let mut command = Command::new(env!("CARGO_BIN_EXE_fln"));
        command.args(["check-source", "--json"]).arg(&prefix);
        if !valid {
            command.arg(&invalid);
        }
        let output = command.output().unwrap();
        assert_eq!(
            output.status.success(),
            valid,
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        if valid {
            let json = String::from_utf8(output.stdout).unwrap();
            for field in [
                "\"commands\":14",
                "\"theorems\":6",
                "\"authority\":true",
                "\"executed\":false",
            ] {
                assert!(json.contains(field), "{json}");
            }
        } else {
            assert!(output.stdout.is_empty());
            assert!(!output.stderr.is_empty());
        }
        assert_eq!(std::fs::read(&prefix).unwrap(), before);
    }
}

#[test]
fn installed_structural_selection_checks_later_inputs_without_partial_success() {
    let prefix = file(include_str!(
        "../../../examples/native_structural_selection.lean"
    ));
    let invalid =
        file("def bad : Bool -> Nat -> Nat | b, .zero => 0 | b, .succ k => bad b (Nat.succ k)");
    let original = std::fs::read(&prefix).unwrap();
    for valid in [true, false, true] {
        let mut command = Command::new(env!("CARGO_BIN_EXE_fln"));
        command.args(["check-source", "--json"]).arg(&prefix);
        if !valid {
            command.arg(&invalid);
        }
        let output = command.output().unwrap();
        assert_eq!(
            output.status.success(),
            valid,
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        if valid {
            let json = String::from_utf8(output.stdout).unwrap();
            for field in [
                "\"commands\":9",
                "\"theorems\":4",
                "\"executed\":false",
                "\"authority\":true",
            ] {
                assert!(json.contains(field), "{json}");
            }
        } else {
            assert!(output.stdout.is_empty());
            assert!(!output.stderr.is_empty());
        }
        assert_eq!(std::fs::read(&prefix).unwrap(), original);
    }
}

#[test]
fn installed_literal_patterns_compute_and_preserve_failed_suffix_isolation() {
    let prefix = file(include_str!(
        "../../../examples/native_literal_patterns.lean"
    ));
    let invalid = file("theorem bad : huge 340282366920938463463374607431768211457 = 17 := by rfl");
    let original = std::fs::read(&prefix).unwrap();
    for valid in [true, false, true] {
        let mut command = Command::new(env!("CARGO_BIN_EXE_fln"));
        command.args(["check-source", "--json"]).arg(&prefix);
        if !valid {
            command.arg(&invalid);
        }
        let result = command.output().unwrap();
        assert_eq!(
            result.status.success(),
            valid,
            "{}",
            String::from_utf8_lossy(&result.stderr)
        );
        if valid {
            let json = String::from_utf8(result.stdout).unwrap();
            for required in [
                "\"commands\":12",
                "\"theorems\":7",
                "\"authority\":true",
                "\"executed\":false",
            ] {
                assert!(json.contains(required), "{json}");
            }
        } else {
            assert!(result.stdout.is_empty());
            assert!(!result.stderr.is_empty());
        }
        assert_eq!(std::fs::read(&prefix).unwrap(), original);
    }
}

#[test]
fn installed_function_children_check_real_recursors_and_preserve_failed_suffixes() {
    let prefix = file(include_str!(
        "../../../examples/native_function_children.lean"
    ));
    let invalid = file("theorem impossible : first (Branching.leaf 4) = 5 := by rfl");
    let before = std::fs::read(&prefix).unwrap();
    for valid in [true, false, true] {
        let mut command = Command::new(env!("CARGO_BIN_EXE_fln"));
        command.args(["check-source", "--json"]).arg(&prefix);
        if !valid {
            command.arg(&invalid);
        }
        let result = command.output().unwrap();
        assert_eq!(
            result.status.success(),
            valid,
            "{}",
            String::from_utf8_lossy(&result.stderr)
        );
        if valid {
            let json = String::from_utf8(result.stdout).unwrap();
            for field in [
                "\"commands\":9",
                "\"theorems\":3",
                "\"authority\":true",
                "\"executed\":false",
            ] {
                assert!(json.contains(field), "{json}");
            }
        } else {
            assert!(result.stdout.is_empty());
            assert!(!result.stderr.is_empty());
        }
        assert_eq!(std::fs::read(&prefix).unwrap(), before);
    }
}
