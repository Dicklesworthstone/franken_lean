//! Closed callable interfaces and opaque handles stored in ordinary source ST cells.
#![forbid(unsafe_code)]
use super::*;
use std::collections::BTreeSet;

fn program(stages: &[(&str, &str)], result: &str) -> String {
    let mut body = format!("ST.pure ({result})");
    for (binder, action) in stages.iter().rev() {
        body = if let Some(local) = binder.strip_prefix("let ") {
            format!("let {local} := {action}; {body}")
        } else {
            format!("ST.bind ({action}) (fun {binder} => {body})")
        };
    }
    format!("#eval runST (fun sigma => {body})\n")
}

fn programs() -> Vec<(&'static str, String, usize)> {
    vec![
        (
            "captured callbacks survive get, set and swap",
            program(
                &[
                    ("baseRef", "ST.Prim.mkRef (σ := sigma) (α := Nat) 10"),
                    ("base", "ST.Prim.Ref.get baseRef"),
                    (
                        "functions",
                        "ST.Prim.mkRef (σ := sigma) (α := Nat -> Nat) (fun n => Nat.add base n)",
                    ),
                    ("before", "ST.Prim.Ref.get functions"),
                    ("_", "ST.Prim.Ref.set functions (fun n => Nat.mul 2 n)"),
                    ("old", "ST.Prim.Ref.swap functions (fun n => Nat.add 30 n)"),
                    ("current", "ST.Prim.Ref.get functions"),
                ],
                "Nat.add (Nat.add (before 2) (before 3)) (Nat.add (old 4) (current 5))",
            ),
            68,
        ),
        (
            "a retrieved multiargument callback can be partially applied",
            program(
                &[
                    (
                        "functions",
                        "ST.Prim.mkRef (σ := sigma) (α := Nat -> Nat -> Nat) (fun x y => Nat.add x y)",
                    ),
                    ("callback", "ST.Prim.Ref.get functions"),
                    ("let suffix : Nat -> Nat", "callback 10"),
                ],
                "suffix 20",
            ),
            30,
        ),
        (
            "callback arguments retain their own callable interfaces",
            program(
                &[
                    (
                        "functions",
                        "ST.Prim.mkRef (σ := sigma) (α := (Nat -> Nat) -> Nat) (fun f => f 7)",
                    ),
                    ("old", "ST.Prim.Ref.swap functions (fun f => f 11)"),
                    ("current", "ST.Prim.Ref.get functions"),
                ],
                "Nat.add (old (fun n => Nat.add n 3)) (current (fun n => Nat.mul n 2))",
            ),
            32,
        ),
        (
            "stored actions run only when explicitly invoked",
            program(
                &[
                    ("counter", "ST.Prim.mkRef (σ := sigma) (α := Nat) 0"),
                    (
                        "let action : ST sigma Nat",
                        "ST.bind (ST.Prim.Ref.get counter) (fun count => ST.bind (ST.Prim.Ref.set counter (Nat.succ count)) (fun _ => ST.pure count))",
                    ),
                    (
                        "actions",
                        "ST.Prim.mkRef (σ := sigma) (α := ST sigma Nat) action",
                    ),
                    ("before", "ST.Prim.Ref.get counter"),
                    ("firstAction", "ST.Prim.Ref.get actions"),
                    ("oldAction", "ST.Prim.Ref.swap actions (ST.pure 100)"),
                    ("afterRead", "ST.Prim.Ref.get counter"),
                    ("firstValue", "firstAction"),
                    ("secondValue", "oldAction"),
                    ("currentAction", "ST.Prim.Ref.get actions"),
                    ("replacement", "currentAction"),
                    ("after", "ST.Prim.Ref.get counter"),
                ],
                "Nat.add (Nat.mul before 1000000) (Nat.add (Nat.mul afterRead 100000) (Nat.add (Nat.mul firstValue 10000) (Nat.add (Nat.mul secondValue 1000) (Nat.add (Nat.mul replacement 10) after))))",
            ),
            2002,
        ),
        (
            "nested references retain identity after replacement",
            program(
                &[
                    ("left", "ST.Prim.mkRef (σ := sigma) (α := Nat) 7"),
                    ("right", "ST.Prim.mkRef (σ := sigma) (α := Nat) 11"),
                    (
                        "holder",
                        "ST.Prim.mkRef (σ := sigma) (α := ST.Ref sigma Nat) left",
                    ),
                    ("snapshot", "ST.Prim.Ref.get holder"),
                    ("old", "ST.Prim.Ref.swap holder right"),
                    ("_", "ST.Prim.Ref.set old 19"),
                    ("fromSnapshot", "ST.Prim.Ref.get snapshot"),
                    ("current", "ST.Prim.Ref.get holder"),
                    ("_", "ST.Prim.Ref.set current 23"),
                    ("fromLeft", "ST.Prim.Ref.get left"),
                    ("fromRight", "ST.Prim.Ref.get right"),
                ],
                "Nat.add fromSnapshot (Nat.add fromLeft fromRight)",
            ),
            61,
        ),
        (
            "Boolean and unit payloads keep scalar semantics",
            program(
                &[
                    ("token", "ST.Prim.mkRef (σ := sigma) (α := Unit) Unit.unit"),
                    ("_", "ST.Prim.Ref.get token"),
                    ("_", "ST.Prim.Ref.swap token Unit.unit"),
                    ("flags", "ST.Prim.mkRef (σ := sigma) (α := Bool) Bool.false"),
                    ("old", "ST.Prim.Ref.swap flags Bool.true"),
                    ("current", "ST.Prim.Ref.get flags"),
                ],
                "match old with | false => (match current with | true => 42 | false => 0) | true => 0",
            ),
            42,
        ),
    ]
}

/// Run through both the decoded diagnostic fixture and the fully admitted ST
/// import closure (the existing callers of check_payloads). No helper bypasses
/// source checking, representation discovery, closure conversion or ownership.
pub(super) fn check(engine: &Engine) {
    let options = KVMap::new();
    let root = engine.logical_root(&options);
    let limits = EngineExecutionLimits::new(Budget::for_stack_bytes(STACK));
    let allowed: BTreeSet<_> = EXTERNS[1..]
        .iter()
        .map(|(target, _)| format!("extern:{target}"))
        .collect();
    let mut observed = BTreeSet::new();
    let mut callback_query = None;
    for (label, source, expected) in programs() {
        let run = || {
            engine
                .execute_source_commands_with_checks(source.as_bytes(), &options, limits)
                .unwrap_or_else(|error| panic!("{label}: {error:?}"))
                .into_complete()
                .unwrap_or_else(|outcome| panic!("{label}: {outcome:?}"))
        };
        let first = run();
        assert_eq!(first.batch.source_evaluation_indices.len(), 1, "{label}");
        let execution = &first.batch.executions[first.batch.source_evaluation_indices[0]];
        assert_scalar(
            execution,
            expected,
            CheckerAdmissionGround::UnsafeQuarantine,
        );
        if callback_query.is_none() {
            callback_query = Some(execution.declaration.clone());
        }
        let bytes = execution.flbc_artifact.clone();
        let replay =
            fln_comp::flbc::decode_canonical(&bytes, fln_comp::flbc::CodecLimits::default())
                .unwrap();
        assert_eq!(
            fln_comp::flbc::encode_canonical(&replay, fln_comp::flbc::CodecLimits::default())
                .unwrap(),
            bytes
        );
        let rows: BTreeSet<_> = replay
            .functions()
            .iter()
            .flat_map(|function| &function.code)
            .filter_map(|instruction| match instruction {
                fln_comp::flbc::Instruction::Intrinsic { row, .. }
                    if row.starts_with("extern:ST.Prim.") =>
                {
                    Some(row.clone())
                }
                _ => None,
            })
            .collect();
        assert!(rows.is_subset(&allowed), "{label}: {rows:?}");
        assert!(rows.contains("extern:ST.Prim.mkRef"), "{label}");
        assert!(rows.contains("extern:ST.Prim.Ref.get"), "{label}");
        observed.extend(rows);
        for _ in 0..2 {
            let exit = fln_vm::interpreter::execute(
                &replay,
                fln_vm::interpreter::ExecutionLimits::default(),
                None,
            )
            .into_complete()
            .unwrap();
            assert_eq!(
                fln::closed_vm_value(&exit).unwrap(),
                Some(ClosedVmValue::Scalar(expected)),
                "{label} canonical replay"
            );
        }
        drop(first);
        let repeated = run();
        assert_eq!(repeated.batch.source_evaluation_indices.len(), 1, "{label}");
        let execution = &repeated.batch.executions[repeated.batch.source_evaluation_indices[0]];
        assert_scalar(
            execution,
            expected,
            CheckerAdmissionGround::UnsafeQuarantine,
        );
        assert_eq!(execution.flbc_artifact, bytes, "{label}");
        drop(repeated);
        assert_eq!(engine.logical_root(&options), root, "{label}");
    }
    assert_eq!(observed, allowed);
    // The new payload families cannot authorize primitives merely because
    // their callable interfaces or opaque handles have already been proved.
    let query = callback_query.unwrap();
    for (target, _) in &EXTERNS[1..] {
        let missing =
            Engine::from_environment(rebuild_environment(engine, None, Some(&name(target))));
        assert!(matches!(
            rejected(&missing, &query, limits),
            EngineExecutionError::Ingress(_)
        ));
    }
    assert_eq!(engine.logical_root(&options), root);
}

#[test]
fn callable_payload_sources_match_the_live_pinned_reference() {
    use std::process::Command;
    let reference = std::env::var_os("FLN_REFERENCE_LEAN")
        .map(PathBuf::from)
        .or_else(|| {
            let library = reference_library()?;
            Some(library.parent()?.parent()?.join("bin/lean"))
        });
    let Some(reference) = reference else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "the pinned Reference is required for callable payloads"
        );
        eprintln!("SKIP: live callable payload oracle requires the pinned Reference");
        return;
    };
    let lock = include_str!(concat!(env!("CARGO_MANIFEST_DIR"), "/../../SUITE.lock"));
    let pin = lock
        .lines()
        .find(|line| line.starts_with("reference "))
        .and_then(|line| {
            line.split_whitespace()
                .find_map(|s| s.strip_prefix("commit="))
        })
        .expect("SUITE.lock Reference commit");
    let version = Command::new(&reference).arg("--githash").output().unwrap();
    assert!(version.status.success());
    assert_eq!(String::from_utf8(version.stdout).unwrap().trim(), pin);
    let unique = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let directory = std::env::temp_dir().join(format!(
        "fln-callable-payloads-{}-{unique}",
        std::process::id()
    ));
    std::fs::create_dir(&directory).unwrap();
    let mut source = "prelude\nimport Init.System.ST\n".to_owned();
    let mut expected = String::new();
    for (_, program, value) in programs() {
        source.push_str(&program);
        expected.push_str(&format!("{value}\n"));
    }
    let file = directory.join("CallablePayloads.lean");
    std::fs::write(&file, source).unwrap();
    let result = Command::new(&reference).arg(&file).output().unwrap();
    std::fs::write(directory.join("oracle.stdout"), &result.stdout).unwrap();
    std::fs::write(directory.join("oracle.stderr"), &result.stderr).unwrap();
    assert!(
        result.status.success(),
        "Reference callable payload oracle failed in {directory:?}: {}{}",
        String::from_utf8_lossy(&result.stdout),
        String::from_utf8_lossy(&result.stderr),
    );
    assert_eq!(String::from_utf8(result.stdout).unwrap(), expected);
}
