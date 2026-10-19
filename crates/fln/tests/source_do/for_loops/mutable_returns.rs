//! Shared pin-checked mutable returns through ordinary source interfaces and FLBC replay.
#![forbid(unsafe_code)]
use super::*;
use fln::{CheckerAdmissionGround, ClosedVmValue, FlbcExecutionLimits};
use fln_comp::flbc::{CodecLimits, decode_canonical, encode_canonical};
use std::collections::BTreeMap;

const SOURCE: &str = include_str!("mutable_returns.lean");
const EXPECTED: &str = include_str!("mutable_returns.expected.tsv");
const HEADER: &str = "prelude\nimport Init.Data.List.Control\nimport Init.Control.Id\n\n";
const COUNT: usize = 53;

struct Probe<'a> {
    label: &'a str,
    kind: &'a str,
    query: &'a str,
    expected: &'a str,
}

fn source_body() -> &'static str {
    SOURCE
        .strip_prefix(HEADER)
        .expect("the exact explicit pin fixture header")
}

fn probes() -> Vec<Probe<'static>> {
    let mut expected = BTreeMap::new();
    for line in EXPECTED.lines() {
        let columns: Vec<_> = line.splitn(3, '\t').collect();
        assert_eq!(columns.len(), 3, "complete fixed oracle row");
        assert!(matches!(columns[1], "Nat" | "String"));
        assert!(
            expected
                .insert(columns[0], (columns[1], columns[2]))
                .is_none(),
            "unique fixed oracle labels",
        );
    }
    assert_eq!(expected.len(), COUNT);
    let mut probes = Vec::new();
    let mut pending = None;
    for line in SOURCE.lines().map(str::trim) {
        if let Some(marker) = line.strip_prefix("-- FLN_MUTABLE_PROBE ") {
            assert!(pending.is_none(), "one marker for each evaluation");
            let columns: Vec<_> = marker.split_whitespace().collect();
            assert_eq!(columns.len(), 2);
            pending = Some((columns[0], columns[1]));
        } else if line.starts_with("#eval ") {
            let (label, kind) = pending.take().expect("every evaluation has a marker");
            let (expected_kind, value) =
                expected.remove(label).expect("every probe has a pin value");
            assert_eq!(kind, expected_kind, "{label}");
            probes.push(Probe {
                label,
                kind,
                query: line,
                expected: value,
            });
        }
    }
    assert!(pending.is_none());
    assert_eq!(probes.len(), COUNT, "preserve every shared pin probe");
    assert!(expected.is_empty(), "every fixed row is executed");
    probes
}

fn fixture_engine() -> Engine {
    // The existing ordinary source library supplies Pure, Bind, ForIn and Id.
    // The pin-only Monad witnesses call these same shared pure/bind operations;
    // no witness, algorithm or dictionary is imported as trusted native data.
    let seed = checked(
        &engine(),
        "structure Prod (A B : Type) where\n  fst : A\n  snd : B\n",
    );
    let (definitions, _) = source_body()
        .split_once("-- FLN_MUTABLE_PROBE ")
        .expect("the shared definitions precede their fixed evaluations");
    checked(&seed, definitions)
}

fn assert_value(exit: &VmExit, probe: &Probe<'_>) {
    match probe.kind {
        "Nat" => {
            let VmExit::Returned(result) = exit else {
                panic!("{} did not return: {exit:?}", probe.label);
            };
            assert_eq!(
                fln_vm::interpreter::nat_decimal(&result.value).as_deref(),
                Some(probe.expected),
                "{}: {}",
                probe.label,
                probe.query,
            );
        }
        "String" => {
            assert_eq!(
                fln::closed_vm_value(exit).expect("closed source result"),
                Some(ClosedVmValue::String(probe.expected.to_owned())),
                "{}: {}",
                probe.label,
                probe.query,
            );
        }
        _ => unreachable!("fixed row kinds were validated"),
    }
}

#[test]
fn mutable_loop_returns_match_the_pin_and_replay_flbc() {
    let base = fixture_engine();
    let options = KVMap::new();
    let before = base.logical_root(&options);
    for probe in probes() {
        let run = base
            .execute_source_commands_with_checks(
                probe.query.as_bytes(),
                &options,
                EngineExecutionLimits::new(limits().admission.kernel),
            )
            .unwrap_or_else(|error| panic!("{}: {error:?}", probe.label))
            .into_complete()
            .unwrap_or_else(|error| panic!("{}: explicit budget: {error:?}", probe.label));
        assert_eq!(run.batch.source_evaluation_indices.len(), 1);
        let execution = &run.batch.executions[run.batch.source_evaluation_indices[0]];
        assert_eq!(execution.checker.schema, "fln.checker-admission/1");
        // Every probe query is an `#eval` line, and #eval's auxiliary is unsafe
        // at the pin (BuiltinEvalCommand.lean:92).
        assert_eq!(
            execution.checker.ground,
            CheckerAdmissionGround::UnsafeQuarantine,
        );
        assert_value(&execution.exit, &probe);
        let module = decode_canonical(&execution.flbc_artifact, CodecLimits::default())
            .expect("independent FLBC validation");
        assert_eq!(
            encode_canonical(&module, CodecLimits::default()).expect("canonical encoding"),
            execution.flbc_artifact,
        );
        let replay = fln::execute_flbc_artifact(
            &execution.flbc_artifact,
            &options,
            FlbcExecutionLimits::default(),
        )
        .unwrap_or_else(|error| panic!("{}: replay: {error:?}", probe.label))
        .into_complete()
        .unwrap_or_else(|error| panic!("{}: replay budget: {error:?}", probe.label));
        assert_value(&replay, &probe);
        assert_eq!(base.logical_root(&options), before);
    }
    eprintln!("all {COUNT} mutable-return values and independent FLBC replays matched the pin");
}

#[test]
fn inactive_ill_typed_returns_fail_without_publishing_and_recovery_succeeds() {
    let base = fixture_engine();
    let options = KVMap::new();
    let before = base.logical_root(&options);
    for source in [
        "def rejectedMutableReturn : MutableState Nat := do\n  let mut total := 0\n  for value in mutableItems true do\n    total := total + value\n    if false then return true\n  return total\n",
        "def rejectedNestedReturn : MutableState Nat := do\n  let mut total := 0\n  let mut count := 0\n  for first in mutableItems true do\n    for second in mutableItems true do\n      total := total + first + second\n      count := count + 1\n      if false then return true\n  return (total + count)\n",
        "def rejectedTerminalReturn : MutableState Nat := do\n  let mut total := 0\n  for value in mutableItems true do\n    if false then\n      total := total + value\n      return true\n  return total\n",
        "def rejectedTerminalOuterReturn : Id Nat := do\n  let mut total := 0\n  if false then\n    total := total + 1\n    return true\n  return total\n",
    ] {
        fln_parse::parse_definition(source.as_bytes())
            .unwrap_or_else(|error| panic!("the negative must reach elaboration: {error:?}"));
        // The payload is the only difference: this counterfactual must pass.
        checked(&base, &source.replace("return true", "return total"));
        assert!(
            base.check_source_files(&[source.as_bytes()], &options, limits())
                .is_err(),
            "inactive return still has the enclosing Nat result type: {source}",
        );
        assert_eq!(base.logical_root(&options), before);
    }
    checked(
        &base,
        "def mutableReturnRecovery : MutableState Nat := do\n  let mut total := 0\n  for value in mutableItems true do\n    total := total + value\n    if value == 2 then return total\n  return total\ntheorem mutableReturnRecoveryValue : (mutableReturnRecovery 0).value = 3 := by rfl\n",
    );
    assert_eq!(base.logical_root(&options), before);
}
