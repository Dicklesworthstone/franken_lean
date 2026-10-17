//! The same source programs are also run by the pinned Reference in CI.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, Name, SourceCheckLimits};

fn limits() -> SourceCheckLimits {
    SourceCheckLimits::new(EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024)))
}

#[test]
fn shared_definitional_simplification_programs_have_checked_verdicts() {
    let base = Engine::with_source_seed(limits().admission).unwrap().into_complete().unwrap();
    let root = base.logical_root(&KVMap::new());
    let mut cases = 0;
    let mut failures = Vec::new();
    for case in include_str!("source_dsimp.lean").split("-- CASE ").skip(1) {
        let (header, source) = case.split_once('\n').unwrap();
        let (name, verdict) = header.split_once(' ').unwrap();
        assert!(matches!(verdict, "accept" | "reject"), "{header}");
        let result = base.check_source_files(&[source.as_bytes()], &KVMap::new(), limits());
        match (verdict, result) {
            ("accept", Ok(result)) => {
                let accepted = result.into_complete().expect("no inconclusive success").engine;
                assert!(accepted.environment().contains(&Name::from_components(["t"])), "{name}");
            }
            ("reject", Err(_)) => {}
            (_, Err(error)) => failures.push(format!("{name}: {error:?}")),
            (_, Ok(_)) => failures.push(format!("{name}: unexpectedly admitted")),
        }
        assert_eq!(base.logical_root(&KVMap::new()), root, "{name}: mutated input engine");
        assert!(!base.environment().contains(&Name::from_components(["bad"])));
        cases += 1;
    }
    assert_eq!(cases, 26, "shared fixture inventory");
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}
