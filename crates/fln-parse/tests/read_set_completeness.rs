//! Positive, negative, iteration, option, and capability read-set coverage.

#![forbid(unsafe_code)]

use fln_core::mode::Mode;
use fln_core::name::Name;
use fln_core::outcome::Outcome;
use fln_hash::domain::{Digest, Domain, hash};
use fln_parse::macro_txn::{
    CanonicalPath, MacroCacheability, MacroCapabilities, MacroInvocationIdentity, MacroMemo,
    MacroMemoLookup, MacroMemoRefusal, MacroObservedValue, MacroReadObservation, MacroReadSource,
    MacroState, MacroStateSlot, MacroStateSurface, MacroTxnBudget, MacroTxnConfig, MacroTxnError,
    MacroValue, OpaqueReadReason, run_macro_transaction, validate_read_set_perturbation,
};
use fln_parse::registry::GrammarEpoch;

fn name(value: &str) -> Name {
    Name::from_components(["Main", value])
}

fn epoch() -> GrammarEpoch {
    GrammarEpoch::from_parts(23, Digest([0x23; 32]))
}

fn identity(label: &str, mode: Mode) -> MacroInvocationIdentity {
    MacroInvocationIdentity::from_canonical_row(
        epoch(),
        mode,
        format!("fln.test.read-set/1\0{label}").into_bytes(),
    )
}

fn product<T>(
    report: fln_parse::macro_txn::MacroRunReport<T>,
) -> fln_parse::macro_txn::MacroTxnProduct<T> {
    match report.into_status() {
        Outcome::Complete(Ok(product)) => product,
        _ => panic!("expected a completed transaction product"),
    }
}

#[test]
fn all_instrumented_reads_are_exact_and_unknown_reads_are_uncacheable() {
    let mut state = MacroState::new();
    state.insert_environment(name("present"), MacroValue::from_text("value"));
    state.insert_extension(name("ext"), MacroValue::from_text("enabled"));
    state.insert_option(name("trace"), MacroValue::from_text("false"));

    let present_path = CanonicalPath::new("/workspace/input.txt").expect("canonical path");
    let absent_path = CanonicalPath::new("/workspace/missing.txt").expect("canonical path");
    let mut capabilities = MacroCapabilities::new();
    capabilities.insert_file(present_path.clone(), b"one".to_vec());

    let invocation = identity("complete", Mode::Sound);
    let complete = product(run_macro_transaction(
        MacroTxnConfig::new(
            invocation.clone(),
            &state,
            &capabilities,
            MacroTxnBudget::generous(),
            None,
        ),
        |txn| {
            assert_eq!(
                txn.read_environment(&name("present"))?,
                Some(MacroValue::from_text("value"))
            );
            assert_eq!(txn.read_environment(&name("missing"))?, None);
            assert_eq!(
                txn.read_option(&name("trace"))?,
                Some(MacroValue::from_text("false"))
            );
            assert_eq!(
                txn.read_file(&present_path)?,
                Some(MacroValue::from_text("one"))
            );
            assert_eq!(txn.read_file(&absent_path)?, None);
            assert_eq!(
                txn.iterate_extensions()?,
                vec![(name("ext"), MacroValue::from_text("enabled"))]
            );
            Ok("semantic-product")
        },
    ));

    assert!(complete.reads().is_complete());
    assert!(matches!(
        complete.cacheability(),
        MacroCacheability::Cacheable
    ));
    assert!(
        complete
            .reads()
            .observations()
            .contains(&MacroReadObservation::StateSlot {
                slot: MacroStateSlot::Environment(name("present")),
                source: MacroReadSource::Snapshot,
                observed: MacroObservedValue::Value(MacroValue::from_text("value")),
            })
    );
    assert!(
        complete
            .reads()
            .observations()
            .contains(&MacroReadObservation::StateSlot {
                slot: MacroStateSlot::Environment(name("missing")),
                source: MacroReadSource::Snapshot,
                observed: MacroObservedValue::Absent,
            })
    );
    assert!(
        complete
            .reads()
            .observations()
            .contains(&MacroReadObservation::StateIteration {
                surface: MacroStateSurface::Extension,
                snapshot_entries: vec![(name("ext"), MacroValue::from_text("enabled"))],
                observed_entries: vec![(name("ext"), MacroValue::from_text("enabled"))],
            })
    );

    let mut memo = MacroMemo::new();
    memo.insert(complete).expect("complete reads are cacheable");
    assert!(matches!(
        memo.lookup(&invocation, &state, &capabilities),
        MacroMemoLookup::Hit(_)
    ));

    let mut stale_negative = state.clone();
    stale_negative.insert_environment(name("missing"), MacroValue::from_text("now-present"));
    assert!(matches!(
        memo.lookup(&invocation, &stale_negative, &capabilities),
        MacroMemoLookup::StaleReadMiss
    ));

    let mut stale_file = capabilities.clone();
    stale_file.insert_file(present_path, b"two".to_vec());
    assert!(matches!(
        memo.lookup(&invocation, &state, &stale_file),
        MacroMemoLookup::StaleReadMiss
    ));

    let unknown = product(run_macro_transaction(
        MacroTxnConfig::new(
            identity("unknown", Mode::Faithful),
            &state,
            &capabilities,
            MacroTxnBudget::generous(),
            None,
        ),
        |txn| {
            txn.mark_uninstrumented_read("host callback outside capability context")?;
            Ok(())
        },
    ));
    assert!(matches!(
        unknown.cacheability(),
        MacroCacheability::Uncacheable { .. }
    ));
    assert!(
        unknown
            .reads()
            .opaque_reasons()
            .contains(&OpaqueReadReason::Uninstrumented(
                "host callback outside capability context".to_string()
            ))
    );
    assert!(matches!(
        MacroMemo::new().insert(unknown),
        Err(MacroMemoRefusal::Uncacheable { .. })
    ));

    let clock = product(run_macro_transaction(
        MacroTxnConfig::new(
            identity("clock", Mode::Faithful),
            &state,
            &capabilities,
            MacroTxnBudget::generous(),
            None,
        ),
        |txn| txn.observe_clock(123),
    ));
    assert_eq!(clock.reads().opaque_reasons().len(), 1);
    assert!(
        clock
            .reads()
            .opaque_reasons()
            .contains(&OpaqueReadReason::Clock)
    );

    let denied = run_macro_transaction(
        MacroTxnConfig::new(
            identity("clock-denied", Mode::Sound),
            &state,
            &capabilities,
            MacroTxnBudget::generous(),
            None,
        ),
        |txn| txn.observe_clock(123),
    );
    assert!(matches!(
        denied.status(),
        Outcome::Complete(Err(failure))
            if matches!(
                failure.error(),
                MacroTxnError::CapabilityDenied {
                    capability: "clock",
                    mode: Mode::Sound
                }
            )
    ));

    let omitted = fln_parse::macro_txn::MacroReadSet::new();
    let before = hash(Domain::Fixture, b"before");
    let after = hash(Domain::Fixture, b"after");
    assert!(
        validate_read_set_perturbation(&omitted, &state, &capabilities, before, after).is_err(),
        "an output-changing perturbation invisible to the declared reads is an internal fault"
    );
    assert!(
        validate_read_set_perturbation(
            memo.lookup(&invocation, &state, &capabilities)
                .hit()
                .expect("memo hit")
                .reads(),
            &stale_negative,
            &capabilities,
            before,
            after,
        )
        .is_ok(),
        "a perturbation that changes a declared negative read is accounted for"
    );
}

trait HitExt<'a, T> {
    fn hit(self) -> Option<&'a fln_parse::macro_txn::MacroTxnProduct<T>>;
}

impl<'a, T> HitExt<'a, T> for MacroMemoLookup<'a, T> {
    fn hit(self) -> Option<&'a fln_parse::macro_txn::MacroTxnProduct<T>> {
        match self {
            MacroMemoLookup::Hit(product) => Some(product),
            MacroMemoLookup::Miss
            | MacroMemoLookup::CollisionMiss
            | MacroMemoLookup::StaleReadMiss => None,
        }
    }
}

#[test]
fn generated_read_and_write_sequences_equal_fresh_execution() {
    let capabilities = MacroCapabilities::new();
    for seed in 0u64..128 {
        let mut initial = MacroState::new();
        initial.insert_environment(name("a"), MacroValue::from_text("initial"));
        initial.set_next_gensym(seed % 5);
        let mut reference = initial.clone();

        let report = run_macro_transaction(
            MacroTxnConfig::new(
                identity(&format!("sequence-{seed}"), Mode::Sound),
                &initial,
                &capabilities,
                MacroTxnBudget::generous(),
                None,
            ),
            |txn| {
                let mut word = seed | 1;
                for step in 0..24u64 {
                    word = word
                        .wrapping_mul(6_364_136_223_846_793_005)
                        .wrapping_add(1_442_695_040_888_963_407);
                    let key = name(match (word >> 5) % 3 {
                        0 => "a",
                        1 => "b",
                        _ => "c",
                    });
                    match word % 5 {
                        0 => {
                            let value = MacroValue::from_text(format!("{seed}:{step}"));
                            txn.set_environment(key.clone(), value.clone())?;
                            reference.insert_environment(key, value);
                        }
                        1 => {
                            txn.remove_environment(key.clone())?;
                            reference.remove_environment(&key);
                        }
                        2 => {
                            assert_eq!(
                                txn.read_environment(&key)?,
                                reference.environment(&key).cloned()
                            );
                        }
                        3 => {
                            let current = reference.next_gensym();
                            assert_eq!(txn.fresh_gensym()?, current);
                            reference.set_next_gensym(current + 1);
                        }
                        _ => {
                            let observed = txn.iterate_environment()?;
                            let expected = ["a", "b", "c"]
                                .into_iter()
                                .filter_map(|key| {
                                    let key = name(key);
                                    reference
                                        .environment(&key)
                                        .cloned()
                                        .map(|value| (key, value))
                                })
                                .collect::<Vec<_>>();
                            assert_eq!(observed, expected);
                        }
                    }
                }
                Ok(())
            },
        );
        let product = product(report);
        let mut published = initial;
        product
            .publish(&mut published, &capabilities)
            .expect("the original snapshot admits its generated journal");
        assert_eq!(published, reference, "seed {seed}");
    }
}
