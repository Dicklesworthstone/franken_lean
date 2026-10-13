use super::*;
use fln_core::expr::Expr;
use fln_core::level::Level;
use fln_core::options::KVMap;
use fln_env::constants::{AxiomVal, ConstantInfo, ConstantVal};
use fln_env::extensions::{CheckpointLimits, ProofBudget};
use fln_env::modules::ModuleEpoch;

fn n(text: &str) -> Name {
    Name::from_components(text.split('.'))
}

fn environment() -> Environment {
    ["A.call", "B.call"]
        .into_iter()
        .fold(Environment::new(), |env, label| {
            env.add_decl(ConstantInfo::Axiom(AxiomVal {
                base: ConstantVal {
                    name: n(label),
                    level_params: Vec::new(),
                    type_: Expr::sort(Level::one()),
                },
                is_unsafe: false,
            }))
            .unwrap()
        })
}

fn standard(symbol: &str) -> ExternEntry {
    ExternEntry::Standard {
        backend: n("all"),
        symbol: symbol.into(),
    }
}

#[test]
fn all_entry_forms_preserve_exact_names_text_and_order() {
    let entries = vec![
        ExternEntry::Adhoc {
            backend: Name::anonymous(),
        },
        ExternEntry::Inline {
            backend: Name::num_overflowing(Name::str(n("backend"), "part.with.dot"), 17),
            pattern: "λ value\0 $1".into(),
        },
        standard("lean_example"),
        ExternEntry::Opaque,
        standard("different"),
    ];
    let base = environment();
    let env = register(&base, &n("A.call"), entries.clone()).unwrap();
    assert_eq!(env.len(), base.len(), "metadata admits no declaration");
    assert_eq!(
        ExternTable::read(&env).unwrap().get(&n("A.call")),
        Some(entries.as_slice())
    );
    assert_eq!(ExternTable::read(&env).unwrap().get(&n("B.call")), None);
    let state = env.extension(&journal_name()).unwrap();
    assert!(supports(&state.descriptor));
    assert_eq!(
        state.descriptor.checkpoint,
        CheckpointSemantics::FullJournal
    );
    assert_eq!(
        decode_entry(&state.entries().next().unwrap().payload).unwrap(),
        (n("A.call"), entries)
    );
}

#[test]
fn last_registration_replaces_the_whole_list_and_empty_is_explicit() {
    let base = environment();
    assert!(ExternTable::read(&base).unwrap().is_empty());
    let first = register(
        &base,
        &n("A.call"),
        vec![standard("first"), ExternEntry::Opaque],
    )
    .unwrap();
    let second = register(&first, &n("A.call"), vec![standard("second")]).unwrap();
    let third = register(&second, &n("A.call"), vec![]).unwrap();
    assert_eq!(
        ExternTable::read(&first)
            .unwrap()
            .get(&n("A.call"))
            .unwrap()
            .len(),
        2
    );
    assert_eq!(
        ExternTable::read(&second).unwrap().get(&n("A.call")),
        Some([standard("second")].as_slice())
    );
    assert_eq!(
        ExternTable::read(&third).unwrap().get(&n("A.call")),
        Some([].as_slice())
    );
    assert_eq!(ExternTable::read(&third).unwrap().len(), 1);
    assert_eq!(third.extension(&journal_name()).unwrap().len(), 3);
    let options = KVMap::new();
    assert_ne!(base.logical_root(&options), first.logical_root(&options));
    assert_ne!(first.logical_root(&options), second.logical_root(&options));
    assert_ne!(second.logical_root(&options), third.logical_root(&options));
}

#[test]
fn unknown_declarations_and_foreign_or_malformed_journals_fail_closed() {
    let base = environment();
    assert_eq!(
        register(&base, &n("missing"), vec![standard("native")]),
        Err(ExternError::UnknownDeclaration(n("missing")))
    );
    let unknown = base
        .register_extension(descriptor())
        .unwrap()
        .push_extension_entry(
            &journal_name(),
            encode_entry(&n("missing"), &[ExternEntry::Opaque]).unwrap(),
        )
        .unwrap();
    assert_eq!(
        ExternTable::read(&unknown),
        Err(ExternError::UnknownDeclaration(n("missing")))
    );
    let good = register(&base, &n("A.call"), vec![standard("native")]).unwrap();
    let bad = good.push_extension_entry(&journal_name(), vec![0]).unwrap();
    assert_eq!(
        ExternTable::read(&bad),
        Err(ExternError::Malformed),
        "an earlier valid row cannot hide a malformed later row"
    );
    let mut foreign = descriptor();
    foreign.provenance = PayloadProvenance::Opaque;
    let foreign = base.register_extension(foreign).unwrap();
    assert_eq!(ExternTable::read(&foreign), Err(ExternError::Malformed));
    assert_eq!(
        register(&foreign, &n("A.call"), vec![]),
        Err(ExternError::Malformed)
    );
    assert_eq!(base, environment(), "failures preserve the input snapshot");
}

#[test]
fn codec_rejects_truncation_extra_bytes_bad_tags_utf8_and_oversized_counts() {
    let good = encode_entry(&n("A.call"), &[standard("symbol")]).unwrap();
    for end in 0..good.len() {
        assert!(decode_entry(&good[..end]).is_err(), "accepted prefix {end}");
    }
    let mut extra = good.clone();
    extra.push(0);
    assert_eq!(decode_entry(&extra), Err(ExternError::Malformed));
    let mut prefix = MAGIC.to_vec();
    write_name(&n("A.call"), &mut prefix).unwrap();
    let mut count_overflow = prefix.clone();
    count_overflow.extend(u32::MAX.to_le_bytes());
    assert_eq!(decode_entry(&count_overflow), Err(ExternError::Limit));
    let mut tag = prefix.clone();
    tag.extend(1_u32.to_le_bytes());
    tag.push(255);
    assert_eq!(decode_entry(&tag), Err(ExternError::Malformed));
    let mut utf8 = prefix;
    utf8.extend(1_u32.to_le_bytes());
    utf8.extend([2, 0]); // Standard, anonymous backend.
    utf8.extend(1_u32.to_le_bytes());
    utf8.push(255);
    assert_eq!(decode_entry(&utf8), Err(ExternError::Malformed));
    assert_eq!(
        decode_entry(&vec![0; MAX_ENTRY_BYTES + 1]),
        Err(ExternError::Limit)
    );
    assert_eq!(
        encode_entry(&n("A.call"), &vec![ExternEntry::Opaque; MAX_ENTRIES + 1]),
        Err(ExternError::Limit)
    );
    assert_eq!(
        encode_entry(&n("A.call"), &[standard(&"x".repeat(MAX_ENTRY_BYTES))]),
        Err(ExternError::Limit)
    );
}

#[test]
fn metering_precedes_iteration_and_payload_parsing_and_failure_has_no_partial_table() {
    let env = register(&environment(), &n("A.call"), vec![standard("symbol")]).unwrap();
    let bytes = env
        .extension(&journal_name())
        .unwrap()
        .entries()
        .next()
        .unwrap()
        .payload
        .len();
    let mut charges = Vec::new();
    let table = ExternTable::read_metered(&env, |amount| {
        charges.push(amount);
        Ok::<_, &'static str>(())
    })
    .unwrap();
    assert_eq!(charges, [1, 1, bytes]);
    assert_eq!(
        table.get(&n("A.call")),
        Some([standard("symbol")].as_slice())
    );
    for rejected_call in 0..3 {
        let mut calls = 0;
        let result = ExternTable::read_metered(&env, |_| {
            let current = calls;
            calls += 1;
            if current == rejected_call {
                Err("spent")
            } else {
                Ok(())
            }
        });
        assert_eq!(result, Err(ExternReadError::Budget("spent")));
        assert_eq!(calls, rejected_call + 1);
    }
    let malformed = env
        .push_extension_entry(&journal_name(), vec![255])
        .unwrap();
    let mut calls = 0;
    let result = ExternTable::read_metered(&malformed, |_| {
        calls += 1;
        if calls == 4 {
            Err("before malformed payload")
        } else {
            Ok(())
        }
    });
    assert_eq!(
        result,
        Err(ExternReadError::Budget("before malformed payload"))
    );
    assert_eq!(ExternTable::read(&malformed), Err(ExternError::Malformed));
    assert_eq!(
        ExternTable::read(&env).unwrap(),
        table,
        "failed reads do not poison a retry"
    );
}

#[test]
fn import_activation_and_full_journal_checkpoint_replay_preserve_exact_roots() {
    let base = environment();
    let env = crate::instances::imported::ImportActivation::new(base.clone())
        .register_extern(&n("A.call"), vec![standard("old")])
        .unwrap()
        .register_extern(&n("A.call"), vec![ExternEntry::Opaque, standard("new")])
        .unwrap()
        .finish()
        .unwrap();
    let limits = CheckpointLimits::new(10, 16_384);
    let epoch = ModuleEpoch::new("registry-test", "0000000000000000000000000000000000000000");
    let checkpoint = env
        .checkpoint_extension(
            &journal_name(),
            None,
            limits,
            ProofBudget::UNBOUNDED,
            &epoch,
            None,
        )
        .into_complete()
        .unwrap()
        .unwrap();
    let restored = base
        .register_extension(descriptor())
        .unwrap()
        .apply_extension_checkpoint(&checkpoint, limits, ProofBudget::UNBOUNDED, None)
        .into_complete()
        .unwrap()
        .unwrap();
    assert_eq!(env, restored);
    assert_eq!(
        env.logical_root(&KVMap::new()),
        restored.logical_root(&KVMap::new())
    );
    assert_eq!(
        ExternTable::read(&env).unwrap(),
        ExternTable::read(&restored).unwrap()
    );
}
