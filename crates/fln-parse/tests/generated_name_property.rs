//! Stable generated-name properties on logical expansion paths.

#![forbid(unsafe_code)]

use fln_core::name::Name;
use fln_syntax::hygiene::{ExpansionOrigin, ExpansionPath};
use std::collections::BTreeSet;

fn origin(command_ordinal: u64) -> ExpansionOrigin {
    ExpansionOrigin::new(
        Name::from_components(["Main", "GeneratedNames"]),
        command_ordinal,
    )
}

fn paths() -> Vec<ExpansionPath> {
    let mut paths = Vec::new();
    for command in 0..4 {
        for invocation in 0..5 {
            for quotation in 0..3 {
                for local in 0..7 {
                    paths.push(
                        ExpansionPath::root(origin(command), invocation)
                            .nested_quotation(quotation)
                            .with_local_ordinal(local),
                    );
                }
            }
        }
    }
    paths
}

fn bases() -> Vec<Name> {
    vec![
        Name::anonymous(),
        Name::from_components(["x"]),
        Name::from_components(["_base", "_invocations", "_local"]),
        Name::num(Name::from_components(["x"]), 7),
        Name::num_overflowing(Name::from_components(["x"]), u64::MAX),
    ]
}

#[test]
fn every_logical_coordinate_has_a_distinct_structural_name() {
    let mut names = BTreeSet::new();
    let mut count = 0usize;
    for base in bases() {
        for path in paths() {
            count += 1;
            assert!(
                names.insert(path.generated_name(&base)),
                "two distinct base/path pairs collapsed"
            );
        }
    }
    assert_eq!(names.len(), count);
}

#[test]
fn repeated_derivation_is_byte_identical_and_has_no_mutable_generator_state() {
    let path = ExpansionPath::root(origin(9), 4)
        .nested_invocation(3)
        .nested_quotation(8)
        .with_local_ordinal(12);
    let base = Name::from_components(["binder"]);
    let expected = path.generated_name(&base);
    for _ in 0..1_000 {
        assert_eq!(path.generated_name(&base), expected);
        assert_eq!(path.canonical(), path.canonical());
    }
}

fn reduce_with_workers(worker_count: usize) -> Vec<(usize, Name)> {
    let work = paths();
    let mut handles = Vec::new();
    for worker in 0..worker_count {
        let local_work = work.clone();
        handles.push(std::thread::spawn(move || {
            local_work
                .into_iter()
                .enumerate()
                .filter(|(index, _)| index % worker_count == worker)
                .map(|(index, path)| {
                    (
                        index,
                        path.generated_name(&Name::from_components(["threaded"])),
                    )
                })
                .collect::<Vec<_>>()
        }));
    }
    let mut reduced = handles
        .into_iter()
        .flat_map(|handle| handle.join().expect("worker completes"))
        .collect::<Vec<_>>();
    reduced.sort_by_key(|(index, _)| *index);
    reduced
}

#[test]
fn productive_one_eight_and_thirty_two_worker_reductions_are_identical() {
    let one = reduce_with_workers(1);
    assert!(!one.is_empty(), "the thread matrix must do productive work");
    assert_eq!(reduce_with_workers(8), one);
    assert_eq!(reduce_with_workers(32), one);
}

fn mutant_omitting_quotation_and_local(path: &ExpansionPath, base: &Name) -> Name {
    let mut name = Name::from_components(["_uniq", "_mutant"]);
    name = name.append_core(base);
    name = name.append_core(&path.origin().module);
    for invocation in path.invocations() {
        name = Name::num(name, *invocation);
    }
    name
}

#[test]
fn quotation_and_local_ordinal_omission_mutants_are_killed() {
    let base = Name::from_components(["x"]);
    let first = ExpansionPath::root(origin(1), 2)
        .nested_quotation(3)
        .with_local_ordinal(4);
    let quotation_changed = ExpansionPath::root(origin(1), 2)
        .nested_quotation(9)
        .with_local_ordinal(4);
    let local_changed = ExpansionPath::root(origin(1), 2)
        .nested_quotation(3)
        .with_local_ordinal(10);

    assert_ne!(
        first.generated_name(&base),
        quotation_changed.generated_name(&base)
    );
    assert_ne!(
        first.generated_name(&base),
        local_changed.generated_name(&base)
    );
    assert_eq!(
        mutant_omitting_quotation_and_local(&first, &base),
        mutant_omitting_quotation_and_local(&quotation_changed, &base)
    );
    assert_eq!(
        mutant_omitting_quotation_and_local(&first, &base),
        mutant_omitting_quotation_and_local(&local_changed, &base)
    );
}
