//! The source seed's constant names, without the `protected` marks: the first half of
//! `scripts/extract/gen_seed_protected.sh` (bead `fln-8xz8`). With `FLN_SEED_NAMES_OUT`
//! set, the names are written there in byte order, one per line, for the pinned `lean`
//! to be asked about. Built unmarked, so a seed that gained or lost constants since the
//! table was generated can still be listed.
use crate::{Budget, EngineAdmissionLimits, EngineBuilder};

#[test]
fn seed_constant_names_are_unique_and_dumpable() {
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let engine = EngineBuilder::new()
        .build_unmarked_source_seed(limits)
        .expect("the source seed builds")
        .into_complete()
        .expect("the source seed completes");
    let mut spelled = Vec::new();
    let mut unspellable = Vec::new();
    for (name, _) in engine.environment.constants() {
        match fln_elab::seed::protected::table_spelling(name) {
            Some(text) => spelled.push(text),
            None => unspellable.push(name.to_display_string()),
        }
    }
    assert_eq!(
        unspellable,
        Vec::<String>::new(),
        "seed constants with no table spelling that reads back as themselves"
    );
    spelled.sort();
    let count = spelled.len();
    spelled.dedup();
    assert_eq!(spelled.len(), count, "two seed constants share a spelling");
    assert!(
        spelled.iter().any(|name| name == "Nat.add"),
        "the seed admits Nat.add"
    );
    if let Some(path) = std::env::var_os("FLN_SEED_NAMES_OUT") {
        let mut text = spelled.join("\n");
        text.push('\n');
        std::fs::write(&path, text).expect("write the seed names");
    }
}
