//! Change only the declared safety of independently built inductive fixtures.
use fln_checker::environment::{ConstantDeclaration, ConstantEntry, ConstantSafety};

pub fn retag(entry: &ConstantEntry, safety: ConstantSafety) -> ConstantEntry {
    let d = entry.declaration();
    let levels = d.level_parameters().to_vec();
    let ty = d.type_().clone();
    let declaration = if let Some(m) = d.inductive_metadata() {
        ConstantDeclaration::inductive(levels, ty, safety, m.clone())
    } else if let Some(m) = d.constructor_metadata() {
        ConstantDeclaration::constructor(levels, ty, safety, m.clone())
    } else if let Some(m) = d.recursor_metadata() {
        ConstantDeclaration::recursor(levels, ty, safety, m.clone())
    } else {
        panic!("expected an inductive-block member")
    };
    ConstantEntry::new(entry.name().clone(), declaration)
}

pub fn unsafe_rows(entries: &[ConstantEntry]) -> Vec<ConstantEntry> {
    entries
        .iter()
        .map(|e| retag(e, ConstantSafety::Unsafe))
        .collect()
}
