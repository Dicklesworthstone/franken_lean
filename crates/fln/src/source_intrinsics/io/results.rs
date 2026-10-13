//! Shared, complete logical data contract for native IO results.
//!
//! Matching these models supplies no executable primitive authority. Each
//! operation independently checks its own genuine imported extern entry.

use super::*;

pub(crate) use stdout::{ErrorFields, error_cases};

/// The finite-word data contract shared by native error codes and a checked
/// `main : IO UInt32` result. This selects no IO operation or native conversion.
/// Main observes the existing logical fields, so unrelated error constructors
/// and their Boolean selection machinery are not prerequisites.
pub(crate) fn word_contract_matches(
    environment: &Environment,
    externs: &mut Option<fln_elab::externs::ExternTable>,
    visited: &mut usize,
    limits: IngressLimits,
) -> Result<bool, IngressError> {
    let names = [
        "UInt32",
        "UInt32.ofBitVec",
        "BitVec",
        "BitVec.ofFin",
        "Fin",
        "Fin.mk",
    ]
    .map(|label| Name::from_components(label.split('.')));
    let mut models: Vec<_> = stdout::result_models()
        .into_iter()
        .filter(|model| names.contains(model.name()))
        .collect();
    if models.len() != names.len() {
        return Ok(false);
    }
    models.extend(stdout::word_bound_models());
    let mut comparison = Comparison { visited, limits };
    for expected in &models {
        if !comparison.constant(environment, expected.clone())? {
            return Ok(false);
        }
    }
    for expected in models {
        check_selected_extern_attribute(environment, expected.name(), externs, visited, limits)?;
    }
    Ok(true)
}

pub(crate) fn contract_matches(
    environment: &Environment,
    externs: &mut Option<fln_elab::externs::ExternTable>,
    visited: &mut usize,
    limits: IngressLimits,
) -> Result<bool, IngressError> {
    if !io_world_contract_matches(environment, externs, visited, limits)? {
        return Ok(false);
    }
    // The u32 payload is in range only under these exact Nat literal,
    // exponentiation and order dictionaries. Match them before erasure.
    let mut models = stdout::result_models();
    models.extend(stdout::word_bound_models());
    // Generated error selection executes Nat.beq. A same-typed replacement
    // must not relabel a native error, so bind its complete implementation
    // closure and every selected extern before authorizing any IO primitive.
    for declaration in
        fln_elab::seed::imported_nat_intrinsic_model_declarations(&Name::from_components([
            "Nat", "beq",
        ]))
        .expect("the complete pinned Nat.beq model")
    {
        match declaration {
            Declaration::Defn(value) => models.push(ConstantInfo::Defn(value)),
            Declaration::Inductive(block) => {
                models.extend(block.types.into_iter().map(ConstantInfo::Induct));
                models.extend(block.ctors.into_iter().map(ConstantInfo::Ctor));
                models.extend(block.recursors.into_iter().map(ConstantInfo::Rec));
            }
            _ => unreachable!("fixed natural-number equality dependency models"),
        }
    }
    let mut comparison = Comparison { visited, limits };
    if !comparison.declaration(environment, fln_elab::seed::bool_seed_declaration())? {
        return Ok(false);
    }
    for expected in &models {
        if !comparison.constant(environment, expected.clone())? {
            return Ok(false);
        }
    }
    for expected in models {
        check_selected_extern_attribute(environment, expected.name(), externs, visited, limits)?;
    }
    Ok(true)
}
