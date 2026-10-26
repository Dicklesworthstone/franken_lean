//! Exact post-admission contract for the pinned String.push extern.
//!
//! Char remains its logical constructor. Runtime preparation projects its
//! existing code point through the checked UInt32/BitVec/Fin fields and calls
//! the bounded native String operation; it never manufactures a Char or proof.

use super::*;

mod model;

const CHAR_OF_NAT_DEPENDENCIES: &str = include_str!("string_push/char_of_nat_dependencies.txt");

/// The same extracted five-column contract grammar binds constants and all
/// executable metadata. Share its metered validation with the Array adapters;
/// a character adapter receives no authority from the String.push contract.
pub(crate) fn char_of_nat_matches(
    environment: &Environment,
    implementations: &fln_elab::implemented_by::ImplementedByTable,
    initializers: Option<&BTreeSet<Name>>,
    externs: &mut Option<fln_elab::externs::ExternTable>,
    visited: &mut usize,
    limits: IngressLimits,
) -> Result<(), IngressError> {
    if !CHAR_OF_NAT_DEPENDENCIES
        .lines()
        .any(|line| line.starts_with("s:Char/s:ofNatAux\t"))
    {
        return Err(IngressError::UnsupportedNode {
            kind: "Char.ofNatAux requires its exact dependency inventory",
        });
    }
    super::array_iteration::matches_inventory(
        CHAR_OF_NAT_DEPENDENCIES,
        environment,
        implementations,
        initializers,
        externs,
        visited,
        limits,
    )
    .map_err(|error| match error {
        IngressError::UnsupportedNode { .. } => IngressError::UnsupportedNode {
            kind: "Char.ofNatAux differs from its complete pinned model or execution metadata",
        },
        error => error,
    })
}

pub(crate) fn source_name() -> Name {
    Name::from_components(["String", "push"])
}

fn models() -> Vec<ConstantInfo> {
    let mut models = model::declarations();
    models.extend(string_internal::scalar_records());
    models.extend(string_length::character_records());
    // This shared function returns arithmetic comparison data only. It does
    // not inspect an IO environment, require stdout, or authorize any effect.
    models.extend(super::io::stdout::word_bound_models());
    models
}

#[cfg(test)]
pub(crate) fn assert_pin_models(environment: &Environment) {
    let limits = IngressLimits::default();
    let mut visited = 0;
    let mut comparison = Comparison {
        visited: &mut visited,
        limits,
    };
    assert!(
        comparison
            .declaration(environment, fln_elab::seed::bool_seed_declaration())
            .unwrap(),
        "String.push requires the exact proof-erasure Boolean family",
    );
    for expected in models() {
        assert!(
            comparison.constant(environment, expected.clone()).unwrap(),
            "String.push model {} differs from the actual pinned declaration",
            expected.name().to_display_string(),
        );
    }
}

pub(crate) fn contract_matches(
    environment: &Environment,
    requested: &Name,
    externs: &mut Option<fln_elab::externs::ExternTable>,
    visited: &mut usize,
    limits: IngressLimits,
) -> Result<bool, IngressError> {
    if requested != &source_name() {
        return Ok(false);
    }
    // The logical definition alone grants no native implementation. Require
    // the genuine standard all-backend extern entry for this exact name.
    if !extern_attribute_matches(environment, requested, true, externs, visited, limits)? {
        return Ok(false);
    }
    let unsupported = || IngressError::UnsupportedNode {
        kind: "native String.push does not match its complete checked contract",
    };
    let models = models();
    let mut comparison = Comparison { visited, limits };
    if !comparison.declaration(environment, fln_elab::seed::bool_seed_declaration())? {
        return Err(unsupported());
    }
    for expected in &models {
        if !comparison.constant(environment, expected.clone())? {
            return Err(unsupported());
        }
    }
    // Exact helper bodies do not erase a conflicting declared implementation.
    // Unrelated extern entries, including IO.getStdout, are not selected here.
    for expected in models {
        check_selected_extern_attribute(environment, expected.name(), externs, visited, limits)?;
    }
    Ok(true)
}
