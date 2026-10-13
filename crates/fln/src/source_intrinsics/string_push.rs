//! Exact post-admission contract for the pinned String.push extern.
//!
//! Char remains its logical constructor. Runtime preparation projects its
//! existing code point through the checked UInt32/BitVec/Fin fields and calls
//! the bounded native String operation; it never manufactures a Char or proof.

use super::*;

mod model;

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
