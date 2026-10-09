//! Exact contracts for the bounded native stdout stream bridge.
//!
//! The native stream stays in a compiler-private carrier. These complete
//! declarations authorize its conversion to ordinary checked Stream fields;
//! no opaque default or replacement println body supplies executable code.

use super::*;

mod bounds;
mod model;

pub(crate) use model::{ErrorFields, error_cases};

pub(crate) fn source_name() -> Name {
    Name::from_components(["IO", "getStdout"])
}

pub(in crate::source_intrinsics) fn word_bound_models() -> Vec<ConstantInfo> {
    let mut constants = bounds::declarations();
    let power = Name::from_components(["Nat", "pow"]);
    for declaration in fln_elab::seed::imported_nat_intrinsic_model_declarations(&power)
        .expect("the complete pinned Nat.pow model")
    {
        match declaration {
            Declaration::Defn(value) => constants.push(ConstantInfo::Defn(value)),
            Declaration::Inductive(block) => {
                constants.extend(block.types.into_iter().map(ConstantInfo::Induct));
                constants.extend(block.ctors.into_iter().map(ConstantInfo::Ctor));
                constants.extend(block.recursors.into_iter().map(ConstantInfo::Rec));
            }
            _ => unreachable!("fixed natural-number power dependency models"),
        }
    }
    constants
}

pub(in crate::source_intrinsics) fn result_models() -> Vec<ConstantInfo> {
    model::result_declarations()
}

#[cfg(test)]
pub(crate) fn assert_pin_models(environment: &Environment) {
    for expected in model::declarations()
        .into_iter()
        .chain(result_models())
        .chain(word_bound_models())
    {
        assert!(
            Comparison {
                visited: &mut 0,
                limits: IngressLimits::default(),
            }
            .constant(environment, expected.clone())
            .unwrap(),
            "stdout model {} differs from the actual pinned declaration",
            expected.name().to_display_string(),
        );
    }
}

pub(crate) fn contract_matches(
    environment: &Environment,
    externs: &mut Option<fln_elab::externs::ExternTable>,
    visited: &mut usize,
    limits: IngressLimits,
) -> Result<bool, IngressError> {
    if !extern_attribute_matches(environment, &source_name(), true, externs, visited, limits)? {
        return Ok(false);
    }
    if !results::contract_matches(environment, externs, visited, limits)? {
        return Err(IngressError::UnsupportedNode {
            kind: "native stdout requires the complete checked IO result models",
        });
    }
    let models = model::declarations();
    let mut comparison = Comparison { visited, limits };
    for expected in &models {
        if !comparison.constant(environment, expected.clone())? {
            return Err(IngressError::UnsupportedNode {
                kind: "native stdout does not match its complete checked layout contract",
            });
        }
    }
    for expected in models {
        check_selected_extern_attribute(environment, expected.name(), externs, visited, limits)?;
    }
    Ok(true)
}
