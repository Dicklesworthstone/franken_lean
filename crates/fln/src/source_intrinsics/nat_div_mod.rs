//! Native division and remainder for the exact imported logical models.
//!
//! The pin defines division by recursive subtraction and gives both operations
//! efficient externs. Running that logical division exhausts ordinary runtime
//! depth even while encoding a four-byte Unicode character. These inventories
//! bind each root's complete ConstantInfo dependency closure from the pinned
//! Prelude artifacts, including fuel proofs, dictionaries, helper bodies,
//! recursor rules, constructors, safety and borrowed-argument metadata.
//! Comparison data are never installed or used to admit source declarations.
//!
//! Only an actual canonical root extern selects this optimization. Explicit
//! foreign helper externs remain refusals. Source implemented_by resolution
//! occurs before this gate; once the canonical root extern is selected, the
//! logical helpers (and their replacement journals) do not execute.

use super::*;

const DIV_DEPENDENCIES: &str = include_str!("nat_div_mod/div_dependencies.txt");
const MOD_DEPENDENCIES: &str = include_str!("nat_div_mod/mod_dependencies.txt");

fn name(label: &str) -> Name {
    Name::from_components(label.split('.'))
}

fn inventory(requested: &Name) -> Option<&'static str> {
    if requested == &name("Nat.div") {
        Some(DIV_DEPENDENCIES)
    } else if requested == &name("Nat.mod") {
        Some(MOD_DEPENDENCIES)
    } else {
        None
    }
}

fn dependency_name(
    encoded: &str,
    visited: &mut usize,
    limits: IngressLimits,
) -> Result<Name, IngressError> {
    let mut result = Name::anonymous();
    for component in encoded.split('/') {
        charge_catalog_node(visited, limits)?;
        result = if let Some(text) = component.strip_prefix("s:") {
            Name::str(result, text)
        } else if let Some(number) = component.strip_prefix("n:") {
            Name::num(
                result,
                number
                    .parse()
                    .expect("fixed Nat division dependency numeric component"),
            )
        } else {
            unreachable!("fixed Nat division dependency component encoding")
        };
    }
    Ok(result)
}

pub(super) fn matches(
    environment: &Environment,
    requested: &Name,
    externs: &mut Option<fln_elab::externs::ExternTable>,
    visited: &mut usize,
    limits: IngressLimits,
) -> Result<bool, IngressError> {
    let Some(dependencies) = inventory(requested) else {
        return Ok(false);
    };
    if dependencies.trim().is_empty() {
        return Err(IngressError::UnsupportedNode {
            kind: "imported Nat division requires its exact dependency inventory",
        });
    }
    if !extern_attribute_matches(environment, requested, true, externs, visited, limits)? {
        return Ok(false);
    }
    for line in dependencies.lines() {
        charge_catalog_node(visited, limits)?;
        let (encoded, digest) = line
            .split_once('\t')
            .expect("fixed Nat division dependency row");
        let dependency = dependency_name(encoded, visited, limits)?;
        if environment
            .entry(&dependency)
            .is_none_or(|entry| entry.digest().to_hex() != digest)
        {
            return Err(IngressError::UnsupportedNode {
                kind: "imported Nat division dependency differs from the exact pinned model",
            });
        }
        // Extension journals are not part of the declaration digest. An
        // explicit conflicting helper extern cannot inherit a native contract.
        check_selected_extern_attribute(environment, &dependency, externs, visited, limits)?;
    }
    Ok(true)
}

#[cfg(test)]
mod tests;
