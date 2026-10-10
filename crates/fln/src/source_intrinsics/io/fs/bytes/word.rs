//! Pure native words retain their complete checked logical model without
//! depending on an IO world or on byte-buffer packing.
//!
//! The base inventory is the complete type/body/recursor and constructor/mutual
//! membership closure of WORD_HELPERS, decoded from SUITE.lock's artifacts.
//! The printing inventory adds the rest of USize.repr's closure, including
//! its decimal conversion, String model, and UTF-8 proof. Comparison data are
//! never installed as declarations and never grant admission.
use super::*;

const DEPENDENCIES: &str = include_str!("word/dependencies.txt");
const REPR_DEPENDENCIES: &str = include_str!("word/repr_dependencies.txt");
const PLATFORM_DEPENDENCIES: &str = include_str!("word/platform_dependencies.txt");
const WORD_HELPERS: [&str; 3] = ["USize.ofBitVec", "USize.ofNat", "USize.toNat"];

fn dependencies_match(
    environment: &Environment,
    inventory: &str,
    externs: &mut Option<fln_elab::externs::ExternTable>,
    visited: &mut usize,
    limits: IngressLimits,
) -> Result<(), IngressError> {
    if inventory.trim().is_empty() {
        return Err(IngressError::UnsupportedNode {
            kind: "pure word conversion requires its exact dependency inventory",
        });
    }
    for line in inventory.lines() {
        charge_catalog_node(visited, limits)?;
        let (encoded, digest) = line
            .split_once('\t')
            .expect("fixed pure word dependency row");
        let dependency = dependency_name(encoded, visited, limits)?;
        if environment
            .entry(&dependency)
            .is_none_or(|entry| entry.digest().to_hex() != digest)
        {
            return Err(IngressError::UnsupportedNode {
                kind: "pure word dependency differs from the exact pinned model",
            });
        }
        // Digests intentionally omit extension journals. An explicit foreign
        // helper extern cannot inherit the native model's selected contract.
        check_selected_extern_attribute(environment, &dependency, externs, visited, limits)?;
    }
    Ok(())
}

pub(crate) fn word_matches(
    environment: &Environment,
    requested: &Name,
    externs: &mut Option<fln_elab::externs::ExternTable>,
    visited: &mut usize,
    limits: IngressLimits,
) -> Result<bool, IngressError> {
    let platform = requested == &name("System.Platform.getNumBits");
    if !platform
        && ![name("USize.ofNat"), name("USize.toNat"), name("USize.repr")].contains(requested)
    {
        return Ok(false);
    }
    if !extern_attribute_matches(environment, requested, true, externs, visited, limits)? {
        return Ok(false);
    }
    if platform {
        // This opaque producer belongs to Prelude itself. Its own complete
        // model establishes Unit, Subtype and the 32-or-64-bit proposition;
        // it needs neither a file world nor the later USize conversion externs.
        dependencies_match(environment, PLATFORM_DEPENDENCIES, externs, visited, limits)?;
        return Ok(true);
    }
    dependencies_match(environment, DEPENDENCIES, externs, visited, limits)?;
    // The shared layout may later serve any word conversion. Establish all
    // three native helper entries before allowing that layout to be cached.
    for helper in WORD_HELPERS {
        if !extern_attribute_matches(environment, &name(helper), true, externs, visited, limits)? {
            return Err(IngressError::UnsupportedNode {
                kind: "pure word conversion requires each native helper extern",
            });
        }
    }
    if requested == &name("USize.repr") {
        // The caller keeps a separate printing-validation bit: constructing
        // the basic word cache cannot skip this root's metadata or model.
        dependencies_match(environment, REPR_DEPENDENCIES, externs, visited, limits)?;
    }
    Ok(true)
}

#[cfg(test)]
mod tests;
