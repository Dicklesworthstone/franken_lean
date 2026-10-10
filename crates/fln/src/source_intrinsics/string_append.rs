//! Execute the pinned public string append through its explicit native extern.
//!
//! The logical definition constructs `String.ofByteArray` from the concrete
//! ByteArray append dictionary and a UTF-8 proof. Strings use a dedicated VM
//! representation, so unfolding that body is not a representation conversion.
//! `dependencies.txt` binds its complete transitive type/body/recursor-rule and
//! constructor/mutual-membership closure, decoded from SUITE.lock's artifacts.
//! This includes both append dictionaries, List recursion, the String and byte
//! layouts, and the proposition which justifies erasing the validity proof.
//! Every digest binds the complete ConstantInfo, including safety and metadata.
//! These comparison data are never installed or used to admit declarations.
//! Runtime replacement resolution keeps priority over this recognizer. Once
//! the root's native extern is selected, its logical helper calls do not run;
//! helper replacement journals therefore select no execution on this path.

use super::*;

const DEPENDENCIES: &str = include_str!("string_append/dependencies.txt");

fn name(label: &str) -> Name {
    Name::from_components(label.split('.'))
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
                    .expect("fixed String.append dependency numeric component"),
            )
        } else {
            unreachable!("fixed String.append dependency component encoding")
        };
    }
    Ok(result)
}

pub(crate) fn imported_string_append_matches(
    environment: &Environment,
    requested: &Name,
    externs: &mut Option<fln_elab::externs::ExternTable>,
    visited: &mut usize,
    limits: IngressLimits,
) -> Result<bool, IngressError> {
    if requested != &name("String.append") {
        return Ok(false);
    }
    if DEPENDENCIES.trim().is_empty() {
        return Err(IngressError::UnsupportedNode {
            kind: "imported String.append requires its exact dependency inventory",
        });
    }
    if !extern_attribute_matches(environment, requested, true, externs, visited, limits)? {
        return Ok(false);
    }
    for line in DEPENDENCIES.lines() {
        charge_catalog_node(visited, limits)?;
        let (encoded, digest) = line
            .split_once('\t')
            .expect("fixed String.append dependency row");
        let dependency = dependency_name(encoded, visited, limits)?;
        if environment
            .entry(&dependency)
            .is_none_or(|entry| entry.digest().to_hex() != digest)
        {
            return Err(IngressError::UnsupportedNode {
                kind: "imported String.append dependency differs from the exact pinned model",
            });
        }
        // Declaration digests do not bind extension journals. A conflicting
        // explicit helper extern must not inherit this native contract.
        check_selected_extern_attribute(environment, &dependency, externs, visited, limits)?;
    }
    Ok(true)
}

#[cfg(test)]
mod tests;
