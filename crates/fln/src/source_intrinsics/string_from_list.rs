//! Exact post-admission authority for the pinned String.ofList operation.
//!
//! The logical model encodes List Char into a proof-carrying ByteArray before
//! constructing String. Its genuine native extern instead traverses the
//! character list. The fixed inventory binds the complete transitive type,
//! value, proof, constructor membership and recursor-rule closure from the pin.
//! These comparison data never admit or install declarations. Every selected
//! extern journal is checked independently of declaration digests.

use super::*;

const DEPENDENCIES: &str = include_str!("string_from_list/dependencies.txt");

#[cfg(test)]
pub(crate) fn dependency_inventory() -> &'static str {
    DEPENDENCIES
}

pub(crate) fn source_name() -> Name {
    Name::from_components(["String", "ofList"])
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
                    .expect("fixed String.ofList dependency numeric component"),
            )
        } else {
            unreachable!("fixed String.ofList dependency component encoding")
        };
    }
    Ok(result)
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
    if !extern_attribute_matches(environment, requested, true, externs, visited, limits)? {
        return Ok(false);
    }
    let Some(row) = fln_vm::extern_table_generated::EXTERN_ROWS
        .iter()
        .find(|row| row.name == "String.ofList")
    else {
        return Err(IngressError::UnsupportedNode {
            kind: "String.ofList requires its generated native row",
        });
    };
    if row.id != "extern:String.ofList"
        || row.kind != "defn"
        || row.module != "Init.Prelude"
        || row.levels != 0
        || row.arity != 1
        || row.effect != "pure"
        || row.safety != "safe"
        || row.symbol != "lean_string_mk"
        || row.ownership != "abi((cs: owned_arg) -> owned_res)"
    {
        return Err(IngressError::UnsupportedNode {
            kind: "String.ofList generated native contract differs from the pin",
        });
    }
    let mut root_seen = false;
    for line in DEPENDENCIES.lines() {
        charge_catalog_node(visited, limits)?;
        let (encoded, digest) = line
            .split_once('\t')
            .expect("fixed String.ofList dependency row");
        let dependency = dependency_name(encoded, visited, limits)?;
        root_seen |= dependency == *requested;
        if environment
            .entry(&dependency)
            .is_none_or(|entry| entry.digest().to_hex() != digest)
        {
            return Err(IngressError::UnsupportedNode {
                kind: "String.ofList dependency differs from its exact pinned contract",
            });
        }
        check_selected_extern_attribute(environment, &dependency, externs, visited, limits)?;
    }
    if !root_seen {
        return Err(IngressError::UnsupportedNode {
            kind: "String.ofList requires its complete dependency inventory",
        });
    }
    Ok(true)
}
