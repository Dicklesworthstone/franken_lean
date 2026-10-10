//! Convert the actual String constructor's logical ByteArray through its
//! selected native UTF-8 extern. The complete constant inventory binds both
//! the validity proposition and the pure helpers used to pack logical bytes.
//! It contains no IO contracts and grants no module-admission authority.
use super::*;

const DEPENDENCIES: &str = include_str!("string_bytes/dependencies.txt");
const HELPERS: [&str; 4] = [
    "String.ofByteArray",
    "ByteArray.emptyWithCapacity",
    "ByteArray.push",
    "UInt8.ofBitVec",
];

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
                    .expect("fixed String byte dependency numeric component"),
            )
        } else {
            unreachable!("fixed String byte dependency component encoding")
        };
    }
    Ok(result)
}

pub(crate) fn matches(
    environment: &Environment,
    requested: &Name,
    externs: &mut Option<fln_elab::externs::ExternTable>,
    visited: &mut usize,
    limits: IngressLimits,
) -> Result<bool, IngressError> {
    if requested != &name("String.ofByteArray") {
        return Ok(false);
    }
    if !extern_attribute_matches(environment, requested, true, externs, visited, limits)? {
        return Ok(false);
    }
    if DEPENDENCIES.trim().is_empty() {
        return Err(IngressError::UnsupportedNode {
            kind: "String byte conversion requires its exact dependency inventory",
        });
    }
    for line in DEPENDENCIES.lines() {
        charge_catalog_node(visited, limits)?;
        let (encoded, digest) = line
            .split_once('\t')
            .expect("fixed String byte dependency row");
        let dependency = dependency_name(encoded, visited, limits)?;
        if environment
            .entry(&dependency)
            .is_none_or(|entry| entry.digest().to_hex() != digest)
        {
            return Err(IngressError::UnsupportedNode {
                kind: "String byte dependency differs from the exact pinned model",
            });
        }
        // ConstantInfo digests do not include extension journals. Every
        // explicit dependency extern must independently retain its contract.
        check_selected_extern_attribute(environment, &dependency, externs, visited, limits)?;
    }
    for helper in HELPERS {
        if !extern_attribute_matches(environment, &name(helper), true, externs, visited, limits)? {
            return Err(IngressError::UnsupportedNode {
                kind: "String byte conversion requires each selected native helper",
            });
        }
    }
    Ok(true)
}

#[cfg(test)]
mod tests;
