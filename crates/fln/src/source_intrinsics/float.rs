//! Native Float operations and scientific literals over the actual Init model.
//!
//! The inventory is the complete type/body/constructor/recursor dependency
//! closure of the supported operations, decoded from the pinned artifacts.
//! It is comparison data only: it installs no declaration and grants no
//! admission authority. Public UInt records retain their logical layout.
use super::*;
use fln_elab::implemented_by::{ImplementedByError, ImplementedByReadError, ImplementedByTable};

const DEPENDENCIES: &str = include_str!("float/dependencies.txt");

const FLOAT_OPERATIONS: &[&str] = &[
    "ofBits", "toBits", "add", "sub", "mul", "div", "neg", "abs", "sqrt", "ceil", "floor", "round",
    "sin", "cos", "tan", "asin", "acos", "atan", "sinh", "cosh", "tanh", "asinh", "acosh", "atanh",
    "exp", "exp2", "log", "log2", "log10", "cbrt", "pow", "atan2", "beq", "isNaN", "isFinite",
    "isInf", "toString", "toUInt32", "toUInt64",
];

fn name(label: &str) -> Name {
    Name::from_components(label.split('.'))
}

pub(crate) fn is_primitive(requested: &Name) -> bool {
    use fln_core::name::LeafView;
    let LeafView::Str(operation) = requested.leaf_view() else {
        return false;
    };
    let family = requested.parent();
    if family == name("Float") {
        FLOAT_OPERATIONS.contains(&operation) || operation == "toFloat32"
    } else if family == name("Float32") {
        FLOAT_OPERATIONS.contains(&operation) || operation == "toFloat"
    } else if family == name("UInt32") || family == name("UInt64") {
        matches!(operation, "ofNat" | "toNat" | "toFloat" | "toFloat32")
    } else {
        false
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
                number.parse().expect("fixed Float numeric name component"),
            )
        } else {
            unreachable!("fixed Float dependency name encoding")
        };
    }
    Ok(result)
}

pub(crate) fn matches(
    environment: &Environment,
    externs: &mut Option<fln_elab::externs::ExternTable>,
    implementations: &mut Option<ImplementedByTable>,
    visited: &mut usize,
    limits: IngressLimits,
) -> Result<bool, IngressError> {
    if DEPENDENCIES.trim().is_empty() {
        return Err(IngressError::UnsupportedNode {
            kind: "Float dependency inventory is empty",
        });
    }
    // The separate seed remains a bounded test dialect. It does not establish
    // the real FloatSpec representation or the imported word contracts.
    if !matches!(
        environment.find(&name("Float.ofScientific")),
        Some(ConstantInfo::Opaque(_))
    ) {
        return Ok(false);
    }
    if implementations.is_none() {
        let table = ImplementedByTable::read_metered(environment, |amount| {
            let observed = visited.saturating_add(amount);
            if observed > limits.max_nodes {
                return Err(IngressError::ResourceLimit {
                    resource: IngressResource::Nodes,
                    limit: limits.max_nodes,
                    observed,
                });
            }
            *visited = observed;
            Ok(())
        })
        .map_err(|error| match error {
            ImplementedByReadError::Budget(error) => error,
            ImplementedByReadError::Registry(ImplementedByError::Limit) => {
                IngressError::MetadataResourceExhausted {
                    kind: "Float implemented_by journal capacity or validation",
                }
            }
            ImplementedByReadError::Registry(_) => IngressError::UnsupportedNode {
                kind: "invalid Float implemented_by journal",
            },
        })?;
        *implementations = Some(table);
    }
    let implementations = implementations
        .as_ref()
        .expect("validated implementation table");
    for line in DEPENDENCIES.lines() {
        charge_catalog_node(visited, limits)?;
        let (encoded, digest) = line.split_once('\t').expect("fixed Float dependency row");
        let dependency = dependency_name(encoded, visited, limits)?;
        if environment
            .entry(&dependency)
            .is_none_or(|entry| entry.digest().to_hex() != digest)
        {
            return Err(IngressError::UnsupportedNode {
                kind: "Float dependency differs from the exact pinned model",
            });
        }
        // Constant digests omit compiler attributes. A changed executable
        // dependency cannot silently inherit this scientific algorithm.
        if implementations.get(&dependency).is_some() {
            return Err(IngressError::UnsupportedNode {
                kind: "Float model dependency selects an executable replacement",
            });
        }
        check_selected_extern_attribute(environment, &dependency, externs, visited, limits)?;
        // Constant scientific conversion also executes these native scaling
        // helpers. Their absence must not authorize the host bit algorithm,
        // even though dynamic scaleB calls are outside this bridge.
        let requires_extern = is_primitive(&dependency)
            || dependency == name("Float.scaleB")
            || dependency == name("Float32.scaleB");
        if requires_extern
            && !extern_attribute_matches(environment, &dependency, true, externs, visited, limits)?
        {
            return Err(IngressError::UnsupportedNode {
                kind: "Float primitive requires its selected native extern",
            });
        }
    }
    Ok(true)
}

#[cfg(test)]
mod tests;
