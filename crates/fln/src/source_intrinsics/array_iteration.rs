//! Authorize only the pin's explicit Array traversal replacement.
//!
//! Constant digests bind the complete safe/unsafe traversal models, data
//! families and computational dependencies. Extension journals are checked
//! separately: a new extern, replacement or initializer can change execution
//! without changing any ConstantInfo digest.
use super::*;

const DEPENDENCIES: &str = include_str!("array_iteration/dependencies.txt");

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
                    .expect("fixed Array iteration numeric name component"),
            )
        } else {
            unreachable!("fixed Array iteration name component encoding")
        };
    }
    Ok(result)
}

pub(crate) fn matches(
    environment: &Environment,
    implementations: &fln_elab::implemented_by::ImplementedByTable,
    initializers: Option<&BTreeSet<Name>>,
    externs: &mut Option<fln_elab::externs::ExternTable>,
    visited: &mut usize,
    limits: IngressLimits,
) -> Result<(), IngressError> {
    if DEPENDENCIES.trim().is_empty() {
        return Err(IngressError::UnsupportedNode {
            kind: "Array iteration requires its exact dependency inventory",
        });
    }
    for line in DEPENDENCIES.lines() {
        charge_catalog_node(visited, limits)?;
        // name, ConstantInfo digest, selected implemented_by target (or -),
        // whether a native extern is present, and the selected recursive
        // companion (or -). Presence is authority even when a name was absent.
        let mut columns = line.split('\t');
        let encoded = columns.next().expect("fixed Array dependency name");
        let digest = columns.next().expect("fixed Array dependency digest");
        let implementation = columns.next().expect("fixed Array dependency replacement");
        let native = columns.next().expect("fixed Array dependency extern");
        let companion = columns.next().expect("fixed Array dependency companion");
        assert!(columns.next().is_none(), "fixed Array dependency row width");
        let dependency = dependency_name(encoded, visited, limits)?;
        if environment
            .entry(&dependency)
            .is_none_or(|entry| entry.digest().to_hex() != digest)
        {
            return Err(IngressError::UnsupportedNode {
                kind: "Array iteration dependency differs from the exact pinned model",
            });
        }
        if initializers.is_some_and(|names| names.contains(&dependency)) {
            return Err(IngressError::UnsupportedNode {
                kind: "Array iteration dependency requires runtime initialization",
            });
        }
        let selected = if implementation == "-" {
            None
        } else {
            Some(dependency_name(implementation, visited, limits)?)
        };
        if implementations.get(&dependency) != selected.as_ref() {
            return Err(IngressError::UnsupportedNode {
                kind: "Array iteration dependency has a different selected implementation",
            });
        }
        let has_logical_body = match environment.find(&dependency) {
            Some(ConstantInfo::Defn(value)) => value.safety == DefinitionSafety::Safe,
            Some(ConstantInfo::Opaque(value)) => !value.is_unsafe,
            _ => false,
        };
        let actual_companion = if has_logical_body {
            let candidate = Name::str(dependency.clone(), "_unsafe_rec");
            environment.contains(&candidate).then_some(candidate)
        } else {
            None
        };
        let expected_companion = if companion == "-" {
            None
        } else {
            Some(dependency_name(companion, visited, limits)?)
        };
        if actual_companion != expected_companion {
            return Err(IngressError::UnsupportedNode {
                kind: "Array iteration dependency has a different recursive companion",
            });
        }
        check_selected_extern_attribute(environment, &dependency, externs, visited, limits)?;
        let has_extern = externs
            .as_ref()
            .is_some_and(|table| table.get(&dependency).is_some());
        if has_extern != (native == "extern") {
            return Err(IngressError::UnsupportedNode {
                kind: "Array iteration dependency has a different selected extern",
            });
        }
        assert!(
            matches!(native, "-" | "extern"),
            "fixed Array dependency extern flag",
        );
    }
    Ok(())
}
