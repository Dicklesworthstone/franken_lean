//! Exact authority for the two native Array observers used by readDir.
//!
//! The existing pin-derived byte inventory contains the complete closure of
//! these helpers. Follow only this subset, validating each declaration before
//! following its type/body/rules/membership. Unrelated byte/word helpers and
//! their extern registrations are not prerequisites for directory execution.
use super::*;
use std::collections::{HashMap, HashSet};

const INVENTORY: &str = include_str!("bytes/dependencies.txt");
pub(crate) const HELPERS: [&str; 2] = ["Array.size", "Array.getInternal"];

fn push<T>(
    values: &mut Vec<T>,
    value: T,
    visited: &mut usize,
    limits: IngressLimits,
) -> Result<(), IngressError> {
    charge_catalog_node(visited, limits)?;
    values
        .try_reserve(1)
        .map_err(|_| IngressError::AllocationFailure {
            resource: IngressResource::ProgramTables,
            requested: values.len().saturating_add(1),
        })?;
    values.push(value);
    Ok(())
}

pub(super) fn contract_matches(
    environment: &Environment,
    externs: &mut Option<fln_elab::externs::ExternTable>,
    visited: &mut usize,
    limits: IngressLimits,
) -> Result<(), IngressError> {
    let refused = || IngressError::UnsupportedNode {
        kind: "directory read requires the complete checked native Array helper dependencies",
    };
    let mut expected = HashMap::new();
    for line in INVENTORY.lines() {
        let (encoded, digest) = line.split_once('\t').expect("fixed Array dependency row");
        let mut name = Name::anonymous();
        for component in encoded.split('/') {
            charge_catalog_node(visited, limits)?;
            name = if let Some(text) = component.strip_prefix("s:") {
                Name::str(name, text)
            } else if let Some(number) = component.strip_prefix("n:") {
                Name::num(name, number.parse().expect("fixed numeric name component"))
            } else {
                unreachable!("fixed dependency component encoding")
            };
        }
        expected
            .try_reserve(1)
            .map_err(|_| IngressError::AllocationFailure {
                resource: IngressResource::ProgramTables,
                requested: expected.len().saturating_add(1),
            })?;
        expected.insert(name, digest);
    }
    let mut pending = Vec::new();
    for helper in HELPERS {
        let name = Name::from_components(helper.split('.'));
        if !extern_attribute_matches(environment, &name, true, externs, visited, limits)? {
            return Err(refused());
        }
        push(&mut pending, name, visited, limits)?;
    }
    let mut complete = HashSet::new();
    while let Some(name) = pending.pop() {
        charge_catalog_node(visited, limits)?;
        if complete.contains(&name) {
            continue;
        }
        let digest = expected.get(&name).ok_or_else(refused)?;
        let entry = environment.entry(&name).ok_or_else(refused)?;
        if entry.digest().to_hex() != *digest {
            return Err(refused());
        }
        check_selected_extern_attribute(environment, &name, externs, visited, limits)?;
        complete
            .try_reserve(1)
            .map_err(|_| IngressError::AllocationFailure {
                resource: IngressResource::ProgramTables,
                requested: complete.len().saturating_add(1),
            })?;
        complete.insert(name.clone());
        let info = environment.find(&name).ok_or_else(refused)?;
        let mut expressions = Vec::new();
        push(
            &mut expressions,
            &info.constant_val().type_,
            visited,
            limits,
        )?;
        let all = match info {
            ConstantInfo::Defn(value) => {
                push(&mut expressions, &value.value, visited, limits)?;
                value.all.as_slice()
            }
            ConstantInfo::Opaque(value) => {
                push(&mut expressions, &value.value, visited, limits)?;
                value.all.as_slice()
            }
            ConstantInfo::Thm(value) => {
                push(&mut expressions, &value.value, visited, limits)?;
                value.all.as_slice()
            }
            ConstantInfo::Induct(value) => {
                for constructor in &value.ctors {
                    push(&mut pending, constructor.clone(), visited, limits)?;
                }
                value.all.as_slice()
            }
            ConstantInfo::Ctor(value) => {
                push(&mut pending, value.induct.clone(), visited, limits)?;
                &[]
            }
            ConstantInfo::Rec(value) => {
                for rule in &value.rules {
                    push(&mut expressions, &rule.rhs, visited, limits)?;
                    push(&mut pending, rule.ctor.clone(), visited, limits)?;
                }
                value.all.as_slice()
            }
            _ => &[],
        };
        for member in all {
            push(&mut pending, member.clone(), visited, limits)?;
        }
        while let Some(expression) = expressions.pop() {
            match expression.node() {
                ExprNode::Const { name, .. } => {
                    push(&mut pending, name.clone(), visited, limits)?;
                }
                ExprNode::App { f, a } => {
                    push(&mut expressions, f, visited, limits)?;
                    push(&mut expressions, a, visited, limits)?;
                }
                ExprNode::Lam {
                    binder_type, body, ..
                }
                | ExprNode::ForallE {
                    binder_type, body, ..
                } => {
                    push(&mut expressions, binder_type, visited, limits)?;
                    push(&mut expressions, body, visited, limits)?;
                }
                ExprNode::LetE {
                    type_, value, body, ..
                } => {
                    push(&mut expressions, type_, visited, limits)?;
                    push(&mut expressions, value, visited, limits)?;
                    push(&mut expressions, body, visited, limits)?;
                }
                ExprNode::Proj {
                    struct_name, expr, ..
                } => {
                    push(&mut pending, struct_name.clone(), visited, limits)?;
                    push(&mut expressions, expr, visited, limits)?;
                }
                ExprNode::MData { expr, .. } => push(&mut expressions, expr, visited, limits)?,
                _ => {}
            }
        }
    }
    Ok(())
}
