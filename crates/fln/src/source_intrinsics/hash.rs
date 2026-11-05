//! Bind the opaque hash mixer to its complete admitted Prelude model.
//!
//! The already-extracted computed-Name inventory includes the entire `mixHash`
//! dependency closure. Treat it only as a pool of pinned declaration digests:
//! walk this root's actual type, value, families and recursor rules, requiring
//! every reached declaration to match. Unrelated Name declarations are not
//! required, and none of these comparison data install or admit a declaration.

use super::*;
use std::collections::HashMap;

const MODEL_POOL: &str = include_str!("../runtime/implemented_by_names.txt");

fn allocation(requested: usize) -> IngressError {
    IngressError::AllocationFailure {
        resource: IngressResource::Nodes,
        requested,
    }
}

fn push<T>(
    pending: &mut Vec<T>,
    value: T,
    visited: &mut usize,
    limits: IngressLimits,
) -> Result<(), IngressError> {
    charge_catalog_node(visited, limits)?;
    pending
        .try_reserve(1)
        .map_err(|_| allocation(pending.len().saturating_add(1)))?;
    pending.push(value);
    Ok(())
}

pub(crate) fn matches(
    environment: &Environment,
    requested: &Name,
    externs: &mut Option<fln_elab::externs::ExternTable>,
    visited: &mut usize,
    limits: IngressLimits,
) -> Result<bool, IngressError> {
    if requested != &Name::from_components(["mixHash"]) {
        return Ok(false);
    }
    if !extern_attribute_matches(environment, requested, true, externs, visited, limits)? {
        return Ok(false);
    }
    let mut expected = HashMap::new();
    for line in MODEL_POOL.lines() {
        charge_catalog_node(visited, limits)?;
        let mut columns = line.split('\t');
        let encoded = columns.next().expect("fixed hash dependency name");
        let digest = columns.next().expect("fixed hash dependency digest");
        let mut label = Name::anonymous();
        for component in encoded.split('/') {
            charge_catalog_node(visited, limits)?;
            label = if let Some(text) = component.strip_prefix("s:") {
                Name::str(label, text)
            } else if let Some(number) = component.strip_prefix("n:") {
                Name::num(label, number.parse().expect("fixed hash name component"))
            } else {
                unreachable!("fixed hash dependency encoding")
            };
        }
        expected
            .try_reserve(1)
            .map_err(|_| allocation(expected.len().saturating_add(1)))?;
        expected.insert(label, digest);
    }
    let mut pending = Vec::new();
    push(&mut pending, requested.clone(), visited, limits)?;
    let mut complete = HashSet::new();
    let mut expressions_seen = HashSet::new();
    while let Some(label) = pending.pop() {
        charge_catalog_node(visited, limits)?;
        if complete.contains(&label) {
            continue;
        }
        complete
            .try_reserve(1)
            .map_err(|_| allocation(complete.len().saturating_add(1)))?;
        complete.insert(label.clone());
        let entry = environment
            .entry(&label)
            .ok_or(IngressError::UnsupportedNode {
                kind: "hash mixer dependency is absent",
            })?;
        let digest = expected.get(&label).ok_or(IngressError::UnsupportedNode {
            kind: "hash mixer dependency is absent from the pinned inventory",
        })?;
        if entry.digest().to_hex() != *digest {
            return Err(IngressError::UnsupportedNode {
                kind: "hash mixer dependency differs from the exact pinned model",
            });
        }
        // The selected root extern takes precedence over its opaque fallback.
        // Its logical helpers are comparison data, never executable bodies.
        // A conflicting explicit ABI must still not inherit native authority.
        check_selected_extern_attribute(environment, &label, externs, visited, limits)?;
        let info = environment.find(&label).expect("existing hash model entry");
        let mut expressions = Vec::new();
        push(
            &mut expressions,
            &info.constant_val().type_,
            visited,
            limits,
        )?;
        let group = match info {
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
                    push(&mut pending, rule.ctor.clone(), visited, limits)?;
                    push(&mut expressions, &rule.rhs, visited, limits)?;
                }
                value.all.as_slice()
            }
            ConstantInfo::Axiom(_) | ConstantInfo::Quot(_) => &[],
        };
        for member in group {
            push(&mut pending, member.clone(), visited, limits)?;
        }
        while let Some(expression) = expressions.pop() {
            charge_catalog_node(visited, limits)?;
            if expressions_seen.contains(&expression.allocation_identity()) {
                continue;
            }
            expressions_seen
                .try_reserve(1)
                .map_err(|_| allocation(expressions_seen.len().saturating_add(1)))?;
            expressions_seen.insert(expression.allocation_identity());
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
                ExprNode::MData { expr, .. } => {
                    push(&mut expressions, expr, visited, limits)?;
                }
                _ => {}
            }
        }
    }
    Ok(true)
}
