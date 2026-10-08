//! Recognize native arithmetic from its complete admitted logical model.
//!
//! The Reference decorates the model with hygienic binder labels and borrowed
//! metadata. Those annotations do not change the de Bruijn term or its native
//! runtime representation. Ignore only labels and transparent metadata; every
//! constant, universe, binder kind, body and inductive rule must still match.
//! No declaration is installed, unfolded, evaluated or accepted by this module.

use super::*;
use std::collections::HashSet;
pub(super) mod st;
mod string_internal;
pub(super) use string_internal::imported_string_internal_matches;

/// A present extern attribute is a separate execution contract. A complete
/// logical model may justify a native optimization without one, but it must
/// never override a conflicting explicit runtime implementation.
fn extern_attribute_matches(
    environment: &Environment,
    requested: &Name,
    required: bool,
    cache: &mut Option<fln_elab::externs::ExternTable>,
    visited: &mut usize,
    limits: IngressLimits,
) -> Result<bool, IngressError> {
    use fln_elab::externs::{ExternEntry, ExternReadError, ExternTable};
    charge_catalog_node(visited, limits)?;
    if cache.is_none() {
        let table = ExternTable::read_metered(environment, |amount| {
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
            ExternReadError::Budget(error) => error,
            ExternReadError::Registry(fln_elab::externs::ExternError::Limit) => {
                IngressError::MetadataResourceExhausted {
                    kind: "native extern attribute journal capacity or allocation",
                }
            }
            ExternReadError::Registry(_) => IngressError::UnsupportedNode {
                kind: "invalid native extern attribute journal",
            },
        })?;
        *cache = Some(table);
    }
    let table = cache
        .as_ref()
        .expect("only successful extern tables are cached");
    let Some(entries) = table.get(requested) else {
        return Ok(!required);
    };
    let label = requested.to_display_string();
    let row = fln_vm::extern_table_generated::EXTERN_ROWS
        .iter()
        .find(|row| row.name == label);
    if let (Some(row), [ExternEntry::Standard { backend, symbol }]) = (row, entries)
        && row
            .attributes
            .split(';')
            .any(|attribute| attribute == "extern")
        && row.entry_class == "standard"
        && row.entry_scope == "all"
        && backend == &Name::from_components(["all"])
        && symbol == row.symbol
    {
        return Ok(true);
    }
    Err(IngressError::UnsupportedNode {
        kind: "native extern attribute does not match the supported ABI",
    })
}

pub(super) fn check_selected_extern_attribute(
    environment: &Environment,
    requested: &Name,
    cache: &mut Option<fln_elab::externs::ExternTable>,
    visited: &mut usize,
    limits: IngressLimits,
) -> Result<(), IngressError> {
    extern_attribute_matches(environment, requested, false, cache, visited, limits).map(|_| ())
}

pub(super) fn nat_add_matches(
    environment: &Environment,
    visited: &mut usize,
    limits: IngressLimits,
) -> Result<bool, IngressError> {
    let mut comparison = Comparison { visited, limits };
    for declaration in std::iter::once(fln_elab::seed::nat_add_seed_declaration())
        .chain(std::iter::once(
            fln_elab::seed::nat_inductive_seed_declaration(),
        ))
        .chain(fln_elab::seed::nat_add_support_seed_declarations())
    {
        if !comparison.declaration(environment, declaration)? {
            return Ok(false);
        }
    }
    Ok(true)
}

pub(super) fn imported_nat_matches(
    environment: &Environment,
    name: &Name,
    visited: &mut usize,
    limits: IngressLimits,
) -> Result<bool, IngressError> {
    let Some(declarations) = fln_elab::seed::imported_nat_intrinsic_model_declarations(name) else {
        return Ok(false);
    };
    let mut comparison = Comparison { visited, limits };
    for declaration in declarations {
        if !comparison.declaration(environment, declaration)? {
            return Ok(false);
        }
    }
    Ok(true)
}

struct Comparison<'a> {
    visited: &'a mut usize,
    limits: IngressLimits,
}

/// Assemble only the existing checked Nat course-of-values models. This is
/// compiler-local recognition data, not an elaborator API or an admitted seed.
pub(super) fn imported_nat_recursion_model_declarations() -> Vec<Declaration> {
    std::iter::once(fln_elab::seed::nat_inductive_seed_declaration())
        .chain(
            fln_elab::seed::nat_add_support_seed_declarations()
                .into_iter()
                .take(6),
        )
        .collect()
}

pub(super) fn imported_nat_recursion_matches(
    environment: &Environment,
    visited: &mut usize,
    limits: IngressLimits,
) -> Result<bool, IngressError> {
    let mut comparison = Comparison { visited, limits };
    for declaration in imported_nat_recursion_model_declarations() {
        if !comparison.declaration(environment, declaration)? {
            return Ok(false);
        }
    }
    Ok(true)
}

pub(super) fn imported_list_recursion_matches(
    environment: &Environment,
    visited: &mut usize,
    limits: IngressLimits,
) -> Result<bool, IngressError> {
    let mut comparison = Comparison { visited, limits };
    for declaration in fln_elab::seed::imported_list_recursion_model_declarations() {
        if !comparison.declaration(environment, declaration)? {
            return Ok(false);
        }
    }
    Ok(true)
}

impl Comparison<'_> {
    fn tick(&mut self) -> Result<(), IngressError> {
        charge_catalog_node(self.visited, self.limits)
    }

    fn declaration(
        &mut self,
        environment: &Environment,
        expected: Declaration,
    ) -> Result<bool, IngressError> {
        match expected {
            Declaration::Defn(value) => self.constant(environment, ConstantInfo::Defn(value)),
            Declaration::Opaque(value) => self.constant(environment, ConstantInfo::Opaque(value)),
            Declaration::Inductive(block) => {
                for value in block.types {
                    if !self.constant(environment, ConstantInfo::Induct(value))? {
                        return Ok(false);
                    }
                }
                for value in block.ctors {
                    if !self.constant(environment, ConstantInfo::Ctor(value))? {
                        return Ok(false);
                    }
                }
                for value in block.recursors {
                    if !self.constant(environment, ConstantInfo::Rec(value))? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            _ => Ok(false),
        }
    }

    fn constant(
        &mut self,
        environment: &Environment,
        expected: ConstantInfo,
    ) -> Result<bool, IngressError> {
        self.tick()?;
        let Some(actual) = environment.find(expected.name()) else {
            return Ok(false);
        };
        self.info(actual, &expected)
    }

    fn info(
        &mut self,
        actual: &ConstantInfo,
        expected: &ConstantInfo,
    ) -> Result<bool, IngressError> {
        let a = actual.constant_val();
        let b = expected.constant_val();
        if a.name != b.name || a.level_params != b.level_params {
            return Ok(false);
        }
        let metadata = match (actual, expected) {
            (ConstantInfo::Defn(a), ConstantInfo::Defn(b)) => {
                a.hints == b.hints && a.safety == b.safety && a.all == b.all
            }
            (ConstantInfo::Opaque(a), ConstantInfo::Opaque(b)) => {
                a.is_unsafe == b.is_unsafe && a.all == b.all
            }
            (ConstantInfo::Induct(a), ConstantInfo::Induct(b)) => {
                a.num_params == b.num_params
                    && a.num_indices == b.num_indices
                    && a.all == b.all
                    && a.ctors == b.ctors
                    && a.num_nested == b.num_nested
                    && a.is_rec == b.is_rec
                    && a.is_unsafe == b.is_unsafe
                    && a.is_reflexive == b.is_reflexive
            }
            (ConstantInfo::Ctor(a), ConstantInfo::Ctor(b)) => {
                a.induct == b.induct
                    && a.cidx == b.cidx
                    && a.num_params == b.num_params
                    && a.num_fields == b.num_fields
                    && a.is_unsafe == b.is_unsafe
            }
            (ConstantInfo::Rec(a), ConstantInfo::Rec(b)) => {
                a.all == b.all
                    && a.num_params == b.num_params
                    && a.num_indices == b.num_indices
                    && a.num_motives == b.num_motives
                    && a.num_minors == b.num_minors
                    && a.rules.len() == b.rules.len()
                    && a.k == b.k
                    && a.is_unsafe == b.is_unsafe
            }
            _ => false,
        };
        if !metadata || !self.expression(&a.type_, &b.type_)? {
            return Ok(false);
        }
        match (actual, expected) {
            (ConstantInfo::Defn(a), ConstantInfo::Defn(b)) => self.expression(&a.value, &b.value),
            (ConstantInfo::Opaque(a), ConstantInfo::Opaque(b)) => {
                self.expression(&a.value, &b.value)
            }
            (ConstantInfo::Rec(a), ConstantInfo::Rec(b)) => {
                for (a, b) in a.rules.iter().zip(&b.rules) {
                    self.tick()?;
                    if a.ctor != b.ctor
                        || a.nfields != b.nfields
                        || !self.expression(&a.rhs, &b.rhs)?
                    {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            _ => Ok(true),
        }
    }

    fn expression(&mut self, actual: &Expr, expected: &Expr) -> Result<bool, IngressError> {
        let mut pending = vec![(actual, expected)];
        let mut compared = HashSet::new();
        while let Some((a, b)) = pending.pop() {
            self.tick()?;
            if a.allocation_identity() == b.allocation_identity() {
                continue;
            }
            compared
                .try_reserve(1)
                .map_err(|_| IngressError::AllocationFailure {
                    resource: IngressResource::ProgramTables,
                    requested: compared.len().saturating_add(1),
                })?;
            if !compared.insert((a.allocation_identity(), b.allocation_identity())) {
                continue;
            }
            pending
                .try_reserve(3)
                .map_err(|_| IngressError::AllocationFailure {
                    resource: IngressResource::PendingTasks,
                    requested: pending.len().saturating_add(3),
                })?;
            match (a.node(), b.node()) {
                (ExprNode::MData { expr, .. }, _) => pending.push((expr, b)),
                (_, ExprNode::MData { expr, .. }) => pending.push((a, expr)),
                (ExprNode::BVar { idx: a }, ExprNode::BVar { idx: b }) if a == b => {}
                (ExprNode::FVar { id: a }, ExprNode::FVar { id: b }) if a == b => {}
                (ExprNode::MVar { id: a }, ExprNode::MVar { id: b }) if a == b => {}
                (ExprNode::Sort { level: a }, ExprNode::Sort { level: b }) if a == b => {}
                (ExprNode::Lit { literal: a }, ExprNode::Lit { literal: b }) if a == b => {}
                (
                    ExprNode::Const {
                        name: a,
                        levels: al,
                    },
                    ExprNode::Const {
                        name: b,
                        levels: bl,
                    },
                ) if a == b && al == bl => {}
                (ExprNode::App { f: af, a: aa }, ExprNode::App { f: bf, a: ba }) => {
                    pending.push((aa, ba));
                    pending.push((af, bf));
                }
                (
                    ExprNode::Lam {
                        binder_type: at,
                        body: ab,
                        binder_info: ai,
                        ..
                    },
                    ExprNode::Lam {
                        binder_type: bt,
                        body: bb,
                        binder_info: bi,
                        ..
                    },
                )
                | (
                    ExprNode::ForallE {
                        binder_type: at,
                        body: ab,
                        binder_info: ai,
                        ..
                    },
                    ExprNode::ForallE {
                        binder_type: bt,
                        body: bb,
                        binder_info: bi,
                        ..
                    },
                ) if ai == bi => {
                    pending.push((ab, bb));
                    pending.push((at, bt));
                }
                (
                    ExprNode::LetE {
                        type_: at,
                        value: av,
                        body: ab,
                        non_dep: an,
                        ..
                    },
                    ExprNode::LetE {
                        type_: bt,
                        value: bv,
                        body: bb,
                        non_dep: bn,
                        ..
                    },
                ) if an == bn => {
                    pending.push((ab, bb));
                    pending.push((av, bv));
                    pending.push((at, bt));
                }
                (
                    ExprNode::Proj {
                        struct_name: an,
                        idx: ai,
                        expr: ae,
                    },
                    ExprNode::Proj {
                        struct_name: bn,
                        idx: bi,
                        expr: be,
                    },
                ) if an == bn && ai == bi => pending.push((ae, be)),
                _ => return Ok(false),
            }
        }
        Ok(true)
    }
}

#[cfg(test)]
mod tests;

#[cfg(test)]
mod imported_tests;
