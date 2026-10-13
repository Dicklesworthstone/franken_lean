//! Exact contracts for native, monomorphic BaseIO observations.
//!
//! The opaque defaults are recognition data from the pin, never executable
//! substitutes or declarations to admit. A native operation requires its
//! complete logical declaration and an explicit matching extern entry.

use super::*;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Operation {
    CheckCanceled,
    Initializing,
}

impl Operation {
    pub(crate) fn from_name(requested: &Name) -> Option<Self> {
        [Self::CheckCanceled, Self::Initializing]
            .into_iter()
            .find(|operation| requested == &operation.source_name())
    }

    pub(crate) fn source_name(self) -> Name {
        Name::from_components([
            "IO",
            match self {
                Self::CheckCanceled => "checkCanceled",
                Self::Initializing => "initializing",
            },
        ])
    }

    pub(crate) fn private_name(self) -> Name {
        Name::num(
            Name::from_components(["_fln_runtime_base_io_primitive"]),
            self as u64,
        )
    }
}

fn constant(label: &str, levels: Vec<Level>) -> Expr {
    Expr::const_(Name::from_components(label.split('.')), levels)
}

fn c(label: &str) -> Expr {
    constant(label, vec![])
}

fn apply(head: Expr, arguments: impl IntoIterator<Item = Expr>) -> Expr {
    arguments.into_iter().fold(head, Expr::app)
}

fn model(operation: Operation) -> ConstantInfo {
    let type_ = Expr::app(c("BaseIO"), c("Bool"));
    ConstantInfo::Opaque(OpaqueVal {
        base: ConstantVal {
            name: operation.source_name(),
            level_params: vec![],
            type_: type_.clone(),
        },
        value: apply(
            constant("Inhabited.default", vec![Level::one()]),
            [
                type_,
                apply(
                    constant("instInhabitedOfMonad", vec![Level::zero(); 2]),
                    [
                        c("Bool"),
                        c("BaseIO"),
                        c("instMonadBaseIO"),
                        c("instInhabitedBool"),
                    ],
                ),
            ],
        ),
        is_unsafe: false,
        all: vec![operation.source_name()],
    })
}

pub(crate) fn primitive_matches(
    environment: &Environment,
    operation: Operation,
    externs: &mut Option<fln_elab::externs::ExternTable>,
    visited: &mut usize,
    limits: IngressLimits,
) -> Result<bool, IngressError> {
    let requested = operation.source_name();
    if !extern_attribute_matches(environment, &requested, true, externs, visited, limits)? {
        return Ok(false);
    }
    if !io_world_contract_matches(environment, externs, visited, limits)? {
        return Err(IngressError::UnsupportedNode {
            kind: "native BaseIO extern requires the complete checked IO world",
        });
    }
    let mut comparison = Comparison { visited, limits };
    if !comparison.declaration(environment, fln_elab::seed::bool_seed_declaration())?
        || !comparison.constant(environment, model(operation))?
    {
        return Err(IngressError::UnsupportedNode {
            kind: "native BaseIO extern does not match its complete checked contract",
        });
    }
    Ok(true)
}

#[cfg(test)]
mod tests;
