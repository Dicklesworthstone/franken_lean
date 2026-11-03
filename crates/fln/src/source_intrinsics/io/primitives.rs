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
    GetEnv,
}

impl Operation {
    pub(crate) fn from_name(requested: &Name) -> Option<Self> {
        [Self::CheckCanceled, Self::Initializing, Self::GetEnv]
            .into_iter()
            .find(|operation| requested == &operation.source_name())
    }

    pub(crate) fn source_name(self) -> Name {
        Name::from_components([
            "IO",
            match self {
                Self::CheckCanceled => "checkCanceled",
                Self::Initializing => "initializing",
                Self::GetEnv => "getEnv",
            },
        ])
    }

    pub(crate) fn private_name(self) -> Name {
        Name::num(
            Name::from_components(["_fln_runtime_base_io_primitive"]),
            self as u64,
        )
    }

    pub(crate) fn source_arity(self) -> usize {
        usize::from(self == Self::GetEnv)
    }

    pub(crate) fn result_type(self) -> Expr {
        if self == Self::GetEnv {
            Expr::app(constant("Option", vec![Level::zero()]), c("String"))
        } else {
            c("Bool")
        }
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
    let result = operation.result_type();
    let action = Expr::app(c("BaseIO"), result.clone());
    let instance = if operation == Operation::GetEnv {
        Expr::app(
            constant("instInhabitedOption", vec![Level::zero()]),
            c("String"),
        )
    } else {
        c("instInhabitedBool")
    };
    let default = apply(
        constant("Inhabited.default", vec![Level::one()]),
        [
            action.clone(),
            apply(
                constant("instInhabitedOfMonad", vec![Level::zero(); 2]),
                [result, c("BaseIO"), c("instMonadBaseIO"), instance],
            ),
        ],
    );
    let (type_, value) = if operation == Operation::GetEnv {
        (
            Expr::forall_e(Name::anonymous(), c("String"), action, BinderInfo::Default),
            Expr::lam(Name::anonymous(), c("String"), default, BinderInfo::Default),
        )
    } else {
        (action, default)
    };
    ConstantInfo::Opaque(OpaqueVal {
        base: ConstantVal {
            name: operation.source_name(),
            level_params: vec![],
            type_,
        },
        value,
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
    let mut models = vec![model(operation)];
    if operation == Operation::GetEnv {
        models.extend(crate::source_intrinsics::string_internal::scalar_records());
        let names = ["Option", "Option.none", "Option.some"]
            .map(|label| Name::from_components(label.split('.')));
        models.extend(
            stdout::result_models()
                .into_iter()
                .filter(|model| names.contains(model.name())),
        );
    }
    let mut comparison = Comparison { visited, limits };
    if !comparison.declaration(environment, fln_elab::seed::bool_seed_declaration())? {
        return Err(IngressError::UnsupportedNode {
            kind: "native BaseIO extern does not match its complete checked contract",
        });
    }
    for expected in &models {
        if !comparison.constant(environment, expected.clone())? {
            return Err(IngressError::UnsupportedNode {
                kind: "native BaseIO extern does not match its complete checked contract",
            });
        }
    }
    for expected in models {
        check_selected_extern_attribute(environment, expected.name(), externs, visited, limits)?;
    }
    Ok(true)
}

#[cfg(test)]
mod tests;
