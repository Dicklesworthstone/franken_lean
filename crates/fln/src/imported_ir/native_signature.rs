//! Recover erased executable arities from the generated native ABI contract.
//!
//! The census arity counts source binders, including erased types. A module's
//! IR need not repeat declarations for imported native callees. In that case
//! only the generated ABI, never the first observed call site, can supply the
//! runtime arity. Explicit IR extern declarations are still checked separately.

use super::{GeneratedExternRow, IrExecutionError, Name, Ownership, extern_row};

pub(super) fn inferred_arity(row: &GeneratedExternRow) -> Result<usize, IrExecutionError> {
    let error = |error: extern_row::ContractError| IrExecutionError::NativeContract {
        declaration: Name::from_components(row.name.split('.')),
        detail: error.to_string(),
    };
    let ownership = Ownership::parse(row.ownership).map_err(error)?;
    executable_arity(&ownership, row.arity as usize).map_err(error)
}

fn executable_arity(
    ownership: &Ownership,
    source_arity: usize,
) -> Result<usize, extern_row::ContractError> {
    let arity = match ownership {
        Ownership::AbiSignature(signature) => {
            let parameters = signature
                .split_once(" -> ")
                .and_then(|(parameters, _)| parameters.strip_prefix('('))
                .and_then(|parameters| parameters.strip_suffix(')'))
                .ok_or_else(|| {
                    extern_row::ContractError::new("malformed generated ABI parameter list")
                })?;
            if parameters.is_empty() || parameters == "()" {
                0
            } else {
                parameters.split(", ").count()
            }
        }
        // A rule-only row has no independent erased telescope. Preserve the
        // existing census-arity requirement rather than guessing from uses.
        _ => source_arity,
    };
    // Counting separators does not authorize an ABI. The existing canonical
    // ownership parser must still accept every parameter and the result,
    // including its refusal of raw pointers and unsupported ownership rules.
    ownership.argument_ownership(arity)?;
    ownership.result_ownership()?;
    Ok(arity)
}

#[cfg(test)]
mod tests;
