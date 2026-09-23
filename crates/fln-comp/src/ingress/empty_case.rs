//! Explicit, non-returning empty elimination. This is untrusted compiler input,
//! not evidence that the source domain is empty. Logical admission is upstream.
use super::*;

/// A compiler-owned `name major` call with no returning control-flow path.
///
/// `major` is evaluated normally; Bool is the inert representation of checked
/// proofs and Constructor is the representation of empty data types. Reaching
/// this call terminates with a VM panic, never fabricates a value of `result`.
/// Closure result ids are subject to ordinary whole-program FIR validation.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EmptyCaseBinding {
    pub name: Name,
    pub major: fir::ValueType,
    pub result: fir::ValueType,
}

const MESSAGE: &str = "empty elimination: unreachable branch reached";

pub(super) fn prepare(
    catalog: &mut PreparedCatalog<'_>,
    cases: &[EmptyCaseBinding],
    source_offset: usize,
    limits: IngressLimits,
) -> Result<(), IngressError> {
    for (index, case) in cases.iter().enumerate() {
        let source_index = source_offset.saturating_add(index);
        if case.name.is_anonymous() {
            return Err(IngressError::AnonymousFunctionName {
                binding: source_index,
            });
        }
        if is_check_system_name(&case.name) {
            return Err(IngressError::CheckSystemFunctionNameCollision {
                binding: source_index,
            });
        }
        if !matches!(
            case.major,
            fir::ValueType::Bool | fir::ValueType::Constructor
        ) {
            return Err(IngressError::UnsupportedNode {
                kind: "empty case major representation",
            });
        }
        charge(IngressResource::ContextDepth, 1, limits.max_context_depth)?;
        charge_fir(fir::ValidationResource::Blocks, 1, limits.fir.max_blocks)?;
        charge(
            IngressResource::LiteralBytes,
            MESSAGE.len(),
            limits.max_literal_bytes,
        )?;
        try_push(
            &mut catalog.functions,
            PreparedFunction {
                source_index,
                name: case.name.clone(),
                universe_arity: 0,
                id: fir::FunctionId::new(0),
                parameters: vec![case.major],
                parameter_ownership: borrowed_argument_ownership(1)?,
                result: case.result,
                result_ownership: default_callable_result_ownership(case.result),
                body: PreparedFunctionBody::EmptyCase,
            },
            IngressResource::ProgramTables,
            limits.fir.max_functions.saturating_sub(1),
        )?;
    }
    Ok(())
}

pub(super) fn assemble(
    function: &PreparedFunction<'_>,
    limits: IngressLimits,
) -> Result<fir::Function, IngressError> {
    let message = fir::ValueId::new(1);
    let mut blocks = Vec::new();
    try_push(
        &mut blocks,
        fir::Block {
            id: fir::BlockId::new(0),
            bindings: vec![fir::Binding {
                id: message,
                ty: fir::ValueType::String,
                operation: fir::Operation::String(MESSAGE.to_owned()),
            }],
            terminator: fir::Terminator::Panic { message },
        },
        IngressResource::ProgramTables,
        limits.fir.max_blocks,
    )?;
    Ok(fir::Function {
        id: function.id,
        parameters: clone_types(&function.parameters)?,
        parameter_ownership: clone_argument_ownership(&function.parameter_ownership)?,
        result: function.result,
        result_ownership: function.result_ownership,
        blocks,
    })
}
