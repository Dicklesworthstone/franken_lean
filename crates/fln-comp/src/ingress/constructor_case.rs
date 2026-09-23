//! Native, lazy constructor dispatch over untrusted but validated catalogs.
use super::*;
use crate::flbc::ArgumentOwnership;

/// `name major branch_0 ... branch_n` tests each constructor's exact tag and
/// object-slot count. Branches have signature `(Constructor) -> result` and
/// receive the shared major. An unmatched runtime object panics, never selects
/// an arbitrary branch. Constructor order is semantic and is not re-sorted.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ConstructorCaseBinding {
    pub name: Name,
    pub constructors: Vec<Name>,
    pub result: fir::ValueType,
}

pub(super) fn prepare(
    catalog: &mut PreparedCatalog<'_>,
    cases: &[ConstructorCaseBinding],
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
        if case.constructors.is_empty() {
            return Err(IngressError::UnsupportedNode {
                kind: "empty constructor case",
            });
        }
        let parameter_count = case.constructors.len().saturating_add(1);
        charge(
            IngressResource::ContextDepth,
            parameter_count,
            limits.max_context_depth,
        )?;
        charge_fir(
            fir::ValidationResource::Blocks,
            case.constructors.len().saturating_mul(2).saturating_add(1),
            limits.fir.max_blocks,
        )?;
        let ownership = default_callable_result_ownership(case.result);
        let closure = catalog
            .closure_types
            .iter()
            .find(|signature| {
                signature.parameters == [fir::ValueType::Constructor]
                    && signature.parameter_ownership == [ArgumentOwnership::Borrowed]
                    && signature.result == case.result
                    && signature.result_ownership == ownership
            })
            .ok_or(IngressError::UnsupportedNode {
                kind: "constructor case branch signature",
            })?;
        let closure_type = fir::ValueType::Closure(closure.id);
        let mut parameters = vec![fir::ValueType::Constructor];
        let mut constructors = Vec::new();
        // Runtime tags, not catalog IDs, discriminate objects. Equal tags must
        // not alias even when their field counts happen to differ.
        let mut tags = [false; 256];
        for name in &case.constructors {
            let constructor = catalog
                .resolve_constructor(name)
                .and_then(|i| catalog.constructors.get(i))
                .ok_or(IngressError::UnsupportedNode {
                    kind: "unknown case constructor",
                })?;
            if tags[usize::from(constructor.declaration.tag)] {
                return Err(IngressError::UnsupportedNode {
                    kind: "duplicate constructor case tag",
                });
            }
            tags[usize::from(constructor.declaration.tag)] = true;
            try_push(
                &mut constructors,
                constructor.declaration.id,
                IngressResource::ProgramTables,
                limits.fir.max_constructors,
            )?;
            try_push(
                &mut parameters,
                closure_type,
                IngressResource::ContextDepth,
                limits.max_context_depth,
            )?;
        }
        try_push(
            &mut catalog.functions,
            PreparedFunction {
                source_index,
                name: case.name.clone(),
                universe_arity: 0,
                id: fir::FunctionId::new(0),
                parameters,
                parameter_ownership: borrowed_argument_ownership(parameter_count)?,
                result: case.result,
                result_ownership: ownership,
                body: PreparedFunctionBody::ConstructorCase(constructors),
            },
            IngressResource::ProgramTables,
            limits.fir.max_functions.saturating_sub(1),
        )?;
    }
    Ok(())
}

pub(super) fn assemble(
    function: &PreparedFunction<'_>,
    constructors: &[fir::ConstructorId],
    limits: IngressLimits,
) -> Result<fir::Function, IngressError> {
    let count = constructors.len();
    let width = |n: usize| {
        u32::try_from(n).map_err(|_| IngressError::IdentifierWidth {
            table: "constructor case",
            observed: n,
        })
    };
    let major = fir::ValueId::new(0);
    let mut blocks = Vec::new();
    for (index, constructor) in constructors.iter().enumerate() {
        let test = fir::ValueId::new(width(
            function
                .parameters
                .len()
                .saturating_add(index.saturating_mul(2)),
        )?);
        let value = fir::ValueId::new(test.get().checked_add(1).ok_or(
            IngressError::IdentifierWidth {
                table: "constructor case value",
                observed: usize::MAX,
            },
        )?);
        try_push(
            &mut blocks,
            fir::Block {
                id: fir::BlockId::new(width(index.saturating_mul(2))?),
                bindings: vec![fir::Binding {
                    id: test,
                    ty: fir::ValueType::Bool,
                    operation: fir::Operation::CtorTest {
                        constructor: *constructor,
                        value: major,
                    },
                }],
                terminator: fir::Terminator::BranchZero {
                    condition: test,
                    zero: fir::BlockId::new(width(index.saturating_mul(2).saturating_add(2))?),
                    nonzero: fir::BlockId::new(width(index.saturating_mul(2).saturating_add(1))?),
                },
            },
            IngressResource::ProgramTables,
            limits.fir.max_blocks,
        )?;
        try_push(
            &mut blocks,
            fir::Block {
                id: fir::BlockId::new(width(index.saturating_mul(2).saturating_add(1))?),
                bindings: vec![fir::Binding {
                    id: value,
                    ty: function.result,
                    operation: fir::Operation::Apply {
                        closure: fir::ValueId::new(width(index.saturating_add(1))?),
                        args: vec![major],
                        argument_ownership: vec![ArgumentOwnership::Borrowed],
                        result_ownership: function.result_ownership,
                    },
                }],
                terminator: fir::Terminator::Return { value },
            },
            IngressResource::ProgramTables,
            limits.fir.max_blocks,
        )?;
    }
    let message = fir::ValueId::new(width(
        function
            .parameters
            .len()
            .saturating_add(count.saturating_mul(2)),
    )?);
    try_push(
        &mut blocks,
        fir::Block {
            id: fir::BlockId::new(width(count.saturating_mul(2))?),
            bindings: vec![fir::Binding {
                id: message,
                ty: fir::ValueType::String,
                operation: fir::Operation::String(
                    "constructor case: unmatched tag or shape".to_owned(),
                ),
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
