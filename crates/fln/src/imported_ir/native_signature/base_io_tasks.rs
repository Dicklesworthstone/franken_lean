//! Completed-task BaseIO operations at the pinned compiler/native boundary.
//!
//! Their census rows describe source binders and use a conservative ownership
//! rule; the native functions in runtime/io.cpp omit types, proofs and world.
//! Keep the complete telescope in first-class closures until saturation. The
//! callbacks receive Golem's inert world and return their payload directly,
//! without an IO.Result envelope. No scheduler or host capability is supplied.

use super::{GeneratedExternRow, IrExecutionError, IrParam, IrType, Name};

pub(super) struct Signature {
    pub(super) erased_prefix: usize,
    pub(super) erased_proofs: usize,
    pub(super) parameters: &'static [IrType],
    pub(super) borrowed: &'static [bool],
    pub(super) result: &'static IrType,
}

pub(super) fn signature(row: &GeneratedExternRow) -> Result<Option<Signature>, IrExecutionError> {
    let (name, symbol, levels, prefix, proofs, parameters, borrowed, result): (
        _,
        _,
        _,
        usize,
        usize,
        &'static [IrType],
        &'static [bool],
        &'static IrType,
    ) = match row.id {
        "extern:BaseIO.asTask" => (
            "BaseIO.asTask",
            "lean_io_as_task",
            0,
            1,
            0,
            &[IrType::Object, IrType::TObject],
            &[false, false],
            &IrType::Object,
        ),
        "extern:BaseIO.mapTask" => (
            "BaseIO.mapTask",
            "lean_io_map_task",
            1,
            2,
            0,
            &[
                IrType::Object,
                IrType::Object,
                IrType::TObject,
                IrType::UInt8,
            ],
            &[false, false, false, false],
            &IrType::Object,
        ),
        "extern:BaseIO.bindTask" => (
            "BaseIO.bindTask",
            "lean_io_bind_task",
            1,
            2,
            0,
            &[
                IrType::Object,
                IrType::Object,
                IrType::TObject,
                IrType::UInt8,
            ],
            &[false, false, false, false],
            &IrType::Object,
        ),
        "extern:IO.wait" => (
            "IO.wait",
            "lean_io_wait",
            0,
            1,
            0,
            &[IrType::Object],
            &[false],
            &IrType::TObject,
        ),
        "extern:IO.getTaskState" => (
            "IO.getTaskState",
            "lean_io_get_task_state",
            1,
            1,
            0,
            &[IrType::Object],
            &[true],
            &IrType::UInt8,
        ),
        "extern:IO.waitAny" => (
            "IO.waitAny",
            "lean_io_wait_any",
            0,
            1,
            1,
            &[IrType::TObject],
            &[true],
            &IrType::TObject,
        ),
        _ => return Ok(None),
    };
    // BaseIO's result is restricted to Type, but map/bind accept an input
    // in Type u. Its universe count therefore differs from its type slots.
    // The original IR records precise borrowing independently of the VM's
    // conservative rule, which retains all native operands across the call.
    if row.name != name
        || row.symbol != symbol
        || row.module != "Init.System.IO"
        || row.kind != "opaque"
        || row.levels != levels
        || row.arity as usize != prefix + parameters.len() + proofs
        || row.effect != "io"
        || row.safety != "safe"
        || row.ownership != "rule(borrowed-args,owned-result)"
        || row.entry_class != "standard"
        || row.entry_scope != "all"
        || row.partition != "toolchain-api"
        || row.mode != "all"
        || row.profile != "faithful,sound"
    {
        return Err(IrExecutionError::NativeContract {
            declaration: Name::from_components(row.name.split('.')),
            detail: "BaseIO task primitive differs from its reviewed native IR bridge".to_owned(),
        });
    }
    Ok(Some(Signature {
        erased_prefix: prefix,
        erased_proofs: proofs,
        parameters,
        borrowed,
        result,
    }))
}

pub(super) fn validate_native_signature(
    row: &GeneratedExternRow,
    params: &[IrParam],
    result: &IrType,
) -> Result<(), IrExecutionError> {
    let Some(signature) = signature(row)? else {
        return Ok(());
    };
    if params.len() != signature.parameters.len() {
        return Ok(());
    }
    if result != signature.result
        || params
            .iter()
            .zip(signature.parameters)
            .zip(signature.borrowed)
            .any(|((parameter, expected), borrowed)| {
                parameter.ty != *expected || parameter.borrow != *borrowed
            })
    {
        return Err(IrExecutionError::NativeContract {
            declaration: Name::from_components(row.name.split('.')),
            detail: "BaseIO task extern differs from its reviewed native operand signature"
                .to_owned(),
        });
    }
    Ok(())
}
