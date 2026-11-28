//! The pin's Task extern telescopes and their native boxed counterparts.
//!
//! Type parameters survive in compiler IR, including two independent universe
//! parameters for map/bind. Their native ABI has no such operands. Keep these
//! slots in first-class wrappers until saturation; direct calls may erase only
//! literal placeholders. Golem implements the completed, managerless Task path,
//! with callbacks executed under the ordinary VM budget and ownership checks.

use super::{GeneratedExternRow, IrExecutionError, IrParam, IrType, Name, inferred_arity};

pub(super) struct Signature {
    pub(super) erased_prefix: usize,
    pub(super) parameters: &'static [IrType],
    pub(super) result: &'static IrType,
}

pub(super) fn signature(row: &GeneratedExternRow) -> Result<Option<Signature>, IrExecutionError> {
    let (name, symbol, kind, prefix, parameters, result, ownership, effect): (
        _,
        _,
        _,
        usize,
        &'static [IrType],
        &'static IrType,
        _,
        _,
    ) = match row.id {
        "extern:Task.pure" => (
            "Task.pure",
            "lean_task_pure",
            "ctor",
            1,
            &[IrType::TObject],
            &IrType::Object,
            "abi((a: owned_arg) -> owned_res)",
            "task",
        ),
        "extern:Task.get" => (
            "Task.get",
            "lean_task_get_own",
            "defn",
            1,
            &[IrType::Object],
            &IrType::TObject,
            "abi((t: owned_arg) -> owned_res)",
            "pure",
        ),
        "extern:Task.spawn" => (
            "Task.spawn",
            "lean_task_spawn",
            "defn",
            1,
            &[IrType::TObject, IrType::TObject],
            &IrType::Object,
            "abi((c: owned_arg, prio: owned_arg) -> owned_res)",
            "task",
        ),
        "extern:Task.map" => (
            "Task.map",
            "lean_task_map",
            "defn",
            2,
            &[
                IrType::TObject,
                IrType::Object,
                IrType::TObject,
                IrType::UInt8,
            ],
            &IrType::Object,
            "abi((f: owned_arg, t: owned_arg, prio: owned_arg, sync: value) -> owned_res)",
            "task",
        ),
        "extern:Task.bind" => (
            "Task.bind",
            "lean_task_bind",
            "defn",
            2,
            &[
                IrType::Object,
                IrType::Object,
                IrType::TObject,
                IrType::UInt8,
            ],
            &IrType::Object,
            "abi((x: owned_arg, f: owned_arg, prio: owned_arg, sync: value) -> owned_res)",
            "task",
        ),
        _ => return Ok(None),
    };
    // These are Init.Core's signatures at the Reference pin. In particular,
    // unknown-result callbacks are TObject, but bind's Task-producing callback
    // is Object; sync is UInt8 before boxing. Neither distinction comes from
    // a call site's observed values or from a supplied wrapper body.
    if row.name != name
        || row.symbol != symbol
        || row.module != "Init.Core"
        || row.kind != kind
        || row.levels as usize != prefix
        || row.arity as usize != prefix + parameters.len()
        || row.effect != effect
        || row.safety != "safe"
        || row.ownership != ownership
        || row.entry_class != "standard"
        || row.entry_scope != "all"
        || row.partition != "toolchain-api"
        || row.mode != "all"
        || row.profile != "faithful,sound"
        || inferred_arity(row)? != parameters.len()
    {
        return Err(IrExecutionError::NativeContract {
            declaration: Name::from_components(row.name.split('.')),
            detail: "Task primitive differs from its reviewed native IR bridge".to_owned(),
        });
    }
    Ok(Some(Signature {
        erased_prefix: prefix,
        parameters,
        result,
    }))
}

/// The optional native-operand prototype must agree with the same reviewed
/// types as a full erased telescope. Task.get consumes a Task and returns an
/// owned retained payload; a prototype cannot turn either into a borrowed ABI.
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
            .any(|(parameter, expected)| parameter.borrow || parameter.ty != *expected)
    {
        return Err(IrExecutionError::NativeContract {
            declaration: Name::from_components(row.name.split('.')),
            detail: "Task extern differs from its reviewed native operand signature".to_owned(),
        });
    }
    Ok(())
}
