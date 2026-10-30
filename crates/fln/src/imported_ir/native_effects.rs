//! Native effects admitted by the explicit imported-IR executor.
//!
//! The reference-cell primitives operate on Golem-owned cells supplied as
//! ordinary checked values. They require no host I/O capability, process
//! state, imported initializer or Reference runtime. Do not generalize this
//! allowlist to every state-class row: some operate on runtime-global state.
//!
//! `take` is the pin's implementation of public modify/modifyGet. Golem moves
//! the occupant through its checked handle API and refuses a vacant or invalid
//! cell; it never invokes the assertion-based raw ABI entry point. Its erased
//! runtime arity is separately bound in native_signature.

use super::{GeneratedExternRow, IrExecutionError, Name, fir, unsupported};

pub(super) fn classify(row: &GeneratedExternRow) -> Result<fir::EffectClass, IrExecutionError> {
    match (row.effect, row.id) {
        ("pure", _) => Ok(fir::EffectClass::Pure),
        (
            "state",
            "extern:ST.Prim.mkRef"
            | "extern:ST.Prim.Ref.get"
            | "extern:ST.Prim.Ref.set"
            | "extern:ST.Prim.Ref.swap"
            | "extern:ST.Prim.Ref.take",
        ) => Ok(fir::EffectClass::State),
        _ => Err(unsupported(
            &Name::from_components(row.name.split('.')),
            "effectful native call",
        )),
    }
}

#[cfg(test)]
mod tests;
