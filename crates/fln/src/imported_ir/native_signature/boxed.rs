//! Native counterparts of the pin's generated array `_boxed` wrappers.
//!
//! `LCNF/ExplicitBoxing.lean` requires a boxed wrapper for every extern and
//! directs partial applications to it. Its signature retains erased type and
//! proof parameters, even though the final native ABI does not. Removing a
//! captured type from a PAP would therefore change its remaining arity when
//! an erased proof is still pending. Keep the complete boxed telescope and
//! forward only the reviewed runtime interval inside the native wrapper.
//!
//! These are native implementations, not permission to interpret toolchain
//! IR. A supplied wrapper body cannot replace them. Its boxed signature must
//! agree with the same reviewed arity; the generated extern row remains the
//! authority for runtime ownership, effects and bounds checks.

use super::{
    ErasedOperands, GeneratedExternRow, IrDecl, IrExecutionError, IrType, Name, array_proofs,
    erased_type_runtime_arity,
};

/// Recognize the compiler's structural suffix, not a dotted-name string or
/// an arbitrary descendant of a native declaration. All such native names
/// are reserved, including wrappers outside the supported array subset.
pub(in crate::imported_ir) fn boxed_row(name: &Name) -> Option<&'static GeneratedExternRow> {
    let base = name.parent();
    (Name::str(base.clone(), "_boxed") == *name)
        .then(|| super::super::native_row(&base))
        .flatten()
}

#[derive(Clone, Copy)]
pub(in crate::imported_ir) struct BoxedNative {
    operands: ErasedOperands,
}

impl BoxedNative {
    pub(in crate::imported_ir) fn from_row(
        row: &GeneratedExternRow,
    ) -> Result<Option<Self>, IrExecutionError> {
        // Void.mk's inert-world convention belongs to the separate state
        // bridge. It has no array boxed-result contract.
        if row.id == "extern:Void.mk" {
            return Ok(None);
        }
        let operands = if let Some(runtime) = erased_type_runtime_arity(row)? {
            Some(ErasedOperands {
                runtime,
                type_prefix: true,
                proof_suffix: false,
            })
        } else {
            array_proofs::erased_operands(row)?
        };
        Ok(operands.map(|operands| Self { operands }))
    }

    pub(in crate::imported_ir) fn arity(self) -> usize {
        self.operands.runtime
            + usize::from(self.operands.type_prefix)
            + usize::from(self.operands.proof_suffix)
    }

    pub(in crate::imported_ir) fn runtime_parameters(self) -> std::ops::Range<usize> {
        let start = usize::from(self.operands.type_prefix);
        start..start + self.operands.runtime
    }

    pub(in crate::imported_ir) fn validate_declaration(
        self,
        declaration: &IrDecl,
    ) -> Result<(), IrExecutionError> {
        let (params, result, sorry) = match declaration {
            IrDecl::Function {
                params,
                result,
                sorry_dep,
                ..
            } => (params, result, sorry_dep.is_some()),
            IrDecl::Extern { params, result, .. } => (params, result, false),
        };
        let object = |ty: &IrType| matches!(ty, IrType::Object | IrType::TObject | IrType::Tagged);
        if params.len() != self.arity()
            || params.iter().any(|p| p.borrow || !object(&p.ty))
            || !object(result)
            || sorry
        {
            return Err(IrExecutionError::NativeContract {
                declaration: declaration.name().clone(),
                detail: "native boxed wrapper differs from its reviewed boxed telescope".to_owned(),
            });
        }
        Ok(())
    }
}
