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
    ErasedOperands, GeneratedExternRow, IrDecl, IrExecutionError, IrParam, IrType, Name, Ownership,
    array_proofs, erased_type_runtime_arity, extern_row,
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
    parameters: &'static [IrType],
    result: &'static IrType,
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
        let Some(operands) = operands else {
            return Ok(None);
        };
        // These types come from the pin's actual extern declarations in
        // Init.Prelude, Init.Data.Array.{Basic,Set} and ByteArray.Basic.
        // The ABI row alone cannot distinguish Object/TObject/Tagged or
        // identify which scalar carrier the compiler must box.
        let (parameters, result): (&'static [IrType], &'static IrType) = match row.id {
            "extern:Array.mkEmpty" => (&[IrType::TObject], &IrType::Object),
            "extern:Array.push" => (&[IrType::Object, IrType::TObject], &IrType::Object),
            "extern:Array.size" => (&[IrType::Object], &IrType::Tagged),
            "extern:Array.replicate" => (&[IrType::TObject, IrType::TObject], &IrType::Object),
            "extern:Array.set!" | "extern:Array.set" => (
                &[IrType::Object, IrType::TObject, IrType::TObject],
                &IrType::Object,
            ),
            "extern:Array.get!Internal" | "extern:Array.get!InternalBorrowed" => (
                &[IrType::TObject, IrType::Object, IrType::TObject],
                &IrType::TObject,
            ),
            "extern:Array.usize" => (&[IrType::Object], &IrType::USize),
            "extern:Array.getInternal" | "extern:Array.getInternalBorrowed" => {
                (&[IrType::Object, IrType::TObject], &IrType::TObject)
            }
            "extern:Array.uget" | "extern:Array.ugetBorrowed" => {
                (&[IrType::Object, IrType::USize], &IrType::TObject)
            }
            "extern:Array.uset" => (
                &[IrType::Object, IrType::USize, IrType::TObject],
                &IrType::Object,
            ),
            "extern:ByteArray.get" => (&[IrType::Object, IrType::TObject], &IrType::UInt8),
            "extern:ByteArray.set" => (
                &[IrType::Object, IrType::TObject, IrType::UInt8],
                &IrType::Object,
            ),
            "extern:ByteArray.uget" => (&[IrType::Object, IrType::USize], &IrType::UInt8),
            "extern:ByteArray.uset" => (
                &[IrType::Object, IrType::USize, IrType::UInt8],
                &IrType::Object,
            ),
            _ => {
                return Err(IrExecutionError::NativeContract {
                    declaration: Name::from_components(row.name.split('.')),
                    detail: "array primitive has no reviewed native IR types".to_owned(),
                });
            }
        };
        if parameters.len() != operands.runtime {
            return Err(IrExecutionError::NativeContract {
                declaration: Name::from_components(row.name.split('.')),
                detail: "array IR types differ from the reviewed runtime arity".to_owned(),
            });
        }
        Ok(Some(Self {
            operands,
            parameters,
            result,
        }))
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

    fn parameter_type(self, index: usize) -> &'static IrType {
        let runtime = self.runtime_parameters();
        if runtime.contains(&index) {
            &self.parameters[index - runtime.start]
        } else {
            &IrType::Erased
        }
    }

    /// Raw externs retain Erased slots and the original borrowing. Accept
    /// only this exact full telescope, separately from the existing native
    /// operand form. A prototype never supplies its own ABI or runtime arity.
    pub(super) fn validate_extern(
        self,
        row: &GeneratedExternRow,
        params: &[IrParam],
        result: &IrType,
    ) -> Result<(), IrExecutionError> {
        let ownership = Ownership::parse(row.ownership)
            .and_then(|ownership| ownership.argument_ownership(self.operands.runtime))
            .map_err(|error| IrExecutionError::NativeContract {
                declaration: Name::from_components(row.name.split('.')),
                detail: error.to_string(),
            })?;
        let runtime = self.runtime_parameters();
        if params.len() != self.arity()
            || result != self.result
            || params.iter().enumerate().any(|(index, parameter)| {
                let borrowed = runtime.contains(&index)
                    && ownership[index - runtime.start] == extern_row::ArgumentOwnership::Borrowed;
                parameter.ty != *self.parameter_type(index) || parameter.borrow != borrowed
            })
        {
            return Err(IrExecutionError::NativeContract {
                declaration: Name::from_components(row.name.split('.')),
                detail: "array extern differs from its reviewed erased telescope".to_owned(),
            });
        }
        Ok(())
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
        if params.len() != self.arity()
            || params.iter().enumerate().any(|(index, parameter)| {
                parameter.borrow || parameter.ty != *boxed_type(self.parameter_type(index))
            })
            || result != boxed_type(self.result)
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

fn boxed_type(ty: &IrType) -> &IrType {
    match ty {
        IrType::Erased | IrType::USize => &IrType::TObject,
        IrType::UInt8 => &IrType::Tagged,
        _ => ty,
    }
}
