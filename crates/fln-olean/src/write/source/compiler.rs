//! Compiled interfaces in the pin's logical module companions.
//!
//! `LCNF/PhaseExt.lean::impureSigExt` stores monomorphic signatures, while
//! `IR/CompilerM.lean::declMapExt` stores opaque headers for ordinary compiled
//! declarations. Executable bodies remain in the separately emitted `.ir`.
//! Both maps are binary-searched in `Name.quickLt` order.
use super::*;
use crate::ir::{IrDecl, IrParam, IrType};
use crate::ir_format as ir;

/// A compiled, monomorphic interface. The caller owns its relationship to the
/// checked source and executable IR. `safe = false` conservatively withholds the
/// compiler's termination assumption; setting it requires separate provenance.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CompilerSignature {
    pub name: Name,
    pub params: Vec<IrParam>,
    pub result: IrType,
    pub safe: bool,
}

impl CompilerSignature {
    /// Preserve the exact arity, borrowing policy, and carriers of native IR.
    /// This copies an interface without admitting or executing the declaration.
    pub fn from_ir(declaration: &IrDecl, safe: bool) -> Self {
        let (name, params, result) = match declaration {
            IrDecl::Function {
                name,
                params,
                result,
                ..
            }
            | IrDecl::Extern {
                name,
                params,
                result,
                ..
            } => (name, params, result),
        };
        Self {
            name: name.clone(),
            params: params.clone(),
            result: result.clone(),
            safe,
        }
    }
}

/// `LCNF/Types.lean::ImpureType`: these names are unqualified, including the
/// compiler's synthetic `obj`/`tobj` types and root `lcErased`/`lcVoid` names.
fn carrier(ty: &IrType) -> WResult<(&'static str, u8)> {
    Ok(match ty {
        IrType::Float => ("Float", ir::IR_TYPE_FLOAT),
        IrType::Float32 => ("Float32", ir::IR_TYPE_FLOAT32),
        IrType::UInt8 => ("UInt8", ir::IR_TYPE_UINT8),
        IrType::UInt16 => ("UInt16", ir::IR_TYPE_UINT16),
        IrType::UInt32 => ("UInt32", ir::IR_TYPE_UINT32),
        IrType::UInt64 => ("UInt64", ir::IR_TYPE_UINT64),
        IrType::USize => ("USize", ir::IR_TYPE_USIZE),
        IrType::Erased => ("lcErased", ir::IR_TYPE_ERASED),
        IrType::Object => ("obj", ir::IR_TYPE_OBJECT),
        IrType::TObject => ("tobj", ir::IR_TYPE_TOBJECT),
        IrType::Tagged => ("tagged", ir::IR_TYPE_TAGGED),
        IrType::Void => ("lcVoid", ir::IR_TYPE_VOID),
        IrType::Struct { .. } | IrType::Union { .. } => {
            return Err(WriteError::Unsupported {
                what: "aggregate LCNF compiler signature carrier",
            });
        }
    })
}

impl Encoder {
    fn compiler_type(&mut self, ty: &IrType) -> WResult<Obj> {
        let (name, _) = carrier(ty)?;
        let expression = self
            .compiler_types
            .entry(name)
            .or_insert_with(|| Expr::const_(Name::from_components([name]), Vec::new()))
            .clone();
        self.expression(&expression)
    }

    fn compiler_extension(&mut self, key: &str, entries: Vec<Obj>) -> WResult<Obj> {
        let name = self.name(&Name::from_components(key.split('.')))?;
        let entries = self.array(entries)?;
        self.ctor(0, vec![name, entries], &[])
    }

    pub(super) fn compiler_blocks(&mut self, rows: &[CompilerSignature]) -> WResult<Vec<Obj>> {
        // The Signature/Param layouts below are independently visible in the
        // pin's stage0/stdlib/Lean/Compiler/LCNF/Basic.c default constructors.
        // A repin must audit them instead of silently carrying field guesses.
        if format::PIN_COMMIT != "8c9756b28d64dab099da31a4c09229a9e6a2ef35" {
            return Err(WriteError::Unsupported {
                what: "LCNF compiler signatures have not been audited for this pin",
            });
        }
        self.source_array_bound(rows.len())?;
        let mut sorted: Vec<_> = rows.iter().collect();
        sorted.sort_by(|left, right| left.name.quick_cmp(&right.name));
        if sorted.iter().any(|row| row.name.is_anonymous())
            || sorted.windows(2).any(|pair| pair[0].name == pair[1].name)
        {
            return Err(WriteError::Contract {
                what: "anonymous or duplicate compiler signature",
            });
        }
        let mut signatures = Vec::with_capacity(sorted.len());
        let mut headers = Vec::with_capacity(sorted.len());
        for row in sorted {
            self.source_array_bound(row.params.len())?;
            let mut ids = HashSet::new();
            let mut params = Vec::with_capacity(row.params.len());
            let mut ir_params = Vec::with_capacity(row.params.len());
            for param in &row.params {
                if param.x == 0 || !ids.insert(param.x) {
                    return Err(WriteError::Contract {
                        what: "zero or duplicate compiler parameter",
                    });
                }
                // FVarId's one-field wrapper is erased. Distinct raw Names are
                // sufficient here: impure carrier expressions have no fvars.
                let id = self.name(&Name::num(Name::anonymous(), param.x))?;
                let binder = self.name(&Name::from_components(["x"]))?;
                let type_ = self.compiler_type(&param.ty)?;
                let mut fields = (0..ir::LCNF_PARAM_POINTERS)
                    .map(|_| Obj::mk_nat(0))
                    .collect::<Vec<_>>();
                fields[ir::LCNF_PARAM_FVAR_ID] = id;
                fields[ir::LCNF_PARAM_BINDER_NAME] = binder;
                fields[ir::LCNF_PARAM_TYPE] = type_;
                let mut scalars = [0; ir::LCNF_PARAM_SCALAR_BYTES];
                scalars[ir::LCNF_PARAM_BORROW_SCALAR] = u8::from(param.borrow);
                params.push(self.ctor(0, fields, &scalars)?);

                let mut fields = (0..ir::PARAM_POINTERS)
                    .map(|_| Obj::mk_nat(0))
                    .collect::<Vec<_>>();
                fields[ir::PARAM_X] = self.nat_u64(param.x)?;
                fields[ir::PARAM_TY] = Obj::mk_nat(usize::from(carrier(&param.ty)?.1));
                let mut scalars = [0; ir::PARAM_SCALAR_BYTES];
                scalars[ir::PARAM_BORROW_SCALAR] = u8::from(param.borrow);
                ir_params.push(self.ctor(0, fields, &scalars)?);
            }
            let name = self.name(&row.name)?;
            let type_ = self.compiler_type(&row.result)?;
            let params = self.array(params)?;
            // Signature: name, empty monomorphic level list, return type,
            // parameter array, then the packed safety byte.
            let mut fields = (0..ir::LCNF_SIGNATURE_POINTERS)
                .map(|_| Obj::mk_nat(0))
                .collect::<Vec<_>>();
            fields[ir::LCNF_SIGNATURE_NAME] = name.clone_ref();
            fields[ir::LCNF_SIGNATURE_LEVEL_PARAMS] = Obj::mk_nat(0);
            fields[ir::LCNF_SIGNATURE_TYPE] = type_;
            fields[ir::LCNF_SIGNATURE_PARAMS] = params;
            let mut scalars = [0; ir::LCNF_SIGNATURE_SCALAR_BYTES];
            scalars[ir::LCNF_SIGNATURE_SAFE_SCALAR] = u8::from(row.safe);
            signatures.push(self.ctor(0, fields, &scalars)?);

            let mut fields = (0..ir::DECL_EXTERN_POINTERS)
                .map(|_| Obj::mk_nat(0))
                .collect::<Vec<_>>();
            fields[ir::DECL_EXTERN_F] = name;
            fields[ir::DECL_EXTERN_XS] = self.array(ir_params)?;
            fields[ir::DECL_EXTERN_TYPE] = Obj::mk_nat(usize::from(carrier(&row.result)?.1));
            // ExternAttrData is the List itself, not another wrapper object.
            fields[ir::DECL_EXTERN_EXT] =
                self.list(vec![Obj::mk_nat(usize::from(ir::EXTERN_ENTRY_OPAQUE))])?;
            headers.push(self.ctor(ir::DECL_EXTERN, fields, &[])?);
        }
        Ok(vec![
            self.compiler_extension(ir::LCNF_IMPURE_SIGNATURE_EXTENSION, signatures)?,
            self.compiler_extension(ir::DECL_MAP_EXTENSION, headers)?,
        ])
    }
}

#[cfg(test)]
mod tests;
