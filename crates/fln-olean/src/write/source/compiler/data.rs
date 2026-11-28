//! Cross-module compiler caches for the checked closed-data ABI.
//!
//! The pin's `LCNF.compileInductives` fills five MapDeclarationExtensions.
//! Their readers deliberately have no fallback for an imported inductive or
//! constructor. A function signature alone therefore cannot make a freshly
//! written data type usable by a downstream compiler.
//!
//! This projection follows `MonoTypes.lean`, `Irrelevant.lean` and
//! `ToImpureType.lean` for monomorphic Type0 families whose relevant fields
//! are exactly Nat/String/Bool or a direct recursive occurrence of the family.
//! Nonrecursive single-field wrappers use their underlying field's carrier and
//! persist both trivial-structure caches. Erased fields, wider scalars, annotated
//! field domains, aliases, dependencies and mutual families are excluded.
//! Runtime builtin families and Name's computed-field layout are also excluded.
//! Object fields precede Bool scalar bytes; each group preserves source order.
//! The layout records are extracted from `ToImpureType.lean` and `Irrelevant.lean`.
//! A separate metadata-only projection covers computed implementations with
//! fixed-width unsigned caches and fields retaining their logical family type.
//! It does not widen the ordinary runtime signature/constructor ABI classifier.

use super::*;
use fln_core::expr::BinderInfo;
use fln_env::constants::InductiveVal;

mod words;

/// A projected data interface. Its fields are private so callers cannot attach
/// an arbitrary layout to an admitted declaration. Construction checks the
/// exact supported shape; it does not itself admit the supplied constants.
#[derive(Debug, Clone)]
pub struct CompilerData {
    name: Name,
    carrier: IrType,
    recursive: bool,
    constructors: Vec<DataConstructor>,
}

#[derive(Debug, Clone)]
struct DataConstructor {
    name: Name,
    mono_type: Expr,
    fields: Vec<IrType>,
}

#[derive(Clone, Copy)]
enum DataProfile<'a> {
    Runtime,
    Computed {
        logical: &'a Name,
        carrier: Option<&'a IrType>,
    },
}

fn scalar_size(ty: &IrType) -> Option<u64> {
    match ty {
        IrType::UInt8 => Some(1),
        IrType::UInt16 => Some(2),
        IrType::UInt32 => Some(4),
        IrType::UInt64 => Some(8),
        _ => None,
    }
}

fn without_metadata<'a, E>(
    mut value: &'a Expr,
    charge: &mut impl FnMut(usize) -> Result<(), E>,
) -> Result<&'a Expr, E> {
    while let ExprNode::MData { expr, .. } = value.node() {
        charge(1)?;
        value = expr;
    }
    Ok(value)
}

// These types use runtime representations that their logical constructor
// telescopes do not completely describe. Keep the exact builtin list from
// LCNF/Util.lean; Lean.Name additionally stores Prelude's computed hash field.
fn runtime_special_family(name: &Name) -> bool {
    [
        "String",
        "UInt8",
        "UInt16",
        "UInt32",
        "UInt64",
        "USize",
        "Float",
        "Float32",
        "Thunk",
        "Task",
        "Array",
        "ByteArray",
        "FloatArray",
        "Nat",
        "Int",
        "Lean.Name",
    ]
    .into_iter()
    .any(|builtin| name == &Name::from_components(builtin.split('.')))
}

impl CompilerData {
    /// The declaration owning these compiler caches.
    pub fn name(&self) -> &Name {
        &self.name
    }

    /// Whether constructors contain direct occurrences of their own family.
    pub fn is_recursive(&self) -> bool {
        self.recursive
    }

    /// The pin's source-facing carrier for this checked layout.
    pub fn carrier(&self) -> &IrType {
        &self.carrier
    }

    /// The sole relevant field when the pin erases this constructor wrapper.
    /// Its persisted constructor layout still describes the source field;
    /// consumers must distinguish that cache from the actual value carrier.
    pub fn unboxed_field(&self) -> Option<&IrType> {
        // A recursive singleton retains its constructor allocation. Only a
        // nonrecursive primitive field can erase the enclosing family here.
        if self.recursive {
            return None;
        }
        let [constructor] = self.constructors.as_slice() else {
            return None;
        };
        let [field] = constructor.fields.as_slice() else {
            return None;
        };
        Some(field)
    }

    /// Canonical constructor order and its field carriers in source order.
    /// Consumers can reserve these layouts without another shape classifier;
    /// Unsigned fields occupy packed scalar bytes, not object slots.
    pub fn constructors(&self) -> impl ExactSizeIterator<Item = (&Name, &[IrType])> {
        self.constructors
            .iter()
            .map(|constructor| (&constructor.name, constructor.fields.as_slice()))
    }

    /// Project one module-owned inductive from an already checked environment.
    /// The lookup must resolve its actual constructor declarations; the caller
    /// charges this traversal to its source/admission budget. Unsupported
    /// layouts return `None` instead of claiming that the pin compiled them.
    pub fn from_inductive<'a, E>(
        inductive: &InductiveVal,
        mut find: impl FnMut(&Name) -> Option<&'a ConstantInfo>,
        mut charge: impl FnMut(usize) -> Result<(), E>,
    ) -> Result<Option<Self>, E> {
        Self::project(inductive, &mut find, &mut charge, DataProfile::Runtime)
    }

    /// Project compiler metadata for a checked computed-field family or its
    /// generated implementation. The caller must separately validate the
    /// complete computed-field declaration and attribute inventory before
    /// publishing an artifact. This method proves only the constructor layout.
    ///
    /// A computed implementation retains its original logical field types.
    /// Resolve those fields through the complete logical family's carrier;
    /// never infer a heap layout from the `_impl` spelling alone. Wider unsigned
    /// fields are supported here without authorizing their use by native FIR.
    pub fn from_computed_inductive<'a, E>(
        inductive: &InductiveVal,
        logical: &InductiveVal,
        mut find: impl FnMut(&Name) -> Option<&'a ConstantInfo>,
        mut charge: impl FnMut(usize) -> Result<(), E>,
    ) -> Result<Option<Self>, E> {
        charge(1)?;
        if logical.ctors.len() < 2 {
            return Ok(None);
        }
        let Some(logical_data) = Self::project(
            logical,
            &mut find,
            &mut charge,
            DataProfile::Computed {
                logical: &logical.base.name,
                carrier: None,
            },
        )?
        else {
            return Ok(None);
        };
        if inductive.base.name == logical.base.name {
            return Ok((inductive == logical).then_some(logical_data));
        }
        if inductive.base.name != Name::str(logical.base.name.clone(), "_impl")
            || inductive.is_rec
            || inductive.ctors.len() != logical.ctors.len()
        {
            return Ok(None);
        }
        for (implementation, original) in inductive.ctors.iter().zip(&logical.ctors) {
            charge(1)?;
            if implementation != &Name::str(original.clone(), "_impl") {
                return Ok(None);
            }
        }
        Self::project(
            inductive,
            &mut find,
            &mut charge,
            DataProfile::Computed {
                logical: &logical.base.name,
                carrier: Some(&logical_data.carrier),
            },
        )
    }

    /// Capture both logical and implementation interfaces before a public
    /// projection hides implementation bodies. The ordinary runtime ABI
    /// classifier remains unchanged; all computed scalar widths are retained.
    pub fn from_computed_family<'a, E>(
        logical: &InductiveVal,
        implementation: &InductiveVal,
        mut find: impl FnMut(&Name) -> Option<&'a ConstantInfo>,
        mut charge: impl FnMut(usize) -> Result<(), E>,
    ) -> Result<Option<[Self; 2]>, E> {
        charge(1)?;
        if implementation.base.name != Name::str(logical.base.name.clone(), "_impl") {
            return Ok(None);
        }
        let Some(original) =
            Self::from_computed_inductive(logical, logical, &mut find, &mut charge)?
        else {
            return Ok(None);
        };
        let Some(physical) =
            Self::from_computed_inductive(implementation, logical, &mut find, &mut charge)?
        else {
            return Ok(None);
        };
        Ok(Some([original, physical]))
    }

    /// Validate an admitted structural UIntN/BitVec/Fin carrier before a
    /// native source module publishes packed word fields. The caller also
    /// reduces the actual finite bound and relation with its checked reducer.
    /// Metadata-only readers may inspect pin layouts without granting any
    /// executable or cast authority from those layouts.
    pub fn validate_unsigned_word_model<'a, E>(
        width: u32,
        mut find: impl FnMut(&Name) -> Option<&'a ConstantInfo>,
        mut charge: impl FnMut(usize) -> Result<(), E>,
    ) -> Result<bool, E> {
        words::unsigned_word_matches(width, &mut find, &mut charge)
    }

    fn project<'a, E>(
        inductive: &InductiveVal,
        find: &mut impl FnMut(&Name) -> Option<&'a ConstantInfo>,
        charge: &mut impl FnMut(usize) -> Result<(), E>,
        profile: DataProfile<'_>,
    ) -> Result<Option<Self>, E> {
        charge(1)?;
        let name = &inductive.base.name;
        let computed_name = matches!(profile, DataProfile::Computed { logical, .. }
            if name == logical && name == &Name::from_components(["Lean", "Name"]));
        if name.is_anonymous()
            || (runtime_special_family(name) && !computed_name)
            || !inductive.base.level_params.is_empty()
            || inductive.num_params != 0
            || inductive.num_indices != 0
            || inductive.num_nested != 0
            || inductive.is_unsafe
            || inductive.all.as_slice() != std::slice::from_ref(name)
            || inductive.ctors.is_empty()
            || inductive.ctors.len() > usize::from(fln_rt::abi::TAG_MAX_CTOR_TAG) + 1
            || !matches!(without_metadata(&inductive.base.type_, charge)?.node(),
                ExprNode::Sort { level } if level == &Level::one())
        {
            return Ok(None);
        }
        charge(inductive.ctors.len())?;
        let mut constructors = Vec::with_capacity(inductive.ctors.len());
        let mut recursive_fields = Vec::new();
        for (index, ctor_name) in inductive.ctors.iter().enumerate() {
            charge(1)?;
            let Some(ConstantInfo::Ctor(ctor)) = find(ctor_name) else {
                return Ok(None);
            };
            if ctor.base.name != *ctor_name
                || ctor.induct != *name
                || ctor.cidx as usize != index
                || ctor.num_params != 0
                || ctor.is_unsafe
                || !ctor.base.level_params.is_empty()
                // The internal all-boxed representation and lean_alloc_ctor
                // require num_objs < LEAN_MAX_CTOR_FIELDS. Keep this total
                // source-field bound even for packed public layouts, including
                // callbacks without a constructor instruction for FIR to check.
                || ctor.num_fields as usize >= fln_rt::abi::MAX_CTOR_FIELDS
            {
                return Ok(None);
            }
            charge(ctor.num_fields as usize)?;
            let mut fields = Vec::with_capacity(ctor.num_fields as usize);
            let mut binders: Vec<(Name, Expr, BinderInfo)> =
                Vec::with_capacity(ctor.num_fields as usize);
            let mut ty = &ctor.base.type_;
            loop {
                charge(1)?;
                ty = without_metadata(ty, charge)?;
                let ExprNode::ForallE {
                    binder_name,
                    binder_type,
                    body,
                    binder_info,
                } = ty.node()
                else {
                    break;
                };
                // toLCNFType.visitForall can retain a `borrowed` annotation.
                // Its mono type is not the plain constant inferred by stripping
                // metadata. Keep annotated domains outside this exact profile.
                let field_type = binder_type;
                let field = match field_type.node() {
                    ExprNode::Const {
                        name: field_name,
                        levels,
                    } if inductive.is_rec && levels.is_empty() && field_name == name => {
                        // compileInductives computes the complete family carrier
                        // before its constructor layouts. Resolve this slot once
                        // all constructors have established whether nullary tags
                        // coexist with heap objects.
                        recursive_fields.push((index, fields.len()));
                        IrType::Object
                    }
                    ExprNode::Const { name, levels }
                        if levels.is_empty() && name == &Name::from_components(["Nat"]) =>
                    {
                        IrType::TObject
                    }
                    ExprNode::Const { name, levels }
                        if levels.is_empty() && name == &Name::from_components(["String"]) =>
                    {
                        IrType::Object
                    }
                    ExprNode::Const { name, levels }
                        if levels.is_empty() && name == &Name::from_components(["Bool"]) =>
                    {
                        IrType::UInt8
                    }
                    ExprNode::Const {
                        name: field_name,
                        levels,
                    } if levels.is_empty() && matches!(profile, DataProfile::Computed { .. }) => {
                        match field_name {
                            name if name == &Name::from_components(["UInt8"]) => IrType::UInt8,
                            name if name == &Name::from_components(["UInt16"]) => IrType::UInt16,
                            name if name == &Name::from_components(["UInt32"]) => IrType::UInt32,
                            name if name == &Name::from_components(["UInt64"]) => IrType::UInt64,
                            name => {
                                let DataProfile::Computed {
                                    logical,
                                    carrier: Some(carrier),
                                } = profile
                                else {
                                    return Ok(None);
                                };
                                if name != logical {
                                    return Ok(None);
                                }
                                carrier.clone()
                            }
                        }
                    }
                    _ => return Ok(None),
                };
                if fields.len() >= ctor.num_fields as usize {
                    return Ok(None);
                }
                fields.push(field);
                binders.push((binder_name.clone(), field_type.clone(), *binder_info));
                ty = body;
            }
            if fields.len() != ctor.num_fields as usize
                || !matches!(ty.node(), ExprNode::Const { name: result, levels }
                    if result == name && levels.is_empty())
            {
                return Ok(None);
            }
            // MonoTypes.toMonoType recursively removes a trivial wrapper
            // from the constructor result as well as from its uses. Recursive
            // singletons are not trivial structures and keep the family result.
            let result_type =
                if !inductive.is_rec && inductive.ctors.len() == 1 && binders.len() == 1 {
                    binders[0].1.clone()
                } else {
                    Expr::const_(name.clone(), Vec::new())
                };
            let mono_type = binders
                .into_iter()
                .rev()
                .fold(result_type, |body, (name, ty, info)| {
                    Expr::forall_e(name, ty, body, info)
                });
            constructors.push(DataConstructor {
                name: ctor_name.clone(),
                mono_type,
                fields,
            });
        }
        if inductive.is_rec != !recursive_fields.is_empty() {
            return Ok(None);
        }
        let nullary = constructors
            .iter()
            .filter(|ctor| ctor.fields.is_empty())
            .count();
        let carrier =
            if !inductive.is_rec && constructors.len() == 1 && constructors[0].fields.len() == 1 {
                constructors[0].fields[0].clone()
            } else if nullary == constructors.len() {
                if constructors.len() == 1 {
                    IrType::Tagged
                } else {
                    IrType::UInt8
                }
            } else if nullary == 0 {
                IrType::Object
            } else {
                IrType::TObject
            };
        for (constructor, field) in recursive_fields {
            charge(1)?;
            constructors[constructor].fields[field] = carrier.clone();
        }
        Ok(Some(Self {
            name: name.clone(),
            carrier,
            recursive: inductive.is_rec,
            constructors,
        }))
    }
}

fn private_extension(module: &str, leaf: &str) -> Name {
    let owner = Name::num(
        Name::from_components(["_private", "Lean", "Compiler", "LCNF", module]),
        0,
    );
    ["Lean", "Compiler", "LCNF", leaf]
        .into_iter()
        .fold(owner, Name::str)
}

// `decl_name%` in mkMapDeclarationExtension retains numeric private-name
// components. These are the actual initializer names in the pinned generated
// MonoTypes.c/ToImpureType.c, not their unqualified source spellings.
fn extension_names() -> [Name; 5] {
    [
        private_extension("MonoTypes", "trivialStructureInfoExt"),
        private_extension("ToImpureType", "impureTrivialStructureInfoExt"),
        Name::from_components(["Lean", "Compiler", "LCNF", "monoTypeExt"]),
        private_extension("ToImpureType", "impureTypeExt"),
        private_extension("ToImpureType", "ctorLayoutExt"),
    ]
}

impl Encoder {
    fn compiler_data_trivial(&mut self, row: &CompilerData) -> WResult<Obj> {
        if row.unboxed_field().is_none() {
            return Ok(Obj::mk_nat(layout::OPTION_NONE));
        }
        let mut fields = (0..ir::LCNF_TRIVIAL_STRUCTURE_INFO_POINTERS)
            .map(|_| Obj::mk_nat(0))
            .collect::<Vec<_>>();
        fields[ir::LCNF_TRIVIAL_STRUCTURE_INFO_CTOR_NAME] = self.name(&row.constructors[0].name)?;
        // This exact profile has no parameters and one relevant field at zero.
        fields[ir::LCNF_TRIVIAL_STRUCTURE_INFO_NUM_PARAMS] = Obj::mk_nat(0);
        fields[ir::LCNF_TRIVIAL_STRUCTURE_INFO_FIELD_IDX] = Obj::mk_nat(0);
        let info = self.ctor(0, fields, &[])?;
        let mut fields = (0..layout::OPTION_SOME_POINTERS)
            .map(|_| Obj::mk_nat(0))
            .collect::<Vec<_>>();
        fields[layout::OPTION_SOME_VAL] = info;
        self.ctor(layout::OPTION_SOME, fields, &[])
    }

    fn compiler_data_map(&mut self, key: &Name, mut entries: Vec<(Name, Obj)>) -> WResult<Obj> {
        self.source_array_bound(entries.len())?;
        entries.sort_by(|left, right| left.0.quick_cmp(&right.0));
        if entries.iter().any(|entry| entry.0.is_anonymous())
            || entries.windows(2).any(|pair| pair[0].0 == pair[1].0)
        {
            return Err(WriteError::Contract {
                what: "anonymous or duplicate compiler data entry",
            });
        }
        let mut values = Vec::with_capacity(entries.len());
        for (name, value) in entries {
            let name = self.name(&name)?;
            values.push(self.ctor(0, vec![name, value], &[])?);
        }
        let name = self.name(key)?;
        let values = self.array(values)?;
        self.ctor(0, vec![name, values], &[])
    }

    pub(in crate::write::source) fn compiler_data_blocks(
        &mut self,
        data: &[CompilerData],
    ) -> WResult<Vec<Obj>> {
        if format::PIN_COMMIT != "8c9756b28d64dab099da31a4c09229a9e6a2ef35" {
            return Err(WriteError::Unsupported {
                what: "LCNF data layouts have not been audited for this pin",
            });
        }
        self.source_array_bound(data.len())?;
        let mut maps: [Vec<(Name, Obj)>; 5] = std::array::from_fn(|_| Vec::new());
        for row in data {
            maps[0].push((row.name.clone(), self.compiler_data_trivial(row)?));
            maps[1].push((row.name.clone(), self.compiler_data_trivial(row)?));
            maps[2].push((row.name.clone(), self.compiler_type(&IrType::Erased)?));
            // computeImpureType caches the inductive's relevant-constructor
            // shape, even for a trivial wrapper. toImpureType consults the
            // separate trivial cache to obtain its underlying public carrier.
            let cached_carrier = if row.unboxed_field().is_some() {
                &IrType::Object
            } else {
                &row.carrier
            };
            maps[3].push((row.name.clone(), self.compiler_type(cached_carrier)?));
            self.source_array_bound(row.constructors.len())?;
            for (index, ctor) in row.constructors.iter().enumerate() {
                maps[2].push((ctor.name.clone(), self.expression(&ctor.mono_type)?));
                self.source_array_bound(ctor.fields.len())?;
                let mut fields = Vec::with_capacity(ctor.fields.len());
                let mut objects = 0_u64;
                let mut scalar_bytes = 0_u64;
                let mut scalar_offsets = [0_u64; 4];
                // ToImpureType groups scalars by decreasing width, preserving
                // source order within each width. Object indices are assigned
                // independently; offsets within the scalar area start at zero.
                for width in [8_u64, 4, 2, 1] {
                    scalar_offsets[width.trailing_zeros() as usize] = scalar_bytes;
                    scalar_bytes += width
                        * ctor
                            .fields
                            .iter()
                            .filter(|ty| scalar_size(ty) == Some(width))
                            .count() as u64;
                }
                for ty in &ctor.fields {
                    let field = match ty {
                        IrType::Object | IrType::TObject => {
                            let mut slots = (0..ir::LCNF_CTOR_FIELD_OBJECT_POINTERS)
                                .map(|_| Obj::mk_nat(0))
                                .collect::<Vec<_>>();
                            slots[ir::LCNF_CTOR_FIELD_OBJECT_I] = self.nat_u64(objects)?;
                            slots[ir::LCNF_CTOR_FIELD_OBJECT_TYPE] = self.compiler_type(ty)?;
                            objects += 1;
                            self.ctor(ir::LCNF_CTOR_FIELD_OBJECT, slots, &[])?
                        }
                        IrType::UInt8 | IrType::UInt16 | IrType::UInt32 | IrType::UInt64 => {
                            let width = scalar_size(ty).ok_or(WriteError::Contract {
                                what: "unsupported checked scalar width",
                            })?;
                            let offset = &mut scalar_offsets[width.trailing_zeros() as usize];
                            let mut slots = (0..ir::LCNF_CTOR_FIELD_SCALAR_POINTERS)
                                .map(|_| Obj::mk_nat(0))
                                .collect::<Vec<_>>();
                            slots[ir::LCNF_CTOR_FIELD_SCALAR_SZ] = self.nat_u64(width)?;
                            slots[ir::LCNF_CTOR_FIELD_SCALAR_OFFSET] = self.nat_u64(*offset)?;
                            slots[ir::LCNF_CTOR_FIELD_SCALAR_TYPE] = self.compiler_type(ty)?;
                            *offset += width;
                            self.ctor(ir::LCNF_CTOR_FIELD_SCALAR, slots, &[])?
                        }
                        _ => {
                            return Err(WriteError::Contract {
                                what: "unsupported checked compiler data field",
                            });
                        }
                    };
                    fields.push(field);
                }
                let name = self.name(&ctor.name)?;
                let index = self.nat_u64(index as u64)?;
                let size = self.nat_u64(objects)?;
                // CtorInfo is shared with the independently extracted IR
                // contract: name, cidx, object count, usize count, scalar bytes.
                let mut info = (0..ir::CTOR_INFO_POINTERS)
                    .map(|_| Obj::mk_nat(0))
                    .collect::<Vec<_>>();
                info[ir::CTOR_INFO_NAME] = name;
                info[ir::CTOR_INFO_CIDX] = index;
                info[ir::CTOR_INFO_SIZE] = size;
                info[ir::CTOR_INFO_SSIZE] = self.nat_u64(scalar_bytes)?;
                let info = self.ctor(0, info, &[])?;
                let fields = self.array(fields)?;
                let mut slots = (0..ir::LCNF_CTOR_LAYOUT_POINTERS)
                    .map(|_| Obj::mk_nat(0))
                    .collect::<Vec<_>>();
                slots[ir::LCNF_CTOR_LAYOUT_CTOR_INFO] = info;
                slots[ir::LCNF_CTOR_LAYOUT_FIELD_INFO] = fields;
                let layout = self.ctor(0, slots, &[])?;
                maps[4].push((ctor.name.clone(), layout));
            }
        }
        extension_names()
            .into_iter()
            .zip(maps)
            .map(|(key, entries)| self.compiler_data_map(&key, entries))
            .collect()
    }
}

#[cfg(test)]
mod tests;
