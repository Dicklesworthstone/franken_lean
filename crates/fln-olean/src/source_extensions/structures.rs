//! The pin's structure journal, retaining field and direct-parent identities.
//!
//! This module only decodes data. Constructor/projection ownership and agreement
//! with admitted declarations are checked by the source importer.
use super::*;
use fln_core::expr::BinderInfo;
use fln_core::name::LeafView;
use std::collections::BTreeMap;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StructureField {
    pub name: Name,
    pub projection: Name,
    pub subobject: Option<Name>,
    pub binder_info: BinderInfo,
    /// Deprecated at the pin; retained as data, never executed by this decoder.
    pub auto_param: Option<Expr>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StructureParent {
    pub name: Name,
    pub subobject: bool,
    pub projection: Name,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StructureEntry {
    pub name: Name,
    /// In physical constructor order, after checking the sorted field-info array
    /// is a bijection with the pin's separate fieldNames array.
    pub fields: Vec<StructureField>,
    /// The extends-clause order, distinct from the physical subobjects.
    pub parents: Vec<StructureParent>,
}

fn scalar_byte(obj: &Obj, pointers: usize, offset: usize) -> Result<u8, DecodeError> {
    obj.try_ctor_scalar_u64(pointers * 8 + offset)
        .map(|word| word as u8)
        .ok_or_else(|| shape("missing structure scalar field"))
}

impl Reader {
    fn optional_name(&mut self, obj: &Obj) -> Result<Option<Name>, DecodeError> {
        if obj.is_scalar() {
            return if obj.unbox() == 0 {
                Ok(None)
            } else {
                Err(shape("unknown field-less Option Name"))
            };
        }
        constructor(obj, 1, 1)?;
        Ok(Some(self.name(&field(obj, 0)?)?))
    }

    fn optional_expr(&mut self, obj: &Obj) -> Result<Option<Expr>, DecodeError> {
        if obj.is_scalar() {
            return if obj.unbox() == 0 {
                Ok(None)
            } else {
                Err(shape("unknown field-less Option Expr"))
            };
        }
        constructor(obj, 1, 1)?;
        let mut heap = NativeHeap::new();
        let value = self
            .conversion
            .project_expr(&mut heap, &field(obj, 0)?)
            .map_err(DecodeError::Conversion)?;
        Ok(Some(
            heap.get(value)
                .map_err(|_| shape("projected structure expression is missing"))?
                .clone(),
        ))
    }

    fn structure_field(&mut self, obj: &Obj) -> Result<StructureField, DecodeError> {
        constructor(obj, 0, format::STRUCTURE_FIELD_POINTERS)?;
        let name = self.name(&field(obj, format::STRUCTURE_FIELD_FIELD_NAME)?)?;
        if !name.parent().is_anonymous()
            || !matches!(name.leaf_view(), LeafView::Str(component) if !component.is_empty())
        {
            return Err(shape("structure field name is not one string component"));
        }
        let binder_info = match scalar_byte(
            obj,
            format::STRUCTURE_FIELD_POINTERS,
            format::STRUCTURE_FIELD_BINDER_INFO_SCALAR,
        )? {
            format::BINDER_DEFAULT => BinderInfo::Default,
            format::BINDER_IMPLICIT => BinderInfo::Implicit,
            format::BINDER_STRICT_IMPLICIT => BinderInfo::StrictImplicit,
            format::BINDER_INST_IMPLICIT => BinderInfo::InstImplicit,
            _ => return Err(shape("unknown structure field binder information")),
        };
        Ok(StructureField {
            name,
            projection: self.name(&field(obj, format::STRUCTURE_FIELD_PROJ_FN)?)?,
            subobject: self
                .optional_name(&field(obj, format::STRUCTURE_FIELD_SUBOBJECT_OPTION)?)?,
            binder_info,
            auto_param: self
                .optional_expr(&field(obj, format::STRUCTURE_FIELD_AUTO_PARAM_OPTION)?)?,
        })
    }

    fn structure_parent(&mut self, obj: &Obj) -> Result<StructureParent, DecodeError> {
        constructor(obj, 0, format::STRUCTURE_PARENT_POINTERS)?;
        let subobject = match scalar_byte(
            obj,
            format::STRUCTURE_PARENT_POINTERS,
            format::STRUCTURE_PARENT_SUBOBJECT_SCALAR,
        )? {
            0 => false,
            1 => true,
            _ => return Err(shape("structure parent subobject flag is not Bool")),
        };
        Ok(StructureParent {
            name: self.name(&field(obj, format::STRUCTURE_PARENT_STRUCT_NAME)?)?,
            subobject,
            projection: self.name(&field(obj, format::STRUCTURE_PARENT_PROJ_FN)?)?,
        })
    }

    pub(super) fn structure(
        &mut self,
        obj: &Obj,
        entries_left: &mut usize,
    ) -> Result<StructureEntry, DecodeError> {
        constructor(obj, 0, format::STRUCTURE_POINTERS)?;
        let name = self.name(&field(obj, format::STRUCTURE_STRUCT_NAME)?)?;
        let names = field(obj, format::STRUCTURE_FIELD_NAMES)?;
        let infos = field(obj, format::STRUCTURE_FIELD_INFO)?;
        let parents = field(obj, format::STRUCTURE_PARENT_INFO)?;
        let count = array_length(&names)?;
        if array_length(&infos)? != count {
            return Err(shape("structure field inventories have different lengths"));
        }
        let parent_count = array_length(&parents)?;
        let cells = count
            .checked_mul(2)
            .and_then(|count| count.checked_add(parent_count))
            .ok_or_else(|| limit("structure field and parent cells"))?;
        *entries_left = entries_left
            .checked_sub(cells)
            .ok_or_else(|| limit("structure field and parent cells"))?;
        // Charge all three arrays before allocating any output. The Name and
        // Expr conversions share the decoder's cumulative conversion meter.
        let mut ordered = BTreeMap::new();
        let mut previous: Option<Name> = None;
        for index in 0..count {
            let row = self.structure_field(&infos.array_child(index))?;
            if previous
                .as_ref()
                .is_some_and(|previous| !previous.quick_lt(&row.name))
            {
                return Err(shape("structure field information is not strictly sorted"));
            }
            previous = Some(row.name.clone());
            if ordered.insert(row.name.clone(), row).is_some() {
                return Err(shape("duplicate structure field information"));
            }
        }
        let mut fields = Vec::new();
        fields
            .try_reserve_exact(count)
            .map_err(|_| limit("structure field allocation"))?;
        for index in 0..count {
            let label = self.name(&names.array_child(index))?;
            fields.push(
                ordered
                    .remove(&label)
                    .ok_or_else(|| shape("structure field order is not a bijection"))?,
            );
        }
        if !ordered.is_empty() {
            return Err(shape("structure field order omits field information"));
        }
        let mut parent_rows = Vec::new();
        parent_rows
            .try_reserve_exact(parent_count)
            .map_err(|_| limit("structure parent allocation"))?;
        let mut seen = BTreeSet::new();
        for index in 0..parent_count {
            let row = self.structure_parent(&parents.array_child(index))?;
            if !seen.insert(row.name.clone()) {
                return Err(shape("duplicate direct structure parent"));
            }
            parent_rows.push(row);
        }
        Ok(StructureEntry {
            name,
            fields,
            parents: parent_rows,
        })
    }
}
