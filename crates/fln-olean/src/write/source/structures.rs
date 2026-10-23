//! The pin's structure extension: sorted structures and field lookup indexes,
//! alongside the constructor's field order and the authored extends order.
use super::*;
use fln_core::expr::BinderInfo;
use fln_core::name::LeafView;

impl Encoder {
    fn structure_field(&mut self, field: &StructureField) -> WResult<Obj> {
        if !field.name.parent().is_anonymous()
            || !matches!(field.name.leaf_view(), LeafView::Str(name) if !name.is_empty())
            || field.projection.is_anonymous()
            || field.subobject.as_ref().is_some_and(Name::is_anonymous)
        {
            return Err(WriteError::Contract {
                what: "invalid structure field identity",
            });
        }
        let mut fields: Vec<_> = (0..layout::STRUCTURE_FIELD_POINTERS)
            .map(|_| Obj::mk_nat(0))
            .collect();
        fields[layout::STRUCTURE_FIELD_FIELD_NAME] = self.name(&field.name)?;
        fields[layout::STRUCTURE_FIELD_PROJ_FN] = self.name(&field.projection)?;
        if let Some(parent) = &field.subobject {
            let parent = self.name(parent)?;
            fields[layout::STRUCTURE_FIELD_SUBOBJECT_OPTION] = self.ctor(1, vec![parent], &[])?;
        }
        if let Some(auto_param) = &field.auto_param {
            let auto_param = self.expression(auto_param)?;
            fields[layout::STRUCTURE_FIELD_AUTO_PARAM_OPTION] =
                self.ctor(1, vec![auto_param], &[])?;
        }
        let mut scalars = [0; layout::STRUCTURE_FIELD_SCALAR_BYTES];
        scalars[layout::STRUCTURE_FIELD_BINDER_INFO_SCALAR] = match field.binder_info {
            BinderInfo::Default => layout::BINDER_DEFAULT,
            BinderInfo::Implicit => layout::BINDER_IMPLICIT,
            BinderInfo::StrictImplicit => layout::BINDER_STRICT_IMPLICIT,
            BinderInfo::InstImplicit => layout::BINDER_INST_IMPLICIT,
        };
        self.ctor(0, fields, &scalars)
    }

    fn structure_parent(&mut self, parent: &StructureParent) -> WResult<Obj> {
        if parent.name.is_anonymous() || parent.projection.is_anonymous() {
            return Err(WriteError::Contract {
                what: "invalid structure parent identity",
            });
        }
        let mut fields: Vec<_> = (0..layout::STRUCTURE_PARENT_POINTERS)
            .map(|_| Obj::mk_nat(0))
            .collect();
        fields[layout::STRUCTURE_PARENT_STRUCT_NAME] = self.name(&parent.name)?;
        fields[layout::STRUCTURE_PARENT_PROJ_FN] = self.name(&parent.projection)?;
        let mut scalars = [0; layout::STRUCTURE_PARENT_SCALAR_BYTES];
        scalars[layout::STRUCTURE_PARENT_SUBOBJECT_SCALAR] = u8::from(parent.subobject);
        self.ctor(0, fields, &scalars)
    }

    fn source_structure(&mut self, row: &StructureEntry) -> WResult<Obj> {
        self.source_array_bound(row.fields.len())?;
        self.source_array_bound(row.parents.len())?;
        let mut field_names = Vec::with_capacity(row.fields.len());
        let mut names = HashSet::new();
        let mut projections = HashSet::new();
        let mut subobjects = HashSet::new();
        let mut physical = HashSet::new();
        for field in &row.fields {
            if !names.insert(&field.name) || !projections.insert(&field.projection) {
                return Err(WriteError::Contract {
                    what: "duplicate structure field or projection",
                });
            }
            if let Some(parent) = &field.subobject {
                if parent == &row.name || !subobjects.insert(parent) {
                    return Err(WriteError::Contract {
                        what: "self or duplicate structure subobject",
                    });
                }
                physical.insert((parent, &field.projection));
            }
            field_names.push(self.name(&field.name)?);
        }
        let mut sorted_fields: Vec<_> = row.fields.iter().collect();
        sorted_fields.sort_by(|left, right| left.name.quick_cmp(&right.name));
        let mut field_info = Vec::with_capacity(sorted_fields.len());
        for field in sorted_fields {
            field_info.push(self.structure_field(field)?);
        }
        let mut seen = HashSet::new();
        let mut parents = Vec::with_capacity(row.parents.len());
        for parent in &row.parents {
            if parent.name == row.name || !seen.insert(&parent.name) {
                return Err(WriteError::Contract {
                    what: "self or duplicate structure parent",
                });
            }
            if parent.subobject != physical.contains(&(&parent.name, &parent.projection)) {
                return Err(WriteError::Contract {
                    what: "structure parent physical subobject flag does not match its field",
                });
            }
            parents.push(self.structure_parent(parent)?);
        }
        let mut fields: Vec<_> = (0..layout::STRUCTURE_POINTERS)
            .map(|_| Obj::mk_nat(0))
            .collect();
        fields[layout::STRUCTURE_STRUCT_NAME] = self.name(&row.name)?;
        fields[layout::STRUCTURE_FIELD_NAMES] = self.array(field_names)?;
        fields[layout::STRUCTURE_FIELD_INFO] = self.array(field_info)?;
        fields[layout::STRUCTURE_PARENT_INFO] = self.array(parents)?;
        self.ctor(0, fields, &[0; layout::STRUCTURE_SCALAR_BYTES])
    }

    pub(super) fn structure_block(&mut self, structures: &[StructureEntry]) -> WResult<Obj> {
        self.source_array_bound(structures.len())?;
        let mut sorted: Vec<_> = structures.iter().collect();
        sorted.sort_by(|left, right| left.name.quick_cmp(&right.name));
        if sorted.iter().any(|row| row.name.is_anonymous())
            || sorted.windows(2).any(|pair| pair[0].name == pair[1].name)
        {
            return Err(WriteError::Contract {
                what: "anonymous or duplicate exported structure",
            });
        }
        let mut entries = Vec::with_capacity(sorted.len());
        for row in sorted {
            entries.push(self.source_structure(row)?);
        }
        let entries = self.array(entries)?;
        let name = self.name(&crate::source_extensions::structure_extension_name())?;
        self.ctor(0, vec![name, entries], &[])
    }
}

#[cfg(test)]
mod tests;
