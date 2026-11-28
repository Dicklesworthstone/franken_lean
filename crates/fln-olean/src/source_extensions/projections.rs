//! Untrusted projection descriptors from the pin's declaration-owned map.
use super::*;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProjectionEntry {
    pub declaration: Name,
    pub constructor: Name,
    pub num_params: u32,
    /// Logical constructor field index, including proof and subobject fields.
    pub field_index: u32,
    /// Whether this projection was generated with an instance receiver.
    pub from_class: bool,
}

impl Reader {
    pub(super) fn projection(&mut self, obj: &Obj) -> Result<ProjectionEntry, DecodeError> {
        constructor(obj, 0, format::PROD_POINTERS)?;
        let declaration = self.name(&field(obj, format::PROD_FST)?)?;
        let info = field(obj, format::PROD_SND)?;
        constructor(&info, 0, format::PROJECTION_POINTERS)?;
        let from_class = info
            .try_ctor_scalar_u64(
                format::PROJECTION_POINTERS * 8 + format::PROJECTION_FROM_CLASS_SCALAR,
            )
            .ok_or_else(|| shape("missing projection class flag"))? as u8;
        let from_class = match from_class {
            0 => false,
            1 => true,
            _ => return Err(shape("invalid projection class flag")),
        };
        Ok(ProjectionEntry {
            declaration,
            constructor: self.name(&field(&info, format::PROJECTION_CTOR_NAME)?)?,
            num_params: natural(&field(&info, format::PROJECTION_NUM_PARAMS)?)?,
            field_index: natural(&field(&info, format::PROJECTION_I)?)?,
            from_class,
        })
    }
}
