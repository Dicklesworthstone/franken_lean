//! Data-only extern attribute payloads. Decoding is not native-call authority.
use super::*;
use crate::ir_format as entry_format;

/// One pinned `Lean.ExternEntry`, preserving backend selection and entry kind.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExternEntry {
    Adhoc { backend: Name },
    Inline { backend: Name, pattern: String },
    Standard { backend: Name, symbol: String },
    Opaque,
}

/// A declaration's explicit extern attribute, in the imported journal order.
/// An absent attribute is distinct from an attribute with an empty entry list.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExternAttribute {
    pub declaration: Name,
    pub entries: Vec<ExternEntry>,
}

fn string(obj: &Obj) -> Result<String, DecodeError> {
    let Some((size, _, _, bytes)) = obj.try_string_view() else {
        return Err(shape("extern payload is not a String"));
    };
    let Some(length) = size.checked_sub(1) else {
        return Err(shape("extern String has no terminator"));
    };
    let Some(value) = bytes.get(..length) else {
        return Err(shape("extern String has an invalid size"));
    };
    if bytes.get(length) != Some(&0) {
        return Err(shape("extern String has no terminator"));
    }
    std::str::from_utf8(value)
        .map(str::to_owned)
        .map_err(|_| shape("extern String is not UTF-8"))
}

impl Reader {
    fn extern_entry(&mut self, obj: &Obj) -> Result<ExternEntry, DecodeError> {
        if obj.is_scalar() {
            return if obj.unbox() == usize::from(entry_format::EXTERN_ENTRY_OPAQUE) {
                Ok(ExternEntry::Opaque)
            } else {
                Err(shape("unknown field-less ExternEntry"))
            };
        }
        let tag = u8::try_from(obj.obj_tag()).map_err(|_| shape("unknown ExternEntry tag"))?;
        match tag {
            entry_format::EXTERN_ENTRY_ADHOC => {
                constructor(obj, tag, entry_format::EXTERN_ENTRY_ADHOC_POINTERS)?;
                Ok(ExternEntry::Adhoc {
                    backend: self.name(&field(obj, entry_format::EXTERN_ENTRY_ADHOC_BACKEND)?)?,
                })
            }
            entry_format::EXTERN_ENTRY_INLINE => {
                constructor(obj, tag, entry_format::EXTERN_ENTRY_INLINE_POINTERS)?;
                Ok(ExternEntry::Inline {
                    backend: self.name(&field(obj, entry_format::EXTERN_ENTRY_INLINE_BACKEND)?)?,
                    pattern: string(&field(obj, entry_format::EXTERN_ENTRY_INLINE_PATTERN)?)?,
                })
            }
            entry_format::EXTERN_ENTRY_STANDARD => {
                constructor(obj, tag, entry_format::EXTERN_ENTRY_STANDARD_POINTERS)?;
                Ok(ExternEntry::Standard {
                    backend: self
                        .name(&field(obj, entry_format::EXTERN_ENTRY_STANDARD_BACKEND)?)?,
                    symbol: string(&field(obj, entry_format::EXTERN_ENTRY_STANDARD_FN)?)?,
                })
            }
            _ => Err(shape("unknown ExternEntry constructor")),
        }
    }

    pub(super) fn extern_attribute(
        &mut self,
        obj: &Obj,
        entries_left: &mut usize,
    ) -> Result<ExternAttribute, DecodeError> {
        constructor(obj, 0, format::PROD_POINTERS)?;
        let declaration = self.name(&field(obj, format::PROD_FST)?)?;
        let mut cursor = field(obj, format::PROD_SND)?;
        let mut entries = Vec::new();
        loop {
            if cursor.is_scalar() {
                if cursor.unbox() != usize::from(format::LIST_NIL) {
                    return Err(shape("unknown field-less extern List constructor"));
                }
                return Ok(ExternAttribute {
                    declaration,
                    entries,
                });
            }
            constructor(&cursor, format::LIST_CONS, format::LIST_CONS_POINTERS)?;
            // List cells share the batch's entry bound with attribute rows.
            // Charge before reading or allocating a cell, including Opaque
            // entries whose scalar representation adds no audited heap object.
            *entries_left = entries_left
                .checked_sub(1)
                .ok_or_else(|| limit("extern entries"))?;
            entries
                .try_reserve(1)
                .map_err(|_| limit("extern entry allocation"))?;
            entries.push(self.extern_entry(&field(&cursor, format::LIST_CONS_HEAD)?)?);
            cursor = field(&cursor, format::LIST_CONS_TAIL)?;
        }
    }
}
