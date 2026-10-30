//! Data-only decoding of the pin's registered macro journal.
//!
//! The payload has the same extracted scoped `KeyedDeclsAttribute.OLeanEntry`
//! layout as application unexpanders. This separate decoder does not activate
//! a macro, classify code, or change source-import metadata/cache semantics.
use super::{DecodeError, DecodeLimits, Reader, Refusal, limit, shape};
use crate::region::OpaqueExtensionBlock;
use fln_core::name::Name;
use fln_rt::convert::Conversion;
use fln_rt::region::{audit, materialize};
use std::collections::BTreeSet;

#[path = "macro_registration_format.rs"]
mod format;
pub use format::MACRO_EXTENSION;

/// One registration, in the order exported by its owning module.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MacroEntry {
    pub key: Name,
    pub declaration: Name,
    /// `Some` requires explicit namespace activation by a later consumer.
    pub scope: Option<Name>,
}

/// Decode one complete module journal. Unknown extensions remain untouched.
pub fn decode(
    blocks: &[OpaqueExtensionBlock],
    limits: DecodeLimits,
) -> Result<Vec<MacroEntry>, DecodeError> {
    Decoder::new(limits).decode(blocks)
}

/// An import sequence shares its entry, byte, object and Name walk allowances.
/// A refused batch poisons the decoder; no later batch exposes a partial import.
pub struct Decoder {
    remaining: DecodeLimits,
    reader: Reader,
    refusal: Option<Refusal>,
}

impl Decoder {
    pub fn new(limits: DecodeLimits) -> Self {
        Self {
            remaining: limits,
            reader: Reader {
                conversion: Conversion::new(),
                indices_left: limits.max_indices,
                keys_left: limits.max_keys,
            },
            refusal: None,
        }
    }

    pub fn remaining_limits(&self) -> DecodeLimits {
        self.remaining
    }

    pub fn decode(
        &mut self,
        blocks: &[OpaqueExtensionBlock],
    ) -> Result<Vec<MacroEntry>, DecodeError> {
        if let Some(refusal) = self.refusal {
            return Err(match refusal {
                Refusal::Resource => limit("macro decoder after resource exhaustion"),
                Refusal::Malformed => shape("macro decoder reused after refusal"),
            });
        }
        let result = self.decode_batch(blocks);
        if let Err(error) = &result {
            self.refusal = Some(if error.is_resource() {
                Refusal::Resource
            } else {
                Refusal::Malformed
            });
        }
        result
    }

    fn decode_batch(
        &mut self,
        blocks: &[OpaqueExtensionBlock],
    ) -> Result<Vec<MacroEntry>, DecodeError> {
        let wanted = Name::from_components(MACRO_EXTENSION.split('.'));
        let mut seen = BTreeSet::new();
        let mut entries = Vec::new();
        for block in blocks {
            if !seen.insert(&block.name) {
                return Err(shape("duplicate macro metadata extension block"));
            }
            if block.name != wanted {
                continue;
            }
            self.remaining.max_entries = self
                .remaining
                .max_entries
                .checked_sub(block.entries.len())
                .ok_or_else(|| limit("macro entries"))?;
            entries
                .try_reserve_exact(block.entries.len())
                .map_err(|_| limit("macro entry allocation"))?;
            for payload in &block.entries {
                self.remaining.max_bytes = self
                    .remaining
                    .max_bytes
                    .checked_sub(payload.len())
                    .ok_or_else(|| limit("macro payload bytes"))?;
                let audited = audit(payload, 0).map_err(DecodeError::Region)?;
                self.remaining.max_objects = self
                    .remaining
                    .max_objects
                    .checked_sub(audited.objects)
                    .ok_or_else(|| limit("macro objects"))?;
                let object = materialize(payload, 0).map_err(DecodeError::Region)?;
                // Both attributes are instantiated from KeyedDeclsAttribute:
                // reuse its already extracted scope and two-Name projection.
                let row = self.reader.app_unexpander(&object)?;
                entries.push(MacroEntry {
                    key: row.key,
                    declaration: row.declaration,
                    scope: row.scope,
                });
            }
        }
        Ok(entries)
    }
}

#[cfg(test)]
#[path = "macros/tests.rs"]
mod tests;
