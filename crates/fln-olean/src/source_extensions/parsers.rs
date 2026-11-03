//! Data-only decoding of the pin's complete parser-extension journal.
//!
//! Every token, syntax kind, category and parser registration remains in its
//! exported order and scope. Decoding does not activate a grammar, evaluate a
//! parser declaration, or grant authority to a same-named ambient declaration.
use super::{
    DecodeError, DecodeLimits, Refusal, constructor, field, format, limit, natural, shape,
};
use crate::region::OpaqueExtensionBlock;
use fln_core::name::Name;
use fln_rt::convert::Conversion;
use fln_rt::obj::Obj;
use fln_rt::region::{audit, materialize};
use std::collections::BTreeSet;

pub use format::{
    PARSER_BOOL_CONSTRUCTOR_FIELDS, PARSER_DESCR_CONSTRUCTOR_FIELDS, PARSER_DESCR_CONSTRUCTORS,
    PARSER_DESCR_TYPE, PARSER_EXTENSION, PARSER_NAME_CONSTRUCTOR_FIELDS, PARSER_NAME_LITERAL_FORMS,
    PARSER_NAT_CONSTRUCTOR_FIELDS, PARSER_NAT_LITERAL_INSTANCE, PARSER_NAT_LITERAL_PROJECTION,
    PARSER_TYPE, PARSER_TYPE_ALIASES, TRAILING_PARSER_DESCR_TYPE, TRAILING_PARSER_TYPE,
};

/// The pin's category dispatch policy for a leading identifier token.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LeadingIdentBehavior {
    Default,
    Symbol,
    Both,
}

/// One complete module's selected journal. Repeated entries are significant.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct ModuleParsers {
    pub entries: Vec<ParserEntry>,
}

impl ModuleParsers {
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }
}

/// One scoped or global row in the original artifact order.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParserEntry {
    /// Scoped rows remain dormant until a consumer activates this namespace.
    pub scope: Option<Name>,
    pub kind: ParserEntryKind,
}

/// All four constructors of `Lean.Parser.ParserExtension.OLeanEntry`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ParserEntryKind {
    Token(String),
    Kind(Name),
    Category {
        category: Name,
        declaration: Name,
        behavior: LeadingIdentBehavior,
    },
    Parser {
        category: Name,
        declaration: Name,
        priority: u32,
    },
}

/// The pin-extracted, structural extension identity.
pub fn extension_name() -> Name {
    Name::from_components(PARSER_EXTENSION.split('.'))
}

/// Decode a complete selected journal, leaving unrelated extension families
/// uninterpreted. Names and tokens remain data; semantic validity is the
/// responsibility of the owner-checked grammar installer.
pub fn decode(
    blocks: &[OpaqueExtensionBlock],
    limits: DecodeLimits,
) -> Result<ModuleParsers, DecodeError> {
    Decoder::new(limits).decode(blocks)
}

/// Import batches share their byte, object, entry and Name walk allowances.
/// Any refusal poisons the decoder, so a caller cannot resume a partial import.
pub struct Decoder {
    remaining: DecodeLimits,
    conversion: Conversion,
    refusal: Option<Refusal>,
}

impl Decoder {
    pub fn new(limits: DecodeLimits) -> Self {
        Self {
            remaining: limits,
            conversion: Conversion::new(),
            refusal: None,
        }
    }

    pub fn remaining_limits(&self) -> DecodeLimits {
        self.remaining
    }

    pub fn decode(
        &mut self,
        blocks: &[OpaqueExtensionBlock],
    ) -> Result<ModuleParsers, DecodeError> {
        if let Some(refusal) = self.refusal {
            return Err(match refusal {
                Refusal::Resource => limit("parser decoder after resource exhaustion"),
                Refusal::Malformed => shape("parser decoder reused after refusal"),
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
    ) -> Result<ModuleParsers, DecodeError> {
        let wanted = extension_name();
        let mut seen = BTreeSet::new();
        let mut entries = Vec::new();
        for block in blocks {
            if !seen.insert(&block.name) {
                return Err(shape("duplicate parser metadata extension block"));
            }
            if block.name != wanted {
                continue;
            }
            self.remaining.max_entries = self
                .remaining
                .max_entries
                .checked_sub(block.entries.len())
                .ok_or_else(|| limit("parser entries"))?;
            entries
                .try_reserve_exact(block.entries.len())
                .map_err(|_| limit("parser entry allocation"))?;
            for payload in &block.entries {
                self.remaining.max_bytes = self
                    .remaining
                    .max_bytes
                    .checked_sub(payload.len())
                    .ok_or_else(|| limit("parser payload bytes"))?;
                let audited = audit(payload, 0).map_err(DecodeError::Region)?;
                self.remaining.max_objects = self
                    .remaining
                    .max_objects
                    .checked_sub(audited.objects)
                    .ok_or_else(|| limit("parser objects"))?;
                let object = materialize(payload, 0).map_err(DecodeError::Region)?;
                entries.push(self.entry(&object)?);
            }
        }
        Ok(ModuleParsers { entries })
    }

    fn name(&mut self, object: &Obj) -> Result<Name, DecodeError> {
        self.conversion
            .project_name(object)
            .map_err(DecodeError::Conversion)
    }

    fn entry(&mut self, object: &Obj) -> Result<ParserEntry, DecodeError> {
        if object.is_scalar() {
            return Err(shape("parser entry lacks its scope wrapper"));
        }
        let (scope, entry) = match object.obj_tag() as u8 {
            format::SCOPE_GLOBAL => {
                constructor(
                    object,
                    format::SCOPE_GLOBAL,
                    format::PARSER_SCOPE_GLOBAL_POINTERS,
                )?;
                (None, field(object, format::PARSER_SCOPE_GLOBAL_ENTRY)?)
            }
            format::SCOPE_SCOPED => {
                constructor(
                    object,
                    format::SCOPE_SCOPED,
                    format::PARSER_SCOPE_SCOPED_POINTERS,
                )?;
                let scope = self.name(&field(object, format::PARSER_SCOPE_SCOPED_NAMESPACE)?)?;
                (
                    Some(scope),
                    field(object, format::PARSER_SCOPE_SCOPED_ENTRY)?,
                )
            }
            _ => return Err(shape("unknown parser scope tag")),
        };
        if entry.is_scalar() {
            return Err(shape("parser journal row is not a constructor"));
        }
        let kind = match entry.obj_tag() as u8 {
            format::PARSER_ENTRY_TOKEN => {
                constructor(
                    &entry,
                    format::PARSER_ENTRY_TOKEN,
                    format::PARSER_TOKEN_POINTERS,
                )?;
                ParserEntryKind::Token(string(&field(&entry, format::PARSER_TOKEN_VAL)?)?)
            }
            format::PARSER_ENTRY_KIND => {
                constructor(
                    &entry,
                    format::PARSER_ENTRY_KIND,
                    format::PARSER_KIND_POINTERS,
                )?;
                ParserEntryKind::Kind(self.name(&field(&entry, format::PARSER_KIND_VAL)?)?)
            }
            format::PARSER_ENTRY_CATEGORY => {
                constructor(
                    &entry,
                    format::PARSER_ENTRY_CATEGORY,
                    format::PARSER_CATEGORY_POINTERS,
                )?;
                let behavior = entry
                    .try_ctor_scalar_u64(
                        format::PARSER_CATEGORY_POINTERS * 8
                            + format::PARSER_CATEGORY_BEHAVIOR_SCALAR,
                    )
                    .ok_or_else(|| shape("parser category lacks its identifier behavior"))?
                    as u8;
                let behavior = match behavior {
                    format::PARSER_IDENT_DEFAULT => LeadingIdentBehavior::Default,
                    format::PARSER_IDENT_SYMBOL => LeadingIdentBehavior::Symbol,
                    format::PARSER_IDENT_BOTH => LeadingIdentBehavior::Both,
                    _ => return Err(shape("unknown parser identifier behavior")),
                };
                ParserEntryKind::Category {
                    category: self.name(&field(&entry, format::PARSER_CATEGORY_CAT_NAME)?)?,
                    declaration: self.name(&field(&entry, format::PARSER_CATEGORY_DECL_NAME)?)?,
                    behavior,
                }
            }
            format::PARSER_ENTRY_PARSER => {
                constructor(
                    &entry,
                    format::PARSER_ENTRY_PARSER,
                    format::PARSER_PARSER_POINTERS,
                )?;
                ParserEntryKind::Parser {
                    category: self.name(&field(&entry, format::PARSER_PARSER_CAT_NAME)?)?,
                    declaration: self.name(&field(&entry, format::PARSER_PARSER_DECL_NAME)?)?,
                    priority: natural(&field(&entry, format::PARSER_PARSER_PRIO)?)?,
                }
            }
            _ => return Err(shape("unknown parser journal constructor")),
        };
        Ok(ParserEntry { scope, kind })
    }
}

fn string(object: &Obj) -> Result<String, DecodeError> {
    let Some((size, _, length, bytes)) = object.try_string_view() else {
        return Err(shape("parser token is not a String"));
    };
    let content = size
        .checked_sub(1)
        .and_then(|length| bytes.get(..length))
        .ok_or_else(|| shape("parser token has an invalid String size"))?;
    if bytes.get(content.len()) != Some(&0) {
        return Err(shape("parser token String lacks its terminator"));
    }
    let content =
        std::str::from_utf8(content).map_err(|_| shape("parser token String is not UTF-8"))?;
    if content.chars().count() != length {
        return Err(shape(
            "parser token String has an inconsistent character count",
        ));
    }
    let mut token = String::new();
    token
        .try_reserve_exact(content.len())
        .map_err(|_| limit("parser token allocation"))?;
    token.push_str(content);
    Ok(token)
}

#[cfg(test)]
#[path = "parsers/tests.rs"]
mod tests;
