//! Data-only `@[deprecated]` payloads: the pin's `deprecatedAttr` (vendored
//! `src/Lean/Linter/Deprecated.lean`), a parametric attribute whose module entries are
//! `(declaration, DeprecationEntry)` pairs. Decoding grants nothing: the importer binds each
//! entry to the module's own admitted declaration before a linter reads it.
use super::externs::string;
use super::*;

/// One `@[deprecated]` registration, in journal order: the declaration and its
/// `DeprecationEntry` (`newName?`, `text?`, `since?`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DeprecationEntry {
    pub declaration: Name,
    pub new_name: Option<Name>,
    pub text: Option<String>,
    pub since: Option<String>,
}

/// An `Option α` field: `none` is the boxed constructor index, `some` a constructor with one
/// object field.
fn option(obj: &Obj) -> Result<Option<Obj>, DecodeError> {
    if obj.is_scalar() {
        return if obj.unbox() == format::OPTION_NONE {
            Ok(None)
        } else {
            Err(shape("unknown Option constructor"))
        };
    }
    constructor(obj, format::OPTION_SOME, format::OPTION_SOME_POINTERS)?;
    field(obj, format::OPTION_SOME_VAL).map(Some)
}

impl Reader {
    pub(super) fn deprecation(&mut self, obj: &Obj) -> Result<DeprecationEntry, DecodeError> {
        constructor(obj, 0, format::PROD_POINTERS)?;
        let declaration = self.name(&field(obj, format::PROD_FST)?)?;
        let entry = field(obj, format::PROD_SND)?;
        constructor(&entry, 0, format::DEPRECATION_POINTERS)?;
        let new_name = option(&field(&entry, format::DEPRECATION_NEW_NAME_OPTION)?)?
            .map(|name| self.name(&name))
            .transpose()?;
        let text = option(&field(&entry, format::DEPRECATION_TEXT_OPTION)?)?
            .map(|text| string(&text))
            .transpose()?;
        let since = option(&field(&entry, format::DEPRECATION_SINCE_OPTION)?)?
            .map(|since| string(&since))
            .transpose()?;
        Ok(DeprecationEntry {
            declaration,
            new_name,
            text,
            since,
        })
    }
}
