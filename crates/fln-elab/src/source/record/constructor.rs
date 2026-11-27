//! Explicit structure constructors use a name relative to the structure, not
//! ordinary namespace lookup (`Lean/Elab/Structure.lean`, `expandCtor`).
use super::*;

fn unsupported(reason: &'static str) -> NatDefinitionElabError {
    failure(SourceInferenceError::UnsupportedRecordConstructor(reason))
}

impl Context {
    /// Apply the ordinary name policy without reparsing the scoped structure
    /// prefix as source syntax. The user name was retained before applying
    /// visibility; numeric macro-scope components remain exactly as authored.
    pub(super) fn record_constructor_name(
        &mut self,
        record: &Name,
        user_record: &Name,
        suffix: &Name,
    ) -> Result<Name, NatDefinitionElabError> {
        self.tick()?;
        let actual = record.append_core(suffix);
        let user = user_record.append_core(suffix);
        self.check_qualified_declaration_name(&actual, &user)?;
        Ok(actual)
    }
}

pub(super) fn name(
    syntax: &Syntax,
    structure_modifiers: &Syntax,
) -> Result<(Name, bool), NatDefinitionElabError> {
    let ctor = match expect_null_args(syntax, "optional structure constructor")? {
        [] => return Ok((Name::from_components(["mk"]), false)),
        [ctor] => expect_node(
            ctor,
            &parser_kind(&["Command", "structCtor"]),
            4,
            "structure constructor",
        )?,
        _ => return Err(failure(SourceInferenceError::Scope)),
    };
    let modifiers = expect_node(
        &ctor[0],
        &parser_kind(&["Command", "declModifiers"]),
        7,
        "structure constructor modifiers",
    )?;
    doc_comment_slot(&modifiers[0])?;
    let visibility = scope::visibility::modifier(&modifiers[2])?;
    let protected = protected_slot(&modifiers[3])?;
    expect_empty_null(&modifiers[1], "constructor without attributes")?;
    for modifier in &modifiers[4..] {
        expect_empty_null(modifier, "constructor without unsupported modifiers")?;
    }
    let Syntax::Ident { val: name, .. } = &ctor[1] else {
        return Err(NatDefinitionElabError::AnonymousDeclarationName);
    };
    if name.is_anonymous() {
        return Err(NatDefinitionElabError::AnonymousDeclarationName);
    }
    expect_atom(&ctor[3], "::", "structure constructor separator")?;
    // The pin rejects a second private/protected modifier on an already private
    // structure (`Lean/Elab/Structure.lean:259-263`). Public/private constructor
    // visibility needs separate publication and lookup metadata, so it remains a
    // typed nonanswer rather than silently applying to the whole structure bundle.
    let structure_modifiers = expect_node(
        structure_modifiers,
        &parser_kind(&["Command", "declModifiers"]),
        7,
        "structure modifiers",
    )?;
    if scope::visibility::modifier(&structure_modifiers[2])? == Some(false)
        && (visibility == Some(false) || protected)
    {
        return Err(failure(SourceInferenceError::Record(
            crate::records::RecordError::InvalidName,
        )));
    }
    if visibility.is_some() {
        return Err(unsupported("constructor visibility is not yet supported"));
    }
    if !expect_null_args(&ctor[2], "constructor parameter overrides")?.is_empty() {
        return Err(unsupported("parameter overrides are not yet supported"));
    }
    Ok((name.clone(), protected))
}
