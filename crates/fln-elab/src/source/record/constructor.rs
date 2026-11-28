//! Explicit structure constructors use a name relative to the structure, not
//! ordinary namespace lookup (`Lean/Elab/Structure.lean`, `expandCtor`).
use super::*;

pub(super) struct Constructor {
    pub name: Name,
    pub protected: bool,
    private: bool,
    explicit: bool,
}

impl Default for Constructor {
    fn default() -> Self {
        Self {
            name: Name::from_components(["mk"]),
            protected: false,
            private: false,
            explicit: false,
        }
    }
}

fn unsupported(reason: &'static str) -> NatDefinitionElabError {
    failure(SourceInferenceError::UnsupportedRecordConstructor(reason))
}

impl Context {
    /// Apply the ordinary name policy without reparsing the scoped structure
    /// prefix as source syntax. The user name was retained before applying
    /// visibility; numeric macro-scope components remain exactly as authored.
    pub(super) fn record_member_name(
        &mut self,
        record: &Name,
        user_record: &Name,
        suffix: &Name,
        private: bool,
    ) -> Result<Name, NatDefinitionElabError> {
        self.tick()?;
        let user = user_record.append_core(suffix);
        let actual = if private {
            if self.source_scope.private_identity().is_none() {
                return Err(unsupported(
                    "a source module identity for private record members",
                ));
            }
            // The user record was saved before applying visibility. Applying
            // the current private prefix here is therefore idempotent, even
            // when the containing module has made the structure private.
            self.source_scope.private_name(&user)
        } else {
            record.append_core(suffix)
        };
        let public = self.source_scope.public_declarations;
        let private_module = self.source_scope.private_module.clone();
        if actual != user {
            self.source_scope.public_declarations = false;
            self.source_scope.private_module = self.source_scope.private_identity().cloned();
        }
        let checked = self.check_qualified_declaration_name(&actual, &user);
        self.source_scope.public_declarations = public;
        self.source_scope.private_module = private_module;
        checked?;
        Ok(actual)
    }

    pub(super) fn record_constructor_name(
        &mut self,
        record: &Name,
        user_record: &Name,
        constructor: &Constructor,
        private_fields: bool,
    ) -> Result<Name, NatDefinitionElabError> {
        // Modern module interfaces hide the constructor whenever a written
        // field is private. Legacy files retain their public constructor.
        let force_private = self.source_scope.private_module.is_some() && private_fields;
        if force_private && constructor.explicit && !constructor.private {
            return Err(unsupported(
                "a private constructor for private structure fields",
            ));
        }
        self.record_member_name(
            record,
            user_record,
            &constructor.name,
            constructor.private || force_private,
        )
    }
}

pub(super) fn name(
    syntax: &Syntax,
    structure_modifiers: &Syntax,
) -> Result<Constructor, NatDefinitionElabError> {
    let ctor = match expect_null_args(syntax, "optional structure constructor")? {
        [] => return Ok(Constructor::default()),
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
    // The pin rejects a second private/protected modifier on an explicitly
    // private structure (`Lean/Elab/Structure.lean:259-263`). A module's default
    // private visibility is distinct from this authored restriction.
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
    if !expect_null_args(&ctor[2], "constructor parameter overrides")?.is_empty() {
        return Err(unsupported("parameter overrides are not yet supported"));
    }
    Ok(Constructor {
        name: name.clone(),
        protected,
        private: visibility == Some(false),
        explicit: true,
    })
}
