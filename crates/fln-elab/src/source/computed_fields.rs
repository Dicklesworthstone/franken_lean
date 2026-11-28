//! Computed-field source views and the pin's mutually elaborated logical getters.
//!
//! Removing `with` from an inductive is only a private staging operation. The
//! ordinary inductive entry keeps refusing it: a caller must also admit the
//! getters, cached representation and executable replacements atomically.
use super::*;
use std::collections::BTreeSet;

/// A fully read source request, without any declaration-admission authority.
pub struct ComputedFieldBlock {
    /// The original declaration with only its computed-field slot emptied.
    pub syntax: Syntax,
    pub family: Name,
    pub fields: Vec<Name>,
    pub inline_fields: Vec<Name>,
    pub protected_fields: Vec<Name>,
    definitions: Vec<Syntax>,
    scope: SourceScope,
}

impl ComputedFieldBlock {
    /// Source signatures in the selected public predecessor, before any
    /// private logical body can participate in elaboration.
    pub fn headers(
        &self,
        environment: &Environment,
        kernel: Budget,
        public_scope: &SourceScope,
    ) -> Result<Vec<Declaration>, NatDefinitionElabError> {
        partial::elaborate_computed_headers(
            &self.definitions,
            environment,
            kernel,
            &self.exported_scope(public_scope),
        )
    }

    /// Whether this group's checked logical bodies belong in the public world.
    pub fn exposes_getters(&self) -> bool {
        !self.scope.exports_declaration() || self.scope.expose_definitions
    }

    /// All signatures enter one private predefinition group before any body.
    /// These are ordinary terminating, explicitly noncomputable definitions;
    /// no logical axiom or unsafe recursive shortcut is introduced.
    pub fn elaborate(
        &self,
        environment: &Environment,
        kernel: Budget,
    ) -> Result<partial::ElaboratedPartial, NatDefinitionElabError> {
        partial::elaborate_computed_group(&self.definitions, environment, kernel, &self.scope)
    }

    /// An exposed field body sees the public predecessor's instance and local
    /// reducibility history, just as its header does. Private bodies retain the
    /// original lexical scope through [`Self::elaborate`].
    pub fn elaborate_exported(
        &self,
        environment: &Environment,
        kernel: Budget,
        public_scope: &SourceScope,
    ) -> Result<partial::ElaboratedPartial, NatDefinitionElabError> {
        partial::elaborate_computed_group(
            &self.definitions,
            environment,
            kernel,
            &self.exported_scope(public_scope),
        )
    }

    fn exported_scope(&self, public_scope: &SourceScope) -> SourceScope {
        let mut selected = public_scope.clone();
        selected.public_declarations = self.scope.public_declarations;
        selected.expose_definitions = self.scope.expose_definitions;
        set_computed_options(&mut selected);
        selected
    }
}

fn set_computed_options(scope: &mut SourceScope) {
    scope.options.insert(
        Name::from_components(["bootstrap", "genMatcherCode"]),
        fln_core::options::DataValue::OfBool(false),
    );
    scope.options.insert(
        Name::from_components(["elaboratingComputedFields"]),
        fln_core::options::DataValue::OfBool(true),
    );
}

fn refused(expected: &'static str) -> NatDefinitionElabError {
    NatDefinitionElabError::UnexpectedSyntax { expected }
}

fn null() -> Syntax {
    Syntax::node(Name::from_components(["null"]), Vec::new())
}

fn atom(text: &str) -> Syntax {
    Syntax::atom(fln_syntax::source::SourceInfo::None, text)
}

/// Read every field modifier before lowering. Unsupported effects never vanish
/// merely because the logical getter is elaborated by an internal adapter.
fn field_attributes(modifiers: &[Syntax]) -> Result<bool, NatDefinitionElabError> {
    let mut computed = false;
    let mut inline = false;
    for attribute in scope::visibility::attributes(&modifiers[1])? {
        let instance = expect_node(
            attribute,
            &parser_kind(&["Term", "attrInstance"]),
            2,
            "computed-field attribute",
        )?;
        let kind = expect_node(
            &instance[0],
            &parser_kind(&["Term", "attrKind"]),
            1,
            "computed-field attribute scope",
        )?;
        expect_empty_null(&kind[0], "global computed-field attributes")?;
        let parts = expect_node(
            &instance[1],
            &parser_kind(&["Attr", "simple"]),
            2,
            "computed_field or inline attribute",
        )?;
        expect_empty_null(&parts[1], "computed-field attribute without arguments")?;
        match &parts[0] {
            Syntax::Ident { val, .. } if val == &Name::from_components(["computed_field"]) => {
                computed = true;
            }
            Syntax::Ident { val, .. } if val == &Name::from_components(["inline"]) => {
                inline = true;
            }
            _ => return Err(refused("computed_field or inline attribute")),
        }
    }
    if !computed {
        return Err(refused(
            "every computed field tagged with @[computed_field]",
        ));
    }
    Ok(inline)
}

/// Prepare one source family. `scope` is the surrounding lexical scope, so a
/// top-level `public inductive` does not accidentally make an unmarked field
/// public; the pin elaborates field modifiers as separate declarations.
pub fn prepare(
    syntax: &Syntax,
    scope: &SourceScope,
) -> Result<Option<ComputedFieldBlock>, NatDefinitionElabError> {
    if !inductive::is_inductive(syntax) {
        return Ok(None);
    }
    let root = expect_node(
        syntax,
        &parser_kind(&["Command", "declaration"]),
        2,
        "inductive declaration",
    )?;
    let (is_class, parts) = inductive::command_parts(&root[1])?;
    if is_class {
        return Ok(None);
    }
    let computed = match expect_null_args(&parts[5], "computed fields")? {
        [] => return Ok(None),
        [computed] => expect_node(
            computed,
            &parser_kind(&["Command", "computedFields"]),
            2,
            "computed fields",
        )?,
        _ => return Err(refused("one computed-field with-block")),
    };
    expect_atom(&computed[0], "with", "computed-field with keyword")?;
    let entries = expect_null_args(&computed[1], "computed-field declarations")?;
    if entries.is_empty() || entries.len() > 8 {
        return Err(refused("one to eight computed fields"));
    }
    let id = expect_node(
        &parts[1],
        &parser_kind(&["Command", "declId"]),
        2,
        "computed-field family name",
    )?;
    let Syntax::Ident { val: family, .. } = &id[0] else {
        return Err(NatDefinitionElabError::AnonymousDeclarationName);
    };
    let family_scope = scope.for_declaration(syntax)?;
    // Private-name concatenation and per-member export worlds require a
    // separate profile. Never double-prefix a private name or expose it.
    if family_scope.private_module.is_some() && !family_scope.public_declarations {
        return Err(refused("a public or legacy computed-field family"));
    }
    let family = family_scope
        .declaration_name(family)
        .map_err(|error| failure(SourceInferenceError::NameScope(error)))?;
    let mut definitions = Vec::new();
    let mut fields = Vec::new();
    let mut inline_fields = Vec::new();
    let mut protected_fields = Vec::new();
    let mut seen = BTreeSet::new();
    let mut group_scope = None;
    for entry in entries {
        let field = expect_node(
            entry,
            &parser_kind(&["Command", "computedField"]),
            5,
            "computed-field declaration",
        )?;
        let modifiers = expect_node(
            &field[0],
            &parser_kind(&["Command", "declModifiers"]),
            7,
            "computed-field modifiers",
        )?;
        doc_comment_slot(&modifiers[0])?;
        let inline = field_attributes(modifiers)?;
        scope::visibility::modifier(&modifiers[2])?;
        let protected = protected_slot(&modifiers[PROTECTED_SLOT])?;
        noncomputable_slot(&modifiers[NONCOMPUTABLE_SLOT])?;
        for modifier in &modifiers[5..] {
            expect_empty_null(modifier, "safe computed field without partial")?;
        }
        let Syntax::Ident { val, .. } = &field[1] else {
            return Err(NatDefinitionElabError::AnonymousDeclarationName);
        };
        if val.is_anonymous() {
            return Err(NatDefinitionElabError::AnonymousDeclarationName);
        }
        let name = family.append_core(val);
        if !seen.insert(name.clone()) {
            return Err(refused("distinct computed-field names"));
        }
        expect_atom(&field[2], ":", "computed-field type separator")?;
        let mut identifier = field[1].clone();
        if let Syntax::Ident {
            val, preresolved, ..
        } = &mut identifier
        {
            *val = Name::from_components(["_root_"]).append_core(&name);
            preresolved.clear();
        }
        let mut modifiers = modifiers.to_vec();
        // The effects are retained above and applied after complete admission.
        // The generic term elaborator must not reinterpret computed_field as simp.
        modifiers[1] = null();
        modifiers[NONCOMPUTABLE_SLOT] = Syntax::node(
            Name::from_components(["null"]),
            vec![Syntax::node(
                parser_kind(&["Command", "noncomputable"]),
                vec![atom("noncomputable")],
            )],
        );
        let definition = Syntax::node(
            parser_kind(&["Command", "declaration"]),
            vec![
                Syntax::node(parser_kind(&["Command", "declModifiers"]), modifiers),
                Syntax::node(
                    parser_kind(&["Command", "definition"]),
                    vec![
                        atom("def"),
                        Syntax::node(
                            parser_kind(&["Command", "declId"]),
                            vec![identifier, null()],
                        ),
                        Syntax::node(
                            parser_kind(&["Command", "optDeclSig"]),
                            vec![
                                null(),
                                Syntax::node(
                                    Name::from_components(["null"]),
                                    vec![Syntax::node(
                                        parser_kind(&["Term", "typeSpec"]),
                                        vec![field[2].clone(), field[3].clone()],
                                    )],
                                ),
                            ],
                        ),
                        Syntax::node(
                            parser_kind(&["Command", "declValEqns"]),
                            vec![Syntax::node(
                                parser_kind(&["Term", "matchAltsWhereDecls"]),
                                vec![
                                    field[4].clone(),
                                    Syntax::node(
                                        parser_kind(&["Termination", "suffix"]),
                                        vec![null(), null()],
                                    ),
                                    null(),
                                ],
                            )],
                        ),
                        null(),
                    ],
                ),
            ],
        );
        let effective = scope.for_declaration(&definition)?;
        let absolute = Name::from_components(["_root_"]).append_core(&name);
        if effective
            .declaration_name(&absolute)
            .map_err(|error| failure(SourceInferenceError::NameScope(error)))?
            != name
        {
            return Err(refused(
                "computed field with the family-qualified visibility",
            ));
        }
        if let Some(previous) = &group_scope {
            if previous != &effective {
                return Err(refused("one visibility scope for a computed-field group"));
            }
        } else {
            group_scope = Some(effective);
        }
        if inline {
            inline_fields.push(name.clone());
        }
        if protected {
            protected_fields.push(name.clone());
        }
        fields.push(name);
        definitions.push(definition);
    }
    let mut syntax = syntax.clone();
    if let Syntax::Node { args, .. } = &mut syntax
        && let Syntax::Node { args, .. } = &mut args[1]
    {
        args[5] = null();
    }
    let mut group_scope = group_scope.ok_or_else(|| refused("nonempty computed-field group"))?;
    // Match the pin's scoped command options; no compiler may create a matcher
    // against the uncached family before its replacements have been installed.
    set_computed_options(&mut group_scope);
    Ok(Some(ComputedFieldBlock {
        syntax,
        family,
        fields,
        inline_fields,
        protected_fields,
        definitions,
        scope: group_scope,
    }))
}
