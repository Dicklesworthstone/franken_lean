//! Module declaration visibility is selected before elaboration. Exposed public
//! bodies and public data signatures must be elaborated in an exported world;
//! these helpers describe that choice but grant no admission authority.
use super::*;

fn refused(expected: &'static str) -> NatDefinitionElabError {
    NatDefinitionElabError::UnexpectedSyntax { expected }
}

/// A canonical visibility modifier, retaining `None` for an inherited default.
pub(in crate::source) fn modifier(syntax: &Syntax) -> Result<Option<bool>, NatDefinitionElabError> {
    let node = match expect_null_args(syntax, "declaration visibility")? {
        [] => return Ok(None),
        [node] => node,
        _ => return Err(refused("one public or private modifier")),
    };
    for (keyword, public) in [("public", true), ("private", false)] {
        if node.kind() == Some(&parser_kind(&["Command", keyword])) {
            let parts = expect_node(
                node,
                &parser_kind(&["Command", keyword]),
                1,
                "declaration visibility",
            )?;
            expect_atom(&parts[0], keyword, "visibility keyword")?;
            return Ok(Some(public));
        }
    }
    Err(refused("public or private declaration visibility"))
}

/// Attribute instances without the separator atoms, from an optional attributes
/// slot. No attribute is consumed here: every caller must interpret or refuse it.
pub(in crate::source) fn attributes(
    syntax: &Syntax,
) -> Result<Vec<&Syntax>, NatDefinitionElabError> {
    let attributes = match expect_null_args(syntax, "inline attributes")? {
        [] => return Ok(Vec::new()),
        [attributes] => expect_node(
            attributes,
            &parser_kind(&["Term", "attributes"]),
            3,
            "inline attributes",
        )?,
        _ => return Err(refused("one inline attribute list")),
    };
    expect_atom(&attributes[0], "@[", "attribute opener")?;
    expect_atom(&attributes[2], "]", "attribute closer")?;
    let entries = expect_null_args(&attributes[1], "attribute list")?;
    if entries.is_empty() || entries.len() % 2 == 0 {
        return Err(refused("nonempty separated attribute list"));
    }
    let mut result = Vec::new();
    for (index, entry) in entries.iter().enumerate() {
        if index % 2 == 0 {
            result.push(entry);
        } else {
            expect_atom(entry, ",", "attribute separator")?;
        }
    }
    Ok(result)
}

/// Only exact global `expose` and `no_expose` tags are visibility attributes.
/// A same-named tag with arguments or local/scoped effects is never ignored.
pub(in crate::source) fn exposure_attribute(
    syntax: &Syntax,
) -> Result<Option<bool>, NatDefinitionElabError> {
    let instance = expect_node(
        syntax,
        &parser_kind(&["Term", "attrInstance"]),
        2,
        "attribute instance",
    )?;
    let Syntax::Node { kind, args, .. } = &instance[1] else {
        return Ok(None);
    };
    if kind != &parser_kind(&["Attr", "simple"]) {
        return Ok(None);
    }
    let [Syntax::Ident { val, .. }, argument] = args.as_slice() else {
        return Ok(None);
    };
    let expose = if val == &Name::from_components(["expose"]) {
        true
    } else if val == &Name::from_components(["no_expose"]) {
        false
    } else {
        return Ok(None);
    };
    let scope = expect_node(
        &instance[0],
        &parser_kind(&["Term", "attrKind"]),
        1,
        "attribute scope",
    )?;
    expect_empty_null(&scope[0], "global exposure attribute")?;
    expect_empty_null(argument, "exposure attribute without arguments")?;
    Ok(Some(expose))
}

/// Top-level data modifiers, distinct from constructor/field modifiers whose
/// individual visibility semantics are not implemented by this source door.
pub(in crate::source) fn data_modifiers(syntax: &Syntax) -> Result<(), NatDefinitionElabError> {
    let parts = expect_node(
        syntax,
        &parser_kind(&["Command", "declModifiers"]),
        7,
        "data declaration modifiers",
    )?;
    super::super::doc_comment_slot(&parts[0])?;
    for attribute in attributes(&parts[1])? {
        if exposure_attribute(attribute)? != Some(true) {
            return Err(refused("only expose attributes on data declarations"));
        }
    }
    modifier(&parts[2])?;
    for part in &parts[3..] {
        expect_empty_null(part, "absent unsupported data modifier")?;
    }
    Ok(())
}

impl SourceScope {
    /// Whether this effective declaration belongs to a module's exported world.
    /// Legacy files already use one public environment and need no projection.
    pub fn exports_declaration(&self) -> bool {
        self.private_module.is_some() && self.public_declarations
    }

    /// Compute one declaration's visibility without mutating section defaults.
    /// The caller must choose the corresponding environment *before* elaboration.
    /// This native slice exports fully exposed definitions, data instances and
    /// complete public data bundles. A public theorem selects its exported
    /// signature world; the theorem driver separately checks its hidden proof.
    /// Ordinary hidden-body public definitions remain explicitly refused.
    pub fn for_declaration(&self, syntax: &Syntax) -> Result<Self, NatDefinitionElabError> {
        let declaration = expect_node(
            syntax,
            &parser_kind(&["Command", "declaration"]),
            2,
            "declaration",
        )?;
        let modifiers = expect_node(
            &declaration[0],
            &parser_kind(&["Command", "declModifiers"]),
            7,
            "declaration modifiers",
        )?;
        let explicit = modifier(&modifiers[2])?;
        if explicit == Some(false) && self.private_module.is_none() {
            return Err(refused("a module identity for private declarations"));
        }
        let mut expose = false;
        let mut no_expose = false;
        for attribute in attributes(&modifiers[1])? {
            match exposure_attribute(attribute)? {
                Some(true) => expose = true,
                Some(false) => no_expose = true,
                None => {}
            }
        }
        let mut effective = self.clone();
        effective.public_declarations =
            explicit.unwrap_or(self.public_declarations || self.private_module.is_none());
        effective.expose_definitions = !no_expose && (expose || self.expose_definitions);
        let kind = declaration[1].kind();
        if kind == Some(&parser_kind(&["Command", "example"])) {
            if explicit == Some(true) && self.private_module.is_some() {
                return Err(refused("private examples in module files"));
            }
            effective.public_declarations = false;
            return Ok(effective);
        }
        if effective.exports_declaration() {
            if kind == Some(&parser_kind(&["Command", "definition"])) {
                if !effective.expose_definitions {
                    return Err(refused(
                        "@[expose] public definitions; hidden bodies are not yet exported",
                    ));
                }
            } else if kind == Some(&parser_kind(&["Command", "instance"])) {
                // MutualDef.finishElab automatically exposes data instances.
                // Whether the result is a proposition is established from the
                // elaborated header, before entering its body. This selector
                // only chooses the public environment for that elaboration.
                if no_expose {
                    return Err(refused("public data instances with exposed bodies"));
                }
            } else if kind == Some(&parser_kind(&["Command", "theorem"])) {
                if expose || no_expose {
                    return Err(refused("public theorems without exposure attributes"));
                }
            } else if kind == Some(&parser_kind(&["Command", "inductive"]))
                || kind == Some(&parser_kind(&["Command", "structure"]))
            {
                if no_expose {
                    return Err(refused("fully exposed public data declarations"));
                }
            } else {
                return Err(refused(
                    "exposed public definitions, data instances, theorems or public data declarations",
                ));
            }
        }
        Ok(effective)
    }

    /// Source-command counterpart to [`Self::for_declaration`]. It preserves the
    /// existing atomic private-mutual route and never turns queries/examples into
    /// exported declarations merely because they occur inside a public section.
    pub fn for_command_source(&self, source: &[u8]) -> Result<Self, NatDefinitionFrontendError> {
        if fln_parse::command_scope::parse(source)?.is_some() {
            let mut effective = self.clone();
            effective.public_declarations = false;
            return Ok(effective);
        }
        if let Some(members) = fln_parse::command_scope::mutual::parse(source)? {
            let mut exports = self.exports_declaration();
            for member in &members {
                exports |= self.for_declaration(member)?.exports_declaration();
            }
            if exports {
                return Err(refused(
                    "private mutual blocks; public mutual export is not yet supported",
                )
                .into());
            }
            return Ok(self.clone());
        }
        let parsed = fln_parse::parse_source_command(source)?;
        if parsed.syntax().kind() == Some(&parser_kind(&["Command", "declaration"])) {
            return self.for_declaration(parsed.syntax()).map_err(Into::into);
        }
        let mut effective = self.clone();
        effective.public_declarations = false;
        Ok(effective)
    }

    /// Visibility for completion before the current declaration is parseable.
    /// This selects a checked prefix environment only; it neither validates nor
    /// permits the unfinished declaration. Queries and ordinary examples use the
    /// private world even inside a public section.
    pub fn for_command_prefix(&self, source: &[u8]) -> Result<Self, NatDefinitionFrontendError> {
        let mut effective = self.clone();
        let Some(prefix) = fln_parse::command_scope::modifiers::prefix(source)? else {
            effective.public_declarations = false;
            return Ok(effective);
        };
        if prefix.public == Some(false) && self.private_module.is_none() {
            return Err(refused("a module identity for private declarations").into());
        }
        effective.public_declarations = prefix.public.unwrap_or(
            !prefix.is_example && (self.public_declarations || self.private_module.is_none()),
        );
        Ok(effective)
    }

    /// Check the pin's prohibition against a public declaration shadowing a local
    /// private declaration. `name` is fully qualified (also for generated bundle
    /// members). Public elaboration itself cannot see this private predecessor.
    pub fn check_public_name(
        &self,
        name: &Name,
        full_env: &Environment,
    ) -> Result<(), NatDefinitionElabError> {
        if self.exports_declaration() && full_env.contains(&self.private_name(name)) {
            return Err(error(ScopeError::PublicShadowsPrivate(name.clone())));
        }
        Ok(())
    }
}

/// Shared selector for source-file and executing module command loops.
pub fn command_scope(
    source: &[u8],
    enclosing: &SourceScope,
) -> Result<SourceScope, NatDefinitionFrontendError> {
    enclosing.for_command_source(source)
}
