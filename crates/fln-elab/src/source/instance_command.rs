//! Canonical named-instance syntax; publication remains outside elaboration.
use super::*;
pub(super) struct Parts<'a> {
    pub keyword: &'a Syntax,
    /// `None` for an anonymous instance, whose name the elaborator generates.
    pub id: Option<&'a Syntax>,
    pub signature: &'a Syntax,
    pub value: &'a Syntax,
    pub priority: u32,
    pub scoped: bool,
    pub local: bool,
}

/// The pin exposes data instances automatically, while a proof instance needs
/// its own `expose` attribute. An expose section only supplies a default for
/// ordinary definitions, and `no_expose` wins over either exposure source.
/// Classify the complete header before the body can constrain its universes or
/// use any private declaration (`MutualDef.finishElab`). Return whether its
/// result is a proposition and whether its body uses the private predecessor.
pub(super) fn prepare_header(
    context: &mut Context,
    parameters: &[LocalDecl],
    result: &Expr,
    attributes: &Syntax,
) -> Result<(bool, bool), NatDefinitionElabError> {
    let sort = context
        .known_type(result)?
        .ok_or_else(|| failure(SourceInferenceError::ExpectedType))?;
    let sort = context.whnf(&sort)?;
    let ExprNode::Sort { level } = sort.node() else {
        return Err(failure(SourceInferenceError::ExpectedType));
    };
    let is_proof = level.normalize().is_zero();
    if is_proof {
        // `levelMVarToParamHeaders` runs before exposure is chosen. Even an
        // explicitly exposed proof may not use its body to specialize an
        // unresolved header universe. Ordinary data instances retain the
        // later generalization path.
        let mut roots: Vec<_> = context
            .source_scope
            .variables
            .locals()
            .decls()
            .iter()
            .chain(parameters)
            .map(|local| local.type_.clone())
            .collect();
        roots.push(result.clone());
        context.generalize_declaration_universes(&roots)?;
    }
    if !context.source_scope.exports_declaration() {
        return Ok((is_proof, false));
    }
    let mut expose = false;
    let mut no_expose = false;
    for attribute in scope::visibility::attributes(attributes)? {
        match scope::visibility::exposure_attribute(attribute)? {
            Some(true) => expose = true,
            Some(false) => no_expose = true,
            None => {}
        }
    }
    if !is_proof && no_expose {
        return Err(NatDefinitionElabError::UnexpectedSyntax {
            expected: "public data instances with exposed bodies",
        });
    }
    Ok((is_proof, is_proof && (no_expose || !expose)))
}

/// An instance's declaration binders and result are fixed in the public world.
/// Unlike theorems, instances may use extra section variables in their bodies:
/// retain their already elaborated public domains, then close only the selected
/// subset. No private inference result can replace any part of this template.
#[derive(Clone)]
pub(super) struct PublicHeader {
    name: Name,
    type_: Expr,
    sections: Vec<LocalDecl>,
}

impl PublicHeader {
    pub(super) fn freeze(
        context: &mut Context,
        name: &Name,
        parameters: &[LocalDecl],
        result: &Expr,
    ) -> Result<Self, NatDefinitionElabError> {
        let mut sections = context.source_scope.variables.locals().decls().to_vec();
        // The complete proof header's universes were made rigid before the
        // exposure decision; retain that exact public template here.
        let mut type_ = context.instantiate(result)?;
        for local in parameters.iter().rev() {
            context.tick()?;
            type_ = Expr::forall_e(
                local.user_name.clone(),
                context.instantiate(&local.type_)?,
                type_
                    .abstract_fvar(&local.id, 0)
                    .map_err(|_| failure(SourceInferenceError::Scope))?,
                local.binder_info,
            );
        }
        for local in &mut sections {
            context.tick()?;
            local.type_ = context.instantiate(&local.type_)?;
            context.require_resolved(std::slice::from_ref(&local.type_))?;
        }
        context.require_resolved(std::slice::from_ref(&type_))?;
        Ok(Self {
            name: name.clone(),
            type_,
            sections,
        })
    }

    pub(super) fn close(
        &self,
        context: &mut Context,
        name: &Name,
        selected: &[LocalDecl],
    ) -> Result<Expr, NatDefinitionElabError> {
        if name != &self.name {
            return Err(failure(SourceInferenceError::Scope));
        }
        let selected: std::collections::HashSet<_> =
            selected.iter().map(|local| &local.id).collect();
        let mut count = 0usize;
        let mut type_ = self.type_.clone();
        for local in self.sections.iter().rev() {
            context.tick()?;
            if selected.contains(&local.id) {
                count += 1;
                type_ = Expr::forall_e(
                    local.user_name.clone(),
                    local.type_.clone(),
                    type_
                        .abstract_fvar(&local.id, 0)
                        .map_err(|_| failure(SourceInferenceError::Scope))?,
                    local.binder_info,
                );
            }
        }
        if count != selected.len() || type_.has_fvar() || type_.has_loose_bvars() {
            return Err(failure(SourceInferenceError::Scope));
        }
        Ok(type_)
    }
}

pub(super) fn parts(syntax: &Syntax) -> Result<Parts<'_>, NatDefinitionElabError> {
    let args = expect_node(
        syntax,
        &parser_kind(&["Command", "instance"]),
        6,
        "named instance",
    )?;
    let attr = expect_node(
        &args[0],
        &parser_kind(&["Term", "attrKind"]),
        1,
        "instance scope",
    )?;
    let (scoped, local) = match expect_null_args(&attr[0], "instance scope")? {
        [] => (false, false),
        [scope] => {
            let local = matches!(scope, Syntax::Node { kind, .. } if kind == &parser_kind(&["Term", "local"]));
            let keyword = if local { "local" } else { "scoped" };
            let parts = expect_node(
                scope,
                &parser_kind(&["Term", keyword]),
                1,
                "global, local or namespace-scoped instance",
            )?;
            expect_atom(&parts[0], keyword, "instance scope keyword")?;
            (!local, local)
        }
        _ => {
            return Err(NatDefinitionElabError::UnexpectedSyntax {
                expected: "global, local or namespace-scoped instance",
            });
        }
    };
    expect_atom(&args[1], "instance", "instance keyword")?;
    let priority = match expect_null_args(&args[2], "instance priority")? {
        [] => 1000,
        [syntax] => {
            let p = expect_node(
                syntax,
                &parser_kind(&["Command", "namedPrio"]),
                5,
                "numeric instance priority",
            )?;
            expect_atom(&p[0], "(", "priority opener")?;
            expect_atom(&p[1], "priority", "priority keyword")?;
            expect_atom(&p[2], ":=", "priority assignment")?;
            expect_atom(&p[4], ")", "priority closer")?;
            let num = expect_node(
                &p[3],
                &Name::from_components(["num"]),
                1,
                "priority numeral",
            )?;
            let Syntax::Atom { val, .. } = &num[0] else {
                return Err(failure(SourceInferenceError::Scope));
            };
            // This bounded profile supports nonnegative decimal u32 priorities.
            if val.is_empty() || !val.bytes().all(|b| b.is_ascii_digit()) {
                return Err(failure(SourceInferenceError::Scope));
            }
            val.parse::<u32>()
                .map_err(|_| failure(SourceInferenceError::Scope))?
        }
        _ => return Err(failure(SourceInferenceError::Scope)),
    };
    let id = match expect_null_args(&args[3], "explicit instance name")? {
        [] => None,
        [id] => Some(id),
        _ => return Err(NatDefinitionElabError::AnonymousDeclarationName),
    };
    Ok(Parts {
        keyword: &args[1],
        id,
        signature: &args[4],
        value: &args[5],
        priority,
        scoped,
        local,
    })
}
fn command_parts(syntax: &Syntax) -> Result<Option<Parts<'_>>, NatDefinitionElabError> {
    let declaration = expect_node(
        syntax,
        &parser_kind(&["Command", "declaration"]),
        2,
        "declaration",
    )?;
    if !matches!(&declaration[1],Syntax::Node{kind,..} if kind==&parser_kind(&["Command","instance"]))
    {
        return Ok(None);
    }
    parts(&declaration[1]).map(Some)
}

pub(super) fn is_scoped(syntax: &Syntax) -> Result<bool, NatDefinitionElabError> {
    Ok(command_parts(syntax)?.is_some_and(|parts| parts.scoped))
}

pub(super) fn is_local(syntax: &Syntax) -> Result<bool, NatDefinitionElabError> {
    Ok(command_parts(syntax)?.is_some_and(|parts| parts.local))
}

pub(super) fn registration(syntax: &Syntax) -> Result<Option<(Name, u32)>, NatDefinitionElabError> {
    let Some(parts) = command_parts(syntax)? else {
        return Ok(None);
    };
    // An anonymous instance is registered under the name its elaboration generates;
    // the caller takes it from the elaborated declaration.
    let Some(id) = parts.id else {
        return Ok(Some((Name::anonymous(), parts.priority)));
    };
    let id = expect_node(
        id,
        &parser_kind(&["Command", "declId"]),
        2,
        "instance identifier",
    )?;
    level_syntax::explicit_parameters(&id[1])?;
    let Syntax::Ident { val, .. } = &id[0] else {
        return Err(NatDefinitionElabError::AnonymousDeclarationName);
    };
    if val.is_anonymous() {
        return Err(NatDefinitionElabError::AnonymousDeclarationName);
    }
    Ok(Some((val.clone(), parts.priority)))
}

pub(super) fn default_attribute(attribute: &Syntax) -> Result<Option<u32>, NatDefinitionElabError> {
    let instance = expect_node(
        attribute,
        &parser_kind(&["Term", "attrInstance"]),
        2,
        "attribute instance",
    )?;
    if !matches!(&instance[1], Syntax::Node { kind, .. }
        if kind == &parser_kind(&["Attr", "default_instance"]))
    {
        return Ok(None);
    }
    let scope = expect_node(
        &instance[0],
        &parser_kind(&["Term", "attrKind"]),
        1,
        "default instance attribute scope",
    )?;
    expect_empty_null(&scope[0], "global default instance attribute")?;
    let parts = expect_node(
        &instance[1],
        &parser_kind(&["Attr", "default_instance"]),
        2,
        "default instance attribute",
    )?;
    expect_atom(
        &parts[0],
        "default_instance",
        "default instance attribute keyword",
    )?;
    Ok(Some(
        match expect_null_args(&parts[1], "default instance priority")? {
            [] => 1000,
            [priority] => scope::simp::priority_value(priority)?,
            _ => {
                return Err(NatDefinitionElabError::UnexpectedSyntax {
                    expected: "one default instance priority",
                });
            }
        },
    ))
}

/// Attribute order is persistent: registering the same declaration again does
/// not erase an earlier, higher-priority default candidate.
pub(super) fn default_registration(syntax: &Syntax) -> Result<Vec<u32>, NatDefinitionElabError> {
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
    let mut priorities = Vec::new();
    for attribute in scope::visibility::attributes(&modifiers[1])? {
        if let Some(priority) = default_attribute(attribute)? {
            priorities.push(priority);
        }
    }
    if !priorities.is_empty()
        && !matches!(&declaration[1], Syntax::Node { kind, .. }
            if ["definition", "theorem", "instance", "abbrev", "opaque", "axiom"]
                .iter().any(|command| kind == &parser_kind(&["Command", command])))
    {
        return Err(NatDefinitionElabError::UnexpectedSyntax {
            expected: "a persistent declaration for default instance registration",
        });
    }
    Ok(priorities)
}
