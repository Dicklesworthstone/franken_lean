//! Source requests for the pin's symmetry-lemma registry. Syntax describes a
//! request only; registration compiles the admitted declaration's actual type.
use super::*;
use crate::symm::{SymmEntry, SymmLemma, SymmRegistryError};

const MAX_ATTRIBUTE_ITEMS: usize = 4096;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Kind {
    Global,
    Local,
    Scoped,
}

fn refused(expected: &'static str) -> NatDefinitionElabError {
    NatDefinitionElabError::UnexpectedSyntax { expected }
}

pub(in crate::source) fn registry_error(error: SymmRegistryError) -> NatDefinitionElabError {
    match error {
        SymmRegistryError::Limit => failure(SourceInferenceError::ResourceLimit),
        error => failure(SourceInferenceError::Symm(error)),
    }
}

pub(in crate::source) fn attribute(
    syntax: &Syntax,
) -> Result<Option<Kind>, NatDefinitionElabError> {
    let parts = expect_node(
        syntax,
        &parser_kind(&["Term", "attrInstance"]),
        2,
        "attribute instance",
    )?;
    let Syntax::Node { kind, args, .. } = &parts[1] else {
        return Ok(None);
    };
    if kind != &parser_kind(&["Attr", "simple"]) {
        return Ok(None);
    }
    let [Syntax::Ident { val, .. }, argument] = args.as_slice() else {
        return Ok(None);
    };
    if val != &Name::from_components(["symm"]) {
        return Ok(None);
    }
    expect_empty_null(argument, "symm without arguments")?;
    let scope = expect_node(
        &parts[0],
        &parser_kind(&["Term", "attrKind"]),
        1,
        "attribute kind",
    )?;
    let kind = match expect_null_args(&scope[0], "symmetry attribute kind")? {
        [] => Kind::Global,
        [syntax] if syntax.kind() == Some(&parser_kind(&["Term", "local"])) => {
            let parts = expect_node(
                syntax,
                &parser_kind(&["Term", "local"]),
                1,
                "local attribute",
            )?;
            expect_atom(&parts[0], "local", "local attribute keyword")?;
            Kind::Local
        }
        [syntax] if syntax.kind() == Some(&parser_kind(&["Term", "scoped"])) => {
            let parts = expect_node(
                syntax,
                &parser_kind(&["Term", "scoped"]),
                1,
                "scoped attribute",
            )?;
            expect_atom(&parts[0], "scoped", "scoped attribute keyword")?;
            Kind::Scoped
        }
        _ => return Err(refused("global, local or scoped symmetry attribute")),
    };
    Ok(Some(kind))
}

pub fn registrations(syntax: &Syntax) -> Result<Vec<Kind>, NatDefinitionElabError> {
    let Syntax::Node { kind, args, .. } = syntax else {
        return Ok(Vec::new());
    };
    if kind != &parser_kind(&["Command", "declaration"]) {
        return Ok(Vec::new());
    }
    let [modifiers, declaration] = args.as_slice() else {
        return Err(refused("a declaration"));
    };
    let modifiers = expect_node(
        modifiers,
        &parser_kind(&["Command", "declModifiers"]),
        7,
        "declaration modifiers",
    )?;
    let mut rows = Vec::new();
    for syntax in visibility::attributes(&modifiers[1])? {
        if rows.len() >= MAX_ATTRIBUTE_ITEMS {
            return Err(failure(SourceInferenceError::ResourceLimit));
        }
        if let Some(kind) = attribute(syntax)? {
            rows.push(kind);
        }
    }
    if !rows.is_empty()
        && ![
            "definition",
            "abbrev",
            "opaque",
            "axiom",
            "theorem",
            "instance",
        ]
        .iter()
        .any(|kind| declaration.kind() == Some(&parser_kind(&["Command", kind])))
    {
        return Err(refused("symm on one admitted constant"));
    }
    Ok(rows)
}

pub fn command(syntax: &Syntax) -> Result<(Vec<Kind>, Vec<Name>), NatDefinitionElabError> {
    let parts = expect_node(
        syntax,
        &parser_kind(&["Command", "attribute"]),
        5,
        "attribute command",
    )?;
    expect_atom(&parts[0], "attribute", "attribute keyword")?;
    expect_atom(&parts[1], "[", "attribute opener")?;
    expect_atom(&parts[3], "]", "attribute closer")?;
    let entries = expect_null_args(&parts[2], "attribute list")?;
    if entries.len() > MAX_ATTRIBUTE_ITEMS * 2 {
        return Err(failure(SourceInferenceError::ResourceLimit));
    }
    if entries.is_empty() || entries.len() % 2 == 0 {
        return Err(refused("a nonempty attribute list"));
    }
    let mut kinds = Vec::new();
    for (index, entry) in entries.iter().enumerate() {
        if index % 2 == 0 {
            // The builtin attribute has no erasure callback at the pin.
            kinds.push(attribute(entry)?.ok_or_else(|| refused("a symmetry attribute"))?);
        } else {
            expect_atom(entry, ",", "attribute separator")?;
        }
    }
    let declarations = expect_null_args(&parts[4], "attribute declarations")?;
    if declarations.len() > MAX_ATTRIBUTE_ITEMS {
        return Err(failure(SourceInferenceError::ResourceLimit));
    }
    if declarations.is_empty() {
        return Err(refused("attribute declarations"));
    }
    let declarations = declarations
        .iter()
        .map(|syntax| {
            let Syntax::Ident { val, .. } = syntax else {
                return Err(refused("an attribute declaration name"));
            };
            Ok(val.clone())
        })
        .collect::<Result<_, _>>()?;
    Ok((kinds, declarations))
}

pub fn compile(
    environment: &Environment,
    scope: &SourceScope,
    declaration: &Name,
    kernel: Budget,
) -> Result<SymmLemma, NatDefinitionElabError> {
    Context::scoped(environment, kernel, scope)?.symm_lemma(declaration)
}

/// Apply one already checked lemma in attribute order. Local rows live only in
/// the supplied lexical clone; global and scoped rows extend the journal.
pub fn apply(
    environment: &Environment,
    scope: &mut SourceScope,
    lemma: &SymmLemma,
    kinds: &[Kind],
) -> Result<Environment, NatDefinitionElabError> {
    let mut next = environment.clone();
    let mut scopes = scope.symm_scopes.clone();
    for kind in kinds {
        if *kind == Kind::Local {
            scopes
                .register_local(&next, lemma.clone())
                .map_err(registry_error)?;
        } else {
            let namespace = if *kind == Kind::Scoped {
                if scope.namespace.is_anonymous() {
                    return Err(refused("scoped symm inside a namespace"));
                }
                Some(scope.namespace.clone())
            } else {
                None
            };
            next = crate::symm::register(
                &next,
                SymmEntry {
                    lemma: lemma.clone(),
                    namespace,
                },
            )
            .map_err(registry_error)?;
        }
    }
    scope.symm_scopes = scopes;
    Ok(next)
}
