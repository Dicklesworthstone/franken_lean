//! Source executable attributes describe checked declarations; they never alter
//! logical bodies or authorize an unrecognised native symbol.
use super::*;
use crate::externs::{ExternEntry, ExternTable};
use crate::implemented_by::ImplementedByTable;
use fln_env::constants::ConstantInfo;

const MAX_ATTRIBUTE_ITEMS: usize = 4096;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Attribute {
    ImplementedBy(Name),
    Extern(Vec<ExternEntry>),
}

fn implemented_error(error: crate::implemented_by::ImplementedByError) -> NatDefinitionElabError {
    match error {
        crate::implemented_by::ImplementedByError::Limit => {
            failure(SourceInferenceError::ResourceLimit)
        }
        error => failure(SourceInferenceError::ImplementedByJournal(error)),
    }
}

fn extern_error(error: crate::externs::ExternError) -> NatDefinitionElabError {
    match error {
        crate::externs::ExternError::Limit => failure(SourceInferenceError::ResourceLimit),
        error => failure(SourceInferenceError::ExternJournal(error)),
    }
}

fn refused(expected: &'static str) -> NatDefinitionElabError {
    NatDefinitionElabError::UnexpectedSyntax { expected }
}

/// Recognize only exact global attributes, retaining their source order.
pub(in crate::source) fn attribute(
    syntax: &Syntax,
) -> Result<Option<Attribute>, NatDefinitionElabError> {
    let instance = expect_node(
        syntax,
        &parser_kind(&["Term", "attrInstance"]),
        2,
        "attribute instance",
    )?;
    let value = match &instance[1] {
        Syntax::Node { kind, args, .. } if kind == &parser_kind(&["Attr", "simple"]) => {
            let [Syntax::Ident { val, .. }, argument] = args.as_slice() else {
                return Ok(None);
            };
            if val != &Name::from_components(["implemented_by"]) {
                return Ok(None);
            }
            let [Syntax::Ident { val, .. }] = expect_null_args(argument, "implemented_by target")?
            else {
                return Err(refused("one implemented_by declaration name"));
            };
            if val.is_anonymous() {
                return Err(refused("a named implemented_by target"));
            }
            Attribute::ImplementedBy(val.clone())
        }
        Syntax::Node { kind, args, .. } if kind == &parser_kind(&["Attr", "extern"]) => {
            let [keyword, entries] = args.as_slice() else {
                return Err(refused("extern attribute"));
            };
            expect_atom(keyword, "extern", "extern attribute keyword")?;
            let entries = expect_null_args(entries, "extern entries")?;
            if entries.len() > MAX_ATTRIBUTE_ITEMS {
                return Err(failure(SourceInferenceError::ResourceLimit));
            }
            let mut values = Vec::new();
            if entries.is_empty() {
                values.push(ExternEntry::Adhoc {
                    backend: Name::from_components(["all"]),
                });
            }
            for entry in entries {
                let parts = expect_node(
                    entry,
                    &parser_kind(&["Attr", "externEntry"]),
                    3,
                    "extern entry",
                )?;
                let backend = match expect_null_args(&parts[0], "extern backend")? {
                    [] => Name::from_components(["all"]),
                    [Syntax::Ident { val, .. }] => val.clone(),
                    _ => return Err(refused("one extern backend")),
                };
                let inline = match expect_null_args(&parts[1], "extern entry kind")? {
                    [] => false,
                    [keyword] => {
                        expect_atom(keyword, "inline", "inline extern keyword")?;
                        true
                    }
                    _ => return Err(refused("an extern entry kind")),
                };
                let string = expect_node(
                    &parts[2],
                    &Name::from_components(["str"]),
                    1,
                    "extern string",
                )?;
                let [Syntax::Atom { val, .. }] = string else {
                    return Err(refused("an extern string literal"));
                };
                let Literal::Str(text) = decode_string(val)? else {
                    return Err(refused("an extern string literal"));
                };
                values.push(if inline {
                    ExternEntry::Inline {
                        backend,
                        pattern: text,
                    }
                } else {
                    ExternEntry::Standard {
                        backend,
                        symbol: text,
                    }
                });
            }
            Attribute::Extern(values)
        }
        _ => return Ok(None),
    };
    let scope = expect_node(
        &instance[0],
        &parser_kind(&["Term", "attrKind"]),
        1,
        "attribute scope",
    )?;
    expect_empty_null(&scope[0], "a global executable attribute")?;
    Ok(Some(value))
}

pub fn registrations(syntax: &Syntax) -> Result<Vec<Attribute>, NatDefinitionElabError> {
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
        if let Some(row) = attribute(syntax)? {
            rows.push(row);
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
        return Err(refused("executable attributes on one admitted constant"));
    }
    Ok(rows)
}

/// Parse standalone command attributes without weakening unknown-attribute refusal.
pub fn command(syntax: &Syntax) -> Result<(Vec<Attribute>, Vec<Name>), NatDefinitionElabError> {
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
    let mut rows = Vec::new();
    for (index, entry) in entries.iter().enumerate() {
        if index % 2 == 0 {
            rows.push(attribute(entry)?.ok_or_else(|| refused("an executable attribute"))?);
        } else {
            expect_atom(entry, ",", "attribute separator")?;
        }
    }
    let names = expect_null_args(&parts[4], "attribute declarations")?;
    if names.len() > MAX_ATTRIBUTE_ITEMS {
        return Err(failure(SourceInferenceError::ResourceLimit));
    }
    let names = names
        .iter()
        .map(|name| {
            let Syntax::Ident { val, .. } = name else {
                return Err(refused("an attribute declaration name"));
            };
            Ok(val.clone())
        })
        .collect::<Result<Vec<_>, _>>()?;
    if names.is_empty() {
        return Err(refused("attribute declarations"));
    }
    Ok((rows, names))
}

/// Use the same namespace, private-name, alias and protected-name rules as
/// ordinary source elaboration, rather than guessing an exact global spelling.
pub fn resolve(
    environment: &Environment,
    scope: &SourceScope,
    requested: &Name,
) -> Result<Option<Name>, NatDefinitionElabError> {
    let aliases = AliasTable::read(environment).map_err(|error| match error {
        crate::aliases::AliasError::Limit => failure(SourceInferenceError::ResourceLimit),
        _ => failure(SourceInferenceError::Scope),
    })?;
    let protected = ProtectedNames::read(environment).map_err(|error| match error {
        crate::protected_names::ProtectedError::Limit => {
            failure(SourceInferenceError::ResourceLimit)
        }
        error => failure(SourceInferenceError::ProtectedJournal(error)),
    })?;
    scope
        .resolve_with_aliases(
            requested,
            |name| environment.contains(name),
            &aliases,
            &protected,
        )
        .map_err(|error| failure(SourceInferenceError::NameScope(error)))
}

pub fn apply(
    environment: &Environment,
    scope: &SourceScope,
    declaration: &Name,
    rows: &[Attribute],
    standalone: bool,
) -> Result<Environment, NatDefinitionElabError> {
    if standalone
        && (!matches!(environment.find(declaration), Some(ConstantInfo::Axiom(_)))
            || ExternTable::read(environment)
                .map_err(extern_error)?
                .get(declaration)
                .is_some()
            || ImplementedByTable::read(environment)
                .map_err(implemented_error)?
                .get(declaration)
                .is_some()
            || rows.iter().any(|row| matches!(row, Attribute::Extern(_))))
    {
        // The pin has already generated a definition's IR before a standalone
        // update; a final journal cannot reconstruct that time-dependent state.
        return Err(refused(
            "initial standalone implemented_by on a bodyless axiom without an executable binding",
        ));
    }
    let mut result = environment.clone();
    for row in rows {
        result = match row {
            Attribute::ImplementedBy(requested) => {
                let target = resolve(&result, scope, requested)?.ok_or_else(|| {
                    failure(SourceInferenceError::ImplementedByJournal(
                        crate::implemented_by::ImplementedByError::UnknownDeclaration(
                            requested.clone(),
                        ),
                    ))
                })?;
                crate::implemented_by::register(&result, declaration, &target)
                    .map_err(implemented_error)?
            }
            Attribute::Extern(entries) => {
                crate::externs::register(&result, declaration, entries.clone())
                    .map_err(extern_error)?
            }
        };
    }
    // Every registration validates its signature/payload, including overwritten
    // rows. Cycles concern the final map after applying the complete list.
    ImplementedByTable::read(&result).map_err(implemented_error)?;
    ExternTable::read(&result).map_err(extern_error)?;
    Ok(result)
}
