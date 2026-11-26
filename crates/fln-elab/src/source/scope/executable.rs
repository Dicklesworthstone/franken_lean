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
    Unbox,
    AnonymousConstructor,
    Coe,
    MatchPattern,
    WeakSpecialize,
    NeverExtract,
    NoSpecialize,
    Export(Name),
    SuggestFor(Vec<Name>),
    InheritDoc(Name),
}

impl Attribute {
    /// Persistent plain tags do not replace or suppress a declaration's code.
    pub fn is_tag(&self) -> bool {
        matches!(
            self,
            Self::Unbox
                | Self::AnonymousConstructor
                | Self::Coe
                | Self::MatchPattern
                | Self::WeakSpecialize
                | Self::NeverExtract
                | Self::NoSpecialize
                | Self::Export(_)
                | Self::SuggestFor(_)
                | Self::InheritDoc(_)
        )
    }

    /// Unlike declaration-owned tags, the pin's coercion map permits registering
    /// an already imported function. The registration belongs to this module.
    pub fn permits_imported_target(&self) -> bool {
        matches!(self, Self::Coe)
    }
}

/// Mirror pinned `Lean/Compiler/ExportAttr.lean:15-22`: every component of an
/// `@[export ...]` symbol must be a string segment starting with an alphabetic
/// character followed by alphanumeric or `_` characters.
fn is_valid_cpp_id(segment: &str) -> bool {
    let mut chars = segment.chars();
    let Some(first) = chars.next() else {
        return false;
    };
    first.is_alphabetic() && chars.all(|ch| ch.is_alphanumeric() || ch == '_')
}

fn is_valid_cpp_name(name: &Name) -> bool {
    if name.is_anonymous() {
        return false;
    }
    let mut current = name.clone();
    for _ in 0..1024 {
        match current.leaf_view() {
            fln_core::name::LeafView::Anonymous => return true,
            fln_core::name::LeafView::Str(segment) if is_valid_cpp_id(segment) => {
                current = current.parent();
            }
            _ => return false,
        }
    }
    false
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

pub(in crate::source) fn match_pattern_error(
    error: crate::match_pattern::MatchPatternError,
) -> NatDefinitionElabError {
    use crate::match_pattern::MatchPatternError;
    match error {
        MatchPatternError::Limit => failure(SourceInferenceError::ResourceLimit),
        MatchPatternError::NotDefinition(_) => refused("match_pattern on an exposed definition"),
        MatchPatternError::UnknownDeclaration(_) => {
            refused("match_pattern on an admitted declaration")
        }
        MatchPatternError::Malformed => refused("a valid match_pattern journal"),
    }
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
            if val == &Name::from_components(["unbox"]) {
                expect_empty_null(argument, "unbox without arguments")?;
                Attribute::Unbox
            } else if val == &Name::from_components(["match_pattern"]) {
                expect_empty_null(argument, "match_pattern without arguments")?;
                Attribute::MatchPattern
            } else if val == &Name::from_components(["pp_using_anonymous_constructor"]) {
                expect_empty_null(argument, "pp_using_anonymous_constructor without arguments")?;
                Attribute::AnonymousConstructor
            } else if val == &Name::from_components(["weak_specialize"]) {
                expect_empty_null(argument, "weak_specialize without arguments")?;
                Attribute::WeakSpecialize
            } else if val == &Name::from_components(["never_extract"]) {
                expect_empty_null(argument, "never_extract without arguments")?;
                Attribute::NeverExtract
            } else if val == &Name::from_components(["nospecialize"]) {
                expect_empty_null(argument, "nospecialize without arguments")?;
                Attribute::NoSpecialize
            } else if val == &Name::from_components(["inherit_doc"]) {
                let [Syntax::Ident { val, .. }] = expect_null_args(argument, "inherit_doc target")?
                else {
                    return Err(refused("one inherit_doc target declaration name"));
                };
                if val.is_anonymous() {
                    return Err(refused("a named inherit_doc target"));
                }
                Attribute::InheritDoc(val.clone())
            } else if val == &Name::from_components(["suggest_for"]) {
                let [Syntax::Ident { val, .. }] = expect_null_args(argument, "suggest_for target")?
                else {
                    return Err(refused("one suggest_for target name"));
                };
                if val.is_anonymous() {
                    return Err(refused("a named suggest_for target"));
                }
                Attribute::SuggestFor(vec![val.clone()])
            } else if val == &Name::from_components(["implemented_by"]) {
                let [Syntax::Ident { val, .. }] =
                    expect_null_args(argument, "implemented_by target")?
                else {
                    return Err(refused("one implemented_by declaration name"));
                };
                if val.is_anonymous() {
                    return Err(refused("a named implemented_by target"));
                }
                Attribute::ImplementedBy(val.clone())
            } else {
                return Ok(None);
            }
        }
        Syntax::Node { kind, args, .. } if kind == &parser_kind(&["Attr", "export"]) => {
            let [keyword, target] = args.as_slice() else {
                return Err(refused("export attribute"));
            };
            expect_atom(keyword, "export", "export attribute keyword")?;
            let Syntax::Ident { val, .. } = target else {
                return Err(refused("an export symbol name"));
            };
            if !is_valid_cpp_name(val) {
                return Err(refused("a valid C++ export symbol name"));
            }
            Attribute::Export(val.clone())
        }
        Syntax::Node { kind, args, .. }
            if kind == &Name::from_components(["Lean", "suggest_for"]) =>
        {
            let [keyword, targets] = args.as_slice() else {
                return Err(refused("suggest_for attribute"));
            };
            expect_atom(keyword, "suggest_for", "suggest_for attribute keyword")?;
            let targets = expect_null_args(targets, "suggest_for targets")?;
            if targets.is_empty() {
                return Err(refused("at least one suggest_for identifier"));
            }
            if targets.len() > MAX_ATTRIBUTE_ITEMS {
                return Err(failure(SourceInferenceError::ResourceLimit));
            }
            let mut names = Vec::with_capacity(targets.len());
            for target in targets {
                let Syntax::Ident { val, .. } = target else {
                    return Err(refused("a suggest_for identifier"));
                };
                if val.is_anonymous() {
                    return Err(refused("a named suggest_for identifier"));
                }
                names.push(val.clone());
            }
            Attribute::SuggestFor(names)
        }
        Syntax::Node { kind, args, .. }
            if kind == &Name::from_components(["Lean", "Attr", "coe"]) =>
        {
            let [keyword] = args.as_slice() else {
                return Err(refused("coe without arguments"));
            };
            expect_atom(keyword, "coe", "coe attribute keyword")?;
            Attribute::Coe
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
        && !(rows.iter().all(Attribute::is_tag)
            && ["structure", "inductive", "classInductive"]
                .iter()
                .any(|kind| declaration.kind() == Some(&parser_kind(&["Command", kind]))))
    {
        return Err(refused("executable attributes on one admitted constant"));
    }
    Ok(rows)
}

/// Resolve a data declaration's own inline tags after its checked
/// inductive bundle has been admitted. Generated constructors and projections
/// do not acquire their type's tags.
pub fn data_registration(
    syntax: &Syntax,
    scope: &SourceScope,
) -> Result<Option<(Name, Vec<Attribute>)>, NatDefinitionElabError> {
    let rows = registrations(syntax)?;
    if rows.is_empty() {
        return Ok(None);
    }
    let root = expect_node(
        syntax,
        &parser_kind(&["Command", "declaration"]),
        2,
        "data declaration",
    )?;
    let parts = if root[1].kind() == Some(&parser_kind(&["Command", "structure"])) {
        expect_node(
            &root[1],
            &parser_kind(&["Command", "structure"]),
            6,
            "data declaration",
        )?
    } else {
        super::super::inductive::command_parts(&root[1])?.1
    };
    let id = expect_node(
        &parts[1],
        &parser_kind(&["Command", "declId"]),
        2,
        "data declaration name",
    )?;
    let Syntax::Ident { val, .. } = &id[0] else {
        return Err(refused("a data declaration name"));
    };
    let name = scope
        .for_declaration(syntax)?
        .declaration_name(val)
        .map_err(|error| failure(SourceInferenceError::NameScope(error)))?;
    Ok(Some((name, rows)))
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
        && rows.iter().any(|row| !row.is_tag())
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
            Attribute::Unbox => {
                crate::unbox::register(&result, declaration).map_err(|error| match error {
                    crate::unbox::UnboxError::Limit => failure(SourceInferenceError::ResourceLimit),
                    crate::unbox::UnboxError::NotInductive(_) => {
                        refused("unbox on an inductive type")
                    }
                    crate::unbox::UnboxError::RecursiveInductive(_) => {
                        refused("unbox on a nonrecursive inductive type")
                    }
                    crate::unbox::UnboxError::UnknownDeclaration(_) => {
                        refused("unbox on an admitted declaration")
                    }
                    crate::unbox::UnboxError::Malformed => refused("a valid unbox journal"),
                })?
            }
            Attribute::MatchPattern => {
                // Public validation uses the exporting view at the pin. The
                // implementation's access to a hidden public body cannot make
                // it an exported pattern rule.
                if !standalone && scope.exports_declaration() && !scope.expose_definitions {
                    return Err(refused("match_pattern on an exposed public definition"));
                }
                crate::match_pattern::register(&result, declaration).map_err(match_pattern_error)?
            }
            Attribute::AnonymousConstructor => {
                crate::delaborator_tags::register_anonymous_constructor(&result, declaration)
                    .map_err(|error| match error {
                        crate::delaborator_tags::DelaboratorTagError::Limit => {
                            failure(SourceInferenceError::ResourceLimit)
                        }
                        crate::delaborator_tags::DelaboratorTagError::UnknownDeclaration(_) => {
                            refused("pp_using_anonymous_constructor on an admitted declaration")
                        }
                        _ => refused("a valid delaborator tag journal"),
                    })?
            }
            Attribute::Coe => {
                crate::delaborator_tags::coercions::register_source(&result, declaration).map_err(
                    |error| match error {
                        crate::delaborator_tags::DelaboratorTagError::Limit => {
                            failure(SourceInferenceError::ResourceLimit)
                        }
                        crate::delaborator_tags::DelaboratorTagError::UnknownDeclaration(_) => {
                            refused("coe on an admitted declaration")
                        }
                        crate::delaborator_tags::DelaboratorTagError::NoExplicitArgument(_) => {
                            refused("coe on a declaration with an explicit argument")
                        }
                        crate::delaborator_tags::DelaboratorTagError::UnsupportedTelescope(_) => {
                            refused("a supported coercion function telescope")
                        }
                        _ => refused("a valid coercion delaborator journal"),
                    },
                )?
            }
            Attribute::WeakSpecialize
            | Attribute::NeverExtract
            | Attribute::NoSpecialize
            | Attribute::Export(_)
            | Attribute::SuggestFor(_) => {
                if !result.contains(declaration) {
                    return Err(refused(
                        "an admitted declaration for compiler/hint attribute",
                    ));
                }
                result
            }
            Attribute::InheritDoc(target) => {
                if !result.contains(declaration) {
                    return Err(refused("an admitted declaration for inherit_doc"));
                }
                if resolve(&result, scope, target)?.is_none() {
                    return Err(refused("a known inherit_doc target declaration"));
                }
                result
            }
        };
    }
    // Every registration validates its signature/payload, including overwritten
    // rows. Cycles concern the final map after applying the complete list.
    ImplementedByTable::read(&result).map_err(implemented_error)?;
    ExternTable::read(&result).map_err(extern_error)?;
    Ok(result)
}
