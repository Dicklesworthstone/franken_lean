//! Exact native source grammar journals. The payload is deliberately not a
//! Lean `.olean` extension: parser descriptions and quoted templates remain
//! native data until their generated parser/macro declarations can be emitted.
//! Reuse the lossless Syntax codec, including pre-resolution and source spans.
use super::*;
use fln_env::extensions::{
    CheckpointSemantics, ExtensionDescriptor, MergeSemantics, PayloadProvenance,
};
use fln_parse::extensions::{Descr, IdentBehavior, NativeSyntaxModule, SyntaxDecl};
use fln_syntax::pin_syntax::{self, PinTrees};
use fln_syntax::source::{BytePos, ByteSpan, SourceInfo};
use std::sync::Arc;

mod descriptions;

const MAGIC: &[u8] = b"FLNSOURCEGRAMMAR\x01";
const MAX_ROWS: usize = 4096;
const MAX_BYTES: usize = 64 * 1024 * 1024;
const MAX_ROW_BYTES: usize = 4 * 1024 * 1024;

fn name() -> Name {
    Name::from_components(["FrankenLean", "sourceGrammar", "v1"])
}

fn descriptor() -> ExtensionDescriptor {
    ExtensionDescriptor {
        name: name(),
        merge: MergeSemantics::AppendOrdered,
        checkpoint: CheckpointSemantics::FullJournal,
        provenance: PayloadProvenance::Understood,
    }
}

pub(super) fn present(environment: &Environment) -> bool {
    environment
        .extension(&name())
        .is_some_and(|state| !state.is_empty())
}

fn malformed() -> EngineExecutionError {
    EngineExecutionError::NotImplemented {
        feature: "malformed native source grammar journal",
    }
}

fn limit(resource: &'static str, limit: usize) -> EngineExecutionError {
    EngineExecutionError::SourceScopeLimit { resource, limit }
}

fn ident(value: &Name) -> Syntax {
    Syntax::Ident {
        info: SourceInfo::None,
        raw_val: ByteSpan::empty_at(BytePos(0)),
        val: value.clone(),
        preresolved: Vec::new(),
    }
}

fn atom(value: impl ToString) -> Syntax {
    Syntax::atom(SourceInfo::None, value.to_string())
}

fn node(kind: &str, args: Vec<Syntax>) -> Syntax {
    Syntax::node(Name::str(name(), kind), args)
}

fn optional_name(value: Option<&Name>) -> Syntax {
    node("optional", value.map(ident).into_iter().collect())
}

fn as_name(value: &Syntax) -> Result<Name, EngineExecutionError> {
    match value {
        Syntax::Ident { val, .. } => Ok(val.clone()),
        _ => Err(malformed()),
    }
}

fn as_text(value: &Syntax) -> Result<&str, EngineExecutionError> {
    match value {
        Syntax::Atom { val, .. } => Ok(val),
        _ => Err(malformed()),
    }
}

fn as_u32(value: &Syntax) -> Result<u32, EngineExecutionError> {
    as_text(value)?.parse().map_err(|_| malformed())
}

fn as_bool(value: &Syntax) -> Result<bool, EngineExecutionError> {
    match as_text(value)? {
        "false" => Ok(false),
        "true" => Ok(true),
        _ => Err(malformed()),
    }
}

fn children<'a>(value: &'a Syntax, suffix: &str) -> Result<&'a [Syntax], EngineExecutionError> {
    match value {
        Syntax::Node { kind, args, .. } if *kind == Name::str(name(), suffix) => Ok(args),
        _ => Err(malformed()),
    }
}

fn as_optional_name(value: &Syntax) -> Result<Option<Name>, EngineExecutionError> {
    match children(value, "optional")? {
        [] => Ok(None),
        [name] => as_name(name).map(Some),
        _ => Err(malformed()),
    }
}

fn encode(
    header: Syntax,
    rhs: Option<&Syntax>,
    source: &[u8],
) -> Result<Arc<[u8]>, EngineExecutionError> {
    if source.len() > MAX_ROW_BYTES {
        return Err(limit("native grammar source bytes", MAX_ROW_BYTES));
    }
    let dump = pin_syntax::print(
        &PinTrees {
            header,
            commands: rhs.cloned().into_iter().collect(),
            messages: Vec::new(),
        },
        source,
    )
    .map_err(|_| malformed())?;
    let size = MAGIC.len() + 8 + source.len() + dump.len();
    if size > MAX_ROW_BYTES {
        return Err(limit("native grammar journal entry bytes", MAX_ROW_BYTES));
    }
    let mut payload = Vec::new();
    payload
        .try_reserve_exact(size)
        .map_err(|_| EngineExecutionError::AllocationFailure {
            resource: "native grammar journal entry",
            requested: size,
        })?;
    payload.extend_from_slice(MAGIC);
    payload.extend_from_slice(&(source.len() as u64).to_le_bytes());
    payload.extend_from_slice(source);
    payload.extend_from_slice(dump.as_bytes());
    Ok(payload.into())
}

pub(super) fn publish(
    environment: &Environment,
    module: &NativeSyntaxModule,
    sources: &BTreeMap<Name, Arc<[u8]>>,
    declared_syntax: bool,
) -> Result<Environment, EngineExecutionError> {
    if !declared_syntax {
        return Ok(environment.clone());
    }
    let mut payloads = Vec::new();
    let rows = module
        .categories
        .len()
        .saturating_add(module.declarations.len())
        .saturating_add(1);
    if environment
        .extension(&name())
        .map_or(0, |state| state.len())
        .saturating_add(rows)
        > MAX_ROWS
    {
        return Err(limit("native grammar journal entries", MAX_ROWS));
    }
    // Even local-only syntax creates parser/macro declarations in the pin.
    // Keep its use visible to the artifact-support gate without exporting any
    // local parser or macro activation to downstream modules.
    payloads.push(encode(node("usage", Vec::new()), None, &[])?);
    for (category, behavior) in &module.categories {
        payloads.push(encode(
            node("category", vec![ident(category), atom(*behavior as u8)]),
            None,
            &[],
        )?);
    }
    for decl in &module.declarations {
        let descr = descriptions::encode(&decl.descr)?;
        let rule = module.rules.get(&decl.decl);
        let variables = rule.map_or_else(Vec::new, |rule| {
            rule.variables
                .iter()
                .map(|(index, name)| node("variable", vec![atom(index), ident(name)]))
                .collect()
        });
        let header = node(
            "declaration",
            vec![
                ident(&decl.module),
                ident(&decl.decl),
                optional_name(decl.category.as_ref()),
                atom(decl.leading),
                atom(decl.priority),
                optional_name(decl.scope.as_ref()),
                descr,
                node("variables", variables),
                atom(rule.is_some_and(|rule| rule.prechecked)),
            ],
        );
        let source = sources
            .get(&decl.decl)
            .map_or(&[][..], |source| source.as_ref());
        payloads.push(encode(header, rule.map(|rule| &rule.rhs), source)?);
    }
    let mut result = environment.clone();
    if result.extension(&name()).is_none() {
        result = result
            .register_extension(descriptor())
            .map_err(|_| malformed())?;
    }
    let state = result.extension(&name()).ok_or_else(malformed)?;
    if state.descriptor != descriptor() {
        return Err(malformed());
    }
    if state.len().saturating_add(payloads.len()) > MAX_ROWS {
        return Err(limit("native grammar journal entries", MAX_ROWS));
    }
    let mut total = 0usize;
    for payload in state
        .entries()
        .map(|entry| entry.payload.as_ref())
        .chain(payloads.iter().map(AsRef::as_ref))
    {
        total = total
            .checked_add(payload.len())
            .filter(|total| *total <= MAX_BYTES)
            .ok_or_else(|| limit("native grammar journal bytes", MAX_BYTES))?;
    }
    for payload in payloads {
        result = result
            .push_extension_entry(&name(), payload)
            .map_err(|_| malformed())?;
    }
    Ok(result)
}

pub(super) fn load(
    environment: &Environment,
    file: &mut FileGrammar,
) -> Result<(), EngineExecutionError> {
    let Some(state) = environment.extension(&name()) else {
        return Ok(());
    };
    if state.descriptor != descriptor() {
        return Err(malformed());
    }
    if state.len() > MAX_ROWS {
        return Err(limit("native grammar journal entries", MAX_ROWS));
    }
    let mut total = 0usize;
    for entry in state.entries() {
        let payload = entry.payload.as_ref();
        total = total
            .checked_add(payload.len())
            .filter(|total| *total <= MAX_BYTES)
            .ok_or_else(|| limit("native grammar journal bytes", MAX_BYTES))?;
        if payload.len() > MAX_ROW_BYTES {
            return Err(limit("native grammar journal entry bytes", MAX_ROW_BYTES));
        }
        let rest = payload.strip_prefix(MAGIC).ok_or_else(malformed)?;
        let (length, rest) = rest.split_at_checked(8).ok_or_else(malformed)?;
        let length = usize::try_from(u64::from_le_bytes(
            length.try_into().map_err(|_| malformed())?,
        ))
        .map_err(|_| malformed())?;
        let (source, dump) = rest.split_at_checked(length).ok_or_else(malformed)?;
        let dump = std::str::from_utf8(dump).map_err(|_| malformed())?;
        let trees = pin_syntax::read(dump, source).map_err(|_| malformed())?;
        if !trees.messages.is_empty() {
            return Err(malformed());
        }
        if children(&trees.header, "usage").is_ok_and(<[Syntax]>::is_empty) {
            if !trees.commands.is_empty() {
                return Err(malformed());
            }
            continue;
        }
        let mut module = NativeSyntaxModule::default();
        if let Ok([category, behavior]) = children(&trees.header, "category") {
            if !trees.commands.is_empty() {
                return Err(malformed());
            }
            let behavior = match as_u32(behavior)? {
                0 => IdentBehavior::Default,
                1 => IdentBehavior::Symbol,
                2 => IdentBehavior::Both,
                _ => return Err(malformed()),
            };
            module.categories.insert(as_name(category)?, behavior);
        } else {
            let [
                owner,
                name,
                category,
                leading,
                priority,
                scope,
                descr,
                variables,
                prechecked,
            ] = children(&trees.header, "declaration")?
            else {
                return Err(malformed());
            };
            let name = as_name(name)?;
            module.declarations.push(Arc::new(SyntaxDecl {
                module: as_name(owner)?,
                decl: name.clone(),
                category: as_optional_name(category)?,
                leading: as_bool(leading)?,
                priority: as_u32(priority)?,
                scope: as_optional_name(scope)?,
                descr: descriptions::decode(descr)?,
            }));
            let variables = children(variables, "variables")?
                .iter()
                .map(|value| {
                    let [index, name] = children(value, "variable")? else {
                        return Err(malformed());
                    };
                    Ok((as_u32(index)? as usize, as_name(name)?))
                })
                .collect::<Result<Vec<_>, EngineExecutionError>>()?;
            match trees.commands.as_slice() {
                [] if variables.is_empty() && !as_bool(prechecked)? => {}
                [rhs] => {
                    module.rules.insert(
                        name,
                        Arc::new(NotationRule {
                            variables,
                            rhs: rhs.clone(),
                            prechecked: as_bool(prechecked)?,
                        }),
                    );
                }
                _ => return Err(malformed()),
            }
        }
        file.import_native(&module)
            .map_err(|feature| EngineExecutionError::NotImplemented { feature })?;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use fln_syntax::tree::Preresolved;

    fn grammar() -> FileGrammar {
        FileGrammar::new(false, &[], Some(Name::from_components(["Consumer"])))
            .unwrap()
            .own_syntax_only()
    }

    #[test]
    fn native_journal_retains_exact_names_hygiene_sources_and_descriptions() {
        let owner = Name::from_components(["Lib"]);
        let kind = Name::str(Name::num(owner.clone(), 7), "quoted.name");
        let source: Arc<[u8]> = Arc::from(" α ".as_bytes());
        let value =
            fln_syntax::hygiene::add_macro_scope(&owner, &Name::from_components(["value"]), 9)
                .unwrap();
        let rhs = Syntax::Ident {
            info: SourceInfo::Original {
                leading: ByteSpan::new(BytePos(0), BytePos(1)).unwrap(),
                pos: BytePos(1),
                trailing: ByteSpan::new(BytePos(3), BytePos(4)).unwrap(),
                end_pos: BytePos(3),
            },
            raw_val: ByteSpan::new(BytePos(1), BytePos(3)).unwrap(),
            val: value.clone(),
            preresolved: vec![
                Preresolved::Namespace { ns: owner.clone() },
                Preresolved::Decl {
                    name: value,
                    fields: vec!["field.with.dot".into()],
                },
            ],
        };
        let rule = Arc::new(NotationRule {
            variables: vec![(1, Name::num(Name::anonymous(), 3))],
            rhs,
            prechecked: true,
        });
        let declaration = Arc::new(SyntaxDecl {
            module: owner.clone(),
            decl: kind.clone(),
            category: Some(Name::from_components(["term"])),
            leading: true,
            priority: 173,
            scope: Some(owner),
            descr: Descr::Node {
                kind: kind.clone(),
                prec: 900,
                body: Box::new(Descr::Symbol("α".into())),
            },
        });
        let module = NativeSyntaxModule {
            declarations: vec![declaration.clone()],
            categories: BTreeMap::new(),
            rules: BTreeMap::from([(kind.clone(), rule.clone())]),
        };
        let base = Environment::new();
        let recorded = publish(
            &base,
            &module,
            &BTreeMap::from([(kind.clone(), source)]),
            true,
        )
        .unwrap();
        assert!(!present(&base));
        assert!(present(&recorded));
        let mut loaded = grammar();
        load(&recorded, &mut loaded).unwrap();
        assert_eq!(
            loaded.native_namespace_anchors(),
            std::slice::from_ref(&declaration.decl)
        );
        assert_eq!(
            loaded.rules().find(|(name, _)| **name == kind).unwrap().1,
            rule.as_ref()
        );
        assert!(
            loaded.export_native().unwrap().is_empty(),
            "imports are not recaptured as new entries"
        );
    }

    #[test]
    fn local_usage_is_recorded_without_activating_or_exporting_syntax() {
        let base = Environment::new();
        let recorded = publish(
            &base,
            &NativeSyntaxModule::default(),
            &BTreeMap::new(),
            true,
        )
        .unwrap();
        assert!(present(&recorded));
        assert_eq!(recorded.extension(&name()).unwrap().len(), 1);
        let mut loaded = grammar();
        load(&recorded, &mut loaded).unwrap();
        assert!(loaded.export_native().unwrap().is_empty());
        assert!(loaded.native_namespace_anchors().is_empty());
        assert!(matches!(
            SourceGrammar::for_environment(&recorded, None, true),
            Err(EngineExecutionError::NotImplemented { .. })
        ));
    }

    #[test]
    fn multiline_crlf_templates_keep_the_source_view_their_unicode_spans_address() {
        let mut library = SourceGrammar::for_module(Some(&Name::from_components(["Lib"])), false);
        assert!(
            library
                .declare("notation \"quoted\" =>\r\n  α".as_bytes(), |_| {
                    Resolution::Unchecked
                })
                .unwrap()
        );
        let expected: Vec<_> = library
            .file
            .rules()
            .map(|(kind, rule)| (kind.clone(), rule.clone()))
            .collect();
        let recorded = library.record(&Environment::new()).unwrap();
        let mut loaded = grammar();
        load(&recorded, &mut loaded).unwrap();
        let actual: Vec<_> = loaded
            .rules()
            .map(|(kind, rule)| (kind.clone(), rule.clone()))
            .collect();
        assert_eq!(actual, expected);
    }

    #[test]
    fn damaged_and_oversized_native_journals_fail_before_returning_a_grammar() {
        for payload in [
            Arc::<[u8]>::from(&MAGIC[..MAGIC.len() - 1]),
            Arc::from([MAGIC, &[255; 8]].concat()),
        ] {
            let env = Environment::new()
                .register_extension(descriptor())
                .unwrap()
                .push_extension_entry(&name(), payload)
                .unwrap();
            assert!(SourceGrammar::for_environment(&env, None, false).is_err());
        }
        let source = vec![0; MAX_ROW_BYTES + 1];
        assert!(matches!(
            encode(node("usage", vec![]), None, &source),
            Err(EngineExecutionError::SourceScopeLimit { .. })
        ));
        let mut descr =
            descriptions::encode(&Descr::Const(Name::from_components(["term"]))).unwrap();
        let Syntax::Node { args, .. } = &mut descr else {
            unreachable!()
        };
        args[0] = atom("(const \"1\")");
        assert!(
            descriptions::decode(&descr).is_err(),
            "a name ordinal must match its exact table position"
        );
    }
}
