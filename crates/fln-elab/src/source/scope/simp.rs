//! Native source simp sets, attached to immutable environment snapshots.
//!
//! This is a versioned source journal, not the Reference's serialized extension.
//! Entries select existing safe definitions or proposition lemmas; they carry no
//! proof authority. The ordinary elaborator and both checkers validate all uses.
use fln_core::{
    expr::{Expr, ExprNode},
    level::{Level, LevelView},
    name::Name,
};
use fln_env::{
    constants::{ConstantInfo, DefinitionSafety},
    environment::Environment,
    extensions::{CheckpointSemantics, ExtensionDescriptor, MergeSemantics, PayloadProvenance},
};
use std::collections::BTreeMap;

/// A `prio` tree's value: a decimal numeral, `default`/`low`/`mid`/`high` (1000, 100, 500 and
/// 10000, vendored `src/Init/Notation.lean`), or either in parentheses. Priority arithmetic and
/// other radixes are refused.
fn priority_value(
    priority: &fln_syntax::tree::Syntax,
) -> Result<u32, crate::NatDefinitionElabError> {
    use super::super::*;
    let refuse = |expected| NatDefinitionElabError::UnexpectedSyntax { expected };
    let Syntax::Node { kind, args, .. } = priority else {
        return Err(refuse("numeric priority"));
    };
    let named = [
        ("prioDefault", 1000),
        ("prioLow", 100),
        ("prioMid", 500),
        ("prioHigh", 10000),
    ];
    if let Some((_, value)) = named
        .iter()
        .find(|(name, _)| kind == &Name::from_components([*name]))
    {
        return Ok(*value);
    }
    if kind == &Name::from_components(["prio(_)"]) {
        let [_, inner, _] = args.as_slice() else {
            return Err(refuse("parenthesized priority"));
        };
        return priority_value(inner);
    }
    let numeral = expect_node(
        priority,
        &Name::from_components(["num"]),
        1,
        "priority numeral",
    )?;
    let [Syntax::Atom { val, .. }] = numeral else {
        return Err(refuse("priority numeral"));
    };
    if val.is_empty() || !val.bytes().all(|b| b.is_ascii_digit()) {
        return Err(refuse("decimal priority"));
    }
    val.parse::<u32>().map_err(|_| refuse("u32 priority"))
}

/// Decode a canonical inline request. This only describes metadata: it must be
/// installed on the successor of ordinary declaration admission, never before.
pub fn registration(
    syntax: &fln_syntax::tree::Syntax,
) -> Result<Option<(Name, u32, bool)>, crate::NatDefinitionElabError> {
    use super::super::*;
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
    let mut simp = None;
    for attribute in super::visibility::attributes(&modifiers[1])? {
        if super::visibility::exposure_attribute(attribute)?.is_some() {
            continue;
        }
        if simp.replace(attribute).is_some() {
            return Err(NatDefinitionElabError::UnexpectedSyntax {
                expected: "one simp attribute beside exposure attributes",
            });
        }
    }
    let Some(attribute) = simp else {
        return Ok(None);
    };
    let instance = expect_node(
        attribute,
        &parser_kind(&["Term", "attrInstance"]),
        2,
        "attribute instance",
    )?;
    let scope = expect_node(
        &instance[0],
        &parser_kind(&["Term", "attrKind"]),
        1,
        "attribute scope",
    )?;
    expect_empty_null(&scope[0], "global attribute")?;
    let parts = expect_node(
        &instance[1],
        &parser_kind(&["Attr", "simp"]),
        4,
        "simp attribute",
    )?;
    expect_atom(&parts[0], "simp", "simp attribute keyword")?;
    expect_empty_null(&parts[1], "default simp phase")?;
    let reverse = match expect_null_args(&parts[2], "simp direction")? {
        [] => false,
        [Syntax::Atom { val, .. }] if val == "←" || val == "<-" => true,
        _ => {
            return Err(NatDefinitionElabError::UnexpectedSyntax {
                expected: "simp direction",
            });
        }
    };
    let priority = match expect_null_args(&parts[3], "simp priority")? {
        [] => 1000,
        [priority] => priority_value(priority)?,
        _ => {
            return Err(NatDefinitionElabError::UnexpectedSyntax {
                expected: "numeric priority",
            });
        }
    };
    let definition = match &declaration[1] {
        Syntax::Node { kind, .. } if kind == &parser_kind(&["Command", "definition"]) => {
            expect_node(&declaration[1], kind, 5, "definition")?
        }
        Syntax::Node { kind, .. } if kind == &parser_kind(&["Command", "theorem"]) => {
            expect_node(&declaration[1], kind, 4, "theorem")?
        }
        _ => {
            return Err(NatDefinitionElabError::UnexpectedSyntax {
                expected: "simp definition or theorem",
            });
        }
    };
    let id = expect_node(
        &definition[1],
        &parser_kind(&["Command", "declId"]),
        2,
        "declaration id",
    )?;
    level_syntax::explicit_parameters(&id[1])?;
    let Syntax::Ident { val, .. } = &id[0] else {
        return Err(NatDefinitionElabError::AnonymousDeclarationName);
    };
    if val.is_anonymous() {
        return Err(NatDefinitionElabError::AnonymousDeclarationName);
    }
    Ok(Some((val.clone(), priority, reverse)))
}

const MAGIC: &[u8] = b"FLNSIMP\x01";
// Preserve the original bytes for ordinary source names. Internal names use
// the shared tagged structural codec in a separately versioned payload, so a
// private numeric component can never be mistaken for a source string "0".
const STRUCTURAL_MAGIC: &[u8] = b"FLNSIMP\x02";
const MAX_ROWS: usize = 4096;
const MAX_BYTES: usize = 16384;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SimpSetError {
    Malformed,
    Limit,
    UnknownDeclaration(Name),
    UnsupportedDeclaration(Name),
}
impl std::fmt::Display for SimpSetError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Malformed => f.write_str("malformed native source simp set"),
            Self::Limit => f.write_str("native source simp set resource limit"),
            Self::UnknownDeclaration(n) => {
                write!(f, "unknown simp declaration {}", n.to_display_string())
            }
            Self::UnsupportedDeclaration(n) => write!(
                f,
                "simp requires a safe definition or supported proof rule: {}",
                n.to_display_string()
            ),
        }
    }
}
impl std::error::Error for SimpSetError {}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SimpEntry {
    pub declaration: Name,
    pub priority: u32,
    pub reverse: bool,
    pub order: usize,
}
fn descriptor() -> ExtensionDescriptor {
    ExtensionDescriptor {
        name: Name::from_components(["FrankenLean", "sourceSimp", "v1"]),
        merge: MergeSemantics::AppendOrdered,
        checkpoint: CheckpointSemantics::FullJournal,
        provenance: PayloadProvenance::Understood,
    }
}
fn validate(env: &Environment, name: &Name, reverse: bool) -> Result<(), SimpSetError> {
    let info = env
        .find(name)
        .ok_or_else(|| SimpSetError::UnknownDeclaration(name.clone()))?;
    let mut ty = match info {
        ConstantInfo::Defn(d) if d.safety == DefinitionSafety::Safe && !reverse => return Ok(()),
        // Theorem admission already establishes that the complete telescope is
        // a proposition. Forward rules can now compile its conclusion to True
        // or a final refutation to False; no new typing authority is added here.
        ConstantInfo::Thm(_) if !reverse => return Ok(()),
        ConstantInfo::Axiom(a) if !a.is_unsafe && !reverse => {
            return if is_proposition(env, &a.base.type_)? {
                Ok(())
            } else {
                Err(SimpSetError::UnsupportedDeclaration(name.clone()))
            };
        }
        ConstantInfo::Thm(t) => &t.base.type_,
        ConstantInfo::Axiom(a) if !a.is_unsafe => &a.base.type_,
        _ => return Err(SimpSetError::UnsupportedDeclaration(name.clone())),
    };
    // Reversed rules retain the bounded equality/Iff classifier.
    let mut applications = 0;
    for _ in 0..MAX_ROWS {
        match ty.node() {
            ExprNode::MData { expr, .. } => ty = expr,
            ExprNode::ForallE { body, .. } if applications == 0 => ty = body,
            ExprNode::App { f, .. } => {
                applications += 1;
                ty = f;
            }
            ExprNode::Const { name: head, levels }
                if (*head == Name::from_components(["Eq"])
                    && applications == 3
                    && levels.len() == 1)
                    || (*head == Name::from_components(["Iff"])
                        && applications == 2
                        && levels.is_empty()) =>
            {
                return Ok(());
            }
            _ => return Err(SimpSetError::UnsupportedDeclaration(name.clone())),
        }
    }
    Err(SimpSetError::Limit)
}

/// The pin's `isPropQuick` / `isArrowProp` sufficient condition, extended to
/// closed telescope variables. Inspect only already admitted types and require
/// their instantiated result sort to be always zero. This does not reconstruct
/// terms or grant proof authority. Aliases/projections needing normalization
/// remain unsupported; the ordinary tactic driver still checks every use.
fn is_proposition(env: &Environment, expression: &Expr) -> Result<bool, SimpSetError> {
    let mut remaining = MAX_ROWS;
    let mut spend = || -> Result<(), SimpSetError> {
        remaining = remaining.checked_sub(1).ok_or(SimpSetError::Limit)?;
        Ok(())
    };
    let mut locals = Vec::new();
    let mut ty = expression;
    let mut arity = 0usize;
    let (mut head_type, parameters, arguments) = loop {
        spend()?;
        match ty.node() {
            ExprNode::MData { expr, .. } => ty = expr,
            ExprNode::ForallE {
                binder_type, body, ..
            } if arity == 0 => {
                locals.push(binder_type);
                ty = body;
            }
            ExprNode::LetE { type_, body, .. } => {
                locals.push(type_);
                ty = body;
            }
            ExprNode::App { f, .. } => {
                arity += 1;
                ty = f;
            }
            ExprNode::Const { name, levels } => {
                let Some(info) = env.find(name) else {
                    return Ok(false);
                };
                let base = info.constant_val();
                if base.level_params.len() != levels.len() {
                    return Ok(false);
                }
                break (&base.type_, base.level_params.as_slice(), levels.as_slice());
            }
            ExprNode::BVar { idx } => {
                let Some(index) = locals.len().checked_sub(*idx as usize + 1) else {
                    return Ok(false);
                };
                break (locals[index], &[][..], &[][..]);
            }
            _ => return Ok(false),
        }
    };
    loop {
        spend()?;
        match head_type.node() {
            ExprNode::MData { expr, .. } | ExprNode::LetE { body: expr, .. } => head_type = expr,
            ExprNode::ForallE { body, .. } if arity != 0 => {
                arity -= 1;
                head_type = body;
            }
            ExprNode::Sort { level } if arity == 0 => {
                return always_zero(level, parameters, arguments, &mut spend);
            }
            _ => return Ok(false),
        }
    }
}

/// Substitute declaration universe parameters once, with the same total meter
/// as the expression walk. Substituted arguments are in the caller's universe
/// context and must not be interpreted as the callee's parameters a second time.
fn always_zero(
    level: &Level,
    parameters: &[Name],
    arguments: &[Level],
    spend: &mut impl FnMut() -> Result<(), SimpSetError>,
) -> Result<bool, SimpSetError> {
    let mut pending = vec![(level, true)];
    while let Some((level, substitute)) = pending.pop() {
        spend()?;
        match level.view() {
            LevelView::Zero => {}
            LevelView::Max(left, right) => {
                pending.extend([(right, substitute), (left, substitute)]);
            }
            LevelView::IMax(_, right) => pending.push((right, substitute)),
            LevelView::Param(name) if substitute => {
                let mut replacement = None;
                for (parameter, argument) in parameters.iter().zip(arguments) {
                    spend()?;
                    if parameter == name {
                        replacement = Some(argument);
                        break;
                    }
                }
                let Some(replacement) = replacement else {
                    return Ok(false);
                };
                pending.push((replacement, false));
            }
            _ => return Ok(false),
        }
    }
    Ok(true)
}
fn take<'a>(bytes: &mut &'a [u8], n: usize) -> Result<&'a [u8], SimpSetError> {
    if bytes.len() < n {
        return Err(SimpSetError::Malformed);
    }
    let (head, tail) = bytes.split_at(n);
    *bytes = tail;
    Ok(head)
}
fn number(bytes: &mut &[u8]) -> Result<u32, SimpSetError> {
    Ok(u32::from_le_bytes(
        take(bytes, 4)?
            .try_into()
            .map_err(|_| SimpSetError::Malformed)?,
    ))
}
fn read_name(bytes: &mut &[u8]) -> Result<Name, SimpSetError> {
    let count = number(bytes)? as usize;
    if count == 0 || count > 256 {
        return Err(SimpSetError::Malformed);
    }
    let mut name = Name::anonymous();
    for _ in 0..count {
        let len = number(bytes)? as usize;
        if len == 0 || len > MAX_BYTES {
            return Err(SimpSetError::Malformed);
        }
        let part = std::str::from_utf8(take(bytes, len)?).map_err(|_| SimpSetError::Malformed)?;
        name = Name::str(name, part);
    }
    Ok(name)
}

/// Read active rows in deterministic priority order (newer ties first).
/// Corrupt entries and dangling references are errors, never an empty simp set.
pub fn read(env: &Environment) -> Result<Vec<SimpEntry>, SimpSetError> {
    let expected = descriptor();
    let Some(extension) = env.extension(&expected.name) else {
        return Ok(Vec::new());
    };
    if extension.descriptor != expected {
        return Err(SimpSetError::Malformed);
    }
    if extension.len() > MAX_ROWS {
        return Err(SimpSetError::Limit);
    }
    let mut active = BTreeMap::new();
    for (order, row) in extension.entries().enumerate() {
        if row.payload.len() > MAX_BYTES {
            return Err(SimpSetError::Limit);
        }
        let mut bytes: &[u8] = &row.payload;
        let structural = match take(&mut bytes, MAGIC.len())? {
            header if header == MAGIC => false,
            header if header == STRUCTURAL_MAGIC => true,
            _ => return Err(SimpSetError::Malformed),
        };
        let operation = take(&mut bytes, 1)?[0];
        let declaration = if structural {
            crate::instances::read_name(&mut bytes).map_err(|_| SimpSetError::Malformed)?
        } else {
            read_name(&mut bytes)?
        };
        let priority = number(&mut bytes)?;
        let reverse = match take(&mut bytes, 1)?[0] {
            0 => false,
            1 => true,
            _ => return Err(SimpSetError::Malformed),
        };
        if !bytes.is_empty() {
            return Err(SimpSetError::Malformed);
        }
        match operation {
            0 => {
                validate(env, &declaration, reverse)?;
                active.insert(
                    declaration.clone(),
                    SimpEntry {
                        declaration,
                        priority,
                        reverse,
                        order,
                    },
                );
            }
            1 if priority == 0 && !reverse => {
                if !env.contains(&declaration) {
                    return Err(SimpSetError::UnknownDeclaration(declaration));
                }
                active.remove(&declaration);
            }
            _ => return Err(SimpSetError::Malformed),
        }
    }
    let mut rows: Vec<SimpEntry> = active.into_values().collect();
    rows.sort_by(|a, b| {
        b.priority
            .cmp(&a.priority)
            .then_with(|| b.order.cmp(&a.order))
    });
    Ok(rows)
}

/// Add/update an already admitted rule, or erase it with `None`. The returned
/// environment owns the change; the caller's environment is never mutated.
pub fn update(
    env: &Environment,
    declaration: &Name,
    rule: Option<(u32, bool)>,
) -> Result<Environment, SimpSetError> {
    let rows = read(env)?;
    let current = rows.iter().find(|r| &r.declaration == declaration);
    if !env.contains(declaration) {
        return Err(SimpSetError::UnknownDeclaration(declaration.clone()));
    }
    if let Some((priority, reverse)) = rule {
        validate(env, declaration, reverse)?;
        if current.is_some_and(|r| r.priority == priority && r.reverse == reverse) {
            return Ok(env.clone());
        }
    } else if current.is_none() {
        return Ok(env.clone());
    }
    let expected = descriptor();
    if env
        .extension(&expected.name)
        .is_some_and(|ext| ext.len() >= MAX_ROWS)
    {
        return Err(SimpSetError::Limit);
    }
    let mut payload = if let Ok(parts) = super::components(declaration) {
        if parts.is_empty() {
            return Err(SimpSetError::Malformed);
        }
        let size = parts
            .iter()
            .try_fold(MAGIC.len() + 10, |n, s| n.checked_add(4 + s.len()))
            .ok_or(SimpSetError::Limit)?;
        if size > MAX_BYTES {
            return Err(SimpSetError::Limit);
        }
        let mut payload = MAGIC.to_vec();
        payload.push(u8::from(rule.is_none()));
        payload.extend((parts.len() as u32).to_le_bytes());
        for part in parts {
            payload.extend((part.len() as u32).to_le_bytes());
            payload.extend(part.as_bytes());
        }
        payload
    } else {
        let mut payload = STRUCTURAL_MAGIC.to_vec();
        payload.push(u8::from(rule.is_none()));
        crate::instances::write_name(declaration, &mut payload).map_err(|error| match error {
            crate::instances::InstanceRegistryError::Limit => SimpSetError::Limit,
            _ => SimpSetError::Malformed,
        })?;
        if payload.len().saturating_add(5) > MAX_BYTES {
            return Err(SimpSetError::Limit);
        }
        payload
    };
    let (priority, reverse) = rule.unwrap_or((0, false));
    payload.extend(priority.to_le_bytes());
    payload.push(u8::from(reverse));
    let env = if env.extension(&expected.name).is_none() {
        env.register_extension(expected.clone())
            .map_err(|_| SimpSetError::Malformed)?
    } else {
        env.clone()
    };
    env.push_extension_entry(&expected.name, payload)
        .map_err(|_| SimpSetError::Malformed)
}

#[cfg(test)]
mod tests {
    use super::*;
    use fln_syntax::tree::Syntax;

    fn child_mut<'a>(syntax: &'a mut Syntax, path: &[usize]) -> &'a mut Syntax {
        let mut syntax = syntax;
        for &index in path {
            let Syntax::Node { args, .. } = syntax else {
                panic!("test syntax path must name a node");
            };
            syntax = &mut args[index];
        }
        syntax
    }

    #[test]
    fn inline_metadata_requires_the_actual_attribute_shape_and_numeric_priority() {
        let parsed = fln_parse::parse_definition(
            "@[simp ← 900] theorem «x.y».{u} {A : Sort u} (x : A) : x = x := by rfl".as_bytes(),
        )
        .unwrap();
        assert_eq!(
            registration(parsed.syntax()).unwrap(),
            Some((Name::from_components(["x.y"]), 900, true))
        );
        let atom = |val: &str| Syntax::Atom {
            info: fln_syntax::source::SourceInfo::None,
            val: val.into(),
        };
        // The declaration's optional attrs / attributes / list / attrInstance
        // are real nested nodes. Near-matching names and ignored extras are not
        // registration requests, even when the declaration itself is valid.
        for (path, replacement) in [
            (&[0, 1, 0, 0][..], atom("@")),
            (&[0, 1, 0, 2][..], atom("}")),
            (&[0, 1, 0, 1, 0, 0, 0][..], atom("local")),
            (&[0, 1, 0, 1, 0, 1, 0][..], atom("unknown")),
            (&[0, 1, 0, 1, 0, 1, 1][..], atom("↓")),
            (&[0, 1, 0, 1, 0, 1, 2, 0][..], atom("->")),
            // The priority is the pin's `num` node itself (`numPrio` adds no node).
            (&[0, 1, 0, 1, 0, 1, 3, 0, 0][..], atom("4294967296")),
            (&[0, 1, 0, 1, 0, 1, 3, 0, 0][..], atom("-1")),
        ] {
            let mut syntax = parsed.syntax().clone();
            *child_mut(&mut syntax, path) = replacement;
            assert!(registration(&syntax).is_err(), "{path:?}");
        }
        let mut duplicate = parsed.syntax().clone();
        let Syntax::Node { args, .. } = child_mut(&mut duplicate, &[0, 1, 0, 1]) else {
            panic!("attribute list");
        };
        args.push(args[0].clone());
        assert!(registration(&duplicate).is_err());
    }

    #[test]
    fn unknown_and_corrupt_sets_fail_closed() {
        let env = Environment::new();
        assert!(read(&env).unwrap().is_empty());
        assert!(matches!(
            update(
                &env,
                &Name::from_components(["missing"]),
                Some((1000, false))
            ),
            Err(SimpSetError::UnknownDeclaration(_))
        ));
        for bytes in [vec![], MAGIC.to_vec(), b"FLNSIMP\x02".to_vec()] {
            let env = env
                .register_extension(descriptor())
                .unwrap()
                .push_extension_entry(&descriptor().name, bytes)
                .unwrap();
            assert_eq!(read(&env), Err(SimpSetError::Malformed));
        }
    }

    #[test]
    fn structural_names_coexist_with_legacy_rows_and_erase_by_exact_identity() {
        use fln_core::{expr::Expr, level::Level};
        use fln_env::constants::{ConstantVal, DefinitionVal, ReducibilityHints};

        let source_name = Name::from_components(["_private", "Main", "0", "rule"]);
        let private_name = Name::str(
            Name::num(Name::from_components(["_private", "Main"]), 0),
            "rule",
        );
        let mut env = Environment::new();
        for name in [&source_name, &private_name] {
            env = env
                .add_decl(ConstantInfo::Defn(DefinitionVal {
                    base: ConstantVal {
                        name: name.clone(),
                        level_params: Vec::new(),
                        type_: Expr::sort(Level::one()),
                    },
                    value: Expr::sort(Level::zero()),
                    hints: ReducibilityHints::Abbrev,
                    safety: DefinitionSafety::Safe,
                    all: vec![name.clone()],
                }))
                .unwrap();
        }
        let legacy = update(&env, &source_name, Some((500, false))).unwrap();
        let both = update(&legacy, &private_name, Some((1000, false))).unwrap();
        let rows = read(&both).unwrap();
        assert_eq!(
            rows.iter().map(|row| &row.declaration).collect::<Vec<_>>(),
            [&private_name, &source_name]
        );
        let payloads: Vec<_> = both
            .extension(&descriptor().name)
            .unwrap()
            .entries()
            .map(|row| row.payload.clone())
            .collect();
        assert!(payloads[0].starts_with(MAGIC));
        assert!(payloads[1].starts_with(STRUCTURAL_MAGIC));
        assert_eq!(
            legacy
                .extension(&descriptor().name)
                .unwrap()
                .entries()
                .next()
                .unwrap()
                .payload,
            payloads[0]
        );
        let erased = update(&both, &private_name, None).unwrap();
        assert_eq!(read(&erased).unwrap(), read(&legacy).unwrap());
        assert_eq!(read(&both).unwrap(), rows);

        // A partial tagged name is a malformed registry, not a missing rule.
        let malformed = legacy
            .push_extension_entry(
                &descriptor().name,
                STRUCTURAL_MAGIC
                    .iter()
                    .copied()
                    .chain([0, 1, 0, 1, 0])
                    .collect::<Vec<_>>(),
            )
            .unwrap();
        assert_eq!(read(&malformed), Err(SimpSetError::Malformed));
    }
}
