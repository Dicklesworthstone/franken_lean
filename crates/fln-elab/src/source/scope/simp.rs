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
pub mod defeq;
pub mod export;
mod imports;
pub use imports::{ImportedSimpRule, import_rules, register_imported_proof};

/// A `prio` tree's value: a decimal numeral, `default`/`low`/`mid`/`high` (1000, 100, 500 and
/// 10000, vendored `src/Init/Notation.lean`), or either in parentheses. Priority arithmetic and
/// other radixes are refused.
pub(in crate::source) fn priority_value(
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
        return Err(refuse("decimal priority"));
    };
    if val.is_empty() || !val.bytes().all(|b| b.is_ascii_digit()) {
        return Err(refuse("decimal priority"));
    }
    val.parse::<u32>().map_err(|_| refuse("u32 priority"))
}

/// A code generator hint: an inlining kind (the pin's `inlineAttrs`, Lean/Compiler/InlineAttrs.lean),
/// or `specialize` without arguments (Lean/Compiler/Specialize.lean).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum CompilerHint {
    /// `inline`, `noinline`, `always_inline`, `inline_if_reduce` or, with `macro_inline: true`,
    /// `macro_inline`. The pin's `checkIsDefinition` applies to each.
    Inlining {
        macro_inline: bool,
    },
    Specialize,
}

/// A code generator hint. Only `macro_inline` changes a value: the pin's compiler unfolds such a
/// definition before evaluating its arguments (`fln_elab::macro_inline`); the others change neither
/// a verdict nor a value. These are enum and parametric attributes, so the pin refuses them `local`
/// or `scoped`, and refuses an inlining kind with arguments. `specialize f` names parameters the pin
/// checks, so it stays refused.
fn compiler_hint(
    attribute: &fln_syntax::tree::Syntax,
) -> Result<Option<CompilerHint>, crate::NatDefinitionElabError> {
    use super::super::*;
    let instance = expect_node(
        attribute,
        &parser_kind(&["Term", "attrInstance"]),
        2,
        "attribute instance",
    )?;
    let hint = match &instance[1] {
        Syntax::Node { kind, args, .. } if kind == &parser_kind(&["Attr", "simple"]) => {
            let [Syntax::Ident { val, .. }, argument] = args.as_slice() else {
                return Ok(None);
            };
            if ![
                "inline",
                "noinline",
                "always_inline",
                "inline_if_reduce",
                "macro_inline",
            ]
            .iter()
            .any(|hint| val == &Name::from_components([*hint]))
            {
                return Ok(None);
            }
            expect_empty_null(argument, "inlining attribute without arguments")?;
            CompilerHint::Inlining {
                macro_inline: val == &Name::from_components(["macro_inline"]),
            }
        }
        Syntax::Node { kind, args, .. } if kind == &parser_kind(&["Attr", "specialize"]) => {
            let [keyword, arguments] = args.as_slice() else {
                return Ok(None);
            };
            expect_atom(keyword, "specialize", "specialize attribute keyword")?;
            expect_empty_null(arguments, "specialize attribute without arguments")?;
            CompilerHint::Specialize
        }
        _ => return Ok(None),
    };
    let scope = expect_node(
        &instance[0],
        &parser_kind(&["Term", "attrKind"]),
        1,
        "attribute scope",
    )?;
    expect_empty_null(&scope[0], "global compiler hint")?;
    Ok(Some(hint))
}

/// A declaration's inlining attributes in order, `true` for `macro_inline`. Any other command
/// has none.
fn inlining_kinds(
    syntax: &fln_syntax::tree::Syntax,
) -> Result<Vec<bool>, crate::NatDefinitionElabError> {
    use super::super::*;
    let Syntax::Node { kind, args, .. } = syntax else {
        return Ok(Vec::new());
    };
    if kind != &parser_kind(&["Command", "declaration"]) || args.len() != 2 {
        return Ok(Vec::new());
    }
    let modifiers = expect_node(
        &args[0],
        &parser_kind(&["Command", "declModifiers"]),
        7,
        "declaration modifiers",
    )?;
    let mut kinds = Vec::new();
    for attribute in super::visibility::attributes(&modifiers[1])? {
        if let Some(CompilerHint::Inlining { macro_inline }) = compiler_hint(attribute)? {
            kinds.push(macro_inline);
        }
    }
    Ok(kinds)
}

/// Whether the declaration's inlining kind is `macro_inline`. The pin keeps one kind per
/// declaration and each attribute in order replaces it (`registerEnumAttributes`'s NameMap,
/// vendored `Lean/Attributes.lean`), so the last inlining attribute decides. [`registration`]
/// validates the attributes and the declaration kind; the elaborator refuses a recursive body.
pub fn macro_inline(
    syntax: &fln_syntax::tree::Syntax,
) -> Result<bool, crate::NatDefinitionElabError> {
    Ok(inlining_kinds(syntax)?.last() == Some(&true))
}

/// Whether any attribute is `macro_inline`. The pin validates each one as it is applied
/// (`isValidMacroInline`), even when a later inlining attribute replaces its kind.
pub fn macro_inline_requested(
    syntax: &fln_syntax::tree::Syntax,
) -> Result<bool, crate::NatDefinitionElabError> {
    Ok(inlining_kinds(syntax)?.contains(&true))
}

/// A reducibility attribute: `reducible`, `irreducible`, `semireducible`, `implicit_reducible` or its
/// alias `instance_reducible` (vendored Lean/ReducibilityAttrs.lean). The pin refuses arguments
/// (`ensureNoArgs`) and the `scoped` kind. `local` would need a section-scoped status, which this
/// engine has no journal for, so it is refused too.
fn reducibility_attribute(
    attribute: &fln_syntax::tree::Syntax,
) -> Result<Option<crate::reducibility::Reducibility>, crate::NatDefinitionElabError> {
    use super::super::*;
    use crate::reducibility::Reducibility;
    let instance = expect_node(
        attribute,
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
    let status = match val.to_display_string().as_str() {
        "reducible" => Reducibility::Reducible,
        "irreducible" => Reducibility::Irreducible,
        "semireducible" => Reducibility::Semireducible,
        "implicit_reducible" | "instance_reducible" => Reducibility::ImplicitReducible,
        _ => return Ok(None),
    };
    expect_empty_null(argument, "reducibility attribute without arguments")?;
    let scope = expect_node(
        &instance[0],
        &parser_kind(&["Term", "attrKind"]),
        1,
        "attribute scope",
    )?;
    expect_empty_null(&scope[0], "global reducibility attribute")?;
    Ok(Some(status))
}

/// The reducibility status a declaration's attributes give it, validated in order as the pin's
/// `validate` does for a global attribute on a declaration of this file:
/// - only a definition takes one ("is not a definition");
/// - `reducible` and `implicit_reducible` need the status `semireducible`;
/// - `irreducible` needs `semireducible` or `implicit_reducible`;
/// - `semireducible` is refused ("declarations are `[semireducible]` by default").
///
/// `def` starts `semireducible` and `abbrev` `reducible`. An `instance` (`implicit_reducible`) is
/// refused here, as is any other declaration: the pin's `isDefinition` admits a data instance, but
/// its name is the instance command's, read elsewhere. Like `registration`, this only describes
/// metadata, installed on the successor of ordinary declaration admission.
pub fn reducibility(
    syntax: &fln_syntax::tree::Syntax,
) -> Result<Option<(Name, crate::reducibility::Reducibility)>, crate::NatDefinitionElabError> {
    use super::super::*;
    use crate::reducibility::Reducibility;
    let refuse = |expected| NatDefinitionElabError::UnexpectedSyntax { expected };
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
    let mut requested = Vec::new();
    for attribute in super::visibility::attributes(&modifiers[1])? {
        if let Some(status) = reducibility_attribute(attribute)? {
            requested.push(status);
        }
    }
    let inline_instance = instance_command::inline_registration(syntax)?.is_some();
    if requested.is_empty() && !inline_instance {
        return Ok(None);
    }
    let mut status = if declaration[1].kind() == Some(&parser_kind(&["Command", "definition"])) {
        Reducibility::Semireducible
    } else if declaration[1].kind() == Some(&parser_kind(&["Command", "abbrev"])) {
        Reducibility::Reducible
    } else if requested.is_empty() {
        return Ok(None);
    } else {
        return Err(refuse("a reducibility attribute on a `def` or an `abbrev`"));
    };
    for next in requested {
        let allowed = match next {
            Reducibility::Reducible | Reducibility::ImplicitReducible => {
                status == Reducibility::Semireducible
            }
            Reducibility::Irreducible => matches!(
                status,
                Reducibility::Semireducible | Reducibility::ImplicitReducible
            ),
            Reducibility::Semireducible => false,
        };
        if !allowed {
            return Err(refuse(
                "a reducibility attribute the declaration's status admits",
            ));
        }
        status = next;
    }
    let id = expect_node(
        &expect_node(
            &declaration[1],
            declaration[1].kind().ok_or_else(|| refuse("declaration"))?,
            if declaration[1].kind() == Some(&parser_kind(&["Command", "definition"])) {
                5
            } else {
                4
            },
            "definition",
        )?[1],
        &parser_kind(&["Command", "declId"]),
        2,
        "declaration id",
    )?;
    let Syntax::Ident { val, .. } = &id[0] else {
        return Err(NatDefinitionElabError::AnonymousDeclarationName);
    };
    if val.is_anonymous() {
        return Err(NatDefinitionElabError::AnonymousDeclarationName);
    }
    Ok(Some((val.clone(), status)))
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
    instance_command::default_registration(syntax)?;
    instance_command::inline_registration(syntax)?;
    let mut simp = None;
    let mut inlining = false;
    let mut macro_inline = false;
    for attribute in super::visibility::attributes(&modifiers[1])? {
        if super::visibility::exposure_attribute(attribute)?.is_some()
            || super::executable::attribute(attribute)?.is_some()
            || instance_command::default_attribute(attribute)?.is_some()
            || instance_command::attribute_priority(attribute)?.is_some()
        {
            continue;
        }
        if let Some(hint) = compiler_hint(attribute)? {
            if let CompilerHint::Inlining {
                macro_inline: requested,
            } = hint
            {
                inlining = true;
                macro_inline |= requested;
            }
            continue;
        }
        // Read by `reducibility`.
        if reducibility_attribute(attribute)?.is_some() {
            continue;
        }
        // Recorded once the declaration is admitted (`deprecated_registration`).
        if super::super::deprecated::deprecated_attribute(attribute)?.is_some() {
            continue;
        }
        if simp.replace(attribute).is_some() {
            return Err(NatDefinitionElabError::UnexpectedSyntax {
                expected: "one simp attribute beside exposure attributes",
            });
        }
    }
    // The pin's `checkIsDefinition`: a definition (`def`, `abbrev`, `instance`) or an opaque
    // constant; a theorem or an axiom is refused, "Declaration `d` is not a definition".
    if inlining
        && !["definition", "abbrev", "instance", "opaque"]
            .iter()
            .any(|kind| declaration[1].kind() == Some(&parser_kind(&["Command", kind])))
    {
        return Err(NatDefinitionElabError::UnexpectedSyntax {
            expected: "an inlining attribute on a definition or an opaque constant",
        });
    }
    // The pin validates each `macro_inline` it applies (`isValidMacroInline`, vendored
    // `Lean/Compiler/InlineAttrs.lean:31`): a definition, so not an opaque constant or a
    // `partial def` (an opaque at the pin), alone in its group and not recursive. The
    // elaborator refuses a recursive body, and the journal a definition in a mutual group.
    if macro_inline
        && (!["definition", "abbrev", "instance"]
            .iter()
            .any(|kind| declaration[1].kind() == Some(&parser_kind(&["Command", kind])))
            || super::super::partial::is_partial(syntax))
    {
        return Err(NatDefinitionElabError::UnexpectedSyntax {
            expected: "a `macro_inline` attribute on a non-recursive definition",
        });
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
// Auxiliary proofs add a new row form; existing v1/v2 rows keep their bytes.
const PROOF_MAGIC: &[u8] = b"FLNSIMP\x03";
// Native additions capture their persistent indexing/flags at registration.
// Later reducibility/class changes cannot rewrite already exported entries.
const SNAPSHOT_MAGIC: &[u8] = b"FLNSIMP\x04";
// A proof's type traversal and an imported library's journal are independent
// resources. Init alone carries more than 4,096 simp events.
const MAX_TYPE_STEPS: usize = 4096;
const MAX_BYTES: usize = 16384;
// Preserve the old 4,096 * 16,384-byte envelope while accounting for each
// retained entry handle too. Small rules may share the available space;
// admitting a larger library never grants more work to any proof classifier.
const MAX_JOURNAL_BYTES: u128 = 4096 * MAX_BYTES as u128;
const ENTRY_ACCOUNTING_BYTES: u128 =
    std::mem::size_of::<fln_env::extensions::ExtensionEntry>() as u128;

fn check_journal_capacity(entries: usize, payload_bytes: u128) -> Result<(), SimpSetError> {
    let bytes = (entries as u128)
        .checked_mul(ENTRY_ACCOUNTING_BYTES)
        .and_then(|overhead| overhead.checked_add(payload_bytes))
        .ok_or(SimpSetError::Limit)?;
    if bytes > MAX_JOURNAL_BYTES {
        return Err(SimpSetError::Limit);
    }
    Ok(())
}

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
    /// Attribute origin: erasure and explicit replacement act on this identity.
    pub declaration: Name,
    /// Already oriented proof, distinct from the origin and never an unfolding.
    pub proof: Option<Name>,
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
    for _ in 0..MAX_TYPE_STEPS {
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
    let mut remaining = MAX_TYPE_STEPS;
    is_proposition_with(env, expression, &mut || {
        remaining = remaining.checked_sub(1).ok_or(SimpSetError::Limit)?;
        Ok(())
    })
}

fn is_proposition_with(
    env: &Environment,
    expression: &Expr,
    spend: &mut impl FnMut() -> Result<(), SimpSetError>,
) -> Result<bool, SimpSetError> {
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
                return always_zero(level, parameters, arguments, spend);
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

enum JournalEntry {
    Add {
        entry: SimpEntry,
        snapshot: Option<export::Snapshot>,
    },
    Erase(Name),
}

/// One decoder for the live simp set and its artifact export. Neither consumer
/// may reinterpret an unknown operation or an imported proof as an unfolding.
fn decode_entry(payload: &[u8], order: usize) -> Result<JournalEntry, SimpSetError> {
    if payload.len() > MAX_BYTES {
        return Err(SimpSetError::Limit);
    }
    let mut bytes = payload;
    let header = take(&mut bytes, MAGIC.len())?;
    let proof_row = header == PROOF_MAGIC;
    let snapshot_row = header == SNAPSHOT_MAGIC;
    let structural = match header {
        header if header == MAGIC => false,
        header if header == STRUCTURAL_MAGIC || proof_row || snapshot_row => true,
        _ => return Err(SimpSetError::Malformed),
    };
    let operation = take(&mut bytes, 1)?[0];
    let declaration = if structural {
        crate::instances::read_name(&mut bytes).map_err(|_| SimpSetError::Malformed)?
    } else {
        read_name(&mut bytes)?
    };
    let proof = if proof_row {
        if operation != 2 {
            return Err(SimpSetError::Malformed);
        }
        Some(crate::instances::read_name(&mut bytes).map_err(|_| SimpSetError::Malformed)?)
    } else {
        None
    };
    let priority = number(&mut bytes)?;
    let reverse = match take(&mut bytes, 1)?[0] {
        0 => false,
        1 => true,
        _ => return Err(SimpSetError::Malformed),
    };
    let snapshot = if snapshot_row {
        if operation != 0 {
            return Err(SimpSetError::Malformed);
        }
        let snapshot = export::Snapshot::read(&mut bytes)?;
        if reverse && snapshot.is_supported() {
            return Err(SimpSetError::Malformed);
        }
        Some(snapshot)
    } else {
        None
    };
    if !bytes.is_empty() {
        return Err(SimpSetError::Malformed);
    }
    match operation {
        0 | 2 if operation == 0 || (proof_row && !reverse) => Ok(JournalEntry::Add {
            entry: SimpEntry {
                declaration,
                proof,
                priority,
                reverse,
                order,
            },
            snapshot,
        }),
        1 if priority == 0 && !reverse => Ok(JournalEntry::Erase(declaration)),
        _ => Err(SimpSetError::Malformed),
    }
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
    check_journal_capacity(extension.len(), extension.payload_bytes())?;
    let mut active: BTreeMap<Name, BTreeMap<Option<Name>, SimpEntry>> = BTreeMap::new();
    for (order, row) in extension.entries().enumerate() {
        match decode_entry(&row.payload, order)? {
            JournalEntry::Add { entry, .. } if entry.proof.is_none() => {
                validate(env, &entry.declaration, entry.reverse)?;
                active.insert(entry.declaration.clone(), BTreeMap::from([(None, entry)]));
            }
            JournalEntry::Erase(declaration) => {
                if !env.contains(&declaration) {
                    return Err(SimpSetError::UnknownDeclaration(declaration));
                }
                active.remove(&declaration);
            }
            JournalEntry::Add { entry, .. } => {
                let proof = entry.proof.as_ref().ok_or(SimpSetError::Malformed)?;
                if !env.contains(&entry.declaration) {
                    return Err(SimpSetError::UnknownDeclaration(entry.declaration));
                }
                imports::validate_proof(env, proof)?;
                // A persisted theorem group replaces a prior ordinary source
                // selection, but its auxiliary lemmas coexist with each other.
                let group = active.entry(entry.declaration.clone()).or_default();
                group.remove(&None);
                group.insert(Some(proof.clone()), entry);
            }
        }
    }
    let mut rows: Vec<SimpEntry> = active
        .into_values()
        .flat_map(BTreeMap::into_values)
        .collect();
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
        // A repeat refreshes the persistent path/flags in the pin. Retain the
        // event even when its name, priority and orientation are unchanged.
        return append(
            env,
            export::snapshot_payload(env, declaration, priority, reverse)?,
        );
    }
    if current.is_none() {
        return Ok(env.clone());
    }
    append(env, source_payload(declaration, rule)?)
}

fn source_payload(declaration: &Name, rule: Option<(u32, bool)>) -> Result<Vec<u8>, SimpSetError> {
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
    Ok(payload)
}

fn append(env: &Environment, payload: Vec<u8>) -> Result<Environment, SimpSetError> {
    let expected = descriptor();
    if payload.len() > MAX_BYTES {
        return Err(SimpSetError::Limit);
    }
    let (entries, bytes) = if let Some(state) = env.extension(&expected.name) {
        if state.descriptor != expected {
            return Err(SimpSetError::Malformed);
        }
        (
            state.len().checked_add(1).ok_or(SimpSetError::Limit)?,
            state
                .payload_bytes()
                .checked_add(payload.len() as u128)
                .ok_or(SimpSetError::Limit)?,
        )
    } else {
        (1, payload.len() as u128)
    };
    check_journal_capacity(entries, bytes)?;
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
        let legacy = append(
            &env,
            source_payload(&source_name, Some((500, false))).unwrap(),
        )
        .unwrap();
        let both = append(
            &legacy,
            source_payload(&private_name, Some((1000, false))).unwrap(),
        )
        .unwrap();
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
