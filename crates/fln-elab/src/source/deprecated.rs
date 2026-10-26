//! `@[deprecated]` in source: the attribute as written on a declaration, the entry it records
//! once the declaration is admitted (`deprecatedAttr`'s `getParam`, vendored
//! `src/Lean/Linter/Deprecated.lean`), and the elaborator's record of every resolution of a
//! deprecated constant where the pin's `Linter.checkDeprecated` runs:
//! - an identifier naming a constant (`elabAppFnResolutions` and `resolveId?`, vendored
//!   `src/Lean/Elab/App.lean:1940`, `src/Lean/Elab/Term/TermElabM.lean:2194`), at the
//!   identifier;
//! - a field of generalized field notation that names a function (`LValResolution.const`,
//!   `src/Lean/Elab/App.lean:1875`), at the field;
//! - a `simp` argument naming a constant (`resolveSimpIdTheorem?`), at the identifier.
//!
//! It is off where the pin's `Term.Context.checkDeprecated` is: in the header and body of a
//! declaration that is itself `@[deprecated]` (`withDeprecationContextFromAttrs`,
//! `src/Lean/Elab/DeclModifiers.lean:358`). `#check c`, `#print c` and attribute arguments name
//! a constant without elaborating it, and record nothing. The option `linter.deprecated`, which
//! falls back to `linter.all` (`getLinterValue`), is read where the constant resolves.
use super::*;
use crate::deprecations::{DeprecatedUse, Deprecation};

/// At most this many uses in one elaboration: past it the elaboration is refused rather than a
/// warning dropped.
const MAX_USES: usize = 4096;

/// A `@[deprecated …]` attribute as written (`"deprecated" (ident)? (str)? ("(" "since" ":="
/// str ")")?`): the replacement as written, the message, the version, and the offset of the
/// attribute, where the pin logs its own warnings.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DeprecatedAttribute {
    pub replacement: Option<Name>,
    pub text: Option<String>,
    pub since: Option<String>,
    pub at: usize,
}

impl DeprecatedAttribute {
    /// The warnings the pin's `getParam` logs for this attribute, in its order
    /// (`src/Lean/Linter/Deprecated.lean:41-44`).
    pub fn warnings(&self) -> Vec<&'static str> {
        let mut warnings = Vec::new();
        if self.replacement.is_none() && self.text.is_none() {
            warnings.push(
                "`[deprecated]` attribute should specify either a new name or a deprecation message",
            );
        }
        if self.since.is_none() {
            warnings.push(
                "`[deprecated]` attribute should specify the date or library version at which the deprecation was introduced, using `(since := \"...\")`",
            );
        }
        warnings
    }
}

fn refused(expected: &'static str) -> NatDefinitionElabError {
    NatDefinitionElabError::UnexpectedSyntax { expected }
}

fn string_literal(syntax: &Syntax) -> Result<String, NatDefinitionElabError> {
    let parts = expect_node(
        syntax,
        &Name::str(Name::anonymous(), "str"),
        1,
        "string literal",
    )?;
    let Syntax::Atom { val, .. } = &parts[0] else {
        return Err(refused("string literal"));
    };
    fln_syntax::literal::decode_string(val).ok_or(NatDefinitionElabError::InvalidStringLiteral)
}

/// One attribute instance read as `@[deprecated …]`, or `None` for another attribute. A
/// `local` or `scoped` one is refused: the pin's parametric attributes are global only.
pub(in crate::source) fn deprecated_attribute(
    attribute: &Syntax,
) -> Result<Option<DeprecatedAttribute>, NatDefinitionElabError> {
    let instance = expect_node(
        attribute,
        &parser_kind(&["Term", "attrInstance"]),
        2,
        "attribute instance",
    )?;
    let kind = Name::from_components(["Lean", "deprecated"]);
    if instance[1].kind() != Some(&kind) {
        return Ok(None);
    }
    let scope = expect_node(
        &instance[0],
        &parser_kind(&["Term", "attrKind"]),
        1,
        "attribute scope",
    )?;
    expect_empty_null(&scope[0], "global deprecated attribute")?;
    let parts = expect_node(&instance[1], &kind, 4, "deprecated attribute")?;
    expect_atom(&parts[0], "deprecated", "deprecated attribute keyword")?;
    let at = parts[0]
        .info()
        .pos(false)
        .ok_or_else(|| refused("a positioned deprecated attribute"))?
        .0;
    let replacement = match expect_null_args(&parts[1], "deprecated replacement")? {
        [] => None,
        [Syntax::Ident { val, .. }] if !val.is_anonymous() => Some(val.clone()),
        _ => return Err(refused("deprecated replacement identifier")),
    };
    let text = match expect_null_args(&parts[2], "deprecated message")? {
        [] => None,
        [literal] => Some(string_literal(literal)?),
        _ => return Err(refused("deprecated message")),
    };
    let since = match expect_null_args(&parts[3], "deprecated since")? {
        [] => None,
        [open, keyword, assign, literal, close] => {
            expect_atom(open, "(", "deprecated since")?;
            expect_atom(keyword, "since", "deprecated since")?;
            expect_atom(assign, ":=", "deprecated since")?;
            expect_atom(close, ")", "deprecated since")?;
            Some(string_literal(literal)?)
        }
        _ => return Err(refused("deprecated since")),
    };
    Ok(Some(DeprecatedAttribute {
        replacement,
        text,
        since,
        at,
    }))
}

/// A declaration command's `@[deprecated …]`, or `None`. Two are refused: the pin's `setParam`
/// sets the parameter once.
pub fn deprecated_registration(
    syntax: &Syntax,
) -> Result<Option<DeprecatedAttribute>, NatDefinitionElabError> {
    let Syntax::Node { kind, args, .. } = syntax else {
        return Ok(None);
    };
    if kind != &parser_kind(&["Command", "declaration"]) || args.len() != 2 {
        return Ok(None);
    }
    let Some(modifiers) = args[0]
        .kind()
        .filter(|kind| **kind == parser_kind(&["Command", "declModifiers"]))
        .and(Some(&args[0]))
    else {
        return Ok(None);
    };
    let modifiers = expect_node(
        modifiers,
        &parser_kind(&["Command", "declModifiers"]),
        7,
        "declaration modifiers",
    )?;
    let mut found = None;
    for attribute in scope::visibility::attributes(&modifiers[1])? {
        if let Some(deprecated) = deprecated_attribute(attribute)?
            && found.replace(deprecated).is_some()
        {
            return Err(refused("one deprecated attribute"));
        }
    }
    Ok(found)
}

/// The entry a declaration command's `@[deprecated …]` records for `declared`, its admitted
/// declaration: the replacement resolved as `realizeGlobalConstNoOverloadWithInfo` resolves it,
/// in the declaration's namespace (`def A.f` is elaborated in `namespace A`). `None` without
/// the attribute. An unknown or ambiguous replacement is the command's refusal, as at the pin.
pub fn deprecation_entry(
    syntax: &Syntax,
    declared: &Name,
    environment: &Environment,
    kernel: Budget,
    scope: &SourceScope,
) -> Result<Option<Deprecation>, NatDefinitionElabError> {
    let Some(attribute) = deprecated_registration(syntax)? else {
        return Ok(None);
    };
    let new_name = match &attribute.replacement {
        None => None,
        Some(written) => {
            let mut declaration_scope = scope.clone();
            declaration_scope.namespace = scope.user_name(declared).parent();
            let mut context = Context::scoped(environment, kernel, &declaration_scope);
            let resolved = context
                .resolve_source_name(written)?
                .filter(|name| context.txn.env.contains(name))
                .ok_or_else(|| failure(SourceInferenceError::UnknownConstant(written.clone())))?;
            Some(resolved)
        }
    };
    Ok(Some(Deprecation {
        declaration: declared.clone(),
        new_name,
        text: attribute.text,
        since: attribute.since,
    }))
}

/// Whether two closed types are definitionally equal with only reducible constants unfolded:
/// the comparison `checkDeprecated` makes between a deprecated constant's type and its
/// replacement's (`withReducible <| isDefEqGuarded`). The pin's reducible transparency unfolds
/// `@[reducible]` constants; this unfolds those and `@[implicit_reducible]` ones (the
/// `instances` transparency). A comparison that does not complete counts as unequal, as a
/// guarded failure does.
pub fn reducibly_same_type(
    environment: &Environment,
    left: &Expr,
    right: &Expr,
    kernel: Budget,
) -> bool {
    if left == right {
        return true;
    }
    let mut context = Context::new(environment, kernel);
    let mut budget = UnificationBudget::new(kernel);
    budget.transparency = UnificationTransparency::Instances;
    context.txn.unify(left, right, budget).is_ok()
}

/// The node kind wrapping a pattern matrix's first input with the matrix's atomic
/// discriminants, which [`Context::recheck_identifiers`] reports before the input elaborates.
pub(super) const RECHECK: &str = "flnDiscriminantRecheck";

/// The identifier of an atomic discriminant (`x` or `@x`, the pin's `isAtomicDiscr`), if
/// `syntax` is one.
pub(super) fn atomic_discriminant(syntax: &Syntax) -> Option<&Syntax> {
    match syntax {
        Syntax::Ident { .. } => Some(syntax),
        Syntax::Node { kind, args, .. }
            if kind == &parser_kind(&["Term", "explicit"])
                && matches!(args.as_slice(), [_, Syntax::Ident { .. }]) =>
        {
            Some(&args[1])
        }
        _ => None,
    }
}

/// The span of `syntax`: its own source info, or its first and last positioned leaves.
pub(super) fn syntax_span(syntax: &Syntax) -> Option<(usize, usize)> {
    let info = syntax.info();
    if let (Some(at), Some(end)) = (info.pos(false), info.end_pos(false)) {
        return Some((at.0, end.0));
    }
    let leaves: Vec<_> = syntax
        .leaves()
        .into_iter()
        .filter_map(|leaf| match leaf {
            fln_syntax::attach::Attached::Token(info) => Some(info),
            fln_syntax::attach::Attached::Missing { .. } => None,
        })
        .collect();
    let at = leaves.iter().find_map(|info| info.pos(false))?;
    let end = leaves.iter().rev().find_map(|info| info.end_pos(false))?;
    Some((at.0, end.0))
}

/// Each component's span of the field path `path`, outermost first, when the path is spelled at
/// the end of `syntax` (`x.f.g`, or a projection's field): the pin's `identComponents` gives each
/// field its own position. A component that is not an identifier is spelled `«…»`.
pub(super) fn field_spans(syntax: Option<&Syntax>, path: &Name) -> Vec<Option<(usize, usize)>> {
    let parts = scope::components(path).unwrap_or_default();
    let mut spans = vec![None; parts.len()];
    let Some(mut end) = syntax.and_then(syntax_span).map(|(_, end)| end) else {
        return spans;
    };
    for (index, part) in parts.iter().enumerate().rev() {
        let plain = part
            .chars()
            .next()
            .is_some_and(fln_syntax::token::is_id_first)
            && part.chars().skip(1).all(fln_syntax::token::is_id_rest);
        let width = part.len() + if plain { 0 } else { "«»".len() };
        let Some(at) = end.checked_sub(width) else {
            break;
        };
        spans[index] = Some((at, end));
        let Some(previous) = at.checked_sub(1) else {
            break;
        };
        end = previous;
    }
    spans
}

impl Context {
    /// Record a resolution of `constant` at `span` where the pin's `checkDeprecated` runs, if
    /// the constant is `@[deprecated]` and the linter is on.
    pub(super) fn note_deprecated(
        &mut self,
        constant: &Name,
        span: Option<(usize, usize)>,
    ) -> Result<(), NatDefinitionElabError> {
        if !self.check_deprecated {
            return Ok(());
        }
        let options = &self.txn.options;
        let linted = match options.find(&Name::from_components(["linter", "deprecated"])) {
            Some(fln_core::options::DataValue::OfBool(value)) => *value,
            _ => options.get_bool(&Name::from_components(["linter", "all"]), true),
        };
        if !linted {
            return Ok(());
        }
        let deprecations = self
            .deprecation_cache
            .read(&self.txn.env)
            .map_err(|_| failure(SourceInferenceError::Scope))?;
        if deprecations.get(constant).is_none() {
            return Ok(());
        }
        if self.deprecated_uses.len() >= MAX_USES {
            return Err(failure(SourceInferenceError::ResourceLimit));
        }
        self.deprecated_uses.push(DeprecatedUse {
            constant: constant.clone(),
            span,
        });
        Ok(())
    }

    /// The pin's first elaboration of atomic `match` discriminants (`x`, `@x`): with no
    /// motive it elaborates each once more before the match itself, to wait for its type
    /// (`tryPostponeIfDiscrTypeIsMVar`, vendored `Lean/Elab/Match.lean:1212-1221`), so a
    /// deprecated constant there is reported twice, at the discriminant. An identifier naming
    /// a local, or nothing, reports nothing here; the match's own elaboration reports it.
    pub(super) fn recheck_identifiers(
        &mut self,
        identifiers: &[Syntax],
    ) -> Result<(), NatDefinitionElabError> {
        for identifier in identifiers {
            let Some(identifier) = atomic_discriminant(identifier) else {
                continue;
            };
            if let Some(constant) = self.discriminant_constant(identifier) {
                self.note_deprecated(&constant, syntax_span(identifier))?;
            }
        }
        Ok(())
    }

    /// The global constant an atomic discriminant's identifier names here, if it names one
    /// rather than a local.
    fn discriminant_constant(&mut self, identifier: &Syntax) -> Option<Name> {
        let Syntax::Ident { val, .. } = identifier else {
            return None;
        };
        if val.has_macro_scopes() || self.txn.lctx.find_by_user_name(val).is_some() {
            return None;
        }
        let resolved = self.resolve_source_name(val).ok().flatten()?;
        (self.txn.lctx.find_by_user_name(&resolved).is_none() && self.txn.env.contains(&resolved))
            .then_some(resolved)
    }

    /// Whether `discriminant` is atomic and names a `@[deprecated]` constant, so that a pattern
    /// matrix carries it to [`Self::recheck_identifiers`]. Only such a matrix is marked: its
    /// inputs are otherwise left exactly as written.
    pub(super) fn names_deprecated_constant(&mut self, discriminant: &Syntax) -> bool {
        let Some(constant) =
            atomic_discriminant(discriminant).and_then(|ident| self.discriminant_constant(ident))
        else {
            return false;
        };
        self.deprecation_cache
            .read(&self.txn.env)
            .is_ok_and(|deprecations| deprecations.get(&constant).is_some())
    }

    /// Hand this completed elaboration's uses to the front door's sink.
    pub(super) fn publish_deprecated_uses(&self) -> Result<(), NatDefinitionElabError> {
        if crate::deprecations::publish(&self.deprecated_uses) {
            Ok(())
        } else {
            Err(failure(SourceInferenceError::ResourceLimit))
        }
    }
}
