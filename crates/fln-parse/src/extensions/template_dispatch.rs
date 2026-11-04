//! One quoted source macro at the mixed source/imported MacroM boundary.
//!
//! Matching observes unexpanded operands. Quoted leaves receive the caller's
//! reference and retain their definition-source identifier backing, while
//! antiquotations retain their original syntax. The caller owns recursion,
//! fresh scopes, cancellation and the aggregate output budget.

use super::*;
use fln_syntax::tree::RawIdentifier;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TemplateExpansionError {
    Invalid(&'static str),
    Limit(&'static str),
}

impl From<&'static str> for TemplateExpansionError {
    fn from(reason: &'static str) -> Self {
        match reason {
            "a quoted macro pattern past the node or depth budget"
            | "quoted macro matching past the node budget"
            | "repetition work overflow"
            | "quoted repetition past the node budget"
            | "a capture path past the depth budget"
            | "macro template work overflow"
            | "a macro template past the node budget"
            | "a captured template value past the node budget" => Self::Limit(reason),
            _ => Self::Invalid(reason),
        }
    }
}

impl NotationRule {
    /// Try this registration's quoted clauses without expanding the result or
    /// any input child. `None` is unsupported syntax, allowing the dispatcher
    /// to try its next registration. No generated declaration is implied by
    /// this native data-only template.
    pub fn expand_root(
        &self,
        input: &Syntax,
        context: &Name,
        macro_scope: u64,
        reference: SourceInfo,
    ) -> Result<Option<Syntax>, TemplateExpansionError> {
        let operands = match input {
            Syntax::Node { kind, args, .. } if !atoms::is_kind(kind) => args.as_slice(),
            _ => std::slice::from_ref(input),
        };
        let mut matched_nodes = 0;
        for rule in self.cases() {
            if quotation::matches_with_budget(rule, operands, &mut matched_nodes)? {
                let template = literal_source(rule, reference)?;
                return quotation::templates::instantiate_rhs(
                    rule,
                    &template,
                    operands,
                    context,
                    macro_scope,
                )
                .map(Some)
                .map_err(Into::into);
            }
        }
        Ok(None)
    }
}

/// Resolve only literal template substrings here, before substitution inserts
/// caller syntax. Rewriting the completed result would corrupt antiquotations
/// and make a later VM macro read the wrong identifier bytes.
fn literal_source(rule: &NotationRule, reference: SourceInfo) -> Result<Syntax, &'static str> {
    let mut visited = 0;
    let mut pending = vec![&rule.rhs];
    while let Some(node) = pending.pop() {
        quotation::templates::charge(&mut visited)?;
        if let Syntax::Node { args, .. } = node {
            pending.extend(args);
        }
    }
    let source = rule
        .source
        .as_deref()
        .map(std::str::from_utf8)
        .transpose()
        .map_err(|_| "quoted template source is not UTF-8")?;
    let source: Arc<str> = Arc::from(source.unwrap_or(""));
    let mut template = rule.rhs.clone();
    let mut pending = vec![&mut template];
    while let Some(node) = pending.pop() {
        match node {
            Syntax::Node { info, args, .. } => {
                *info = reference;
                pending.extend(args);
            }
            Syntax::Atom { info, .. } => *info = reference,
            Syntax::Ident { info, raw_val, .. } => {
                *info = reference;
                if let Some(span) = raw_val.source_span() {
                    *raw_val = RawIdentifier::owned(Arc::clone(&source), span)
                        .ok_or("quoted template identifier has no definition-source backing")?;
                }
            }
            Syntax::Missing => {}
        }
    }
    Ok(template)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn literal_backing_is_owned_before_caller_captures_are_inserted() {
        let definition = "long quotation source: saved";
        let span = ByteSpan::new(BytePos(23), BytePos(28)).unwrap();
        let literal = Syntax::Ident {
            info: SourceInfo::Synthetic {
                pos: span.start(),
                end_pos: span.end(),
                canonical: true,
            },
            raw_val: span.into(),
            val: Name::from_components(["saved"]),
            preresolved: Vec::new(),
        };
        let variable = Name::from_components(["capture"]);
        let rule = NotationRule {
            variables: vec![(vec![0], variable.clone())],
            rhs: Syntax::node(
                Name::from_components(["pair"]),
                vec![literal, synthetic_ident(variable)],
            ),
            prechecked: false,
            pattern: None,
            source: Some(Arc::from(definition.as_bytes())),
            starts_registration: true,
            fallbacks: Vec::new(),
        };
        let caller = Syntax::Ident {
            info: SourceInfo::Synthetic {
                pos: BytePos(0),
                end_pos: BytePos(3),
                canonical: true,
            },
            raw_val: ByteSpan::new(BytePos(0), BytePos(3)).unwrap().into(),
            val: Name::from_components(["arg"]),
            preresolved: Vec::new(),
        };
        let reference = SourceInfo::Synthetic {
            pos: BytePos(0),
            end_pos: BytePos(3),
            canonical: false,
        };
        let expanded = rule
            .expand_root(
                &Syntax::node(Name::from_components(["testMacro"]), vec![caller.clone()]),
                &Name::from_components(["Main"]),
                17,
                reference,
            )
            .unwrap()
            .unwrap();
        let Syntax::Node { info, args, .. } = &expanded else {
            panic!("quotation did not preserve its node")
        };
        assert_eq!(*info, reference);
        assert_eq!(args[1], caller);
        let Syntax::Ident {
            info, raw_val, val, ..
        } = &args[0]
        else {
            panic!("quotation lost its literal identifier")
        };
        assert_eq!(*info, reference);
        let source = SourceText::from_utf8(b"arg").unwrap();
        assert_eq!(raw_val.text(&source), Some("saved"));
        assert_eq!(raw_val.owned_backing(), Some(definition));
        assert!(val.has_macro_scopes());
    }

    #[test]
    fn oversized_template_expansion_has_a_typed_resource_stop() {
        let rule = NotationRule {
            variables: Vec::new(),
            rhs: null_node(vec![Syntax::Missing; MAX_TEMPLATE_NODES]),
            prechecked: false,
            pattern: None,
            source: None,
            starts_registration: true,
            fallbacks: Vec::new(),
        };
        let result = rule.expand_root(
            &Syntax::node(Name::from_components(["large"]), Vec::new()),
            &Name::anonymous(),
            1,
            SourceInfo::None,
        );
        assert!(matches!(result, Err(TemplateExpansionError::Limit(_))));
    }

    #[test]
    fn failed_clauses_share_the_matching_budget() {
        let clause = NotationRule {
            variables: Vec::new(),
            rhs: Syntax::Missing,
            prechecked: false,
            pattern: Some(null_node(vec![Syntax::Missing])),
            source: None,
            starts_registration: false,
            fallbacks: Vec::new(),
        };
        let rule = NotationRule {
            starts_registration: true,
            fallbacks: vec![clause.clone(); MAX_TEMPLATE_NODES],
            ..clause
        };
        // Every clause fails at arity checking, before inspecting its pattern.
        assert_eq!(
            rule.expand_root(
                &Syntax::node(Name::from_components(["clauses"]), Vec::new()),
                &Name::anonymous(),
                1,
                SourceInfo::None,
            ),
            Err(TemplateExpansionError::Limit(
                "quoted macro matching past the node budget"
            ))
        );
    }
}
