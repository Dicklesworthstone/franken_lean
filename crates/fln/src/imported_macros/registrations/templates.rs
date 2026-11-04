//! Invocation-local quoted templates in the same registry as imported MacroM.
//!
//! The source driver supplies an exact active grammar snapshot. It changes
//! neither the checked-owner inventory nor the persistent import registry.
//! Recursive Macro.expandMacro? and the tactic provider therefore see the same
//! candidates as the outer tree walk, with one scope/state/budget progression.

use super::*;
use crate::imported_macros::{MacroExecution, SyntaxConversionError};
use fln_parse::extensions::{NotationRule, TemplateExpansionError};

impl RegisteredMacros {
    pub(crate) fn with_source_templates(
        &self,
        rules: &BTreeMap<Name, Arc<NotationRule>>,
        module: &Name,
    ) -> Result<Self, MacroRegistrationError> {
        if rules.is_empty() {
            return Ok(self.clone());
        }
        let mut candidates = self.candidates.as_ref().clone();
        for (kind, rule) in rules {
            if ["num", "str", "ident", "char", "scientific", "name"]
                .iter()
                .any(|atomic| *kind == Name::from_components([*atomic]))
            {
                return Err(MacroRegistrationError::Owner {
                    module: module.clone(),
                    declaration: kind.clone(),
                    reason: "atomic source templates require term-position dispatch in the mixed macro tree",
                });
            }
            // Native journals currently carry clause order within their own
            // source world, not interleaved artifact registration positions.
            // Never guess the winner of a cross-world same-kind collision.
            if self.global.contains_key(kind)
                || self.scoped.values().any(|table| table.contains_key(kind))
            {
                return Err(MacroRegistrationError::Owner {
                    module: module.clone(),
                    declaration: kind.clone(),
                    reason: "source-template and artifact macro registration order for one syntax kind",
                });
            }
            let mut registrations: Vec<NotationRule> = Vec::new();
            for case in rule.cases() {
                let clause = NotationRule {
                    variables: case.variables.clone(),
                    rhs: case.rhs.clone(),
                    prechecked: case.prechecked,
                    pattern: case.pattern.clone(),
                    source: case.source.clone(),
                    starts_registration: case.starts_registration,
                    fallbacks: Vec::new(),
                };
                if case.starts_registration {
                    registrations.push(clause);
                } else if let Some(registration) = registrations.last_mut() {
                    registration.fallbacks.push(clause);
                } else {
                    return Err(MacroRegistrationError::Owner {
                        module: module.clone(),
                        declaration: kind.clone(),
                        reason: "source template clause chain starts inside a registration",
                    });
                }
            }
            let label = Name::from_components(["_fln", "sourceTemplate"]).append_core(kind);
            let registered: Vec<_> = registrations
                .into_iter()
                .enumerate()
                .map(|(index, template)| RegisteredMacro {
                    module: module.clone(),
                    declaration: Name::num(label.clone(), index as u64),
                    compiled: Arc::new(MacroCode {
                        compiled: OnceLock::new(),
                        deferred: None,
                        native: None,
                        template: Some(Arc::new(template)),
                    }),
                    no_fallback: false,
                })
                .collect();
            candidates.insert(kind.clone(), Arc::from(registered));
        }
        Ok(Self {
            candidates: Arc::new(candidates),
            ..self.clone()
        })
    }
}

pub(super) fn execute(
    template: &NotationRule,
    input: &Syntax,
    invocation: MacroInvocation<'_>,
    limits: MacroLimits,
    cancellation: Option<&dyn CancellationProbe>,
    reference: Option<&Syntax>,
) -> MacroExecution {
    let outcome = (|| {
        if cancellation.is_some_and(CancellationProbe::is_cancelled) {
            return Outcome::Inconclusive(Inconclusive::cancelled("source template expansion"));
        }
        let checked = (|| {
            super::super::syntax::inject(input, invocation.source, limits.syntax)?;
            inject_state(invocation.state, &mut StateBudget::new(limits.syntax))?;
            Ok::<_, SyntaxConversionError>(())
        })();
        if let Err(error) = checked {
            return conversion_outcome(error);
        }
        let reference =
            super::super::native_tactics::info_from_reference(reference.unwrap_or(input));
        let expanded = template.expand_root(
            input,
            &invocation.context.quotation_context,
            invocation.context.current_macro_scope,
            reference,
        );
        if cancellation.is_some_and(CancellationProbe::is_cancelled) {
            return Outcome::Inconclusive(Inconclusive::cancelled(
                "after source template expansion",
            ));
        }
        match expanded {
            Ok(Some(syntax)) => Outcome::Complete(Ok(MacroResult::Expanded {
                syntax,
                state: invocation.state.clone(),
            })),
            Ok(None) => Outcome::Complete(Ok(MacroResult::Unsupported {
                state: invocation.state.clone(),
            })),
            Err(TemplateExpansionError::Invalid(reason)) => {
                conversion_outcome(SyntaxConversionError::Malformed(reason))
            }
            Err(TemplateExpansionError::Limit(reason)) => {
                Outcome::Inconclusive(Inconclusive::dependency_unavailable(format!(
                    "source template expansion: {reason}",
                )))
            }
        }
    })();
    MacroExecution {
        outcome,
        vm_usage: None,
        reference_functions: Vec::new(),
        native_functions: vec!["source-template:quoted".into()],
    }
}
