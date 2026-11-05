//! Invocation-local quoted templates in the same registry as imported MacroM.
//!
//! The source driver supplies an exact active grammar snapshot. It changes
//! neither the checked-owner inventory nor the persistent import registry.
//! Recursive Macro.expandMacro? and the tactic provider therefore see the same
//! candidates as the outer tree walk, with one scope/state/budget progression.

use super::*;
use crate::imported_macros::{MacroExecution, SyntaxConversionError};
use fln_parse::extensions::{
    FileGrammar, NotationRule, TemplateClauseOrder, TemplateExpansionError, TemplateSnapshot,
};

impl RegisteredMacros {
    pub(crate) fn bind_source_grammar(&self, grammar: &mut FileGrammar) {
        grammar.bind_runtime_macros(
            self.global
                .keys()
                .chain(self.scoped.values().flat_map(|table| table.keys()))
                .cloned(),
            self.scoped.keys().cloned(),
            self.active_scopes.iter().cloned(),
        );
    }

    pub(crate) fn with_source_templates(
        &self,
        snapshot: &TemplateSnapshot,
        module: &Name,
    ) -> Result<Self, MacroRegistrationError> {
        if snapshot.rules.is_empty() {
            return Ok(self.clone());
        }
        let mut candidates = self.candidates.as_ref().clone();
        for (kind, rule) in snapshot.rules.iter() {
            let invalid = |reason| MacroRegistrationError::Owner {
                module: module.clone(),
                declaration: kind.clone(),
                reason,
            };
            let Some(orders) = snapshot.orders.get(kind) else {
                return Err(invalid("source macro clause ordering is absent"));
            };
            if orders.len() != rule.cases().count() {
                return Err(invalid(
                    "source macro clause ordering has a different length",
                ));
            }
            let mut registrations: Vec<(TemplateClauseOrder, NotationRule)> = Vec::new();
            for (case, order) in rule.cases().zip(orders) {
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
                    registrations.push((*order, clause));
                } else if let Some((previous_order, registration)) = registrations.last_mut() {
                    if previous_order != order {
                        return Err(invalid(
                            "one source macro registration has different clause ordering",
                        ));
                    }
                    registration.fallbacks.push(clause);
                } else {
                    return Err(invalid(
                        "source template clause chain starts inside a registration",
                    ));
                }
            }
            let label = Name::from_components(["_fln", "sourceTemplate"]).append_core(kind);
            let previous = self.candidates.get(kind);
            let total = registrations
                .len()
                .checked_add(previous.map_or(0, |chain| chain.len()))
                .ok_or(MacroRegistrationError::Limit("mixed macro candidates"))?;
            let mut registered = Vec::new();
            registered
                .try_reserve_exact(total)
                .map_err(|_| MacroRegistrationError::Limit("mixed macro candidate allocation"))?;
            for (index, (order, template)) in registrations.into_iter().enumerate() {
                registered.push((
                    order,
                    RegisteredMacro {
                        module: module.clone(),
                        declaration: Name::num(label.clone(), index as u64),
                        scope: None,
                        compiled: Arc::new(MacroCode {
                            compiled: OnceLock::new(),
                            deferred: None,
                            native: None,
                            template: Some(Arc::new(template)),
                        }),
                        no_fallback: false,
                    },
                ));
            }
            for candidate in previous.into_iter().flat_map(|chain| chain.iter()) {
                let precedence = match &candidate.scope {
                    None => [0, 0, 0],
                    Some(namespace) => snapshot
                        .activations
                        .get(namespace)
                        .copied()
                        .or_else(|| {
                            snapshot
                                .initially_active
                                .contains(namespace)
                                .then_some([0, 0, 0])
                        })
                        .ok_or_else(|| {
                            invalid(
                                "imported macro activation is absent from the source chronology",
                            )
                        })?,
                };
                if registered
                    .iter()
                    .any(|(order, _)| order.imported && order.precedence == precedence)
                {
                    return Err(invalid(
                        "native-template and artifact imports have no shared registration order",
                    ));
                }
                registered.push((
                    TemplateClauseOrder {
                        precedence,
                        imported: false,
                    },
                    candidate.clone(),
                ));
            }
            // Source registrations are newer than imports at a shared scoped
            // activation. Stable ties preserve that order, each registration's
            // clauses, and the already-established imported candidate order.
            registered.sort_by_key(|(order, _)| std::cmp::Reverse(order.precedence));
            let registered: Vec<_> = registered.into_iter().map(|(_, entry)| entry).collect();
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
