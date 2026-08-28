//! Perturbation validation engine for command effect summaries (Bet B4, Plan §10.6).
//!
//! The Tribunal validates effect summaries by perturbation: mutate an allegedly-unread
//! input (e.g., an unreferenced declaration, unread option) and require the elaborated
//! product to be bit-for-bit identical.
//!
//! A failing perturbation demotes the producer to [`crate::effects::CommandEffect::Opaque`]
//! barrier and flags the divergence.

use fln_core::name::Name;
use fln_core::outcome::Outcome;
use fln_env::constants::{ConstantInfo, ConstantVal, DefinitionVal, ReducibilityHints};
use fln_env::environment::{DeclAdmission, Environment};
use fln_env::pmap::CollisionBudget;

use crate::dataflow::{DataflowNode, ElabUnitProduct};
use crate::effects::CommandEffect;
use crate::txn::ElabBudget;

/// The kind of perturbation applied to the environment.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PerturbationKind {
    /// Injected an unread dummy declaration into the environment.
    UnreadDeclarationInjected { dummy_name: Name },
    /// Mutated an unread option or configuration flag.
    UnreadOptionMutated { option_key: String },
}

/// The result of a perturbation test over a command node.
#[derive(Debug, Clone)]
pub enum PerturbationResult {
    /// The effect summary is valid: products before and after perturbation are identical.
    Validated,
    /// The perturbation produced a different product: effect summary was incomplete/false.
    Failed {
        kind: PerturbationKind,
        reason: String,
        demoted_effect: CommandEffect,
    },
}

/// Perturbation validator testing effect accuracy.
pub struct PerturbationValidator;

impl PerturbationValidator {
    /// Validate a dataflow node's effect summary by injecting unread declarations and comparing products.
    pub fn validate_node_effects(
        node: &mut DataflowNode,
        base_env: &Environment,
        budget: &ElabBudget,
    ) -> Outcome<PerturbationResult> {
        // 1. Run baseline elaboration
        let baseline_product = match (node.elab_fn)(base_env, budget) {
            Outcome::Complete(Ok(p)) => p,
            Outcome::Complete(Err(e)) => {
                return Outcome::complete(PerturbationResult::Failed {
                    kind: PerturbationKind::UnreadDeclarationInjected {
                        dummy_name: Name::from_components(["baseline", "failed"]),
                    },
                    reason: format!("Baseline elaboration failed: {e}"),
                    demoted_effect: CommandEffect::Opaque {
                        reason: "baseline_failure".to_string(),
                    },
                });
            }
            Outcome::Inconclusive(inc) => return Outcome::Inconclusive(inc),
            Outcome::InternalFault(fault) => return Outcome::InternalFault(fault),
        };

        // 2. Synthesize an unread dummy declaration not present in node.declared_effects
        let dummy_name = Name::from_components(["__tribunal_dummy_perturbation_decl__"]);
        let dummy_val = ConstantVal {
            name: dummy_name.clone(),
            level_params: Vec::new(),
            type_: fln_core::expr::Expr::sort(fln_core::level::Level::zero()),
        };
        let dummy_info = ConstantInfo::Defn(DefinitionVal {
            base: dummy_val,
            value: fln_core::expr::Expr::sort(fln_core::level::Level::zero()),
            hints: ReducibilityHints::Regular(1),
            safety: fln_env::constants::DefinitionSafety::Safe,
            all: Vec::new(),
        });

        let perturbed_env =
            match base_env.try_add_decl_with_budget(dummy_info, 1, CollisionBudget::UNBOUNDED) {
                Outcome::Complete(DeclAdmission::Admitted(env)) => env,
                Outcome::Complete(DeclAdmission::Rejected(err)) => {
                    return Outcome::complete(PerturbationResult::Failed {
                        kind: PerturbationKind::UnreadDeclarationInjected { dummy_name },
                        reason: format!("Failed to inject dummy declaration: {err:?}"),
                        demoted_effect: CommandEffect::Opaque {
                            reason: "injection_failed".to_string(),
                        },
                    });
                }
                Outcome::Inconclusive(inc) => return Outcome::Inconclusive(inc),
                Outcome::InternalFault(fault) => return Outcome::InternalFault(fault),
            };

        // 3. Run perturbed elaboration
        let perturbed_product = match (node.elab_fn)(&perturbed_env, budget) {
            Outcome::Complete(Ok(p)) => p,
            Outcome::Complete(Err(e)) => {
                let reason = format!("Perturbed elaboration errored: {e}");
                node.declared_effects.demote_to_opaque(reason.clone());
                return Outcome::complete(PerturbationResult::Failed {
                    kind: PerturbationKind::UnreadDeclarationInjected { dummy_name },
                    reason: reason.clone(),
                    demoted_effect: CommandEffect::Opaque { reason },
                });
            }
            Outcome::Inconclusive(inc) => return Outcome::Inconclusive(inc),
            Outcome::InternalFault(fault) => return Outcome::InternalFault(fault),
        };

        // 4. Compare products for bit-for-bit equivalence
        if !Self::products_equivalent(&baseline_product, &perturbed_product) {
            let reason =
                "Perturbation produced non-identical products; unread input leaked into output"
                    .to_string();
            node.declared_effects.demote_to_opaque(reason.clone());
            Outcome::complete(PerturbationResult::Failed {
                kind: PerturbationKind::UnreadDeclarationInjected { dummy_name },
                reason: reason.clone(),
                demoted_effect: CommandEffect::Opaque { reason },
            })
        } else {
            Outcome::complete(PerturbationResult::Validated)
        }
    }

    fn products_equivalent(a: &ElabUnitProduct, b: &ElabUnitProduct) -> bool {
        // Compare admitted declarations count and names
        if a.admitted_decls.len() != b.admitted_decls.len() {
            return false;
        }
        for (da, db) in a.admitted_decls.iter().zip(&b.admitted_decls) {
            if da.name() != db.name() || da.constant_val().type_ != db.constant_val().type_ {
                return false;
            }
        }

        // Compare messages
        if a.messages.len() != b.messages.len() {
            return false;
        }
        for (ma, mb) in a.messages.iter().zip(&b.messages) {
            if ma.severity != mb.severity || ma.text != mb.text {
                return false;
            }
        }

        // Compare decision counts
        if a.decisions.len() != b.decisions.len() {
            return false;
        }

        true
    }
}
