//! Publish the pin's derived recursor wrappers with their inductive command.
//! Candidate generation has no admission authority: the original family and
//! every generated definition still pass both checking seats, in order.
use super::*;
use fln_elab::inductive::auxiliaries::{
    AuxiliaryError, below_declaration, brec_on_declarations, cases_on_declaration,
    rec_on_declaration,
};
use fln_elab::source::SourceInferenceError;
use fln_env::constants::{DefinitionVal, InductiveVal, RecursorVal};
use std::collections::HashSet;

#[derive(Default)]
struct Candidates {
    declarations: Vec<Declaration>,
    reducible: Vec<Name>,
    tagged: Vec<Name>,
    protected: Vec<Name>,
}

impl Candidates {
    fn push(&mut self, definition: DefinitionVal, tagged: bool, protected: bool) {
        let name = definition.base.name.clone();
        self.reducible.push(name.clone());
        if tagged {
            self.tagged.push(name.clone());
        }
        if protected {
            self.protected.push(name);
        }
        self.declarations.push(Declaration::Defn(definition));
    }
}

fn is_prop_former(inductive: &InductiveVal, mut remaining: usize) -> Result<bool, AuxiliaryError> {
    let mut type_ = &inductive.base.type_;
    loop {
        remaining = remaining
            .checked_sub(1)
            .ok_or(AuxiliaryError::ResourceLimit)?;
        match type_.node() {
            ExprNode::ForallE { body, .. } => type_ = body,
            ExprNode::MData { expr, .. } => type_ = expr,
            ExprNode::Sort { level } => return Ok(level.is_zero()),
            _ => return Err(AuxiliaryError::InvalidTelescope),
        }
    }
}

/// Nested motives can eliminate different imported containers, each with its
/// own universe. Collect only admitted families actually named by the checked
/// recursor telescope, under the same bounded input-walk policy as generation.
fn course_families(
    environment: &fln_env::environment::Environment,
    block: &[InductiveVal],
    recursor: &RecursorVal,
    mut remaining: usize,
) -> Result<Vec<InductiveVal>, AuxiliaryError> {
    let mut families = block.to_vec();
    let mut names: HashSet<_> = block
        .iter()
        .map(|family| family.base.name.clone())
        .collect();
    let mut seen = HashSet::new();
    let mut work = vec![&recursor.base.type_];
    while let Some(term) = work.pop() {
        remaining = remaining
            .checked_sub(1)
            .ok_or(AuxiliaryError::ResourceLimit)?;
        if !seen.insert(term.allocation_identity()) {
            continue;
        }
        match term.node() {
            ExprNode::Const { name, .. } => {
                if !names.contains(name)
                    && let Some(ConstantInfo::Induct(family)) = environment.find(name)
                {
                    names.insert(name.clone());
                    families.push(family.clone());
                }
            }
            ExprNode::App { f, a } => work.extend([f, a]),
            ExprNode::Lam {
                binder_type, body, ..
            }
            | ExprNode::ForallE {
                binder_type, body, ..
            } => work.extend([binder_type, body]),
            ExprNode::LetE {
                type_, value, body, ..
            } => work.extend([type_, value, body]),
            ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => work.push(expr),
            _ => {}
        }
    }
    Ok(families)
}

fn frontend(reason: SourceInferenceError) -> EngineExecutionError {
    EngineExecutionError::Frontend(DefinitionFrontendError::Elaborate(
        fln_elab::NatDefinitionElabError::Inference(reason),
    ))
}

impl Engine {
    pub(super) fn finish_source_inductive_auxiliaries(
        &self,
        result: Outcome<DeclarationBatchAdmission>,
        options: &KVMap,
        limits: EngineAdmissionLimits,
    ) -> Result<Outcome<DeclarationBatchAdmission>, EngineExecutionError> {
        let mut batch = match result {
            Outcome::Complete(batch) => batch,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
        let mut candidates = Candidates::default();
        let mut course_recursors = Vec::new();
        // mkAuxConstructions tests PUnit once after admitting the inductive
        // block. A prelude-free bootstrap can therefore generate recOn before
        // PUnit exists, just as the pin does.
        let has_unit = batch
            .engine
            .environment()
            .contains(&Name::from_components(["PUnit"]));
        let has_prod = batch
            .engine
            .environment()
            .contains(&Name::from_components(["Prod"]));
        let budget = fln_elab::records::RecordBudget::default();
        for admission in &batch.admissions {
            let Declaration::Inductive(block) = &admission.declaration else {
                continue;
            };
            for inductive in &block.types {
                let recursor_name = Name::str(inductive.base.name.clone(), "rec");
                let Some(ConstantInfo::Rec(recursor)) =
                    batch.engine.environment().find(&recursor_name)
                else {
                    return Err(EngineExecutionError::UnexpectedPublication {
                        detail: "an admitted source inductive has no checked recursor",
                    });
                };
                let rec_on = rec_on_declaration(recursor, budget)
                    .map_err(|error| frontend(SourceInferenceError::Auxiliary(error)))?;
                candidates.push(rec_on, true, true);
                if has_unit {
                    let cases_on = cases_on_declaration(inductive, recursor, &block.types, budget)
                        .map_err(|error| frontend(SourceInferenceError::Auxiliary(error)))?;
                    candidates.push(cases_on, true, false);
                }
                // The pin's mkBelow/mkBRecOn guard excludes nonrecursive and
                // Prop-valued families, even those with large elimination.
                if !has_unit
                    || !has_prod
                    || !inductive.is_rec
                    || is_prop_former(inductive, budget.max_nodes)
                        .map_err(|error| frontend(SourceInferenceError::Auxiliary(error)))?
                {
                    continue;
                }
                let nested = if inductive.all.first() == Some(&inductive.base.name) {
                    inductive.num_nested
                } else {
                    0
                };
                if nested as usize >= budget.max_binders {
                    return Err(frontend(SourceInferenceError::Auxiliary(
                        AuxiliaryError::ResourceLimit,
                    )));
                }
                for index in 0..=nested {
                    let recursor_name = if index == 0 {
                        recursor_name.clone()
                    } else {
                        Name::str(inductive.base.name.clone(), format!("rec_{index}"))
                    };
                    let Some(ConstantInfo::Rec(recursor)) =
                        batch.engine.environment().find(&recursor_name)
                    else {
                        return Err(EngineExecutionError::UnexpectedPublication {
                            detail: "an admitted recursive family has no checked nested recursor",
                        });
                    };
                    let families = course_families(
                        batch.engine.environment(),
                        &block.types,
                        recursor,
                        budget.max_nodes,
                    )
                    .map_err(|error| frontend(SourceInferenceError::Auxiliary(error)))?;
                    let below = below_declaration(recursor, &families, budget)
                        .map_err(|error| frontend(SourceInferenceError::Auxiliary(error)))?;
                    candidates.push(below, true, true);
                    course_recursors.push((recursor, families));
                }
            }
        }
        // Every motive's below definition must precede all of the mutually
        // dependent brecOn helpers. The helper is protected and reducible, but
        // only brecOn itself receives the auxiliary-recursion tag.
        for (recursor, families) in course_recursors {
            let [go, brec_on] = brec_on_declarations(recursor, &families, budget)
                .map_err(|error| frontend(SourceInferenceError::Auxiliary(error)))?;
            candidates.push(go, false, true);
            candidates.push(brec_on, true, true);
        }
        if candidates.declarations.is_empty() {
            return Ok(Outcome::Complete(batch));
        }
        let mut successor = match batch
            .engine
            .admit_declarations(&candidates.declarations, options, limits)
            .map_err(EngineExecutionError::from)?
        {
            Outcome::Complete(successor) => successor,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
        for name in &candidates.reducible {
            successor.engine.environment = fln_elab::reducibility::register(
                successor.engine.environment(),
                name,
                fln_elab::reducibility::Reducibility::Reducible,
            )
            .map_err(|error| {
                frontend(SourceInferenceError::Unification(Box::new(
                    fln_elab::constraint::unify::UnificationError::Reducibility(error),
                )))
            })?;
        }
        successor.engine.environment = fln_elab::aux_recursors::register_module(
            successor.engine.environment(),
            &candidates.tagged,
        )
        .map_err(|error| frontend(SourceInferenceError::AuxiliaryJournal(error)))?;
        successor.engine.environment = fln_elab::protected_names::register_module(
            successor.engine.environment(),
            &candidates.protected,
        )
        .map_err(|error| frontend(SourceInferenceError::ProtectedJournal(error)))?;
        // Keep every council receipt in the command's admission stream so
        // module export and replay carry the actual generated definitions.
        // A late collision, budget stop, or journal error exposes no prefix.
        batch.admissions.extend(successor.admissions);
        batch.engine = successor.engine;
        batch.result_logical_root = batch.engine.logical_root(options);
        Ok(Outcome::Complete(batch))
    }
}
