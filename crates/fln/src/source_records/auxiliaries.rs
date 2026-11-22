//! Publish the pin's derived recursor wrappers with their inductive command.
//! Candidate generation has no admission authority: the original family and
//! every generated definition still pass both checking seats, in order.
use super::*;
use fln_elab::inductive::auxiliaries::{
    AuxiliaryError, CtorIdxConstMeta, below_declaration, brec_on_declarations,
    cases_on_declaration, ctor_elim_declarations, ctor_idx_declarations, no_confusion_declarations,
    rec_on_declaration,
};
use fln_elab::source::SourceInferenceError;
use fln_env::constants::{DefinitionVal, InductiveVal, RecursorVal};
use std::collections::HashSet;

#[derive(Default)]
struct AuxiliaryMetadata {
    reducible: Vec<Name>,
    tagged: Vec<Name>,
    protected: Vec<Name>,
}

#[derive(Default)]
struct Candidates {
    declarations: Vec<Declaration>,
    metadata: AuxiliaryMetadata,
}

impl Candidates {
    fn push(&mut self, definition: DefinitionVal, reducible: bool, tagged: bool, protected: bool) {
        let name = definition.base.name.clone();
        if reducible {
            self.metadata.reducible.push(name.clone());
        }
        if tagged {
            self.metadata.tagged.push(name.clone());
        }
        if protected {
            self.metadata.protected.push(name);
        }
        self.declarations.push(Declaration::Defn(definition));
    }
}

fn has_ctor_elim_deps(env: &fln_env::environment::Environment) -> bool {
    [
        ["Nat"].as_slice(),
        &["Nat", "ble"],
        &["cond"],
        &["Eq"],
        &["Eq", "ndrec"],
        &["Eq", "symm"],
        &["PULift"],
        &["PULift", "up"],
        &["PULift", "down"],
    ]
    .into_iter()
    .all(|parts| env.contains(&Name::from_components(parts.iter().copied())))
}

fn has_no_confusion_deps(env: &fln_env::environment::Environment) -> bool {
    [
        ["PUnit"].as_slice(),
        &["Eq"],
        &["Eq", "refl"],
        &["Eq", "ndrec"],
        &["HEq"],
        &["HEq", "refl"],
        &["eq_of_heq"],
    ]
    .into_iter()
    .all(|parts| env.contains(&Name::from_components(parts.iter().copied())))
}

fn has_no_confusion_enum_deps(env: &fln_env::environment::Environment) -> bool {
    [
        ["noConfusionEnum"].as_slice(),
        &["noConfusionTypeEnum"],
        &["Nat"],
        &["instDecidableEqNat"],
    ]
    .into_iter()
    .all(|parts| env.contains(&Name::from_components(parts.iter().copied())))
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
                candidates.push(rec_on, true, true, true);
                if has_unit {
                    let cases_on = cases_on_declaration(inductive, recursor, &block.types, budget)
                        .map_err(|error| frontend(SourceInferenceError::Auxiliary(error)))?;
                    candidates.push(cases_on, true, true, false);
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
                    candidates.push(below, true, true, true);
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
            candidates.push(go, true, false, true);
            candidates.push(brec_on, true, true, true);
        }
        if candidates.declarations.is_empty() {
            return Ok(Outcome::Complete(batch));
        }
        let mut metadata = AuxiliaryMetadata::default();
        match self.admit_auxiliary_declarations(
            &mut batch,
            candidates,
            &mut metadata,
            options,
            limits,
        )? {
            Outcome::Complete(()) => {}
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        }
        batch = match self.finish_source_inductive_ctor_auxiliaries(
            batch,
            &mut metadata,
            options,
            limits,
        )? {
            Outcome::Complete(batch) => batch,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
        batch = match self.finish_source_inductive_no_confusion(
            batch,
            &mut metadata,
            options,
            limits,
        )? {
            Outcome::Complete(batch) => batch,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
        // Apply all auxiliary metadata journals once after every auxiliary
        // declaration has passed both checking seats, preserving an unbroken
        // chain of kernel declaration transitions (`pair[0].result == pair[1].base`)
        // before `sizeOf` elaboration runs.
        for name in &metadata.reducible {
            batch.engine.environment = fln_elab::reducibility::register(
                batch.engine.environment(),
                name,
                fln_elab::reducibility::Reducibility::Reducible,
            )
            .map_err(|error| {
                frontend(SourceInferenceError::Unification(Box::new(
                    fln_elab::constraint::unify::UnificationError::Reducibility(error),
                )))
            })?;
        }
        if !metadata.tagged.is_empty() {
            batch.engine.environment = fln_elab::aux_recursors::register_module(
                batch.engine.environment(),
                &metadata.tagged,
            )
            .map_err(|error| frontend(SourceInferenceError::AuxiliaryJournal(error)))?;
        }
        if !metadata.protected.is_empty() {
            batch.engine.environment = fln_elab::protected_names::register_module(
                batch.engine.environment(),
                &metadata.protected,
            )
            .map_err(|error| frontend(SourceInferenceError::ProtectedJournal(error)))?;
        }
        batch = match self.finish_source_inductive_size_of(batch, options, limits)? {
            Outcome::Complete(batch) => batch,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
        batch.result_logical_root = batch.engine.logical_root(options);
        Ok(Outcome::Complete(batch))
    }

    fn admit_auxiliary_declarations(
        &self,
        batch: &mut DeclarationBatchAdmission,
        candidates: Candidates,
        metadata: &mut AuxiliaryMetadata,
        options: &KVMap,
        limits: EngineAdmissionLimits,
    ) -> Result<Outcome<()>, EngineExecutionError> {
        if candidates.declarations.is_empty() {
            return Ok(Outcome::Complete(()));
        }
        let successor = match batch
            .engine
            .admit_declarations(&candidates.declarations, options, limits)
            .map_err(EngineExecutionError::from)?
        {
            Outcome::Complete(successor) => successor,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
        // Keep every council receipt in the command's admission stream so
        // module export and replay carry the actual generated definitions.
        // A late collision, budget stop, or journal error exposes no prefix.
        batch.admissions.extend(successor.admissions);
        batch.engine = successor.engine;
        metadata.reducible.extend(candidates.metadata.reducible);
        metadata.tagged.extend(candidates.metadata.tagged);
        metadata.protected.extend(candidates.metadata.protected);
        Ok(Outcome::Complete(()))
    }

    /// Generate and admit `<T>.ctorIdx`, enumeration `<T>.toCtorIdx`, and
    /// `<T>.ctorElimType`/`<T>.ctorElim`/`<ctor>.elim` for newly admitted
    /// inductive blocks, matching pinned `Lean/Elab/MutualInductive.lean:1552-1553`,
    /// `Lean/Meta/Constructions/CtorIdx.lean`, and `CtorElim.lean`.
    fn finish_source_inductive_ctor_auxiliaries(
        &self,
        mut batch: DeclarationBatchAdmission,
        metadata: &mut AuxiliaryMetadata,
        options: &KVMap,
        limits: EngineAdmissionLimits,
    ) -> Result<Outcome<DeclarationBatchAdmission>, EngineExecutionError> {
        if !options.get_bool(&Name::from_components(["genCtorIdx"]), true)
            || !batch
                .engine
                .environment()
                .contains(&Name::from_components(["Nat"]))
        {
            return Ok(Outcome::Complete(batch));
        }
        let budget = fln_elab::records::RecordBudget::default();
        let inductives: Vec<InductiveVal> = batch
            .admissions
            .iter()
            .filter_map(|admission| match &admission.declaration {
                Declaration::Inductive(block) => Some(block.types.iter().cloned()),
                _ => None,
            })
            .flatten()
            .collect();
        let mut idx_candidates = Candidates::default();
        let mut elim_targets = Vec::new();
        for inductive in &inductives {
            let ctor_idx_name = Name::str(inductive.base.name.clone(), "ctorIdx");
            // `CtorIdx.lean:47`: `if (← hasConst declName) then return`
            if batch.engine.environment().contains(&ctor_idx_name) {
                continue;
            }
            let cases_on_name = Name::str(inductive.base.name.clone(), "casesOn");
            let Some(ConstantInfo::Defn(cases_on)) =
                batch.engine.environment().find(&cases_on_name)
            else {
                continue;
            };
            let mut ctors = Vec::with_capacity(inductive.ctors.len());
            for ctor_name in &inductive.ctors {
                let Some(ConstantInfo::Ctor(ctor)) = batch.engine.environment().find(ctor_name)
                else {
                    return Err(EngineExecutionError::UnexpectedPublication {
                        detail: "an admitted source inductive is missing a checked constructor",
                    });
                };
                ctors.push(ctor.clone());
            }
            let generated = ctor_idx_declarations(inductive, &ctors, cases_on, budget, |n| {
                batch
                    .engine
                    .environment()
                    .find(n)
                    .map(CtorIdxConstMeta::from_constant)
            })
            .map_err(|error| frontend(SourceInferenceError::Auxiliary(error)))?;
            let Some(cands) = generated else {
                continue;
            };
            // `CtorIdx.lean:81-97`: `ctorIdx` uses `Regular(h+1)` hints and is
            // protected, not `@[reducible]` and not an auxiliary recursor.
            idx_candidates.push(cands.ctor_idx, false, false, true);
            if let Some(to_ctor_idx) = cands.to_ctor_idx
                && !batch.engine.environment().contains(&to_ctor_idx.base.name)
            {
                // `CtorIdx.lean:100-115`: `toCtorIdx` is protected and `@[reducible]`.
                idx_candidates.push(to_ctor_idx, true, false, true);
            }
            if inductive.ctors.len() > 1 {
                elim_targets.push((inductive.clone(), ctors));
            }
        }
        match self.admit_auxiliary_declarations(
            &mut batch,
            idx_candidates,
            metadata,
            options,
            limits,
        )? {
            Outcome::Complete(()) => {}
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        }
        if elim_targets.is_empty() || !has_ctor_elim_deps(batch.engine.environment()) {
            return Ok(Outcome::Complete(batch));
        }
        let mut elim_candidates = Candidates::default();
        for (inductive, ctors) in &elim_targets {
            let cases_on_name = Name::str(inductive.base.name.clone(), "casesOn");
            let Some(ConstantInfo::Defn(cases_on)) =
                batch.engine.environment().find(&cases_on_name)
            else {
                continue;
            };
            let generated = ctor_elim_declarations(inductive, ctors, cases_on, budget, |n| {
                batch.engine.environment().find(n)
            })
            .map_err(|error| frontend(SourceInferenceError::Auxiliary(error)))?;
            let Some(cands) = generated else {
                continue;
            };
            // `CtorElim.lean:105-106, 157-160, 205-210`:
            // `ctorElimType` is protected + reducible; `ctorElim` and each
            // `<ctor>.elim` are protected + reducible + `markAuxRecursor`.
            elim_candidates.push(cands.ctor_elim_type, true, false, true);
            elim_candidates.push(cands.ctor_elim, true, true, true);
            for ctor_elim in cands.constructor_elims {
                elim_candidates.push(ctor_elim, true, true, true);
            }
        }
        match self.admit_auxiliary_declarations(
            &mut batch,
            elim_candidates,
            metadata,
            options,
            limits,
        )? {
            Outcome::Complete(()) => Ok(Outcome::Complete(batch)),
            Outcome::Inconclusive(reason) => Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => Ok(Outcome::InternalFault(fault)),
        }
    }

    /// Generate and admit `<T>.noConfusionType` and `<T>.noConfusion` for newly
    /// admitted inductive blocks once `PUnit`, `Eq`, and `HEq` exist in the
    /// environment, matching pinned `Lean/Elab/MutualInductive.lean:1554` and
    /// `Lean/Meta/Constructions/NoConfusion.lean`.
    fn finish_source_inductive_no_confusion(
        &self,
        mut batch: DeclarationBatchAdmission,
        metadata: &mut AuxiliaryMetadata,
        options: &KVMap,
        limits: EngineAdmissionLimits,
    ) -> Result<Outcome<DeclarationBatchAdmission>, EngineExecutionError> {
        if !has_no_confusion_deps(batch.engine.environment()) {
            return Ok(Outcome::Complete(batch));
        }
        let use_enum_helper = has_no_confusion_enum_deps(batch.engine.environment());
        let budget = fln_elab::records::RecordBudget::default();
        let inductives: Vec<InductiveVal> = batch
            .admissions
            .iter()
            .filter_map(|admission| match &admission.declaration {
                Declaration::Inductive(block) => Some(block.types.iter().cloned()),
                _ => None,
            })
            .flatten()
            .collect();
        let mut nc_candidates = Candidates::default();
        for inductive in &inductives {
            let cases_on_name = Name::str(inductive.base.name.clone(), "casesOn");
            let Some(ConstantInfo::Defn(cases_on)) =
                batch.engine.environment().find(&cases_on_name)
            else {
                continue;
            };
            let mut ctors = Vec::with_capacity(inductive.ctors.len());
            for ctor_name in &inductive.ctors {
                let Some(ConstantInfo::Ctor(ctor)) = batch.engine.environment().find(ctor_name)
                else {
                    return Err(EngineExecutionError::UnexpectedPublication {
                        detail: "an admitted source inductive is missing a checked constructor",
                    });
                };
                ctors.push(ctor.clone());
            }
            let generated = no_confusion_declarations(
                inductive,
                &ctors,
                cases_on,
                use_enum_helper,
                budget,
                |n| batch.engine.environment().find(n),
            )
            .map_err(|error| frontend(SourceInferenceError::Auxiliary(error)))?;
            let Some(cands) = generated else {
                continue;
            };
            // `NoConfusion.lean:144-145, 254-259` (core: protected + reducible)
            // vs `NoConfusion.lean:392-430` (enum: reducible, not protected).
            let protected = !cands.is_enum_construction;
            nc_candidates.push(cands.no_confusion_type, true, false, protected);
            nc_candidates.push(cands.no_confusion, true, false, protected);
        }
        match self.admit_auxiliary_declarations(
            &mut batch,
            nc_candidates,
            metadata,
            options,
            limits,
        )? {
            Outcome::Complete(()) => Ok(Outcome::Complete(batch)),
            Outcome::Inconclusive(reason) => Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => Ok(Outcome::InternalFault(fault)),
        }
    }

    /// Generate and admit `<first>._sizeOf_<k>`, `<I>._sizeOf_inst`, and
    /// `<ctor>.sizeOf_spec` for newly admitted non-Prop safe inductive blocks
    /// once `SizeOf` and arithmetic prelude constants exist in the environment
    /// (vendored `Lean/Meta/SizeOf.lean:492-530`).
    fn finish_source_inductive_size_of(
        &self,
        mut batch: DeclarationBatchAdmission,
        options: &KVMap,
        limits: EngineAdmissionLimits,
    ) -> Result<Outcome<DeclarationBatchAdmission>, EngineExecutionError> {
        let blocks: Vec<_> = batch
            .admissions
            .iter()
            .filter_map(|admission| match &admission.declaration {
                Declaration::Inductive(block) => Some(block.types.clone()),
                _ => None,
            })
            .collect();
        for block in &blocks {
            let defs = match fln_elab::source::size_of::generate_inductive_size_of_defs(
                batch.engine.environment(),
                block,
                limits.kernel,
            ) {
                Ok(Some(defs)) => defs,
                Ok(None) => continue,
                Err(error) => {
                    return Err(EngineExecutionError::Frontend(
                        DefinitionFrontendError::Elaborate(error),
                    ));
                }
            };
            let mut successor = match batch
                .engine
                .admit_declarations(&defs.declarations, options, limits)
                .map_err(EngineExecutionError::from)?
            {
                Outcome::Complete(successor) => successor,
                Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
                Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
            };
            for fn_name in &defs.functions {
                successor.engine.environment = fln_elab::reducibility::register(
                    successor.engine.environment(),
                    fn_name,
                    fln_elab::reducibility::Reducibility::Semireducible,
                )
                .map_err(|error| {
                    frontend(SourceInferenceError::Unification(Box::new(
                        fln_elab::constraint::unify::UnificationError::Reducibility(error),
                    )))
                })?;
            }
            for inst_name in &defs.instances {
                successor.engine = match successor.engine.register_checked_source_instance(
                    inst_name,
                    1000,
                    None,
                    false,
                    limits.kernel,
                )? {
                    Outcome::Complete(engine) => engine,
                    Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
                    Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
                };
            }
            batch.admissions.extend(successor.admissions);
            batch.engine = successor.engine;

            let specs = match fln_elab::source::size_of::generate_inductive_size_of_specs(
                batch.engine.environment(),
                block,
                limits.kernel,
            ) {
                Ok(Some(specs)) => specs,
                Ok(None) => continue,
                Err(error) => {
                    return Err(EngineExecutionError::Frontend(
                        DefinitionFrontendError::Elaborate(error),
                    ));
                }
            };
            let mut spec_batch = match batch
                .engine
                .admit_declarations(&specs.declarations, options, limits)
                .map_err(EngineExecutionError::from)?
            {
                Outcome::Complete(successor) => successor,
                Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
                Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
            };
            batch.admissions.extend(spec_batch.admissions);
            for spec_name in &specs.theorems {
                let checked = match spec_batch.engine.apply_checked_source_simp(
                    spec_name,
                    Some((1000, false)),
                    true,
                    true,
                    options,
                    limits,
                )? {
                    Outcome::Complete(checked) => checked,
                    Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
                    Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
                };
                batch.admissions.extend(checked.admissions);
                spec_batch.engine = checked.engine;
            }
            batch.engine = spec_batch.engine;
        }
        Ok(Outcome::Complete(batch))
    }
}
