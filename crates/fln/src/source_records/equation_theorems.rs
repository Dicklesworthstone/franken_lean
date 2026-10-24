//! Equation theorems a command names, generated before it is elaborated.
//!
//! The pin generates `f.eq_<n>`, `f.eq_def` and `f.eq_unfold` when it first resolves one of
//! these reserved names, or when `rw [f]` asks for `f`'s equations, and adds them to the
//! environment for good (`realizeConst`, vendored `Lean/Meta/Eqns.lean`). This engine reads
//! the command's syntax for those references (`fln_elab::source::equation_theorems::requests`)
//! and admits each generated theorem through K1 and the independent checker before the
//! command runs, so the elaborator finds an ordinary theorem. A definition whose equations
//! are not generated here is skipped: the reference itself is refused, typed, when it is
//! elaborated.
use super::*;
use fln_elab::source::equation_theorems as equations;
use fln_syntax::tree::Syntax;

/// Whether `source` can name an equation theorem at all: a cheap filter before parsing.
pub(crate) fn may_name_equation_theorems(source: &[u8]) -> bool {
    source.windows(3).any(|window| window == b"eq_")
        || source.windows(2).any(|w| w == b"rw")
        || source.windows(7).any(|window| window == b"rewrite")
}

impl Engine {
    /// Generate and admit the equation theorems `syntaxes` refer to. `None` when there are
    /// none to generate.
    pub(crate) fn realize_equation_theorems(
        &self,
        syntaxes: &[&Syntax],
        scope: &fln_elab::source::scope::SourceScope,
        options: &KVMap,
        limits: EngineAdmissionLimits,
    ) -> Result<Outcome<Option<DeclarationBatchAdmission>>, EngineExecutionError> {
        let elaborate =
            |error| EngineExecutionError::Frontend(DefinitionFrontendError::Elaborate(error));
        let requests = equations::requests(syntaxes, self.environment(), scope, limits.kernel)
            .map_err(elaborate)?;
        if requests.is_empty() {
            return Ok(Outcome::Complete(None));
        }
        let base_logical_root = self.logical_root(options);
        let mut engine = self.clone();
        let mut admissions = Vec::new();
        for request in &requests {
            let declarations =
                match equations::realize(engine.environment(), request, limits.kernel) {
                    Ok(declarations) => declarations,
                    Err(fln_elab::NatDefinitionElabError::Inference(
                        fln_elab::source::SourceInferenceError::EquationTheorem(_),
                    )) => continue,
                    Err(error) => return Err(elaborate(error)),
                };
            if declarations.is_empty() {
                continue;
            }
            let mut batch = match engine
                .admit_declarations(&declarations, options, limits)
                .map_err(EngineExecutionError::from)?
            {
                Outcome::Complete(batch) => batch,
                Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
                Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
            };
            // The pin's `inferDefEqAttr`: a theorem proved by reflexivity is a `dsimp` rule.
            for admitted in &batch.admissions {
                if let Declaration::Thm(theorem) = &admitted.declaration {
                    batch.engine.environment = fln_elab::source::scope::simp::defeq::infer(
                        batch.engine.environment(),
                        &theorem.base.name,
                        limits.kernel,
                    )
                    .map_err(elaborate)?;
                }
            }
            engine = batch.engine;
            admissions.extend(batch.admissions);
        }
        if admissions.is_empty() {
            return Ok(Outcome::Complete(None));
        }
        let result_logical_root = engine.logical_root(options);
        Ok(Outcome::Complete(Some(DeclarationBatchAdmission {
            engine,
            base_logical_root,
            result_logical_root,
            admissions,
            local_instance: None,
        })))
    }
}

/// Merge a command's admission row into the one its generated equation theorems opened, so
/// that rows stay one per command, in command order.
pub(crate) fn push_command_admission(
    rows: &mut Vec<SourceCommandAdmission>,
    row: SourceCommandAdmission,
) {
    match rows.last_mut() {
        Some(last) if last.command_index == row.command_index => {
            last.admission.engine = row.admission.engine;
            last.admission.result_logical_root = row.admission.result_logical_root;
            last.admission.admissions.extend(row.admission.admissions);
            last.admission.local_instance = row.admission.local_instance;
        }
        _ => rows.push(row),
    }
}
