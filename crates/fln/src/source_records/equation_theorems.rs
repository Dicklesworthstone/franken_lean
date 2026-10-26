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
use fln_elab::source::scope::simp::equations as simp_equations;
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
        source_base: Option<&Environment>,
    ) -> Result<Outcome<Option<DeclarationBatchAdmission>>, EngineExecutionError> {
        let requests = match elaboration_outcome(equations::requests(
            syntaxes,
            self.environment(),
            scope,
            limits.kernel,
        ))? {
            Outcome::Complete(requests) => requests,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
        if requests.is_empty() {
            return Ok(Outcome::Complete(None));
        }
        let base_logical_root = self.logical_root(options);
        let mut engine = self.clone();
        let mut admissions = Vec::new();
        for request in &requests {
            // Plain equation references and simp attributes share the same
            // candidate builder and post-admission provenance. Preparing it
            // before admission never blesses an arbitrary existing `eq_1`.
            let origin = match request {
                equations::Request::Equations(origin) => Some(origin.clone()),
                equations::Request::Name(name) => equations::target(engine.environment(), name)
                    .and_then(|(origin, suffix)| {
                        (suffix == equations::Suffix::Equation).then_some(origin)
                    }),
            };
            let mut prepared = None;
            if let Some(origin) = origin {
                let candidate = if source_base.is_some_and(|base| !base.contains(&origin)) {
                    simp_equations::prepare_owned(engine.environment(), &origin, limits.kernel)
                } else {
                    simp_equations::prepare(engine.environment(), &origin, limits.kernel)
                };
                match elaboration_outcome(candidate)? {
                    Outcome::Complete(simp_equations::Preparation::Ready(candidate)) => {
                        prepared = Some(candidate);
                    }
                    Outcome::Complete(
                        simp_equations::Preparation::NotRequired
                        | simp_equations::Preparation::Unsupported,
                    ) => {}
                    Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
                    Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
                }
            }
            let declarations = if let Some(candidate) = &prepared {
                if candidate.existing {
                    continue;
                }
                vec![candidate.declaration.clone()]
            } else {
                let realized =
                    match equations::realize(engine.environment(), request, limits.kernel) {
                        Ok(declarations) => Ok(declarations),
                        Err(fln_elab::NatDefinitionElabError::Inference(
                            fln_elab::source::SourceInferenceError::EquationTheorem(_),
                        )) => continue,
                        Err(error) => Err(error),
                    };
                match elaboration_outcome(realized)? {
                    Outcome::Complete(declarations) => declarations,
                    Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
                    Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
                }
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
            if let Some(candidate) = &prepared {
                batch.engine.environment = match elaboration_outcome(simp_equations::finish(
                    batch.engine.environment(),
                    candidate,
                    limits.kernel,
                ))? {
                    Outcome::Complete(environment) => environment,
                    Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
                    Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
                };
            } else {
                // Match equations and the distinct eq_def/eq_unfold requests
                // retain their existing generators and inferred metadata.
                for admitted in &batch.admissions {
                    if let Declaration::Thm(theorem) = &admitted.declaration {
                        batch.engine.environment = match elaboration_outcome(
                            fln_elab::source::scope::simp::defeq::infer_generated(
                                batch.engine.environment(),
                                &theorem.base.name,
                                limits.kernel,
                            ),
                        )? {
                            Outcome::Complete(environment) => environment,
                            Outcome::Inconclusive(reason) => {
                                return Ok(Outcome::Inconclusive(reason));
                            }
                            Outcome::InternalFault(fault) => {
                                return Ok(Outcome::InternalFault(fault));
                            }
                        };
                    }
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
