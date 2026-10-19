//! The operand-type retry in the pin's `elabSubst`, BuiltinNotation.lean:491-504.
//! A failed cast check must not leave equations or hole assignments in the
//! context used to construct the reverse cast. Spent work is never refunded.
use super::*;

impl Context {
    pub(super) fn substitution_operand(
        &mut self,
        syntax: &Syntax,
        expected: &Expr,
        equality: &Equality,
        proof: &Expr,
    ) -> Result<Typed, NatDefinitionElabError> {
        let mut trial = self.clone();
        let direct = (|| {
            let term = trial.term(syntax, Some(expected.clone()))?;
            trial.finish_term(term, Some(expected))
        })();
        self.txn.budget.heartbeats_consumed = trial.txn.budget.heartbeats_consumed;
        let original_error = match direct {
            Ok(term) => {
                *self = trial;
                return Ok(term);
            }
            Err(error) if observation_complete(&error) => {
                // This is a successful read-only observation, not a failed
                // candidate. Preserve its payload and propagate the stop.
                *self = trial;
                return Err(error);
            }
            Err(error) if definite_mismatch(&error) || attempt_deferral(&error) => error,
            Err(error) => return Err(error),
        };
        if !self.independently_typed_operand(syntax)? {
            return Err(original_error);
        }
        let mut retry = self.clone();
        let recovered = retry.reverse_substitution_operand(syntax, expected, equality, proof);
        self.txn.budget.heartbeats_consumed = retry.txn.budget.heartbeats_consumed;
        match recovered {
            Ok(Some(term)) => {
                *self = retry;
                Ok(term)
            }
            Ok(None) => Err(original_error),
            Err(error) if observation_complete(&error) => {
                *self = retry;
                Err(error)
            }
            Err(error) if instances::nonmatch(&error) => Err(original_error),
            Err(error) => Err(error),
        }
    }

    /// The native term driver checks expectations while elaborating, unlike
    /// the pin's separate elabTerm/ensureHasType boundary. Retry only syntax
    /// whose type can be recovered without choosing a new interpretation:
    /// an exact local name or an explicit type ascription. Contextual lambdas,
    /// overloaded globals, `rfl`, constructors and applications keep their
    /// original expected-type path. A recovered term must be fully determined.
    fn independently_typed_operand(
        &mut self,
        mut syntax: &Syntax,
    ) -> Result<bool, NatDefinitionElabError> {
        loop {
            self.tick()?;
            if let Some(inner) = parenthesized_inner(syntax)? {
                syntax = inner;
                continue;
            }
            return Ok(match syntax {
                Syntax::Ident { val, .. } => self.txn.lctx.find_by_user_name(val).is_some(),
                Syntax::Node { kind, .. } => kind == &parser_kind(&["Term", "typeAscription"]),
                _ => false,
            });
        }
    }

    fn reverse_substitution_operand(
        &mut self,
        syntax: &Syntax,
        expected: &Expr,
        equality: &Equality,
        proof: &Expr,
    ) -> Result<Option<Typed>, NatDefinitionElabError> {
        let operand = self.term(syntax, None)?;
        self.flush(false)?;
        let operand = Typed {
            value: self.instantiate(&operand.value)?,
            type_: self.instantiate(&operand.type_)?,
        };
        let determined = |expr: &Expr| !expr.has_expr_mvar() && !expr.has_level_mvar();
        if !determined(&operand.value) || !determined(&operand.type_) {
            return Ok(None);
        }
        // Within `first`/`try`, check_attempt_equation uses the speculative
        // unifier before the normal closed conversion boundary. Its unsupported
        // equation is not itself a mismatch. Establish that independently on
        // this fully inferred operand before attempting reverse transport.
        if !matches!(
            self.coercion_conversion(&operand.type_, expected)?,
            coercions::Conversion::Refuted(Verdict::Rejected {
                class: fln_kernel::verdict::RejectClass::NotDefEq,
                ..
            })
        ) {
            return Ok(None);
        }
        let abstracted = self.kabstract(&operand.type_, &equality.rhs)?;
        if !abstracted.has_loose_bvars() {
            return Ok(None);
        }
        let rewritten = self.substitute(&abstracted, &equality.lhs)?;
        if !self.coercion_eq(expected, &rewritten)? {
            return Ok(None);
        }
        let reverse = Equality {
            level: equality.level.clone(),
            alpha: equality.alpha.clone(),
            lhs: equality.rhs.clone(),
            rhs: equality.lhs.clone(),
        };
        let reverse_proof = self.symm(
            &equality.level,
            &equality.alpha,
            &equality.lhs,
            &equality.rhs,
            proof.clone(),
        )?;
        self.substitution_transport(&reverse, abstracted, operand, reverse_proof)
            .map(Some)
    }
}

/// An inconclusive or deferred equation is not evidence of a type mismatch.
fn definite_mismatch(error: &NatDefinitionElabError) -> bool {
    matches!(
        error,
        NatDefinitionElabError::Inference(SourceInferenceError::TypeMismatch { .. })
    ) || matches!(error,
        NatDefinitionElabError::Inference(SourceInferenceError::ConversionRefused(verdict))
            if matches!(verdict.as_ref(), Verdict::Rejected {
                class: fln_kernel::verdict::RejectClass::NotDefEq, ..
            })
    )
}

/// A speculative unifier can stop on a closed equation inside a tactic
/// attempt. It only permits the isolated probe above, never immediate recovery.
/// Unknown metavariables, invalid contexts, cancellation and limits do not.
fn attempt_deferral(error: &NatDefinitionElabError) -> bool {
    matches!(error,
        NatDefinitionElabError::Inference(SourceInferenceError::Unification(reason))
            if matches!(reason.as_ref(), UnificationError::Deferred(
                UnificationDeferred::UnsupportedEquation
            ))
    )
}

fn observation_complete(error: &NatDefinitionElabError) -> bool {
    matches!(
        error,
        NatDefinitionElabError::Inference(SourceInferenceError::ObservationComplete)
    )
}

#[cfg(test)]
mod tests;
