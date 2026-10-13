//! Explicit termination measures keep their inferred type and selected
//! well-founded dictionary. This is the `WF.Rel.elabWFRel` construction from
//! the pin: pull the relation back along the packed measure using `invImage`,
//! then feed its projections to the checked fixpoint. No relation is guessed
//! from the spelling of a measure or a user instance.
use super::*;

mod cleanup;

pub(super) struct Measure {
    pub value: Typed,
    dictionary: Expr,
    pub natural: bool,
    pub captures: HashSet<usize>,
}

impl Context {
    fn well_founded_application(
        &mut self,
        name: &[&str],
        arguments: impl IntoIterator<Item = Expr>,
    ) -> Result<Typed, NatDefinitionElabError> {
        let mut function = self.constant(&Name::from_components(name.iter().copied()))?;
        for value in arguments {
            self.tick()?;
            let type_ = self
                .known_type(&value)?
                .ok_or_else(|| failure(SourceInferenceError::ExpectedType))?;
            function = self.match_apply(function, Typed { value, type_ })?;
        }
        Ok(function)
    }

    pub(super) fn select_well_founded_relation(
        &mut self,
        value: Typed,
        parameters: &[LocalDecl],
    ) -> Result<Measure, NatDefinitionElabError> {
        let target = self
            .well_founded_application(&["WellFoundedRelation"], [value.type_.clone()])?
            .value;
        let dictionary = self
            .coercion_instance(target)?
            .ok_or_else(|| failure(SourceInferenceError::InstanceSynthesisRequired))?;
        self.require_resolved_terms(std::slice::from_ref(&dictionary))?;

        // `isNatLtWF` compares both the codomain and the actual dictionary at
        // default transparency. The probe retains consumed work but does not
        // publish its assignments or local names. A custom relation on Nat
        // must go through the generic fixpoint even when its measure is Nat.
        let mut trial = self.clone();
        let natural = (|| {
            let nat = Expr::const_(Name::from_components(["Nat"]), Vec::new());
            if !trial.well_founded_default_conversion(&value.type_, &nat)? {
                return Ok(false);
            }
            trial.well_founded_default_conversion(
                &dictionary,
                &Expr::const_(Name::from_components(["Nat", "lt_wfRel"]), Vec::new()),
            )
        })();
        self.txn.budget.heartbeats_consumed = trial.txn.budget.heartbeats_consumed;
        let natural = natural?;

        // The pin determines FixedParams before elaborating the relation. Our
        // typed call analysis determines the remaining fixed parameters while
        // elaborating the body. A codomain/dictionary dependency is therefore
        // tentatively captured now and checked at EVERY recursive call before
        // it may be omitted from the pack. This permits Fin n with fixed n,
        // without admitting a family whose n changes during recursion.
        let mut roots = self.elimination_reads(&value.type_)?;
        if !natural {
            // The canonical Nat specialization discards this dictionary
            // after conversion, so its incidental reads are not captures.
            roots.extend(self.elimination_reads(&dictionary)?);
        }
        let locals = self.txn.lctx.clone();
        let mut used = HashSet::new();
        self.add_decreasing_dependencies(&locals, &mut used, roots)?;
        let captures = parameters
            .iter()
            .enumerate()
            .filter_map(|(index, parameter)| used.contains(&parameter.id).then_some(index))
            .collect();
        Ok(Measure {
            value,
            dictionary,
            natural,
            captures,
        })
    }

    pub(super) fn well_founded_fix(
        &mut self,
        domain: Expr,
        motive: Expr,
        measure_fn: Expr,
        measure: &Measure,
    ) -> Result<Typed, NatDefinitionElabError> {
        let fix_name = if measure.natural {
            Name::from_components(["WellFounded", "Nat", "fix"])
        } else {
            Name::from_components(["WellFounded", "fix"])
        };
        if !matches!(
            self.txn.env.find(&fix_name),
            Some(ConstantInfo::Defn(definition)) if definition.safety == DefinitionSafety::Safe
        ) {
            return Err(failure(SourceInferenceError::UnknownConstant(fix_name)));
        }
        if measure.natural {
            return self.well_founded_application(
                &["WellFounded", "Nat", "fix"],
                [domain, motive, measure_fn],
            );
        }
        let inverse = self
            .well_founded_application(
                &["invImage"],
                [
                    domain.clone(),
                    measure.value.type_.clone(),
                    measure_fn,
                    measure.dictionary.clone(),
                ],
            )?
            .value;
        let relation = Expr::proj(
            Name::from_components(["WellFoundedRelation"]),
            0,
            inverse.clone(),
        );
        let proof = Expr::proj(Name::from_components(["WellFoundedRelation"]), 1, inverse);
        let proof_type = self
            .known_type(&proof)?
            .ok_or_else(|| failure(SourceInferenceError::ExpectedType))?;
        // `WF.mkFix` puts the well-founded proof behind Lean.opaqueId. Without
        // this checked imported wrapper a user could unfold accessibility
        // proofs and compute a generic fixpoint that the pin keeps opaque.
        let proof = self
            .well_founded_application(&["Lean", "opaqueId"], [proof_type, proof])?
            .value;
        self.well_founded_application(&["WellFounded", "fix"], [domain, motive, relation, proof])
    }

    /// Expose only the inverse image introduced by our checked fixpoint.
    /// A source-defined relation remains intact; ordinary apply/exact uses
    /// the existing conversion policy to inspect it. The Nat specialization
    /// stores InvImage directly, while the generic construction stores the
    /// first projection of the invImage dictionary, as the pin does.
    pub(super) fn decreasing_relation_parts(
        &mut self,
        target: &Expr,
    ) -> Result<(Expr, Expr, Expr, Expr), NatDefinitionElabError> {
        self.tick()?;
        let (head, arguments) = operators::spine(target);
        if matches!(head.node(), ExprNode::Const { name, .. }
            if name == &Name::from_components(["InvImage"]))
            && arguments.len() == 6
        {
            return Ok((
                if self
                    .well_founded
                    .as_ref()
                    .is_some_and(|state| state.natural_measure)
                {
                    // Keep the existing direct-Nat comparison used by
                    // GuessLex probes. Nat.fix's relation is a lambda over
                    // the standard LT dictionary, definitionally Nat.lt.
                    Expr::const_(Name::from_components(["Nat", "lt"]), Vec::new())
                } else {
                    arguments[2].clone()
                },
                arguments[3].clone(),
                arguments[4].clone(),
                arguments[5].clone(),
            ));
        }
        let ExprNode::Proj {
            struct_name,
            idx: 0,
            expr,
        } = head.node()
        else {
            return Err(failure(SourceInferenceError::ExpectedType));
        };
        if struct_name != &Name::from_components(["WellFoundedRelation"]) || arguments.len() != 2 {
            return Err(failure(SourceInferenceError::ExpectedType));
        }
        let (constructor, inverse) = operators::spine(expr);
        if !matches!(constructor.node(), ExprNode::Const { name, .. }
            if name == &Name::from_components(["invImage"]))
            || inverse.len() != 4
        {
            return Err(failure(SourceInferenceError::ExpectedType));
        }
        Ok((
            Expr::proj(struct_name.clone(), 0, inverse[3].clone()),
            inverse[2].clone(),
            arguments[0].clone(),
            arguments[1].clone(),
        ))
    }
}
