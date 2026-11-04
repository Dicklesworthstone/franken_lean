//! Existential propagation through ordinary checked introduction/elimination.
//!
//! The pin eagerly opens Exists facts, including under `grind only`. A witness
//! introduced here is scoped to an Exists.elim minor premise; neither the
//! environment nor a sibling search branch receives a choice function.
use super::*;

fn existential(expression: &Expr) -> Option<(Level, Expr, Expr)> {
    let ExprNode::App { f, a: predicate } = expression.node() else {
        return None;
    };
    let ExprNode::App { f, a: domain } = f.node() else {
        return None;
    };
    let ExprNode::Const { name: head, levels } = f.node() else {
        return None;
    };
    if *head != name("Exists") {
        return None;
    }
    let [level] = levels.as_slice() else {
        return None;
    };
    Some((level.clone(), domain.clone(), predicate.clone()))
}

fn negation(
    context: &mut Context,
    proposition: &Expr,
    proof: Expr,
    depth: usize,
) -> Result<Typed, Error> {
    let Some((level, domain, predicate)) = existential(proposition) else {
        return Ok(Typed {
            value: proof,
            type_: arrow(proposition.clone(), constant("False")),
        });
    };
    if depth >= MAX_FACTS {
        return Err(failure(SourceInferenceError::ResourceLimit));
    }
    let witness = context.equality_local(domain.clone())?;
    eliminate::add_local(&mut context.txn.lctx, &witness);
    let value = Expr::fvar(witness.id.clone());
    let property = normalize(context, &Expr::app(predicate.clone(), value.clone()))?;
    let evidence = context.equality_local(property.clone())?;
    let exists = apply(
        Expr::const_(name("Exists.intro"), vec![level]),
        [domain, predicate, value, Expr::fvar(evidence.id.clone())],
    );
    let body = context.close_equality_binder(&evidence, Expr::app(proof, exists), true)?;
    // Flatten consecutive existentials before pattern selection. A lambda in
    // `forall x, not (Exists (fun y => R x y))` is not an E-matching pattern;
    // `forall x y, not (R x y)` exposes the actual ground predicate instead.
    let body = negation(context, &property, body, depth + 1)?;
    Ok(Typed {
        value: context.close_equality_binder(&witness, body.value, true)?,
        type_: context.close_equality_binder(&witness, body.type_, false)?,
    })
}

impl State {
    /// `not (Exists p)` supplies `forall x, not (p x)` to E-matching. Build
    /// the implication from the original proof and Exists.intro so no native
    /// inference about truth or a new trusted lemma is needed.
    pub(super) fn negated_existential(
        &mut self,
        context: &mut Context,
        proposition: &Expr,
        proof: &Expr,
    ) -> Result<(), Error> {
        if existential(proposition).is_none() {
            return Ok(());
        }
        let before = context.clone();
        let result = negation(context, proposition, proof.clone(), 0);
        restore(context, before);
        self.enqueue(context, result?)
    }

    pub(super) fn unopened_existential(
        &self,
        context: &mut Context,
    ) -> Result<Option<Typed>, Error> {
        for fact in &self.facts {
            context.tick()?;
            if !self.opened_existentials.contains(&fact.type_) && existential(&fact.type_).is_some()
            {
                return Ok(Some(fact.clone()));
            }
        }
        Ok(None)
    }

    pub(super) fn eliminate_existential(
        &self,
        context: &mut Context,
        target: &Expr,
        depth: usize,
        fact: &Typed,
    ) -> Result<Option<Expr>, Error> {
        let Some((level, domain, predicate)) = existential(&fact.type_) else {
            return Err(unsupported());
        };
        // E-matching can produce further existentials. Their depth is bounded
        // independently of propositional case splits, even for a cyclic rule.
        if self.opened_existentials.len() >= MAX_FACTS {
            return Err(failure(SourceInferenceError::ResourceLimit));
        }
        let before = context.clone();
        let result: Result<Option<Expr>, Error> = (|| {
            let mut branch = self.clone();
            branch.opened_existentials.insert(fact.type_.clone());
            let witness = context.equality_local(domain.clone())?;
            eliminate::add_local(&mut context.txn.lctx, &witness);
            let property = normalize(
                context,
                &Expr::app(predicate.clone(), Expr::fvar(witness.id.clone())),
            )?;
            let evidence = context.equality_local(property.clone())?;
            eliminate::add_local(&mut context.txn.lctx, &evidence);
            branch.enqueue(
                context,
                Typed {
                    value: Expr::fvar(evidence.id.clone()),
                    type_: property,
                },
            )?;
            let Some(proof) = branch.solve(context, target, depth)? else {
                return Ok(None);
            };
            let proof = context.close_equality_binder(&evidence, proof, true)?;
            let proof = context.close_equality_binder(&witness, proof, true)?;
            Ok(Some(apply(
                Expr::const_(name("Exists.elim"), vec![level]),
                [domain, predicate, target.clone(), fact.value.clone(), proof],
            )))
        })();
        restore(context, before);
        result
    }
}
