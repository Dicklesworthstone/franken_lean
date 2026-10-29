//! `simp +decide` (`Simp.Config.decide`): the pin's `simpUsingDecide` simproc (vendored
//! `src/Lean/Meta/Tactic/Simp/Rewrite.lean:286-300`). A proposition with no free or meta
//! variables, other than `True` and `False`, whose `Decidable` instance evaluates to `true` or
//! `false` becomes `True` or `False`, proved by `eq_true_of_decide` or `eq_false_of_decide` over
//! `Eq.refl` (`Init/SimpLemmas.lean:30-34`). Anything else, a proposition without an instance
//! among them, is left alone, as the pin's `catch _ => return .continue` leaves it; exhaustion
//! and faults remain terminal.
//!
//! `preDefault` runs it at every node before the node's other rewrites (`Rewrite.lean:536-540`),
//! so the outermost such proposition is decided first: the walk here is pre-order and the rule
//! is tried before every other rule.
//!
//! The evaluation is the kernel's, as for this engine's `decide` tactic
//! (`decision_computes_true`), where the pin reduces with `whnf` at default transparency. A
//! proposition whose decision the kernel computes through a definition that transparency does
//! not unfold is decided here and left alone at the pin.
use super::*;
use crate::source::instances::{SearchResult, nonmatch, registry_error};

impl Context {
    /// The first proposition, in pre-order over the subterms simp visits, that
    /// `simpUsingDecide` rewrites in `target`: the proof `p = True` or `p = False`, and `p`.
    pub(super) fn simp_decide_evidence(
        &mut self,
        target: &Expr,
    ) -> Result<Option<(Typed, Expr)>, NatDefinitionElabError> {
        let mut stack = vec![target.clone()];
        let mut seen = HashSet::new();
        while let Some(term) = stack.pop() {
            self.tick()?;
            if !seen.insert(term.allocation_identity()) {
                continue;
            }
            if !term.has_fvar()
                && !term.has_expr_mvar()
                && !term.has_level_mvar()
                && !term.has_loose_bvars()
                && !is_truth(&term)
                && let Some(evidence) = self.simp_decide_node(&term)?
            {
                return Ok(Some((evidence, term)));
            }
            let children: Vec<Expr> = self
                .simp_visited_children(&term)
                .into_iter()
                .cloned()
                .collect();
            stack.extend(children.into_iter().rev());
        }
        Ok(None)
    }

    /// `simpUsingDecide` at one closed node.
    fn simp_decide_node(&mut self, term: &Expr) -> Result<Option<Typed>, NatDefinitionElabError> {
        // `mkDecide` needs a proposition.
        let Some(sort) = self.known_type(term)? else {
            return Ok(None);
        };
        let sort = self.whnf(&sort)?;
        if !self.proof_types_match(&sort, &Expr::sort(Level::zero()))? {
            return Ok(None);
        }
        let Some(dictionary) = self.simp_decidable_dictionary(term)? else {
            return Ok(None);
        };
        let computation = Expr::app(
            Expr::app(self.decide_constant(), term.clone()),
            dictionary.clone(),
        );
        let (lemma, result, boolean) = if self.decision_computes_true(computation.clone())? {
            ("eq_true_of_decide", "True", "true")
        } else if self.decision_computes_false(computation)? {
            ("eq_false_of_decide", "False", "false")
        } else {
            return Ok(None);
        };
        let lemma = Name::from_components([lemma]);
        // Resolve first, so an environment without the lemma is a typed refusal.
        self.constant(&lemma)?;
        let reflexive = Expr::app(
            Expr::app(
                Expr::const_(Name::from_components(["Eq", "refl"]), vec![Level::one()]),
                Expr::const_(Name::from_components(["Bool"]), Vec::new()),
            ),
            Expr::const_(Name::from_components(["Bool", boolean]), Vec::new()),
        );
        let value = [term.clone(), dictionary, reflexive]
            .into_iter()
            .fold(Expr::const_(lemma, Vec::new()), Expr::app);
        let type_ = equality::equation(
            Level::one(),
            Expr::sort(Level::zero()),
            term.clone(),
            Expr::const_(Name::from_components([result]), Vec::new()),
        );
        Ok(Some(Typed { value, type_ }))
    }

    /// `term`'s `Decidable` instance, or `None` where the search finds none. Nothing the search
    /// assigns survives; the instance found is closed.
    pub(super) fn simp_decidable_dictionary(
        &mut self,
        term: &Expr,
    ) -> Result<Option<Expr>, NatDefinitionElabError> {
        let registry = self
            .registry_cache
            .read_with_scopes(&self.txn.env, &self.source_scope.instance_scopes)
            .map_err(registry_error)?;
        let domain = Expr::app(
            Expr::const_(Name::from_components(["Decidable"]), Vec::new()),
            term.clone(),
        );
        let mut trial = self.rewrite_trial();
        let found = (|| {
            let hole = trial.hole(domain)?;
            let ExprNode::MVar { id } = hole.node() else {
                return Err(failure(SourceInferenceError::Scope));
            };
            if trial.search_instance(id.clone(), &registry)? != SearchResult::Solved {
                return Ok(None);
            }
            let value = trial.instantiate(&hole)?;
            Ok((!value.has_expr_mvar() && !value.has_level_mvar()).then_some(value))
        })();
        self.charge_rewrite_trial(&trial);
        match found {
            Ok(found) => Ok(found),
            Err(error) if nonmatch(&error) => Ok(None),
            Err(error) => Err(error),
        }
    }
}

/// `Expr.isTrue` or `Expr.isFalse`.
fn is_truth(term: &Expr) -> bool {
    matches!(term.node(), ExprNode::Const { name, levels }
        if levels.is_empty()
            && (name == &Name::from_components(["True"])
                || name == &Name::from_components(["False"])))
}
