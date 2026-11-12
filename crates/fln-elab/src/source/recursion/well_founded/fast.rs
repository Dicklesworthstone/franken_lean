//! A checked proof for the canonical successor-distance case. This only shortens
//! the default proof of a goal that omega already handles; supplied scripts and
//! every other arithmetic or relation shape retain the ordinary proof driver.
use super::*;

struct SubStep {
    prefix: Vec<bool>,
    index: Expr,
    bound: Expr,
}

fn named(expression: &Expr, path: &[&str], levels: usize) -> bool {
    matches!(expression.node(), ExprNode::Const { name, levels: actual }
        if name == &Name::from_components(path.iter().copied())
            && actual.len() == levels
            && actual.iter().all(|level| level == &Level::zero()))
}

fn null(arguments: Vec<Syntax>) -> Syntax {
    Syntax::node(Name::from_components(["null"]), arguments)
}

fn atom(value: &str) -> Syntax {
    Syntax::atom(fln_syntax::source::SourceInfo::None, value)
}

fn apply(path: &[&str]) -> Syntax {
    Syntax::node(
        parser_kind(&["Tactic", "apply"]),
        vec![
            atom("apply"),
            Syntax::Ident {
                info: fln_syntax::source::SourceInfo::None,
                raw_val: fln_syntax::source::ByteSpan::default().into(),
                val: Name::from_components(path.iter().copied()),
                preresolved: Vec::new(),
            },
        ],
    )
}

fn script(prefix: &[bool]) -> Syntax {
    let mut instructions = Vec::new();
    for &right in prefix {
        instructions.push(apply(&[
            "_root_",
            "Prod",
            "Lex",
            if right { "right" } else { "left" },
        ]));
    }
    instructions.push(apply(&["_root_", "Nat", "sub_succ_lt_self"]));
    instructions.push(Syntax::node(
        parser_kind(&["Tactic", "assumption"]),
        vec![atom("assumption")],
    ));
    instructions.push(Syntax::node(
        parser_kind(&["Tactic", "done"]),
        vec![atom("done")],
    ));
    let mut rows = Vec::new();
    for instruction in instructions {
        if !rows.is_empty() {
            rows.push(null(Vec::new()));
        }
        rows.push(instruction);
    }
    Syntax::node(
        parser_kind(&["Tactic", "tacticSeq"]),
        vec![Syntax::node(
            parser_kind(&["Tactic", "tacticSeq1Indented"]),
            vec![null(rows)],
        )],
    )
}

impl Context {
    /// Inspect only exposed syntax. In particular, an arbitrary user relation
    /// or arithmetic instance is never unfolded to make this shortcut apply.
    fn fast_decreasing_spine(
        &mut self,
        expression: &Expr,
    ) -> Result<(Expr, Vec<Expr>), NatDefinitionElabError> {
        let mut head = expression.clone();
        let mut arguments = Vec::new();
        loop {
            self.tick()?;
            match head.node() {
                ExprNode::MData { expr, .. } => head = expr.clone(),
                ExprNode::App { f, a } => {
                    arguments.push(a.clone());
                    head = f.clone();
                }
                _ => break,
            }
        }
        arguments.reverse();
        Ok((head, arguments))
    }

    fn fast_nat_binary(
        &mut self,
        expression: &Expr,
        subtraction: bool,
    ) -> Result<Option<(Expr, Expr)>, NatDefinitionElabError> {
        let (class, field, instance, operation) = if subtraction {
            ("HSub", "hSub", "instHSub", "instSubNat")
        } else {
            ("HAdd", "hAdd", "instHAdd", "instAddNat")
        };
        let (head, arguments) = self.fast_decreasing_spine(expression)?;
        if !named(&head, &[class, field], 3)
            || arguments.len() != 6
            || !arguments[..3]
                .iter()
                .all(|argument| named(argument, &["Nat"], 0))
        {
            return Ok(None);
        }
        let (dictionary, fields) = self.fast_decreasing_spine(&arguments[3])?;
        if !named(&dictionary, &[instance], 1)
            || fields.len() != 2
            || !named(&fields[0], &["Nat"], 0)
            || !named(&fields[1], &[operation], 0)
        {
            return Ok(None);
        }
        Ok(Some((arguments[4].clone(), arguments[5].clone())))
    }

    fn fast_nat_one(&mut self, expression: &Expr) -> Result<bool, NatDefinitionElabError> {
        let one = Expr::lit(Literal::Nat(fln_core::expr::NatLit::from_u64(1)));
        if expression == &one {
            return Ok(true);
        }
        let (head, arguments) = self.fast_decreasing_spine(expression)?;
        if !named(&head, &["OfNat", "ofNat"], 1)
            || arguments.len() != 3
            || !named(&arguments[0], &["Nat"], 0)
            || arguments[1] != one
        {
            return Ok(false);
        }
        let (instance, fields) = self.fast_decreasing_spine(&arguments[2])?;
        Ok(named(&instance, &["instOfNatNat"], 0) && fields.as_slice() == [one])
    }

    /// Ordinary direct-parameter tuples need none of the extra conversion
    /// probes below. A matching distance goal must have a subtraction as its
    /// current Nat coordinate, possibly inside exposed product constructors.
    fn fast_current_sub_measure(
        &mut self,
        expression: &Expr,
    ) -> Result<bool, NatDefinitionElabError> {
        let (head, arguments) = self.fast_decreasing_spine(expression)?;
        let current = if named(&head, &["LT", "lt"], 1) && arguments.len() == 4 {
            arguments[3].clone()
        } else if named(&head, &["Prod", "Lex"], 2) && arguments.len() == 6 {
            arguments[5].clone()
        } else {
            return Ok(false);
        };
        let mut pending = vec![current];
        while let Some(coordinate) = pending.pop() {
            self.tick()?;
            if self.fast_nat_binary(&coordinate, true)?.is_some() {
                return Ok(true);
            }
            let (head, arguments) = self.fast_decreasing_spine(&coordinate)?;
            if named(&head, &["Prod", "mk"], 2) && arguments.len() == 4 {
                pending.push(arguments[3].clone());
                pending.push(arguments[2].clone());
            }
        }
        Ok(false)
    }

    /// `assumption` can unfold ordinary predicate definitions that omega
    /// intentionally leaves opaque. Require the bound fact in the same
    /// exposed canonical notation as the arithmetic goal before using it.
    fn fast_decreasing_bound_fact(
        &mut self,
        index: &Expr,
        bound: &Expr,
    ) -> Result<bool, NatDefinitionElabError> {
        let locals = self.txn.lctx.clone();
        for local in locals.decls() {
            self.tick()?;
            if self.is_matrix_hypothesis(local) {
                continue;
            }
            let type_ = self.instantiate(&local.type_)?;
            let (head, arguments) = self.fast_decreasing_spine(&type_)?;
            if named(&head, &["LT", "lt"], 1)
                && arguments.len() == 4
                && named(&arguments[0], &["Nat"], 0)
                && named(&arguments[1], &["instLTNat"], 0)
                && &arguments[2] == index
                && &arguments[3] == bound
            {
                return Ok(true);
            }
        }
        Ok(false)
    }

    /// Follow the same right-before-left lexicographic constructors as the
    /// default proof. Definitional equality is only a private selection probe;
    /// the ordinary `apply` below must still establish every constructor step.
    fn fast_decreasing_sub_prefix(
        &mut self,
        expression: &Expr,
    ) -> Result<Option<SubStep>, NatDefinitionElabError> {
        let mut target = expression.clone();
        let mut prefix = Vec::new();
        loop {
            // Applying a cleaned relation family can leave a beta redex. No
            // ordinary definition or user relation is delta-unfolded here.
            target = self.reduce_source_head(&target, UnificationTransparency::None, false)?;
            let (head, arguments) = self.fast_decreasing_spine(&target)?;
            if named(&head, &["LT", "lt"], 1)
                && arguments.len() == 4
                && named(&arguments[0], &["Nat"], 0)
                && named(&arguments[1], &["instLTNat"], 0)
            {
                let Some((next_bound, next_index)) = self.fast_nat_binary(&arguments[2], true)?
                else {
                    return Ok(None);
                };
                let Some((bound, index)) = self.fast_nat_binary(&arguments[3], true)? else {
                    return Ok(None);
                };
                let Some((previous, increment)) = self.fast_nat_binary(&next_index, false)? else {
                    return Ok(None);
                };
                return Ok((next_bound == bound
                    && previous == index
                    && self.fast_nat_one(&increment)?)
                .then_some(SubStep {
                    prefix,
                    index,
                    bound,
                }));
            }
            if !named(&head, &["Prod", "Lex"], 2) || arguments.len() != 6 {
                return Ok(None);
            }
            let (next_head, next) = self.fast_decreasing_spine(&arguments[4])?;
            let (current_head, current) = self.fast_decreasing_spine(&arguments[5])?;
            if !named(&next_head, &["Prod", "mk"], 2)
                || !named(&current_head, &["Prod", "mk"], 2)
                || next.len() != 4
                || current.len() != 4
                || next[..2] != arguments[..2]
                || current[..2] != arguments[..2]
            {
                return Ok(None);
            }
            let right = if next[2] == current[2] {
                true
            } else {
                let mut trial = self.clone();
                let equal = trial.well_founded_default_conversion(&next[2], &current[2]);
                self.txn.budget.heartbeats_consumed = trial.txn.budget.heartbeats_consumed;
                self.txn.nat_sub_model_cache = trial.txn.nat_sub_model_cache;
                equal?
            };
            let selected = if right { 3 } else { 2 };
            target = Expr::app(
                Expr::app(arguments[selected].clone(), next[selected].clone()),
                current[selected].clone(),
            );
            prefix.push(right);
        }
    }

    /// Only default-generated proofs call this method. The actual admitted
    /// lemma and lex constructors are applied by the normal proof driver, so
    /// the original goal receives an ordinary checked proof term. Failure
    /// restores semantic state without refunding work or swallowing stops.
    pub(super) fn try_fast_decreasing_sub(
        &mut self,
        goal: &tactics::ProofGoal,
    ) -> Result<bool, NatDefinitionElabError> {
        let snapshot = self.clone();
        let result = (|| {
            self.txn.lctx = goal.lctx.clone();
            let target = self.instantiate(&goal.target)?;
            if !self.fast_current_sub_measure(&target)? {
                return Ok(false);
            }
            let Some(step) = self.fast_decreasing_sub_prefix(&target)? else {
                return Ok(false);
            };
            if !self.fast_decreasing_bound_fact(&step.index, &step.bound)? {
                return Ok(false);
            }
            let syntax = script(&step.prefix);
            let state = self.start_decreasing_proof(&syntax, vec![goal.clone()])?;
            self.run_decreasing_proof(&syntax, state)?;
            Ok(true)
        })();
        if matches!(result, Ok(true)) {
            self.txn.lctx = snapshot.txn.lctx;
            return result;
        }
        let spent = self.txn.budget.heartbeats_consumed;
        let model_cache = self.txn.nat_sub_model_cache.clone();
        *self = snapshot;
        self.txn.budget.heartbeats_consumed = spent;
        self.txn.nat_sub_model_cache = model_cache;
        match result {
            Err(problem) if tactics::backtrack::recoverable(&problem) => Ok(false),
            result => result,
        }
    }
}
