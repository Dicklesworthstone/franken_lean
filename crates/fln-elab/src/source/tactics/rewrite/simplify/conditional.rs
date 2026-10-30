//! The default conditional pre-simprocs, before branch congruence (vendored
//! `Lean/Meta/Tactic/Simp/BuiltinSimprocs/Core.lean:14-36`). Simplify the condition
//! with the same selected rules, then use `ite_cond_eq_true/false` or
//! `dite_cond_eq_true/false` to select a branch. Every result is an ordinary
//! equality proof checked with its enclosing declaration.
//!
//! Selected head definitions are exposed before looking for the conditional,
//! as the pin's `Simp.reduceStep` does before `simpStep`. This matters for
//! `simp [g, f]` when `g` calls `f` with recursive branches: searching for `g`
//! through both arguments of `f` first duplicates work exponentially. No rule
//! is tried in a discarded branch. A symbolic condition leaves the existing
//! congruence path available, and `simp only` has no default simprocs.

use super::*;
use fln_env::constants::DefinitionVal;

/// Bound native-stack re-entry while simplifying nested conditions. Head
/// discovery is an optional bounded search; longer chains use ordinary simp.
const MAX_CONDITION_DEPTH: usize = 64;
const MAX_HEAD_REDUCTIONS: usize = 64;

pub(super) struct Selections {
    definitions: HashMap<Name, DefinitionVal>,
    locals: HashMap<FVarId, Expr>,
}

struct Conditional {
    level: Level,
    type_: Expr,
    condition: Expr,
    dictionary: Expr,
    yes: Expr,
    no: Expr,
    dependent: bool,
}

fn constant(name: &str) -> Expr {
    Expr::const_(Name::from_components([name]), Vec::new())
}

fn truth(term: &Expr) -> Option<bool> {
    match term.node() {
        ExprNode::Const { name, levels } if levels.is_empty() => {
            if name == &Name::from_components(["True"]) {
                Some(true)
            } else if name == &Name::from_components(["False"]) {
                Some(false)
            } else {
                None
            }
        }
        _ => None,
    }
}

/// The imported `ite`/`dite` shape, or the equivalent constant-motive recursor
/// this elaborator emits for a source `if`.
fn conditional(term: &Expr) -> Option<Conditional> {
    let (head, args) = simp_key_spine(term);
    let ExprNode::Const { name, levels } = head.node() else {
        return None;
    };
    let [level] = levels.as_slice() else {
        return None;
    };
    let [a, b, c, d, e] = args.as_slice() else {
        return None;
    };
    if name == &Name::from_components(["ite"]) || name == &Name::from_components(["dite"]) {
        return Some(Conditional {
            level: level.clone(),
            type_: (*a).clone(),
            condition: (*b).clone(),
            dictionary: (*c).clone(),
            yes: (*d).clone(),
            no: (*e).clone(),
            dependent: name == &Name::from_components(["dite"]),
        });
    }
    if name != &Name::from_components(["Decidable", "rec"]) {
        return None;
    }
    let ExprNode::Lam { body, .. } = b.node() else {
        return None;
    };
    if body.has_loose_bvar(0) {
        return None;
    }
    let type_ = body.subst_loose(0, &[Expr::sort(Level::zero())]).ok()?;
    Some(Conditional {
        level: level.clone(),
        type_,
        condition: (*a).clone(),
        dictionary: (*e).clone(),
        yes: (*d).clone(),
        no: (*c).clone(),
        dependent: true,
    })
}

/// `simp_visited_children` normally visits whole application arguments. An
/// over-applied conditional has a function prefix that must be simplified
/// first, before congruence visits either function-valued branch.
fn conditional_prefix(term: &Expr) -> Option<Expr> {
    let (_, args) = simp_key_spine(term);
    if args.len() <= 5 {
        return None;
    }
    let mut prefix = term.clone();
    for _ in 5..args.len() {
        let ExprNode::App { f, .. } = prefix.node() else {
            return None;
        };
        prefix = f.clone();
    }
    conditional(&prefix).map(|_| prefix)
}

impl Context {
    /// Run only the default pre-step, before whole-target normalization or
    /// post-rule indexing can visit either branch. Its returned index remains
    /// the rule's index in the full set, as location rewriting requires.
    pub(super) fn simp_pre_rewrite<T>(
        &mut self,
        rules: &[SimpRule<'_>],
        try_rule: impl FnMut(&mut Self, &SimpRule<'_>) -> Result<SimpRewrite<T>, NatDefinitionElabError>,
    ) -> Result<Option<(usize, T)>, NatDefinitionElabError> {
        self.simp_first_rewrite(
            rules,
            false,
            |_, rule| Ok(matches!(rule, SimpRule::Conditional { .. })),
            try_rule,
        )
    }

    pub(super) fn conditional_selections(
        &mut self,
        rules: &[SimpRule<'_>],
    ) -> Result<Selections, NatDefinitionElabError> {
        let mut selections = Selections {
            definitions: HashMap::new(),
            locals: HashMap::new(),
        };
        for rule in rules {
            if !self.simp_rule_may_unfold(rule) {
                continue;
            }
            match self.simp_unfold_selection_for_rule(rule)? {
                Some(unfold::Selection::Global(definition)) => {
                    selections
                        .definitions
                        .insert(definition.base.name.clone(), definition);
                }
                Some(unfold::Selection::Local(id, value)) => {
                    selections.locals.insert(id, value);
                }
                None => {}
            }
        }
        Ok(selections)
    }

    /// Expose just a node's head. Its arguments are borrowed unchanged: an
    /// unselected definition never unfolds, and no branch receives a rewrite.
    fn conditional_head(
        &mut self,
        original: &Expr,
        selections: &Selections,
    ) -> Result<(Option<Conditional>, bool), NatDefinitionElabError> {
        let mut term = original.clone();
        let mut changed = false;
        for _ in 0..MAX_HEAD_REDUCTIONS {
            self.tick()?;
            // Metadata is handled by visiting its child, retaining the wrapper.
            if matches!(term.node(), ExprNode::MData { .. }) {
                return Ok((None, changed));
            }
            if let Some(found) = conditional(&term) {
                return Ok((Some(found), changed));
            }
            let (head, _) = simp_key_spine(&term);
            // At this transparency a rigid ordinary constant or parameter
            // cannot expose a conditional. Avoid a WHNF query for every such
            // node of every default-simp target.
            let reduces = match head.node() {
                ExprNode::Const { name, .. } => matches!(
                    self.txn.env.find(name),
                    Some(ConstantInfo::Rec(_) | ConstantInfo::Quot(_))
                ),
                ExprNode::FVar { .. }
                | ExprNode::MVar { .. }
                | ExprNode::Sort { .. }
                | ExprNode::Lit { .. } => false,
                _ => true,
            };
            if reduces {
                let reduced =
                    self.whnf_with_transparency(&term, UnificationTransparency::None, false)?;
                if !self.rewrite_same(&term, &reduced)? {
                    term = reduced;
                    changed = true;
                    continue;
                }
            }
            let unfolded = match head.node() {
                ExprNode::Const { name, .. } => {
                    let Some(definition) = selections.definitions.get(name) else {
                        return Ok((None, changed));
                    };
                    self.unfold_selected_definition(&term, definition)?
                }
                ExprNode::FVar { id } => {
                    let Some(value) = selections.locals.get(id) else {
                        return Ok((None, changed));
                    };
                    let (_, arguments) = simp_key_spine(&term);
                    arguments.into_iter().fold(value.clone(), |function, arg| {
                        Expr::app(function, arg.clone())
                    })
                }
                _ => return Ok((None, changed)),
            };
            if self.rewrite_same(&term, &unfolded)? {
                return Ok((None, changed));
            }
            term = unfolded;
            changed = true;
        }
        Ok((None, changed))
    }

    /// The binder traversal must respect the same head reductions as the
    /// direct pre-step, or it could reopen a lambda in an erased argument.
    pub(super) fn simp_conditional_head_exposed(
        &mut self,
        term: &Expr,
        selections: &Selections,
    ) -> Result<bool, NatDefinitionElabError> {
        Ok(self.conditional_head(term, selections)?.1)
    }

    pub(super) fn simp_conditional_evidence(
        &mut self,
        target: &Expr,
        rules: &[SimpRule<'_>],
        depth: usize,
    ) -> Result<Option<(Typed, Expr)>, NatDefinitionElabError> {
        // The seed has no imported simproc proof lemmas. It keeps its existing
        // simplification semantics rather than manufacturing their authority.
        if !self
            .txn
            .env
            .contains(&Name::from_components(["ite_cond_eq_true"]))
            || !self
                .txn
                .env
                .contains(&Name::from_components(["dite_cond_eq_true"]))
        {
            return Ok(None);
        }
        let selections = self.conditional_selections(rules)?;
        let mut stack = vec![target.clone()];
        let mut seen = HashSet::new();
        while let Some(term) = stack.pop() {
            self.tick()?;
            if !seen.insert(term.allocation_identity()) {
                continue;
            }
            // Binder-aware lifting opens these nodes under fresh locals; raw
            // bound variables must not escape into a condition's proof.
            if !term.has_loose_bvars() {
                let (found, exposed) = self.conditional_head(&term, &selections)?;
                if let Some(found) = found {
                    let original = self.rewrite_trial();
                    let evidence = self.simp_conditional_node(&term, found, rules, depth)?;
                    if let Some(evidence) = evidence {
                        return Ok(Some((evidence, term)));
                    }
                    self.restore_simp_trial(original);
                }
                // A selected head can discard its arguments entirely. If its
                // unfolding has no decidable conditional at the head, let the
                // ordinary unfolding expose its new children before visiting
                // them; never simplify a condition in an erased argument.
                if exposed {
                    continue;
                }
            }
            let children: Vec<Expr> = self
                .simp_visited_children(&term)
                .into_iter()
                .cloned()
                .collect();
            stack.extend(children.into_iter().rev());
            if let Some(prefix) = conditional_prefix(&term) {
                stack.push(prefix);
            }
        }
        Ok(None)
    }

    fn simp_conditional_node(
        &mut self,
        original: &Expr,
        found: Conditional,
        rules: &[SimpRule<'_>],
        depth: usize,
    ) -> Result<Option<Typed>, NatDefinitionElabError> {
        if depth >= MAX_CONDITION_DEPTH {
            return Err(failure(SourceInferenceError::ResourceLimit));
        }
        let nested: Vec<_> = rules
            .iter()
            .map(|rule| match rule {
                SimpRule::Conditional { .. } => SimpRule::Conditional { depth: depth + 1 },
                rule => rule.clone(),
            })
            .collect();
        let (condition, proof) = self.simp_expression_with_rules(&nested, &found.condition)?;
        let Some(yes) = truth(&condition) else {
            return Ok(None);
        };
        let condition_proof = proof.unwrap_or_else(|| {
            app(
                Expr::const_(Name::from_components(["Eq", "refl"]), vec![Level::one()]),
                [Expr::sort(Level::zero()), condition],
            )
        });
        let lemma = match (found.dependent, yes) {
            (false, true) => "ite_cond_eq_true",
            (false, false) => "ite_cond_eq_false",
            (true, true) => "dite_cond_eq_true",
            (true, false) => "dite_cond_eq_false",
        };
        // Refuse a malformed/incomplete imported environment rather than
        // constructing a reference to an absent proof declaration.
        let lemma_name = Name::from_components([lemma]);
        if !self.txn.env.contains(&lemma_name) {
            return Err(failure(SourceInferenceError::UnknownConstant(lemma_name)));
        }
        let branch = if yes {
            found.yes.clone()
        } else {
            found.no.clone()
        };
        let result = if found.dependent {
            let lemma = if yes { "of_eq_true" } else { "of_eq_false" };
            let name = Name::from_components([lemma]);
            if !self.txn.env.contains(&name) {
                return Err(failure(SourceInferenceError::UnknownConstant(name)));
            }
            let evidence = app(
                constant(lemma),
                [found.condition.clone(), condition_proof.clone()],
            );
            self.whnf_with_transparency(
                &Expr::app(branch, evidence),
                UnificationTransparency::None,
                false,
            )?
        } else {
            branch
        };
        let value = app(
            Expr::const_(lemma_name, vec![found.level.clone()]),
            [
                found.type_.clone(),
                found.condition,
                found.dictionary,
                found.yes,
                found.no,
                condition_proof,
            ],
        );
        Ok(Some(Typed {
            value,
            type_: equality::equation(found.level, found.type_, original.clone(), result),
        }))
    }
}
