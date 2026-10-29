//! Proof-producing simplification with explicit and immutable registered rules.
//! Rules are tried deterministically and re-instantiated for every application.
//! An unsuccessful alternative restores its complete elaboration state while
//! retaining spent work. Every productive step is ordinary Eq.rec transport.

mod aclt;
mod arith;
mod binders;
mod config;
mod decide;
mod dsimp;
mod locations;
mod simpa;
mod simproc;
mod suggest;
mod unfold;

use super::matching::RigidTypeHead;
use super::*;
use crate::lctx::LocalContext;
use aclt::{SimpPlace, SimpReach, SimpRewrite};
pub(in crate::source) use config::SimpConfig;
use fln_core::expr::BinderInfo;
use fln_env::environment::Environment;
use simproc::NatSimprocs;
use std::collections::{HashMap, HashSet};
use std::sync::{Arc, Mutex, PoisonError};
use unfold::UnfoldResult;

const MAX_SIMPLIFICATION_STEPS: usize = 256;

/// Registered names are resolved once by the attribute command. They must not
/// be reparsed or captured by a same-named local or a later namespace scope.
#[derive(Clone)]
pub(in crate::source) enum SimpRule<'a> {
    Explicit(RewriteRule<'a>),
    Global(scope::simp::SimpEntry),
    /// A wildcard selects a proof by local identity, not its display spelling.
    /// Location simplification remaps this identity when replacing the local.
    Local(FVarId),
    /// `+arith`'s linear normalization (`arith.rs`), always the last rule: the pin's
    /// `simpArith` runs after `rewritePost` (`Rewrite.lean:542-546`). It rewrites; it never
    /// closes a goal by itself.
    Arith,
    /// `+decide`'s decision of closed propositions (`decide.rs`), always the first rule: the
    /// pin's `simpUsingDecide` ends `preDefault` (`Rewrite.lean:536-540`), which runs at a node
    /// before its post rewrites.
    Decide,
    /// The default `Nat` simplification procedures the call runs (`simproc.rs`), after every
    /// theorem and before `+arith`'s normalization: the pin's `userPostSimprocs` follows
    /// `rewritePost` and precedes `simpArith` (`Rewrite.lean:542-546`).
    Simprocs(NatSimprocs),
}
impl SimpRule<'_> {
    fn reverse(&self) -> bool {
        match self {
            Self::Explicit(rule) => rule.reverse,
            Self::Global(rule) => rule.reverse,
            Self::Local(_) | Self::Arith | Self::Decide | Self::Simprocs(_) => false,
        }
    }
}

impl Context {
    /// Expand explicitly selected definitions for the `unfold` tactic.
    /// Resolution, safety and local-shadowing semantics are shared with explicit
    /// simp unfolding; callers decide which proof-state locations are replaced.
    pub(in crate::source) fn unfold_tactic_expression(
        &mut self,
        names: &[Syntax],
        target: &Expr,
    ) -> Result<(Expr, bool), NatDefinitionElabError> {
        let mut current = target.clone();
        let mut changed = false;
        for syntax in names {
            self.tick()?;
            self.unfold_tactic = true;
            let unfolded = self.unfold_simp_term(syntax, false, &current);
            self.unfold_tactic = false;
            match unfolded? {
                UnfoldResult::NotDefinition => {
                    let name = match syntax {
                        Syntax::Ident { val, .. } => val.clone(),
                        _ => return Err(error(TacticError::MalformedScript)),
                    };
                    return Err(error(TacticError::UnfoldFailed(name)));
                }
                UnfoldResult::Unchanged => {}
                UnfoldResult::Changed(next) => {
                    current = next;
                    changed = true;
                }
            }
        }
        Ok((current, changed))
    }

    /// Recognize a refutation only when the antecedent is known to be a
    /// proposition. An unknown sort is not permission to guess Prop.
    pub(super) fn simp_negated_proposition(
        &mut self,
        type_: &Expr,
    ) -> Result<Option<Expr>, NatDefinitionElabError> {
        self.tick()?;
        // `¬ p` itself: simp prepares its facts at reducible transparency, which keeps `Not`
        // folded, and the pin's `preprocess` reads it as `p = False` (`Expr.not?`).
        if let ExprNode::App { f, a } = type_.node()
            && matches!(f.node(), ExprNode::Const { name, levels }
                if name == &Name::from_components(["Not"]) && levels.is_empty())
        {
            return Ok(Some(a.clone()));
        }
        let ExprNode::ForallE {
            binder_type, body, ..
        } = type_.node()
        else {
            return Ok(None);
        };
        if !matches!(body.node(), ExprNode::Const { name, levels }
            if name == &Name::from_components(["False"]) && levels.is_empty())
        {
            return Ok(None);
        }
        let Some(sort) = self.known_type(binder_type)? else {
            return Ok(None);
        };
        let sort = self.whnf(&sort)?;
        Ok(
            matches!(sort.node(), ExprNode::Sort { level } if level.is_zero())
                .then(|| binder_type.clone()),
        )
    }

    /// A selected proof of P rewrites P to True; a selected refutation rewrites
    /// P to False. Build an actual equivalence, retaining the original evidence,
    /// then use the same explicit propext/transport path as Iff rewrite rules.
    pub(super) fn simp_proposition_rewrite_rule(
        &mut self,
        rule: Typed,
        reverse: bool,
    ) -> Result<Typed, NatDefinitionElabError> {
        if equality_target(&rule.type_).is_some() {
            return Ok(rule);
        }
        self.tick()?;
        let Some(sort) = self.known_type(&rule.type_)? else {
            return Ok(rule);
        };
        let sort = self.whnf(&sort)?;
        if sort.has_expr_mvar()
            || sort.has_level_mvar()
            || !self.proof_types_match(&sort, &Expr::sort(Level::zero()))?
        {
            return Ok(rule);
        }
        // Reversing a fact's generated True/False rule is not an orientation
        // request on an equality. Keep that unsupported form a typed refusal.
        if reverse {
            return Err(error(TacticError::ExpectedEquality));
        }
        let lambda = |domain, body| Expr::lam(Name::anonymous(), domain, body, BinderInfo::Default);
        let (left, right, forward, backward) =
            if let Some(proposition) = self.simp_negated_proposition(&rule.type_)? {
                let false_ = self.constant(&Name::from_components(["False"]))?.value;
                let recursor =
                    Expr::const_(Name::from_components(["False", "rec"]), vec![Level::zero()]);
                let motive = lambda(false_.clone(), proposition.clone());
                let from_false = lambda(
                    false_.clone(),
                    app(recursor, [motive, Expr::bvar(0).expect("zero index")]),
                );
                (proposition, false_, rule.value, from_false)
            } else {
                let true_ = self.constant(&Name::from_components(["True"]))?.value;
                let intro = self
                    .constant(&Name::from_components(["True", "intro"]))?
                    .value;
                let to_true = lambda(rule.type_.clone(), intro);
                let from_true = lambda(true_.clone(), rule.value);
                (rule.type_, true_, to_true, from_true)
            };
        let iff = self.constant(&Name::from_components(["Iff"]))?.value;
        let intro = self
            .constant(&Name::from_components(["Iff", "intro"]))?
            .value;
        Ok(Typed {
            value: app(intro, [left.clone(), right.clone(), forward, backward]),
            type_: app(iff, [left, right]),
        })
    }

    /// An erasure names a global declaration, even when a local has the same
    /// spelling. Hypothesis erasure belongs to the separate `[*]` profile.
    fn simp_erasure_name(&mut self, name: &Name) -> Result<Name, NatDefinitionElabError> {
        for _ in 0..self
            .source_scope
            .opened
            .len()
            .saturating_add(
                scope::components(&self.source_scope.namespace)
                    .map_err(|e| failure(SourceInferenceError::NameScope(e)))?
                    .len(),
            )
            .saturating_add(1)
        {
            self.tick()?;
        }
        self.source_scope
            .resolve(name, |candidate| self.txn.env.contains(candidate))
            .map_err(|e| failure(SourceInferenceError::NameScope(e)))?
            .ok_or_else(|| failure(SourceInferenceError::UnknownConstant(name.clone())))
    }

    /// Keep the origin of a bare global selection while assembling this call's
    /// rule set. Applied lemmas have their own expression origin: erasing the
    /// global does not erase an explicitly instantiated proof. Only a bare
    /// identifier selects a global: the pin's `resolveSimpIdTheorem?` matches
    /// `$id:ident`, so `(f)` is an ordinary term rule (bead `franken_lean-jxw`'s
    /// `native_default_simp` row). Local shadowing follows ordinary term lookup.
    fn simp_rule_global(
        &mut self,
        syntax: &Syntax,
    ) -> Result<Option<Name>, NatDefinitionElabError> {
        self.tick()?;
        let Syntax::Ident { val, .. } = syntax else {
            return Ok(None);
        };
        // A local, or a field of one (`h.symm`, `v.property`): the pin resolves a dotted name
        // whose head is a local as a projection of that local before any global name, so it
        // is elaborated as a term, not looked up as a constant.
        let mut head = val.clone();
        while !head.parent().is_anonymous() {
            head = head.parent();
        }
        if self.txn.lctx.find_by_user_name(val).is_some()
            || self.txn.lctx.find_by_user_name(&head).is_some()
        {
            return Ok(None);
        }
        let resolved = self
            .resolve_source_name(val)?
            .ok_or_else(|| failure(SourceInferenceError::UnknownConstant(val.clone())))?;
        let global = self.txn.lctx.find_by_user_name(&resolved).is_none()
            && self.txn.env.contains(&resolved);
        // `resolveSimpIdTheorem?` resolves it with `Term.resolveId?`, which checks it.
        if global {
            self.note_deprecated(
                &resolved,
                super::super::super::deprecated::syntax_span(syntax),
            )?;
        }
        Ok(global.then_some(resolved))
    }

    /// The pin elaborates a non-identifier simp argument as a theorem at once
    /// (`elabSimpTheorem`) and refuses it unless its type is a proposition under
    /// its binders (`checkTypeIsProp`: "Invalid simp theorem: Expected a
    /// proposition"). A pi type is a proposition exactly when its sort is `Prop`,
    /// so the sort of the term's type decides; a level that does not normalize to
    /// zero is not a proposition there either. A term this trial cannot elaborate
    /// keeps the per-use path, which refuses or skips it as before.
    fn check_simp_term_is_proposition(
        &mut self,
        syntax: &Syntax,
    ) -> Result<(), NatDefinitionElabError> {
        let mut trial = self.rewrite_trial();
        let sort = (|| -> Result<Option<Expr>, NatDefinitionElabError> {
            let term = trial.term(syntax, None)?;
            trial.flush(false)?;
            let type_ = trial.instantiate(&term.type_)?;
            let Some(sort) = trial.known_type(&type_)? else {
                return Ok(None);
            };
            let sort = trial.whnf(&sort)?;
            Ok(Some(trial.instantiate(&sort)?))
        })();
        self.charge_rewrite_trial(&trial);
        // The pin elaborates a term rule once (`elabSimpArgs`): this trial is that elaboration
        // for the deprecated constants it names, and [`Self::simp_rule_term`] checks none.
        if let Some(uses) = trial.deprecated_uses.get(self.deprecated_uses.len()..) {
            self.deprecated_uses.extend_from_slice(uses);
        }
        let Ok(Some(sort)) = sort else {
            return Ok(());
        };
        match sort.node() {
            ExprNode::Sort { level } if !level.normalize().is_zero() => {
                Err(error(TacticError::InvalidSimpTheorem))
            }
            _ => Ok(()),
        }
    }

    /// Read the admitted type before allocating a fresh instance of the proof.
    /// Unknown metadata remains an ordinary elaboration candidate.
    fn registered_simp_type(
        &mut self,
        rule: &SimpRule<'_>,
    ) -> Result<Option<Expr>, NatDefinitionElabError> {
        let SimpRule::Global(rule) = rule else {
            return Ok(None);
        };
        self.tick()?;
        Ok(self
            .txn
            .env
            .find(rule.proof.as_ref().unwrap_or(&rule.declaration))
            .map(|info| info.constant_val().type_.clone()))
    }

    /// Reject only stable, different outer types. Selected-definition expansion
    /// cannot change an admitted inductive, Sort, or forall into another head.
    fn simp_rule_may_prove(
        &mut self,
        rule: &SimpRule<'_>,
        target: &Expr,
    ) -> Result<bool, NatDefinitionElabError> {
        let Some(type_) = self.registered_simp_type(rule)? else {
            return Ok(true);
        };
        Ok(!self.rewrite_types_have_distinct_heads(&type_, target)?)
    }

    /// A registered fact P rewrites the proposition P, not its evidence.
    /// For a rigid admitted proposition, discard the rule only if every target
    /// occurrence has a distinct rigid head or cannot itself be a type. This
    /// runs before fresh universes, proof construction, or premise conversion.
    /// Equality, equivalence, parameters, aliases, and explicit/local rules keep
    /// the full matcher. No successful conversion is inferred by this filter.
    fn simp_rule_may_rewrite(
        &mut self,
        rule: &SimpRule<'_>,
        target: &Expr,
    ) -> Result<bool, NatDefinitionElabError> {
        let SimpRule::Global(entry) = rule else {
            return Ok(true);
        };
        self.tick()?;
        let Some(info) = self
            .txn
            .env
            .find(entry.proof.as_ref().unwrap_or(&entry.declaration))
        else {
            return Ok(true);
        };
        // A definition selects its body, rather than a rewrite of its type.
        // Keep unsupported reversed facts on the existing typed-refusal path.
        if entry.reverse
            || entry.proof.is_none() && matches!(info, fln_env::constants::ConstantInfo::Defn(_))
        {
            return Ok(true);
        }
        let type_ = info.constant_val().type_.clone();
        let Some(head @ RigidTypeHead::Inductive(_)) = self.rigid_rewrite_type_head(&type_)? else {
            return Ok(true);
        };
        if matches!(&head, RigidTypeHead::Inductive(name)
            if name == &Name::from_components(["Eq"])
                || name == &Name::from_components(["Iff"]))
        {
            return Ok(true);
        }
        let mut pending = vec![target];
        let mut visited = HashSet::new();
        while let Some(term) = pending.pop() {
            self.tick()?;
            if !visited.insert(term.allocation_identity()) {
                continue;
            }
            pending.extend(children(term).into_iter().rev().flatten());
            if let Some(actual) = self.rigid_rewrite_type_head(term)?
                && actual != head
            {
                continue;
            }
            let cannot_be_type = match term.node() {
                ExprNode::Lit { .. } => true,
                ExprNode::FVar { id } => {
                    let type_ = self.txn.lctx.find(id).map(|local| local.type_.clone());
                    match type_ {
                        Some(type_) => self
                            .rigid_rewrite_type_head(&type_)?
                            .is_some_and(|head| head != RigidTypeHead::Sort),
                        None => false,
                    }
                }
                _ => self
                    .rigid_rewrite_constant_result(term)?
                    .is_some_and(|head| head != RigidTypeHead::Sort),
            };
            if !cannot_be_type {
                return Ok(true);
            }
        }
        Ok(false)
    }

    /// Whether `rule` may match in the target `index` was built from. The pin's simp
    /// retrieves candidates from a discrimination tree keyed at reducible
    /// transparency and unifies only those; trying all of `Init`'s ~10,000
    /// registered rules at every step exhausted the elaboration budget on ordinary
    /// files (fln-simp-default-set-a4nb). A rule's key is memoized per environment
    /// and charges nothing: it reads only the rule's admitted type. A term or local
    /// rule, an unfolded definition and every shape not keyed here may match.
    fn simp_rule_admitted(
        &self,
        rule: &SimpRule<'_>,
        index: Option<&SimpTargetIndex>,
        side: SimpKeySide,
    ) -> bool {
        if matches!(
            rule,
            SimpRule::Arith | SimpRule::Decide | SimpRule::Simprocs(_)
        ) {
            return matches!(side, SimpKeySide::Rewrite);
        }
        let (Some(index), Some(entry)) = (index, simp_rule_entry(rule)) else {
            return true;
        };
        self.with_simp_key(&entry, index.environment, &index.table, side, |key| {
            key.is_none_or(|key| index.admits(key))
        })
    }

    /// Read a registered rule's memoized key in the environment `environment`
    /// identifies, computing it on first use. Borrowed, not cloned: admission
    /// reads one key per registered rule at every step.
    fn with_simp_key<R>(
        &self,
        entry: &scope::simp::SimpEntry,
        environment: SimpKeyEnvironment,
        table: &crate::reducibility::ReducibilityTable,
        side: SimpKeySide,
        read: impl FnOnce(Option<&SimpKey>) -> R,
    ) -> R {
        let cache = Arc::clone(&self.simp_key_cache.0);
        let mut memo = cache.lock().unwrap_or_else(PoisonError::into_inner);
        if memo.environment.as_ref() != Some(&environment) {
            *memo = SimpKeyMemo {
                environment: Some(environment),
                ..SimpKeyMemo::default()
            };
        }
        let identity = (
            entry.declaration.clone(),
            entry.proof.clone(),
            entry.reverse,
        );
        let keys = memo
            .rules
            .entry(identity)
            .or_insert_with(|| simp_rule_keys(&self.txn.env, table, entry));
        read(keys[side as usize].as_ref())
    }

    /// The key `rule` rewrites at. The pin's simp retrieves a rule at a node only when
    /// the node's own key matches, so the occurrence search tries no other node: before
    /// this, every admitted rule inferred the type of, and unified against, every
    /// subterm of the target. `None` (every node) for term and local rules, unfolded
    /// definitions and every shape not keyed here.
    pub(super) fn simp_rule_node_key(
        &mut self,
        rule: &SimpRule<'_>,
    ) -> Result<Option<SimpKey>, NatDefinitionElabError> {
        let Some(entry) = simp_rule_entry(rule) else {
            return Ok(None);
        };
        self.tick()?;
        let table = crate::reducibility::table(&self.txn.env).map_err(|error| {
            failure(SourceInferenceError::Unification(Box::new(
                UnificationError::Reducibility(error),
            )))
        })?;
        let environment = simp_key_environment(&self.txn.env);
        Ok(
            self.with_simp_key(&entry, environment, &table, SimpKeySide::Rewrite, |key| {
                key.cloned()
            }),
        )
    }

    /// Whether a rule keyed `key` may match at `node` itself. A node whose head the pin's
    /// key path may reduce (a reducible or non-constant head, a projection, a binder) is
    /// not filtered, so this skips only nodes the pin's retrieval cannot return the rule
    /// for.
    pub(super) fn simp_node_admits(
        &mut self,
        key: &SimpKey,
        node: &Expr,
    ) -> Result<bool, NatDefinitionElabError> {
        Ok(self
            .simp_root_index(node)?
            .is_none_or(|index| index.admits(key)))
    }

    /// Whether `rule` is a registered definition that occurs nowhere in the target `index`
    /// was built from. The pin's simp unfolds a definition at the nodes it heads; here each
    /// one walked and rebuilt the whole target, once per registered definition per step.
    /// The goal loop's own normalization step (`simp_normalize`) now does the beta and zeta
    /// reduction that walk used to supply.
    fn simp_definition_absent(&self, rule: &SimpRule<'_>, index: Option<&SimpTargetIndex>) -> bool {
        let (Some(index), SimpRule::Global(entry)) = (index, rule) else {
            return false;
        };
        entry.proof.is_none()
            && !entry.reverse
            && matches!(
                self.txn.env.find(&entry.declaration),
                Some(ConstantInfo::Defn(_))
            )
            && !index.applications.contains_key(&entry.declaration)
    }

    /// Every application a candidate rule's key may need to find in `target`: the
    /// target's own, closed over the values of definitions the key path may unfold at
    /// reducible or instance transparency, plus each primitive projection's function
    /// with any arguments. A superset of what a reducible key lookup reaches, so the
    /// filter only skips rules that cannot match. A numeral is a literal key, as in the
    /// pin's `DiscrTree`, so it never supplies a `Nat.succ` root: when it did, a match
    /// that unifies offsets let `Nat.succ_eq_add_one` rewrite `3` to `2 + 1`, then `2`
    /// to `1 + 1`, at every step. `None` (no filtering) past its work bound.
    fn simp_target_index(
        &mut self,
        target: &Expr,
    ) -> Result<Option<SimpTargetIndex>, NatDefinitionElabError> {
        const MAX_KEY_NODES: usize = 1 << 16;
        self.tick()?;
        let table = crate::reducibility::table(&self.txn.env).map_err(|error| {
            failure(SourceInferenceError::Unification(Box::new(
                UnificationError::Reducibility(error),
            )))
        })?;
        let env = &self.txn.env;
        let mut applications: HashMap<Name, Vec<Vec<SimpArgKey>>> = HashMap::new();
        let mut unfolded = HashSet::new();
        let mut visited = HashSet::new();
        // Only whole applications are entries: a spine's function prefixes would
        // admit every rule on its head while comparing no argument.
        let mut pending = vec![target.clone()];
        while let Some(term) = pending.pop() {
            if !visited.insert(term.allocation_identity()) {
                continue;
            }
            if visited.len() > MAX_KEY_NODES {
                return Ok(None);
            }
            let (head, args) = simp_key_spine(&term);
            match head.node() {
                ExprNode::Const { name, .. } => {
                    let keys = args
                        .iter()
                        .map(|arg| simp_target_arg_key(env, &table, &self.txn.lctx, arg, 0))
                        .collect();
                    applications.entry(name.clone()).or_default().push(keys);
                    if simp_key_unfolds(env, &table, name) {
                        if let Some(reduced) = simp_key_unfold_reducible(env, &table, &term) {
                            pending.push(reduced);
                        } else if unfolded.insert(name.clone())
                            && let Some(ConstantInfo::Defn(definition)) = env.find(name)
                        {
                            pending.push(definition.value.clone());
                        }
                    }
                }
                ExprNode::Proj {
                    struct_name, idx, ..
                } => {
                    if let Ok(idx) = usize::try_from(*idx)
                        && let Some(projection) = self.simp_projection_function(struct_name, idx)
                        && let Some(ConstantInfo::Induct(structure)) = env.find(struct_name)
                    {
                        let mut keys = vec![SimpArgKey::Any; structure.num_params as usize + 1];
                        keys.extend(
                            args.iter().map(|arg| {
                                simp_target_arg_key(env, &table, &self.txn.lctx, arg, 0)
                            }),
                        );
                        applications.entry(projection).or_default().push(keys);
                    }
                }
                // A `let` is keyed as both: the pin keys what its zeta reduction leaves.
                ExprNode::ForallE { .. } | ExprNode::Lam { .. } | ExprNode::LetE { .. } => {
                    for (key, keyed) in [
                        (
                            simp_arrow_key(),
                            !matches!(head.node(), ExprNode::Lam { .. }),
                        ),
                        (
                            simp_other_key(),
                            !matches!(head.node(), ExprNode::ForallE { .. }),
                        ),
                    ] {
                        if keyed {
                            applications.entry(key).or_default().push(Vec::new());
                        }
                    }
                }
                ExprNode::MVar { .. } => {
                    applications
                        .entry(simp_other_key())
                        .or_default()
                        .push(Vec::new());
                }
                _ => {}
            }
            pending.extend(args.into_iter().cloned());
            if !matches!(head.node(), ExprNode::Const { .. }) {
                pending.extend(children(head).into_iter().flatten().cloned());
            }
        }
        Ok(Some(SimpTargetIndex {
            applications,
            environment: simp_key_environment(env),
            table,
        }))
    }

    /// The index of `node`'s own application, for a rule that must match at `node` itself
    /// (dsimp rewrites one node at a time). `None` (no filtering) where the pin's key path
    /// may reduce the node: a let-bound local, a projection or a beta redex at the head.
    pub(super) fn simp_root_index(
        &mut self,
        node: &Expr,
    ) -> Result<Option<SimpTargetIndex>, NatDefinitionElabError> {
        self.tick()?;
        let table = crate::reducibility::table(&self.txn.env).map_err(|error| {
            failure(SourceInferenceError::Unification(Box::new(
                UnificationError::Reducibility(error),
            )))
        })?;
        let env = &self.txn.env;
        let (head, args) = simp_key_spine(node);
        // A raw numeral (the `2` inside `OfNat.ofNat Nat 2 _`) is a literal key at the pin,
        // which no constant-rooted rule retrieves. Matching `Nat.succ ?n` there rewrote it
        // to `1 + 1`, building `OfNat.ofNat Nat (1 + 1) _`, which the pin never does.
        // A local without a value is the pin's `.fvar` key and a sort its `.other` key, so
        // there too only a rule the pin keys as a star (unkeyed here) is retrieved. Every
        // registered rule was tried at every local and sort: under `Init`'s default set,
        // `dsimp` on `P (eval x f)` classified and unified thousands of rules at `P`, `x`,
        // `f` and at `eval x f` itself, whose key is its unfolding `f x`.
        let rigid = match head.node() {
            ExprNode::Lit { .. } | ExprNode::Sort { .. } => args.is_empty(),
            ExprNode::FVar { id } => self
                .txn
                .lctx
                .find(id)
                .is_some_and(|local| local.value.is_none()),
            _ => false,
        };
        if rigid {
            return Ok(Some(SimpTargetIndex {
                applications: HashMap::new(),
                environment: simp_key_environment(env),
                table,
            }));
        }
        // A `∀` is the pin's `.arrow` key and a `fun` its `.other` key: only a rule rooted at
        // the same binder. An application headed by a metavariable is `.other` too: there
        // every rule was tried, at a pending decreasing proof `?h x y …` some 8,000 to 14,000
        // heartbeats each, which stopped `ackermann`'s default `decreasing_by` at the limit.
        let keys = match head.node() {
            ExprNode::ForallE { .. } if args.is_empty() => vec![simp_arrow_key()],
            ExprNode::Lam { .. } if args.is_empty() => vec![simp_other_key()],
            ExprNode::LetE { .. } if args.is_empty() => vec![simp_arrow_key(), simp_other_key()],
            ExprNode::MVar { id } if !self.txn.mvars.is_assigned(id) => vec![simp_other_key()],
            _ => Vec::new(),
        };
        if !keys.is_empty() {
            return Ok(Some(SimpTargetIndex {
                applications: keys
                    .into_iter()
                    .map(|key| (key, vec![Vec::new()]))
                    .collect(),
                environment: simp_key_environment(env),
                table,
            }));
        }
        // A primitive projection `s.i a…` is keyed as its projection function applied to the
        // structure's parameters and the structure, all open, then to its own arguments. The
        // pin keys it `.proj`, so this admits a superset of what it retrieves. Unindexed, every
        // `*.sizeOf_spec` rule was tried at `hiddenSize.1 a` inside a `termination_by` measure,
        // some 14,000 heartbeats each.
        if let ExprNode::Proj {
            struct_name, idx, ..
        } = head.node()
            && let Ok(idx) = usize::try_from(*idx)
            && let Some(projection) = self.simp_projection_function(struct_name, idx)
            && let Some(ConstantInfo::Induct(structure)) = env.find(struct_name)
        {
            let mut keys = vec![SimpArgKey::Any; structure.num_params as usize + 1];
            keys.extend(
                args.iter()
                    .map(|arg| simp_target_arg_key(env, &table, &self.txn.lctx, arg, 0)),
            );
            return Ok(Some(SimpTargetIndex {
                applications: HashMap::from([(projection, vec![keys])]),
                environment: simp_key_environment(env),
                table,
            }));
        }
        let ExprNode::Const { name, .. } = head.node() else {
            return Ok(None);
        };
        let reduced;
        let (name, args) = if simp_key_unfolds(env, &table, name) {
            // Keyed as the pin's `whnfR` keys it, by the unfolding at the node's own
            // arguments: `Ne Nat x y` is the arrow `x = y → False`, not every `Eq`.
            let Some(unfolded) = simp_key_unfold_reducible(env, &table, node) else {
                return Ok(None);
            };
            reduced = unfolded;
            let (head, args) = simp_key_spine(&reduced);
            match head.node() {
                // An application too short to unfold keeps its own reducible head, as the
                // pin's key does. `dsimp` on the bare `eval` of `P (eval x f)` admitted, and
                // classified, every registered rule there.
                ExprNode::Const { name, .. } if simp_key_unfolds(env, &table, name) => (name, args),
                _ => return self.simp_root_index(&reduced),
            }
        } else {
            (name, args)
        };
        let keys = args
            .iter()
            .map(|arg| simp_target_arg_key(env, &table, &self.txn.lctx, arg, 0))
            .collect();
        Ok(Some(SimpTargetIndex {
            applications: HashMap::from([(name.clone(), vec![keys])]),
            environment: simp_key_environment(env),
            table,
        }))
    }

    /// The projection function behind a primitive projection: the structure's
    /// constructor field name at `idx`, after its parameters.
    fn simp_projection_function(&self, structure: &Name, idx: usize) -> Option<Name> {
        let fln_env::constants::ConstantInfo::Induct(inductive) = self.txn.env.find(structure)?
        else {
            return None;
        };
        let [constructor] = inductive.ctors.as_slice() else {
            return None;
        };
        let fln_env::constants::ConstantInfo::Ctor(constructor) = self.txn.env.find(constructor)?
        else {
            return None;
        };
        let mut type_ = &constructor.base.type_;
        let mut index = 0usize;
        while let ExprNode::ForallE {
            binder_name, body, ..
        } = type_.node()
        {
            if index == constructor.num_params as usize + idx {
                return match binder_name.leaf_view() {
                    LeafView::Str(field) => Some(Name::str(structure.clone(), field)),
                    _ => None,
                };
            }
            index += 1;
            type_ = body;
        }
        None
    }

    fn selected_simp_term(&mut self, rule: &SimpRule<'_>) -> Result<Typed, NatDefinitionElabError> {
        match rule {
            SimpRule::Explicit(rule) => self.simp_rule_term(rule.syntax),
            SimpRule::Global(rule) => {
                self.constant(rule.proof.as_ref().unwrap_or(&rule.declaration))
            }
            SimpRule::Local(id) => {
                self.tick()?;
                let local = self
                    .txn
                    .lctx
                    .find(id)
                    .ok_or_else(|| failure(SourceInferenceError::Scope))?;
                Ok(Typed {
                    value: Expr::fvar(id.clone()),
                    type_: local.type_.clone(),
                })
            }
            // Arithmetic normalization, decision and the procedures have no single proof term
            // to select.
            SimpRule::Arith | SimpRule::Decide | SimpRule::Simprocs(_) => {
                Err(error(TacticError::MalformedScript))
            }
        }
    }

    /// A bare, explicitly selected induction hypothesis can use its checked
    /// companion without changing the public hypothesis's application API.
    /// Both declarations must still be in this branch. Following only direct
    /// local aliases preserves annotations and local shadowing; ordinary term
    /// applications continue to elaborate the full conditional hypothesis.
    ///
    /// A rule is elaborated at each use here, where the pin elaborates it once while reading the
    /// arguments; that reading reported its deprecated constants (`simp_rules`), so none is
    /// reported again.
    fn simp_rule_term(&mut self, syntax: &Syntax) -> Result<Typed, NatDefinitionElabError> {
        if let Some(term) = self.specialized_induction_rule(syntax)? {
            return Ok(term);
        }
        let check = std::mem::replace(&mut self.check_deprecated, false);
        let term = self.term(syntax, None);
        self.check_deprecated = check;
        term
    }

    fn specialized_induction_rule(
        &mut self,
        syntax: &Syntax,
    ) -> Result<Option<Typed>, NatDefinitionElabError> {
        if let Syntax::Ident { val, .. } = syntax {
            let mut selected = self.txn.lctx.find_by_user_name(val).cloned();
            let mut seen = std::collections::HashSet::new();
            while let Some(local) = selected {
                self.tick()?;
                if !seen.insert(local.id.clone()) {
                    break;
                }
                if let Some((_, specialized)) = self
                    .induction_specializations
                    .iter()
                    .rev()
                    .find(|(raw, _)| raw == &local.user_name)
                    && let Some(companion) = self.txn.lctx.find_by_user_name(specialized)
                {
                    return Ok(Some(Typed {
                        value: Expr::fvar(companion.id.clone()),
                        type_: companion.type_.clone(),
                    }));
                }
                selected = match local.value.as_ref().map(Expr::node) {
                    Some(ExprNode::FVar { id }) => self.txn.lctx.find(id).cloned(),
                    _ => None,
                };
            }
        }
        Ok(None)
    }

    fn simp_rules<'a>(
        &mut self,
        args: &'a [Syntax],
    ) -> Result<Vec<SimpRule<'a>>, NatDefinitionElabError> {
        Ok(self.simp_selection(args)?.0)
    }

    /// The rules a `simp`, `simpa` or `dsimp` call's slots `args` select, with its configuration.
    /// `+decide`'s decision joins them first and `+arith`'s normalization last.
    fn simp_selection<'a>(
        &mut self,
        args: &'a [Syntax],
    ) -> Result<(Vec<SimpRule<'a>>, SimpConfig), NatDefinitionElabError> {
        self.tick()?;
        // `simp`'s six slots, or the pin's `simpa` (`"simpa" "?"? "!"? simpaArgsRest`), whose
        // arguments are `simpaArgsRest`'s first four slots and whose fifth is its evidence.
        let (keyword, config, discharger, only, arguments, location) = match args {
            [keyword, config, discharger, only, arguments, location] => {
                (keyword, config, discharger, only, arguments, Some(location))
            }
            [keyword, question, bang, rest] => {
                expect_empty_null(question, "plain simpa")?;
                expect_empty_null(bang, "plain simpa")?;
                let rest = expect_node(
                    rest,
                    &parser_kind(&["Tactic", "simpaArgsRest"]),
                    5,
                    "simpa arguments",
                )?;
                (keyword, &rest[0], &rest[1], &rest[2], &rest[3], None)
            }
            _ => return Err(error(TacticError::MalformedScript)),
        };
        let simpa = matches!(keyword, Syntax::Atom { val, .. } if val == "simpa");
        let dsimp = matches!(keyword, Syntax::Atom { val, .. } if val == "dsimp");
        expect_atom(
            keyword,
            if simpa {
                "simpa"
            } else if dsimp {
                "dsimp"
            } else {
                "simp"
            },
            "simplification keyword",
        )?;
        let config = self.simp_config(config, dsimp)?;
        // `dsimp` decides nothing here: its `decide` is not wired to its reductions.
        if dsimp && config.decide {
            return Err(NatDefinitionElabError::UnexpectedSyntax {
                expected: "default simplification configuration",
            });
        }
        expect_empty_null(discharger, "default simplification discharger")?;
        if !simpa {
            let location = location.ok_or_else(|| error(TacticError::MalformedScript))?;
            self.rewrite_locations(location)?;
        }
        let mut rules = self.simp_rule_selection(dsimp, only, arguments)?;
        if config.decide {
            rules.insert(0, SimpRule::Decide);
        }
        // `arith` is honoured as the pin's `updateArith` does: off while the environment lacks
        // `Nat.Linear.ExprCnstr.eq_of_toNormPoly_eq`.
        if config.arith
            && self.txn.env.contains(&Name::from_components([
                "Nat",
                "Linear",
                "ExprCnstr",
                "eq_of_toNormPoly_eq",
            ]))
        {
            rules.push(SimpRule::Arith);
        }
        Ok((rules, config))
    }

    /// The rules `simp_rules` selects, before `+arith`'s normalization joins them last.
    fn simp_rule_selection<'a>(
        &mut self,
        dsimp: bool,
        only: &'a Syntax,
        arguments: &'a Syntax,
    ) -> Result<Vec<SimpRule<'a>>, NatDefinitionElabError> {
        let use_default = match expect_null_args(only, "optional explicit simp set")? {
            [] => true,
            [only] => {
                expect_atom(only, "only", "explicit-set simplification")?;
                false
            }
            _ => return Err(error(TacticError::MalformedScript)),
        };
        // Even `simp []` reads the default set; `simp only` never reads it. A
        // malformed registry therefore cannot silently become an empty success.
        let mut defaults = if use_default {
            let mut rules = scope::simp::read(&self.txn.env)
                .map_err(|e| failure(SourceInferenceError::SimpSet(e)))?;
            // The enclosing scope's `attribute [local simp]` rules, after the registered ones; a
            // rule already registered is not read twice.
            for local in &self.source_scope.local_simp {
                if !rules
                    .iter()
                    .any(|rule| rule.declaration == local.declaration)
                {
                    rules.push(local.clone());
                }
            }
            rules.into_iter().map(SimpRule::Global).collect()
        } else if dsimp {
            Vec::new()
        } else {
            // The pin's `simp only` set starts as `eq_self` and `iff_self` (`simpOnlyBuiltins`,
            // `Lean/Elab/Tactic/Simp.lean:512,565`) before its arguments, so an erasure in them
            // applies. The default set has both as `@[simp]` (`Init/SimpLemmas.lean:36,272`).
            // An environment declaring neither (the source seed) keeps an empty set.
            let mut builtins = Vec::new();
            for name in [["eq_self"], ["iff_self"]] {
                self.tick()?;
                let declaration = Name::from_components(name);
                if self.txn.env.contains(&declaration) {
                    builtins.push(SimpRule::Global(scope::simp::SimpEntry {
                        declaration,
                        proof: None,
                        // `@[simp]`'s default priority.
                        priority: 1000,
                        reverse: false,
                        order: 0,
                    }));
                }
            }
            builtins
        };
        for _ in &defaults {
            self.tick()?;
        }
        // The default set's procedures; `simp only` and `dsimp only` start with none
        // (`mkSimpContext`, `Lean/Elab/Tactic/Simp.lean:568`).
        let mut procedures = if use_default {
            NatSimprocs::all()
        } else {
            NatSimprocs::default()
        };
        let mut arguments = expect_null_args(arguments, "optional simp rule list")?;
        // `simpa`'s rule list is its own `simpArgs` node (`simpaArgsRest`); `simp`'s is inline.
        if let [Syntax::Node { kind, args, .. }] = arguments
            && kind == &parser_kind(&["Tactic", "simpArgs"])
        {
            arguments = args.as_slice();
        }
        if arguments.is_empty() {
            return Ok(self.simp_rules_with_procedures(defaults, procedures));
        }
        let [open, rows, close] = arguments else {
            return Err(error(TacticError::MalformedScript));
        };
        expect_atom(open, "[", "simp rule opener")?;
        expect_atom(close, "]", "simp rule closer")?;
        let rows = expect_null_args(rows, "simp rules")?;
        let mut rules: Vec<(Option<Name>, SimpRule<'a>)> = Vec::new();
        let mut wildcard_ids = std::collections::HashSet::new();
        for (index, row) in rows.iter().enumerate() {
            self.tick()?;
            if index % 2 == 1 {
                expect_atom(row, ",", "simp rule separator")?;
                continue;
            }
            if matches!(row, Syntax::Node { kind, .. } if kind == &parser_kind(&["Tactic", "simpStar"]))
            {
                if dsimp {
                    // The pin's dsimp argument category does not admit `[*]`.
                    return Err(error(TacticError::MalformedScript));
                }
                let parts = expect_node(
                    row,
                    &parser_kind(&["Tactic", "simpStar"]),
                    1,
                    "simp wildcard",
                )?;
                expect_atom(&parts[0], "*", "simp wildcard marker")?;
                // Work on an immutable snapshot: rule elaboration may allocate
                // holes, but never contributes synthetic premises to `[*]`.
                let locals = self.txn.lctx.decls().to_vec();
                for local in locals {
                    self.tick()?;
                    if self.is_matrix_hypothesis(&local) || !wildcard_ids.insert(local.id.clone()) {
                        continue;
                    }
                    let type_ = self.instantiate(&local.type_)?;
                    let Some(sort) = self.known_type(&type_)? else {
                        continue;
                    };
                    let sort = self.whnf(&sort)?;
                    if !sort.has_expr_mvar()
                        && !sort.has_level_mvar()
                        && self.proof_types_match(&sort, &Expr::sort(Level::zero()))?
                    {
                        rules.push((None, SimpRule::Local(local.id)));
                    }
                }
                continue;
            }
            if matches!(row, Syntax::Node { kind, .. } if kind == &parser_kind(&["Tactic", "simpErase"]))
            {
                let parts = expect_node(
                    row,
                    &parser_kind(&["Tactic", "simpErase"]),
                    2,
                    "simp erasure",
                )?;
                expect_atom(&parts[0], "-", "simp erasure marker")?;
                let Syntax::Ident { val, .. } = &parts[1] else {
                    return Err(error(TacticError::MalformedScript));
                };
                // `elabSimpArg`: a procedure's name erases the procedure (`.eraseSimproc`).
                if let Some(procedure) = self.simp_procedure_argument(val)? {
                    procedures.remove(procedure);
                    continue;
                }
                let name = self.simp_erasure_name(val)?;
                for _ in 0..rules.len().saturating_add(defaults.len()) {
                    self.tick()?;
                }
                rules.retain(|(origin, _)| origin.as_ref() != Some(&name));
                defaults.retain(
                    |rule| !matches!(rule, SimpRule::Global(entry) if entry.declaration == name),
                );
                continue;
            }
            let parts = expect_node(row, &parser_kind(&["Tactic", "simpLemma"]), 3, "simp lemma")?;
            expect_empty_null(&parts[0], "default post-order simp rule")?;
            let reverse = match expect_null_args(&parts[1], "simp direction")? {
                [] => false,
                [Syntax::Atom { val, .. }] if val == "←" || val == "<-" => true,
                _ => return Err(error(TacticError::MalformedScript)),
            };
            // A procedure's name adds the procedure, `post` and with any `←` unread
            // (`resolveSimpIdTheorem?`'s `.simproc`, then `.addSimproc declName post`).
            if let Syntax::Ident { val, .. } = &parts[2]
                && let Some(procedure) = self.simp_procedure_argument(val)?
            {
                procedures.insert(procedure);
                continue;
            }
            // `term` below runs the normal heap-driven elaborator on the native
            // stack. Refuse a nested proof script in the rule, whether the
            // source parser or a direct Syntax caller built it, so this one
            // level of re-entry can never grow with source-controlled depth.
            let mut pending = vec![&parts[2]];
            while let Some(term) = pending.pop() {
                self.tick()?;
                if let Syntax::Node { kind, args, .. } = term {
                    if kind == &parser_kind(&["Term", "byTactic"]) {
                        return Err(error(TacticError::MalformedScript));
                    }
                    pending.extend(args);
                }
            }
            let origin = self.simp_rule_global(&parts[2])?;
            if !matches!(parts[2], Syntax::Ident { .. }) {
                self.check_simp_term_is_proposition(&parts[2])?;
            }
            if let Some(name) = &origin {
                // One selected direction per named rule. In particular,
                // `simp [← lemma]` must not retain the default forward rule.
                for _ in 0..rules.len().saturating_add(defaults.len()) {
                    self.tick()?;
                }
                rules.retain(|(previous, _)| previous.as_ref() != Some(name));
                defaults.retain(
                    |rule| !matches!(rule, SimpRule::Global(entry) if &entry.declaration == name),
                );
            }
            rules.push((
                origin.clone(),
                SimpRule::Explicit(RewriteRule {
                    syntax: &parts[2],
                    reverse,
                    global: origin,
                }),
            ));
        }
        // Explicit arguments have precedence; registered rules follow in their
        // stable priority/registration order. `only` leaves this tail empty.
        let rules = rules
            .into_iter()
            .map(|(_, rule)| rule)
            .chain(defaults)
            .collect();
        Ok(self.simp_rules_with_procedures(rules, procedures))
    }

    /// `rules` followed by the call's procedures, where there are any and this environment
    /// declares what their results are built from (the source seed does not).
    fn simp_rules_with_procedures<'a>(
        &self,
        mut rules: Vec<SimpRule<'a>>,
        procedures: NatSimprocs,
    ) -> Vec<SimpRule<'a>> {
        if !procedures.is_empty() && self.simp_procedures_supported() {
            rules.push(SimpRule::Simprocs(procedures));
        }
        rules
    }

    fn restore_simp_trial(&mut self, mut original: Self) {
        original.txn.budget.heartbeats_consumed = self.txn.budget.heartbeats_consumed;
        *self = original;
    }

    /// Only selected definitions participate in conversion of a side condition.
    fn simp_premise_target(
        &mut self,
        target: &Expr,
        rules: &[SimpRule<'_>],
    ) -> Result<Expr, NatDefinitionElabError> {
        let mut target = target.clone();
        // A registered theorem never unfolds; only definitions take part here.
        let unfoldable: Vec<_> = rules
            .iter()
            .filter(|rule| self.simp_rule_may_unfold(rule))
            .collect();
        for _ in 0..MAX_SIMPLIFICATION_STEPS {
            let mut changed = false;
            // A registered definition that occurs nowhere in `target` unfolds nothing, and its
            // walk only beta- and zeta-normalizes, as every walk does. Under the default set
            // each one walked every rule statement at every trial: simp on a `Prod.Lex` goal,
            // which the pin leaves unchanged at once, spent the whole work limit here.
            let index = self.simp_target_index(&target)?;
            let (mut walked, mut skipped) = (false, false);
            for rule in &unfoldable {
                if self.simp_definition_absent(rule, index.as_ref()) {
                    skipped = true;
                    continue;
                }
                self.tick()?;
                match self.unfold_simp_rule(rule, &target)? {
                    UnfoldResult::Changed(next) => {
                        target = next;
                        changed = true;
                        walked = true;
                    }
                    UnfoldResult::Unchanged => walked = true,
                    UnfoldResult::NotDefinition => {}
                }
            }
            if skipped && !walked {
                // The normalization the first skipped definition's walk performed.
                let normalized = self.simp_unfold_selected(&target, None)?;
                if !self.simp_same_up_to_ascriptions(&normalized, &target)? {
                    target = normalized;
                    changed = true;
                }
            }
            if !changed {
                return Ok(target);
            }
        }
        Err(failure(SourceInferenceError::ResourceLimit))
    }

    fn simp_selected_proof(
        &mut self,
        target: &Expr,
        rules: &[SimpRule<'_>],
    ) -> Result<Option<Expr>, NatDefinitionElabError> {
        let index = self.simp_target_index(target)?;
        for rule in rules {
            if !self.simp_rule_admitted(rule, index.as_ref(), SimpKeySide::Prove) {
                continue;
            }
            self.tick()?;
            if !self.simp_rule_may_prove(rule, target)? {
                continue;
            }
            let selected = self.selected_simp_term(rule)?;
            let type_ = self.simp_premise_target(&selected.type_, rules)?;
            let Some(universe) = self.known_type(&type_)? else {
                continue;
            };
            let universe = self.whnf(&universe)?;
            if !matches!(universe.node(), ExprNode::Sort { level } if level.is_zero()) {
                continue;
            }
            let mut budget = UnificationBudget::new(self.kernel);
            budget.zeta_delta = false;
            if self.proof_types_match_with_budget(&type_, target, budget)? {
                let value = self.instantiate(&selected.value)?;
                if !value.has_expr_mvar() && !value.has_level_mvar() {
                    return Ok(Some(value));
                }
            }
        }
        Ok(None)
    }

    pub(super) fn simp_discharge_premise(
        &mut self,
        id: &MVarId,
        target: &Expr,
        rules: &[SimpRule<'_>],
    ) -> Result<Option<Expr>, NatDefinitionElabError> {
        let target = self.simp_premise_target(target, rules)?;
        if let Some(value) = self.simp_selected_proof(&target, rules)? {
            return Ok(Some(value));
        }
        let goal = ProofGoal {
            id: id.clone(),
            target,
            lctx: self.txn.lctx.clone(),
            introduced: Vec::new(),
        };
        if let Some(value) = self.simp_reflexivity(&goal, rules)? {
            return Ok(Some(value));
        }
        if rules.is_empty() {
            return Ok(None);
        }
        let original = self.rewrite_trial();
        let value = self.rewrite_simp_premise(&goal.target, rules)?;
        if value.is_none() {
            self.restore_simp_trial(original);
        }
        Ok(value)
    }

    /// Construct a premise proof using the selected equalities and definitions.
    /// Parents live on the heap; rewriting a premise never recursively invokes
    /// the same selected set. Inner rules may discharge reflexive premises only.
    fn rewrite_simp_premise(
        &mut self,
        target: &Expr,
        rules: &[SimpRule<'_>],
    ) -> Result<Option<Expr>, NatDefinitionElabError> {
        let (root, mut goal) = self.proof_goal(target.clone())?;
        let mut parents = Vec::new();
        let mut history = vec![target.clone()];
        loop {
            self.tick()?;
            self.txn.lctx = goal.lctx.clone();
            let mut advanced = false;
            let target = self.instantiate(&goal.target)?;
            let index = self.simp_target_index(&target)?;
            for rule in rules {
                if !self.simp_rule_admitted(rule, index.as_ref(), SimpKeySide::Rewrite) {
                    continue;
                }
                self.tick()?;
                let original = self.rewrite_trial();
                let Some(((next_goal, value), _)) = self.simp_step(&goal, rule, &[])? else {
                    self.restore_simp_trial(original);
                    continue;
                };
                if parents.len() >= MAX_SIMPLIFICATION_STEPS {
                    return Err(failure(SourceInferenceError::ResourceLimit));
                }
                let next_target = self.instantiate(&next_goal.target)?;
                for previous in &history {
                    self.tick()?;
                    if self.rewrite_same(previous, &next_target)? {
                        return Err(error(TacticError::SimplificationCycle));
                    }
                }
                history.push(next_target);
                parents.push((goal, value));
                goal = next_goal;
                advanced = true;
                break;
            }
            if advanced {
                continue;
            }
            let value = match self.simp_selected_proof(&goal.target, rules)? {
                Some(value) => Some(value),
                None => self.simp_reflexivity(&goal, rules)?,
            };
            let Some(value) = value else {
                return Ok(None);
            };
            self.close_proof_goal(goal, value)?;
            while let Some((parent, value)) = parents.pop() {
                self.tick()?;
                self.close_proof_goal(parent, value)?;
            }
            return Ok(Some(self.instantiate(&root)?));
        }
    }

    fn simp_step(
        &mut self,
        goal: &ProofGoal,
        rule: &SimpRule<'_>,
        premise_rules: &[SimpRule<'_>],
    ) -> Result<SimpRewrite<(ProofGoal, Expr)>, NatDefinitionElabError> {
        let target = self.instantiate(&goal.target)?;
        if !self.simp_rule_may_rewrite(rule, &target)? {
            return Ok(None);
        }
        match self.unfold_simp_rule(rule, &target)? {
            UnfoldResult::Unchanged => Ok(None),
            UnfoldResult::Changed(next_target) => {
                let (child, next_goal) = self.proof_goal(next_target)?;
                Ok(Some(((next_goal, child), SimpPlace::of(SimpReach::Unfold))))
            }
            UnfoldResult::NotDefinition => {
                let Some((term, occurrence, reverse, place)) =
                    self.simp_rule_evidence(&target, rule, premise_rules)?
                else {
                    return Ok(None);
                };
                self.rewrite_transport(goal, term, &occurrence, reverse, false)
                    .map(|step| Some((step, place)))
            }
        }
    }

    /// Check a candidate only after the shared automatic-closure policy admits
    /// it. Full K1 assignment conversion alone would unfold ordinary definitions
    /// that are absent from this tactic's explicit rule set.
    ///
    /// The pin closes a goal only once its simp result is `True` (`simpTargetCore`,
    /// `Lean/Meta/Tactic/Simp/Main.lean:784`), every reflexive leaf having become `True` through
    /// `eq_self` or `iff_self`, which are rules here too wherever they are declared. In the
    /// source seed, which declares neither, the reflexive closing below stands in for them; a
    /// quantified goal whose leaf closes is `∀ y, True` at the pin, and `True` only through
    /// `implies_true`, so `rules` decide whether it closes: `∀ y : Nat, y + 0 = y := by simp
    /// only [Nat.add_zero]` is "unsolved goals ⊢ ∀ (y : Nat), True" at v4.32.0.
    fn simp_reflexivity(
        &mut self,
        goal: &ProofGoal,
        rules: &[SimpRule<'_>],
    ) -> Result<Option<Expr>, NatDefinitionElabError> {
        let target = self.whnf_with_transparency(
            &goal.target,
            UnificationTransparency::Abbreviations,
            false,
        )?;
        let candidate = if matches!(target.node(), ExprNode::Const { name, levels }
            if name == &Name::from_components(["True"]) && levels.is_empty())
        {
            Some(
                self.constant(&Name::from_components(["True", "intro"]))?
                    .value,
            )
        } else if self.txn.env.contains(&Name::from_components(["eq_self"])) {
            // Where `eq_self` is declared, `simp only` and the default set both carry it and
            // `iff_self` as rules, which rewrite every reflexive leaf to `True`. The pin closes
            // nothing else: `n = n` with `eq_self` erased, `HEq a a` and `n + 0 = n` stay open.
            return Ok(None);
        } else if matches!(target.node(), ExprNode::ForallE { .. }) {
            // The source seed declares no `eq_self`: reflexive leaves close here instead.
            if !self.simp_rules_close_implications(rules)? {
                return Ok(None);
            }
            self.simp_quantified_reflexivity(goal, target)?
        } else {
            self.automatic_reflexivity_candidate(goal, false)?
        };
        let Some(candidate) = candidate else {
            return Ok(None);
        };
        let target = self.instantiate(&goal.target)?;
        let mut trial = self.rewrite_trial();
        let hole = trial.hole(target)?;
        let result = trial
            .txn
            .unify(&hole, &candidate, UnificationBudget::new(trial.kernel));
        self.charge_rewrite_trial(&trial);
        match result {
            Ok(report) => {
                assert!(report.awakened.is_empty(), "private source queue");
                let candidate = trial.instantiate(&candidate)?;
                *self = trial;
                Ok(Some(candidate))
            }
            Err(error) => {
                let error = failure(SourceInferenceError::Unification(Box::new(error)));
                if Self::rewrite_nonmatch(&error) {
                    Ok(None)
                } else {
                    Err(error)
                }
            }
        }
    }

    /// Conversion mode's `simp` (`Conv.evalSimp`, vendored src/Lean/Elab/Tactic/Conv/Simp.lean):
    /// `expr` rewritten by the rules a `simp` tactic's six slots `args` select, step by step as
    /// [`Self::simplify_goal_with_rules`] rewrites a goal, but closing nothing. Returns the
    /// result and its equation `expr = result`, `None` when every step was definitional (the
    /// pin's `applySimpResult` then only changes `lhs`). Making no progress is no failure here:
    /// conv's `simp` calls `Simp.main` directly, without the goal's "no progress" check.
    pub(in crate::source) fn simp_expression_with(
        &mut self,
        args: &[Syntax],
        expr: &Expr,
    ) -> Result<(Expr, Option<Expr>), NatDefinitionElabError> {
        let rules = self.simp_rules(args)?;
        let original = self.instantiate(expr)?;
        let mut current = original.clone();
        let mut proof: Option<Expr> = None;
        let mut history = vec![current.clone()];
        let mut steps = 0usize;
        let permute = self.simp_rules_permute(&rules)?;
        loop {
            self.tick()?;
            let next = if let Some(normalized) = self.simp_normalize(&current)? {
                Some((normalized, None))
            } else {
                let index = self.simp_target_index(&current)?;
                self.simp_first_rewrite(
                    &rules,
                    permute,
                    |this, rule| {
                        Ok(
                            this.simp_rule_admitted(rule, index.as_ref(), SimpKeySide::Rewrite)
                                && !this.simp_definition_absent(rule, index.as_ref()),
                        )
                    },
                    |this, rule| {
                        if !this.simp_rule_may_rewrite(rule, &current)? {
                            return Ok(None);
                        }
                        match this.unfold_simp_rule(rule, &current)? {
                            UnfoldResult::Unchanged => Ok(None),
                            UnfoldResult::Changed(next) => {
                                Ok(Some(((next, None), SimpPlace::of(SimpReach::Unfold))))
                            }
                            UnfoldResult::NotDefinition => {
                                let Some((evidence, occurrence, reverse, place)) =
                                    this.simp_rule_evidence(&current, rule, &rules)?
                                else {
                                    return Ok(None);
                                };
                                let (next, step) = this.conv_congr_arg_step(
                                    &current,
                                    evidence,
                                    &occurrence,
                                    reverse,
                                    false,
                                )?;
                                Ok(Some(((next, Some(step)), place)))
                            }
                        }
                    },
                )?
                .map(|(_, found)| found)
            };
            let Some((next, step)) = next else {
                break;
            };
            if steps >= MAX_SIMPLIFICATION_STEPS {
                return Err(failure(SourceInferenceError::ResourceLimit));
            }
            for previous in &history {
                self.tick()?;
                if self.rewrite_same(previous, &next)? {
                    return Err(error(TacticError::SimplificationCycle));
                }
            }
            history.push(next.clone());
            steps += 1;
            if let Some(step) = step {
                proof = Some(match proof {
                    None => step,
                    Some(previous) => {
                        let alpha = self
                            .known_type(&original)?
                            .ok_or_else(|| failure(SourceInferenceError::ExpectedType))?;
                        let alpha = self.instantiate(&alpha)?;
                        let sort = self
                            .known_type(&alpha)?
                            .ok_or_else(|| failure(SourceInferenceError::ExpectedType))?;
                        let level = self.sort_level(&Typed {
                            value: alpha.clone(),
                            type_: sort,
                        })?;
                        let trans = Name::from_components(["Eq", "trans"]);
                        if !self.txn.env.contains(&trans) {
                            return Err(failure(SourceInferenceError::UnknownConstant(trans)));
                        }
                        [
                            alpha,
                            original.clone(),
                            current.clone(),
                            next.clone(),
                            previous,
                            step,
                        ]
                        .into_iter()
                        .fold(Expr::const_(trans, vec![level]), Expr::app)
                    }
                });
            }
            current = next;
        }
        Ok((current, proof))
    }

    pub(in crate::source) fn simplify_proof_goal(
        &mut self,
        proof: &mut ProofState<'_>,
        goal: ProofGoal,
        args: &[Syntax],
    ) -> Result<(), NatDefinitionElabError> {
        if self.simplify_at_locations(proof, &goal, args)? {
            return Ok(());
        }
        let (rules, config) = self.simp_selection(args)?;
        if config.fail_if_unchanged {
            return self.simplify_goal_with_rules(proof, goal, &rules, 0, None);
        }
        let start = proof.work.len();
        let result = self.simplify_goal_with_rules(proof, goal.clone(), &rules, 0, None);
        simp_unchanged(proof, goal, start, result)
    }

    // Hypothesis and goal simplification share one productive-step limit. A
    // changed hypothesis is sufficient progress when the target stays unchanged.
    fn simplify_goal_with_rules(
        &mut self,
        proof: &mut ProofState<'_>,
        mut goal: ProofGoal,
        rules: &[SimpRule<'_>],
        mut steps: usize,
        completion: Option<&Typed>,
    ) -> Result<(), NatDefinitionElabError> {
        let mut history = vec![self.instantiate(&goal.target)?];
        let permute = self.simp_rules_permute(rules)?;
        loop {
            self.tick()?;
            self.txn.lctx = goal.lctx.clone();
            let mut advanced = false;
            let target = self.instantiate(&goal.target)?;
            if let Some(normalized) = self.simp_normalize(&target)? {
                if steps >= MAX_SIMPLIFICATION_STEPS {
                    return Err(failure(SourceInferenceError::ResourceLimit));
                }
                for previous in &history {
                    self.tick()?;
                    if self.rewrite_same(previous, &normalized)? {
                        return Err(error(TacticError::SimplificationCycle));
                    }
                }
                history.push(normalized.clone());
                let (value, next_goal) = self.proof_goal(normalized)?;
                proof.work.push(Work::Close(goal, value));
                goal = next_goal;
                steps += 1;
                continue;
            }
            let index = self.simp_target_index(&target)?;
            let transition = self.simp_first_rewrite(
                rules,
                permute,
                |this, rule| {
                    Ok(
                        this.simp_rule_admitted(rule, index.as_ref(), SimpKeySide::Rewrite)
                            && !this.simp_definition_absent(rule, index.as_ref()),
                    )
                },
                |this, rule| this.simp_step(&goal, rule, rules),
            )?;
            if let Some((_, (next_goal, value))) = transition {
                if steps >= MAX_SIMPLIFICATION_STEPS {
                    return Err(failure(SourceInferenceError::ResourceLimit));
                }
                let next_target = self.instantiate(&next_goal.target)?;
                for previous in &history {
                    self.tick()?;
                    if self.rewrite_same(previous, &next_target)? {
                        return Err(error(TacticError::SimplificationCycle));
                    }
                }
                history.push(next_target);
                proof.work.push(Work::Close(goal, value));
                goal = next_goal;
                steps += 1;
                advanced = true;
            }
            if advanced {
                continue;
            }
            if let Some(completion) = completion {
                let mut budget = UnificationBudget::new(self.kernel);
                budget.zeta_delta = false;
                if !self.proof_types_match_with_budget(&completion.type_, &goal.target, budget)? {
                    return Err(error(TacticError::NoMatchingAssumption));
                }
                self.close_proof_goal(goal, completion.value.clone())?;
            } else if let Some(value) = self.simp_selected_proof(&goal.target, rules)? {
                self.close_proof_goal(goal, value)?;
            } else if let Some(value) = self.simp_reflexivity(&goal, rules)? {
                self.close_proof_goal(goal, value)?;
            } else if steps > 0 {
                // Simplification can expose a non-reflexive remaining goal.
                // Later instructions must solve it; progress is not completion.
                proof.work.push(Work::Goal(goal));
            } else {
                return Err(error(TacticError::SimplificationNoProgress));
            }
            return Ok(());
        }
    }
}

/// The registered entry a rule's discrimination keys are read from: a registered rule's own,
/// or the global theorem a bare identifier argument selects, which the pin's `elabSimpArgs`
/// inserts into the same discrimination tree (`SimpTheorems.addConst`). A term, a local and an
/// unfolded definition stay unkeyed (`simp_rule_keys` reads a definition as no key).
fn simp_rule_entry<'r>(
    rule: &'r SimpRule<'_>,
) -> Option<std::borrow::Cow<'r, scope::simp::SimpEntry>> {
    match rule {
        SimpRule::Global(entry) => Some(std::borrow::Cow::Borrowed(entry)),
        SimpRule::Explicit(RewriteRule {
            global: Some(declaration),
            reverse,
            ..
        }) => Some(std::borrow::Cow::Owned(scope::simp::SimpEntry {
            declaration: declaration.clone(),
            proof: None,
            priority: 1000,
            reverse: *reverse,
            order: 0,
        })),
        _ => None,
    }
}

/// `failIfUnchanged := false`: a call that changed nothing leaves its goal open, as the pin's
/// `simpGoal` then returns the goal it was given, rather than failing. Only the typed no-progress
/// refusal of an attempt that pushed no work since `start` is absorbed.
fn simp_unchanged(
    proof: &mut ProofState<'_>,
    goal: ProofGoal,
    start: usize,
    result: Result<(), NatDefinitionElabError>,
) -> Result<(), NatDefinitionElabError> {
    match result {
        Err(NatDefinitionElabError::Inference(SourceInferenceError::Tactic(
            TacticError::SimplificationNoProgress,
        ))) if proof.work.len() == start => {
            proof.work.push(Work::Goal(goal));
            Ok(())
        }
        result => result,
    }
}

/// An application's head and arguments in order, looking through metadata.
fn simp_key_spine(expr: &Expr) -> (&Expr, Vec<&Expr>) {
    let mut head = expr;
    let mut args = Vec::new();
    loop {
        match head.node() {
            ExprNode::App { f, a } => {
                args.push(a);
                head = f;
            }
            ExprNode::MData { expr, .. } => head = expr,
            _ => break,
        }
    }
    args.reverse();
    (head, args)
}

/// Which pattern of a rule a key describes: the one it rewrites (oriented), or its
/// stated left side, which a selected proof must match.
#[derive(Clone, Copy)]
enum SimpKeySide {
    Rewrite = 0,
    Prove = 1,
}

/// One argument of a discrimination key. A rule's argument is `Any` (a pattern
/// variable, or a shape the pin's key leaves open), the rigid constant it requires,
/// or a numeral's value; a target's argument may also be `Other`, a rigid
/// non-constant head (a parameter, a sort) that no constant key matches.
#[derive(Clone, Debug, PartialEq, Eq)]
enum SimpArgKey {
    Any,
    Const(Name),
    /// A constant with keyed arguments of its own, compared position by position: the
    /// pin's key path continues into an argument's arguments (`List.length (List.filterMap
    /// f l)` is not `List.length (xs ++ [])`). Bounded at [`SIMP_KEY_LEVELS`].
    App(Name, Vec<SimpArgKey>),
    /// A numeral, keyed by its value as the pin's `toNatLit?` keys it.
    Lit(fln_core::expr::NatLit),
    Other,
}

/// How many argument levels below a key's head are keyed. The pin's path has no bound;
/// two levels separate the candidates whose heads and argument heads agree.
const SIMP_KEY_LEVELS: usize = 2;

impl SimpArgKey {
    fn admits(&self, target: &Self) -> bool {
        match (self, target) {
            (Self::Any, _) | (_, Self::Any) => true,
            (Self::Const(rule) | Self::App(rule, _), Self::Const(target))
            | (Self::Const(rule), Self::App(target, _)) => rule == target,
            (Self::App(rule, rule_args), Self::App(target, target_args)) => {
                rule == target
                    && rule_args
                        .iter()
                        .zip(target_args)
                        .all(|(rule, target)| rule.admits(target))
            }
            (Self::Lit(rule), Self::Lit(target)) => rule == target,
            _ => false,
        }
    }
}

/// A rule's key: its pattern's rigid head and the keys of that head's keyed
/// arguments, in order; positions the pin's key ignores are `Any`.
#[derive(Clone, Debug)]
pub(super) struct SimpKey {
    head: Name,
    /// Keep the full arity even when trailing wildcard argument keys are omitted.
    /// A relation passed as a function is not an occurrence of its application.
    arity: usize,
    args: Vec<SimpArgKey>,
}

/// A target's applications by rigid head, with the environment they were read in.
pub(super) struct SimpTargetIndex {
    applications: HashMap<Name, Vec<Vec<SimpArgKey>>>,
    environment: SimpKeyEnvironment,
    table: Arc<crate::reducibility::ReducibilityTable>,
}

impl SimpTargetIndex {
    /// Some application has enough arguments for the rule and agrees with its keys.
    /// The pin's `.const name nargs` distinguishes arities exactly. Allowing extra
    /// target arguments conservatively retains rewrites of application prefixes.
    fn admits(&self, key: &SimpKey) -> bool {
        self.applications
            .get(&key.head)
            .is_some_and(|applications| {
                applications.iter().any(|args| {
                    args.len() >= key.arity
                        && key
                            .args
                            .iter()
                            .zip(args)
                            .all(|(rule, target)| rule.admits(target))
                })
            })
    }
}

/// What a rule's key depends on: the declarations and reducibility statuses.
type SimpKeyEnvironment = (
    Option<[u8; 32]>,
    (Option<[u8; 32]>, Option<[u8; 32]>),
    usize,
);

fn simp_key_environment(env: &Environment) -> SimpKeyEnvironment {
    (
        crate::reducibility::journal_digest(env),
        crate::instances::registry_identity(env),
        env.len(),
    )
}

/// Registered rules' keys, a pure function of the environment they were read in.
/// Speculative snapshots share it, so restoring one never discards or changes it.
#[derive(Clone, Default)]
pub(in crate::source) struct SimpKeyCache(Arc<Mutex<SimpKeyMemo>>);

#[derive(Default)]
struct SimpKeyMemo {
    environment: Option<SimpKeyEnvironment>,
    rules: HashMap<(Name, Option<Name>, bool), [Option<SimpKey>; 2]>,
    /// Whether a registered theorem's statement is a permutation (`aclt.rs`).
    perms: HashMap<Name, bool>,
}

/// A registered rule's `[rewrite, prove]` keys, read from its admitted type: the
/// pattern it rewrites (oriented) and its stated left side. A refutation, an
/// unfolded definition and an unreadable shape are unkeyed.
fn simp_rule_keys(
    env: &Environment,
    table: &crate::reducibility::ReducibilityTable,
    entry: &scope::simp::SimpEntry,
) -> [Option<SimpKey>; 2] {
    let Some(info) = env.find(entry.proof.as_ref().unwrap_or(&entry.declaration)) else {
        return [None, None];
    };
    if entry.proof.is_none() && matches!(info, ConstantInfo::Defn(_)) {
        return [None, None];
    }
    let mut body = &info.constant_val().type_;
    loop {
        match body.node() {
            ExprNode::ForallE { body: next, .. } => body = next,
            ExprNode::MData { expr, .. } => body = expr,
            _ => break,
        }
    }
    let (head, args) = simp_key_spine(body);
    let named = |text: &[&str]| Name::from_components(text.iter().copied());
    let (forward, backward) = match head.node() {
        ExprNode::Const { name, .. } if *name == named(&["Eq"]) && args.len() == 3 => {
            (Some(args[1]), Some(args[2]))
        }
        ExprNode::Const { name, .. } if *name == named(&["Iff"]) && args.len() == 2 => {
            (Some(args[0]), Some(args[1]))
        }
        ExprNode::Const { name, .. } if *name == named(&["Not"]) && args.len() == 1 => {
            (Some(args[0]), None)
        }
        // A refutation `p → False` loses its premise binder above; keep it unkeyed.
        ExprNode::Const { name, .. } if *name == named(&["False"]) => (None, None),
        ExprNode::Const { .. } => (Some(body), None),
        _ => (None, None),
    };
    let pattern = if entry.reverse { backward } else { forward };
    let key =
        |pattern: Option<&Expr>| pattern.and_then(|pattern| simp_pattern_key(env, table, pattern));
    [key(pattern), key(forward)]
}

/// A pattern's rigid head and argument keys. A head the pin's key path would
/// reduce at reducible transparency (an abbreviation other than a structure
/// projection) and numerals, which the pin keys as literals, stay unkeyed.
fn simp_pattern_key(
    env: &Environment,
    table: &crate::reducibility::ReducibilityTable,
    pattern: &Expr,
) -> Option<SimpKey> {
    if simp_key_noindex(pattern) {
        return None;
    }
    let pattern = simp_key_head_beta(pattern);
    let (head, args) = simp_key_spine(&pattern);
    match head.node() {
        // The pin keys a `∀` as `.arrow` and a `fun` as `.other`: only the same binder in
        // the target matches.
        ExprNode::ForallE { .. } if args.is_empty() => {
            return Some(SimpKey {
                head: simp_arrow_key(),
                arity: 0,
                args: Vec::new(),
            });
        }
        ExprNode::Lam { .. } if args.is_empty() => {
            return Some(SimpKey {
                head: simp_other_key(),
                arity: 0,
                args: Vec::new(),
            });
        }
        ExprNode::Const { .. } => {}
        _ => return None,
    }
    let args: Vec<Expr> = args.into_iter().cloned().collect();
    simp_constant_key(env, table, head, &args, 0)
}

/// `term`, an application of a reducible head, unfolded with its actual arguments and
/// beta-reduced through at most 8 reducible heads, as the pin's `whnfR` reduces a target node
/// before keying it. `None` where the result may still reduce in ways this does not
/// perform: a recursor, quotient or matcher head, a projection. An application too short
/// to unfold is returned as it stands, its head still reducible: unfolding it would give a
/// lambda, which the pin's `reduceUntilBadKey` does not key, so the pin keys this term.
/// A local head is returned for the caller to key: only one without a value is rigid. A
/// sort head is returned too. The pin stops one unfolding short of a sort (a "bad key")
/// and keys the reducible head itself, but no rule key here is rooted at a reducible
/// constant, so both admit exactly the unkeyed rules.
fn simp_key_unfold_reducible(
    env: &Environment,
    table: &crate::reducibility::ReducibilityTable,
    term: &Expr,
) -> Option<Expr> {
    let mut term = term.clone();
    for _ in 0..8 {
        let (head, args) = simp_key_spine(&term);
        let ExprNode::Const { name, .. } = head.node() else {
            break;
        };
        if !simp_key_unfolds(env, table, name) {
            break;
        }
        let Some(ConstantInfo::Defn(definition)) = env.find(name) else {
            return None;
        };
        let mut body = &definition.value;
        let mut parameters = 0usize;
        while let ExprNode::Lam { body: next, .. } = body.node() {
            if parameters == args.len() {
                // A partial application unfolds to a lambda, which the pin's
                // `reduceUntilBadKey` refuses as a key: it keeps this term.
                return Some(term);
            }
            body = next;
            parameters += 1;
        }
        let substituted: Vec<Expr> = args[..parameters]
            .iter()
            .map(|arg| (*arg).clone())
            .collect();
        let reduced = body.subst_loose(0, &substituted).ok()?;
        term = args[parameters..]
            .iter()
            .fold(reduced, |function, arg| Expr::app(function, (*arg).clone()));
        term = simp_key_head_beta(&term);
    }
    let (head, _) = simp_key_spine(&term);
    match head.node() {
        ExprNode::Const { name, .. } => {
            let stuck = matches!(
                env.find(name),
                Some(ConstantInfo::Rec(_) | ConstantInfo::Quot(_))
            ) || simp_key_unfolds(env, table, name)
                || matches!(name.leaf_view(), LeafView::Str(text)
                    if text.starts_with("match_") || text == "casesOn" || text == "rec")
                || env.find(name).is_none();
            (!stuck).then_some(term)
        }
        ExprNode::ForallE { .. }
        | ExprNode::Lit { .. }
        | ExprNode::FVar { .. }
        | ExprNode::Sort { .. } => Some(term),
        _ => None,
    }
}

/// `pattern` with a head beta redex reduced, as the pin's `DiscrTree.mkPath` reduces it before
/// keying: `Fin.induction_zero` states `(fun i => Fin.induction zero hs i) 0 = zero`, and was
/// unkeyed and tried at every node of every target. At most 8 redexes; a substitution this
/// cannot perform leaves the pattern as it is (unkeyed).
fn simp_key_head_beta(pattern: &Expr) -> Expr {
    let mut pattern = pattern.clone();
    for _ in 0..8 {
        let (head, args) = simp_key_spine(&pattern);
        let ExprNode::Lam { body, .. } = head.node() else {
            break;
        };
        let Some((first, rest)) = args.split_first() else {
            break;
        };
        let Ok(reduced) = body.subst_loose(0, std::slice::from_ref(*first)) else {
            break;
        };
        pattern = rest
            .iter()
            .fold(reduced, |function, arg| Expr::app(function, (*arg).clone()));
    }
    pattern
}

/// The pin's `.arrow` key, which every `∀` is indexed under (dependent or not), and a rule
/// rooted at one is keyed by.
fn simp_arrow_key() -> Name {
    Name::from_components(["«arrow»"])
}

/// The pin's `.other` key: a `fun` in the target or a rule rooted at one, and in the target
/// an application headed by a metavariable, which the pin's `getMatch` keys as `.other` too.
/// An `.other` node retrieves no `.arrow` rule, and an `.arrow` node no `.other` rule.
fn simp_other_key() -> Name {
    Name::from_components(["«other»"])
}

/// The key of `head args` with a constant head, as the pin's `whnfR` reaches it: a
/// reducible head is unfolded with the actual arguments substituted for its parameters
/// (`Nat.Coprime m n` is keyed as `Eq Nat (Nat.gcd …) 1`, `a > b` under `LT.lt`), through at
/// most 8 reducible heads. Only heads are substituted, never terms: a parameter used as an
/// argument becomes that argument, and one used as the head resolves to the argument's head.
/// `None` where the result is not keyed: a partial application (a `fun`), a numeral, or a
/// head that is still a bound variable.
fn simp_constant_key(
    env: &Environment,
    table: &crate::reducibility::ReducibilityTable,
    head: &Expr,
    args: &[Expr],
    depth: usize,
) -> Option<SimpKey> {
    const MAX_UNFOLDINGS: usize = 8;
    let ExprNode::Const { name, .. } = head.node() else {
        return None;
    };
    if *name == Name::from_components(["OfNat", "ofNat"]) {
        return None;
    }
    if !simp_key_unfolds(env, table, name) {
        let arguments: Vec<&Expr> = args.iter().collect();
        let mut keys = simp_key_arguments(env, table, name, &arguments, 0);
        while keys.last() == Some(&SimpArgKey::Any) {
            keys.pop();
        }
        return Some(SimpKey {
            head: name.clone(),
            arity: args.len(),
            args: keys,
        });
    }
    if depth == MAX_UNFOLDINGS {
        return None;
    }
    let Some(ConstantInfo::Defn(definition)) = env.find(name) else {
        return None;
    };
    let mut body = &definition.value;
    let mut parameters = 0usize;
    loop {
        match body.node() {
            ExprNode::Lam { body: next, .. } => {
                body = next;
                parameters += 1;
            }
            ExprNode::MData { expr, .. } => body = expr,
            _ => break,
        }
    }
    if args.len() < parameters {
        return None;
    }
    // A loose bound variable of the body is a parameter; the outermost is index 0.
    let actual = |expr: &Expr| -> Expr {
        match expr.node() {
            ExprNode::BVar { idx } => usize::try_from(*idx)
                .ok()
                .and_then(|idx| parameters.checked_sub(idx + 1))
                .map_or_else(|| expr.clone(), |parameter| args[parameter].clone()),
            _ => expr.clone(),
        }
    };
    let (body_head, body_args) = simp_key_spine(body);
    let resolved_head = actual(body_head);
    let (next_head, head_args) = simp_key_spine(&resolved_head);
    let next_args: Vec<Expr> = head_args
        .into_iter()
        .cloned()
        .chain(body_args.into_iter().map(actual))
        .chain(args[parameters..].iter().cloned())
        .collect();
    simp_constant_key(env, table, next_head, &next_args, depth + 1)
}

/// The argument keys of a pattern `head args`, at the positions the pin's key
/// reads: an instance argument never, an implicit one only when it is a type, an
/// explicit one unless it may be a proof. A position counts only where the
/// binder type, read at the actual type arguments, shows that statically; an
/// undecided position is left open, as `Any`.
fn simp_key_arguments(
    env: &Environment,
    table: &crate::reducibility::ReducibilityTable,
    head: &Name,
    args: &[&Expr],
    level: usize,
) -> Vec<SimpArgKey> {
    let Some(info) = env.find(head) else {
        return Vec::new();
    };
    let mut binders: Vec<&Expr> = Vec::new();
    let mut keys = Vec::new();
    let mut type_ = &info.constant_val().type_;
    while keys.len() < args.len() {
        match type_.node() {
            ExprNode::ForallE {
                binder_type,
                body,
                binder_info,
                ..
            } => {
                let keyed = match binder_info {
                    BinderInfo::InstImplicit => false,
                    BinderInfo::Implicit | BinderInfo::StrictImplicit => {
                        simp_key_is_sort(binder_type)
                    }
                    BinderInfo::Default => {
                        !simp_key_arg_is_proof(env, binder_type, &binders, args, args[keys.len()])
                    }
                };
                keys.push(if keyed {
                    simp_rule_arg_key(env, table, args[keys.len()], level)
                } else {
                    SimpArgKey::Any
                });
                binders.push(binder_type);
                type_ = body;
            }
            ExprNode::MData { expr, .. } => type_ = expr,
            _ => break,
        }
    }
    keys
}

/// Whether an explicit argument is certainly a proof, which the pin's key never reads
/// (`DiscrTree.ignoreArg` asks `isProof`): its binder type, read at the actual type
/// arguments, is a proposition, or its own head is a theorem or returns one's statement.
/// Undecided is not a proof, as the pin's `isProof` answers false for a type it cannot yet
/// see: `ite c a b` at `Eq`'s side is keyed, so `ite_eq_left_iff` is never tried at
/// `List.length xs = List.length ys`.
fn simp_key_arg_is_proof(
    env: &Environment,
    binder_type: &Expr,
    binders: &[&Expr],
    args: &[&Expr],
    arg: &Expr,
) -> bool {
    let returns_prop = |name: &Name| {
        env.find(name).is_some_and(|info| {
            let mut result = &info.constant_val().type_;
            loop {
                match result.node() {
                    ExprNode::ForallE { body, .. } => result = body,
                    ExprNode::MData { expr, .. } => result = expr,
                    _ => break matches!(result.node(), ExprNode::Sort { level } if level.is_zero()),
                }
            }
        })
    };
    // A type is a proposition when its head returns `Prop`; a `∀` is one when its body is.
    let is_proposition = |type_: &Expr| {
        let mut type_ = type_;
        while let ExprNode::ForallE { body, .. } | ExprNode::MData { expr: body, .. } = type_.node()
        {
            type_ = body;
        }
        match simp_key_spine(type_).0.node() {
            ExprNode::Const { name, .. } => returns_prop(name),
            ExprNode::BVar { idx } => usize::try_from(*idx)
                .ok()
                .and_then(|idx| binders.len().checked_sub(idx + 1))
                .and_then(|binder| args.get(binder))
                .is_some_and(|actual| match simp_key_spine(actual).0.node() {
                    ExprNode::Const { name, .. } => returns_prop(name),
                    _ => false,
                }),
            _ => false,
        }
    };
    if is_proposition(binder_type) {
        return true;
    }
    let ExprNode::Const { name, .. } = simp_key_spine(arg).0.node() else {
        return false;
    };
    match env.find(name) {
        Some(ConstantInfo::Thm(_)) => true,
        Some(info) => {
            let mut result = &info.constant_val().type_;
            while let ExprNode::ForallE { body, .. } | ExprNode::MData { expr: body, .. } =
                result.node()
            {
                result = body;
            }
            matches!(simp_key_spine(result).0.node(), ExprNode::Const { name, .. } if returns_prop(name))
        }
        None => false,
    }
}

fn simp_key_is_sort(type_: &Expr) -> bool {
    matches!(
        simp_key_spine(simp_key_without_out_param(type_)).0.node(),
        ExprNode::Sort { .. }
    )
}

/// `outParam T` and `semiOutParam T` are `T` (reducible identities in `Init.Prelude`).
fn simp_key_without_out_param(type_: &Expr) -> &Expr {
    match simp_key_spine(type_) {
        (head, args)
            if args.len() == 1
                && matches!(head.node(), ExprNode::Const { name, .. }
                    if *name == Name::from_components(["outParam"])
                        || *name == Name::from_components(["semiOutParam"])) =>
        {
            args[0]
        }
        _ => type_,
    }
}

/// A rule's argument key: a numeral's value, the rigid constant the pin's key fixes
/// there, or `Any` for a pattern variable, a reducible head, and the `Nat` offsets
/// (`n + 1`, `Nat.succ n`) the pin leaves open as stars.
fn simp_rule_arg_key(
    env: &Environment,
    table: &crate::reducibility::ReducibilityTable,
    arg: &Expr,
    level: usize,
) -> SimpArgKey {
    if simp_key_noindex(arg) {
        return SimpArgKey::Any;
    }
    if let Some(value) = simp_key_numeral(arg) {
        return SimpArgKey::Lit(value);
    }
    let (head, args) = simp_key_spine(arg);
    match head.node() {
        ExprNode::Const { name, .. }
            if !simp_key_is_numeral_or_offset(name, &args)
                && !simp_key_unfolds(env, table, name) =>
        {
            if level + 1 >= SIMP_KEY_LEVELS {
                return SimpArgKey::Const(name.clone());
            }
            let mut keys = simp_key_arguments(env, table, name, &args, level + 1);
            while keys.last() == Some(&SimpArgKey::Any) {
                keys.pop();
            }
            if keys.is_empty() {
                SimpArgKey::Const(name.clone())
            } else {
                SimpArgKey::App(name.clone(), keys)
            }
        }
        _ => SimpArgKey::Any,
    }
}

/// A `no_index` term: the pin's `DiscrTree.hasNoindexAnnotation`, an `mdata` holding exactly
/// `noindex := true`, which its key path reads as a star (`pushArgs`).
fn simp_key_noindex(expr: &Expr) -> bool {
    matches!(expr.node(), ExprNode::MData { data, .. }
        if data.len() == 1 && data.get_bool(&Name::from_components(["noindex"]), false))
}

/// The value of a numeral as the pin's `DiscrTree` reads one (`isNumeral`,
/// `toNatLit?`): a raw literal, `OfNat.ofNat _ n _` over a numeral, `Nat.zero`,
/// and `Nat.succ` of a numeral whose value fits a word.
fn simp_key_numeral(expr: &Expr) -> Option<fln_core::expr::NatLit> {
    let (head, args) = simp_key_spine(expr);
    let named = |name: &Name, text: [&str; 2]| *name == Name::from_components(text);
    match (head.node(), args.as_slice()) {
        (
            ExprNode::Lit {
                literal: fln_core::expr::Literal::Nat(value),
            },
            [],
        ) => Some(value.clone()),
        (ExprNode::Const { name, .. }, [_, value, _]) if named(name, ["OfNat", "ofNat"]) => {
            simp_key_numeral(value)
        }
        (ExprNode::Const { name, .. }, []) if named(name, ["Nat", "zero"]) => {
            Some(fln_core::expr::NatLit::from_u64(0))
        }
        (ExprNode::Const { name, .. }, [value]) if named(name, ["Nat", "succ"]) => {
            let value = simp_key_numeral(value)?.to_u64()?.checked_add(1)?;
            Some(fln_core::expr::NatLit::from_u64(value))
        }
        _ => None,
    }
}

fn simp_key_is_numeral_or_offset(name: &Name, args: &[&Expr]) -> bool {
    let named = |text: &[&str]| *name == Name::from_components(text.iter().copied());
    if named(&["OfNat", "ofNat"]) || named(&["Nat", "zero"]) || named(&["Nat", "succ"]) {
        return true;
    }
    (named(&["HAdd", "hAdd"]) || named(&["Add", "add"]) || named(&["Nat", "add"]))
        && args.last().is_some_and(|last| {
            let (head, _) = simp_key_spine(last);
            match head.node() {
                ExprNode::Lit { .. } => true,
                ExprNode::Const { name, .. } => *name == Name::from_components(["OfNat", "ofNat"]),
                _ => false,
            }
        })
}

/// A target's argument key: a numeral's value, its rigid constant head, `Other` for
/// a parameter or a sort, and `Any` for whatever may reduce or unify further (an
/// unread `Nat.succ`, a reducible head, a let-bound local, a binder, a metavariable).
fn simp_target_arg_key(
    env: &Environment,
    table: &crate::reducibility::ReducibilityTable,
    lctx: &LocalContext,
    arg: &Expr,
    level: usize,
) -> SimpArgKey {
    if let Some(value) = simp_key_numeral(arg) {
        return SimpArgKey::Lit(value);
    }
    let (head, args) = simp_key_spine(arg);
    match head.node() {
        ExprNode::Const { name, .. } => {
            // A `Nat.succ` whose value is not read here may still be a numeral.
            if *name == Name::from_components(["OfNat", "ofNat"])
                || *name == Name::from_components(["Nat", "succ"])
                || simp_key_unfolds(env, table, name)
            {
                SimpArgKey::Any
            } else if level + 1 >= SIMP_KEY_LEVELS || args.is_empty() {
                SimpArgKey::Const(name.clone())
            } else {
                // Every position: the rule's key leaves open the ones the pin ignores.
                SimpArgKey::App(
                    name.clone(),
                    args.iter()
                        .map(|arg| simp_target_arg_key(env, table, lctx, arg, level + 1))
                        .collect(),
                )
            }
        }
        ExprNode::FVar { id } => match lctx.find(id) {
            Some(local) if local.value.is_none() => SimpArgKey::Other,
            _ => SimpArgKey::Any,
        },
        ExprNode::Sort { .. } => SimpArgKey::Other,
        _ => SimpArgKey::Any,
    }
}

/// Whether the key path may see through `name`: at reducible transparency, where the
/// pin's simp computes both a rule's keys and a target's. An instance is rigid there.
/// Unfolding instances admitted rules the pin never retrieves: `instAddNat` opens
/// `Nat.add`, whose recursor body mentions `Nat.succ`, so `Nat.succ_eq_add_one`
/// rewrote `3` to `2 + 1` at every step of `two + 1 = 3`, and every `Nat.add`-rooted
/// rule was tried at every `Eq` goal. Structure projections are rigid keys: the pin
/// keys `a + b` as `HAdd.hAdd`.
fn simp_key_unfolds(
    env: &Environment,
    table: &crate::reducibility::ReducibilityTable,
    name: &Name,
) -> bool {
    let Some(ConstantInfo::Defn(definition)) = env.find(name) else {
        return false;
    };
    let mut value = &definition.value;
    while let ExprNode::Lam { body, .. } = value.node() {
        value = body;
    }
    if matches!(value.node(), ExprNode::Proj { .. }) {
        return false;
    }
    match table.get(name) {
        Some(status) => status == crate::reducibility::Reducibility::Reducible,
        None => definition.hints == ReducibilityHints::Abbrev,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use fln_env::constants::{AxiomVal, ConstantVal};

    fn n(text: &str) -> Name {
        Name::from_components(text.split('.'))
    }
    fn c(text: &str) -> Expr {
        Expr::const_(n(text), Vec::new())
    }
    fn bvar(index: u32) -> Expr {
        Expr::bvar(index).unwrap()
    }
    fn apps(head: Expr, args: &[Expr]) -> Expr {
        args.iter()
            .fold(head, |function, arg| Expr::app(function, arg.clone()))
    }
    fn pi(binder: Expr, body: Expr, info: BinderInfo) -> Expr {
        Expr::forall_e(Name::anonymous(), binder, body, info)
    }
    fn eq(type_: Expr, left: Expr, right: Expr) -> Expr {
        apps(
            Expr::const_(n("Eq"), vec![Level::one()]),
            &[type_, left, right],
        )
    }

    /// `Eq`, the data type `Nat` with `f` and `Nat.succ`, a class `C` with an
    /// operation `op`, and the rules `fx : ∀ a b : Nat, f a = b` (keyed by `f`) and
    /// `fne : ∀ a b : Nat, ¬ f a = b` (keyed by `Eq` at `Nat` with `f` on the left).
    fn environment() -> Environment {
        use BinderInfo::{Default, Implicit, InstImplicit};
        let type0 = Expr::sort(Level::one());
        let nat = c("Nat");
        let axioms = [
            (
                "Eq",
                vec![n("u")],
                pi(
                    Expr::sort(Level::param(n("u"))),
                    pi(
                        bvar(0),
                        pi(bvar(1), Expr::sort(Level::zero()), Default),
                        Default,
                    ),
                    Implicit,
                ),
            ),
            (
                "Not",
                Vec::new(),
                pi(
                    Expr::sort(Level::zero()),
                    Expr::sort(Level::zero()),
                    Default,
                ),
            ),
            ("Nat", Vec::new(), type0.clone()),
            (
                "List",
                Vec::new(),
                pi(type0.clone(), type0.clone(), Default),
            ),
            ("C", Vec::new(), pi(type0.clone(), type0.clone(), Default)),
            (
                "op",
                Vec::new(),
                pi(
                    type0,
                    pi(
                        Expr::app(c("C"), bvar(0)),
                        pi(bvar(1), pi(bvar(2), bvar(3), Default), Default),
                        InstImplicit,
                    ),
                    Implicit,
                ),
            ),
            ("f", Vec::new(), pi(nat.clone(), nat.clone(), Default)),
            (
                "Nat.succ",
                Vec::new(),
                pi(nat.clone(), nat.clone(), Default),
            ),
            (
                "fx",
                Vec::new(),
                pi(
                    nat.clone(),
                    pi(
                        nat.clone(),
                        eq(nat.clone(), Expr::app(c("f"), bvar(1)), bvar(0)),
                        Default,
                    ),
                    Default,
                ),
            ),
            (
                "fne",
                Vec::new(),
                pi(
                    nat.clone(),
                    pi(
                        nat.clone(),
                        Expr::app(c("Not"), eq(nat, Expr::app(c("f"), bvar(1)), bvar(0))),
                        Default,
                    ),
                    Default,
                ),
            ),
        ];
        axioms
            .into_iter()
            .fold(Environment::new(), |env, (name, level_params, type_)| {
                env.add_decl(ConstantInfo::Axiom(AxiomVal {
                    base: ConstantVal {
                        name: n(name),
                        level_params,
                        type_,
                    },
                    is_unsafe: false,
                }))
                .unwrap()
            })
    }

    #[test]
    fn keys_read_type_arguments_and_leave_instances_proofs_and_offsets_open() {
        let env = environment();
        let table = crate::reducibility::table(&env).unwrap();
        let key = |pattern: Expr| simp_pattern_key(&env, &table, &pattern).unwrap();
        // `f a = b` at `Nat`: the type and the left side's head are keyed.
        let at_nat = key(eq(c("Nat"), Expr::app(c("f"), bvar(0)), bvar(1)));
        assert_eq!(at_nat.head, n("Eq"));
        assert_eq!(
            at_nat.args,
            [SimpArgKey::Const(n("Nat")), SimpArgKey::Const(n("f"))]
        );
        // At a pattern variable's type a side is keyed when its own head shows it is data
        // (`f` returns `Nat`); a pattern variable stays open.
        let polymorphic = key(eq(bvar(2), Expr::app(c("f"), bvar(0)), bvar(1)));
        assert_eq!(
            polymorphic.args,
            [SimpArgKey::Any, SimpArgKey::Const(n("f"))]
        );
        let open = key(eq(bvar(2), bvar(0), Expr::app(c("f"), bvar(1))));
        assert_eq!(
            open.args,
            [SimpArgKey::Any, SimpArgKey::Any, SimpArgKey::Const(n("f"))]
        );
        // A head beta redex is keyed as the head it reduces to (`(fun i => f i) a` as `f`),
        // and its argument stays open.
        let redex = key(Expr::app(
            Expr::lam(
                Name::anonymous(),
                c("Nat"),
                Expr::app(c("f"), bvar(0)),
                BinderInfo::Default,
            ),
            bvar(0),
        ));
        assert_eq!(redex.head, n("f"));
        assert!(redex.args.is_empty());
        // An instance argument is never keyed; a `Nat` offset is left open.
        let operation = key(apps(
            c("op"),
            &[
                c("Nat"),
                bvar(3),
                Expr::app(c("Nat.succ"), bvar(0)),
                Expr::app(c("f"), bvar(1)),
            ],
        ));
        assert_eq!(
            operation.args,
            [
                SimpArgKey::Const(n("Nat")),
                SimpArgKey::Any,
                SimpArgKey::Any,
                SimpArgKey::Const(n("f")),
            ]
        );
    }

    #[test]
    fn a_rule_is_admitted_only_where_its_argument_keys_can_match_and_skipping_is_free() {
        let env = environment();
        let mut context = Context::new(&env, Budget::DEFAULT);
        for name in ["x", "y"] {
            context
                .txn
                .lctx
                .add_param(FVarId(n(name)), n(name), c("Nat"), BinderInfo::Default);
        }
        context
            .txn
            .lctx
            .add_let(FVarId(n("z")), n("z"), c("Nat"), c("Nat"));
        let rule = |name: &str| {
            SimpRule::Global(scope::simp::SimpEntry {
                declaration: n(name),
                proof: None,
                priority: 1000,
                reverse: false,
                order: 0,
            })
        };
        let (rewrite, refutation) = (rule("fx"), rule("fne"));
        let local = |name: &str| Expr::fvar(FVarId(n(name)));
        // Each target with whether `fx` (head `f`) and `fne` (`f _ = _` at `Nat`) may match.
        let cases = [
            // A parameter is rigid: `f a = b` cannot match `x = y`.
            (eq(c("Nat"), local("x"), local("y")), false, false),
            (
                eq(c("Nat"), Expr::app(c("f"), local("x")), local("y")),
                true,
                true,
            ),
            // Nested anywhere in the target, as an argument of another application.
            (
                eq(
                    c("Nat"),
                    Expr::app(
                        c("Nat.succ"),
                        eq(c("Nat"), Expr::app(c("f"), local("x")), local("y")),
                    ),
                    local("y"),
                ),
                true,
                true,
            ),
            // Another type at `Eq`'s keyed type argument.
            (
                eq(
                    Expr::app(c("List"), c("Nat")),
                    Expr::app(c("f"), local("x")),
                    local("y"),
                ),
                true,
                false,
            ),
            // A let-bound local may unfold to anything; its value is not read.
            (eq(c("Nat"), local("z"), local("y")), false, true),
        ];
        for (target, rewrites, refutes) in cases {
            let before = context.txn.budget.heartbeats_consumed;
            let index = context.simp_target_index(&target).unwrap();
            assert_eq!(context.txn.budget.heartbeats_consumed, before + 1);
            for _ in 0..1000 {
                assert_eq!(
                    context.simp_rule_admitted(&rewrite, index.as_ref(), SimpKeySide::Rewrite),
                    rewrites,
                    "{target:?}"
                );
                assert_eq!(
                    context.simp_rule_admitted(&refutation, index.as_ref(), SimpKeySide::Rewrite),
                    refutes,
                    "{target:?}"
                );
                assert!(context.simp_rule_admitted(
                    &SimpRule::Local(FVarId(n("x"))),
                    index.as_ref(),
                    SimpKeySide::Rewrite
                ));
            }
            assert_eq!(context.txn.budget.heartbeats_consumed, before + 1);
        }
    }

    #[test]
    fn a_function_argument_does_not_admit_rules_for_its_application() {
        let nat = c("Nat");
        let env = environment()
            .add_decl(ConstantInfo::Axiom(AxiomVal {
                base: ConstantVal {
                    name: n("higherOrder"),
                    level_params: Vec::new(),
                    type_: pi(
                        pi(nat.clone(), nat.clone(), BinderInfo::Default),
                        Expr::sort(Level::zero()),
                        BinderInfo::Default,
                    ),
                },
                is_unsafe: false,
            }))
            .unwrap();
        let mut context = Context::new(&env, Budget::DEFAULT);
        let rule = SimpRule::Global(scope::simp::SimpEntry {
            declaration: n("fx"),
            proof: None,
            priority: 1000,
            reverse: false,
            order: 0,
        });
        let key = context.simp_rule_node_key(&rule).unwrap().unwrap();
        // `fx : ∀ a b, f a = b` has no rigid argument keys. Its omitted
        // wildcard must still count: passing `f` is not applying `f a`.
        assert!(key.args.is_empty());
        let passed = Expr::app(c("higherOrder"), c("f"));
        let index = context.simp_target_index(&passed).unwrap();
        assert!(!context.simp_rule_admitted(&rule, index.as_ref(), SimpKeySide::Rewrite));
        assert!(!context.simp_node_admits(&key, &c("f")).unwrap());
        let under_lambda = Expr::app(
            c("higherOrder"),
            Expr::lam(
                Name::anonymous(),
                nat,
                Expr::app(c("f"), bvar(0)),
                BinderInfo::Default,
            ),
        );
        let index = context.simp_target_index(&under_lambda).unwrap();
        assert!(context.simp_rule_admitted(&rule, index.as_ref(), SimpKeySide::Rewrite));
        assert!(
            context
                .simp_node_admits(&key, &Expr::app(c("f"), c("Nat.zero")))
                .unwrap()
        );
    }

    #[test]
    fn numerals_are_literal_keys_and_targets_unfold_only_reducible_definitions() {
        use fln_core::expr::{Literal, NatLit};
        use fln_env::constants::{DefinitionSafety, DefinitionVal};
        let numeral = |value: u64| Expr::lit(Literal::Nat(NatLit::from_u64(value)));
        let nat = c("Nat");
        let rule_type = |left: Expr, right: Expr| eq(nat.clone(), left, right);
        // `fzero : f 0 = 0` keys `f` at the literal 0; `succ_rule : ∀ n, Nat.succ n = n`
        // is rooted at `Nat.succ`. `wrap n := Nat.succ n` is a plain definition.
        let base = [
            (
                "fzero",
                rule_type(Expr::app(c("f"), numeral(0)), numeral(0)),
            ),
            (
                "succ_rule",
                pi(
                    nat.clone(),
                    rule_type(Expr::app(c("Nat.succ"), bvar(0)), bvar(0)),
                    BinderInfo::Default,
                ),
            ),
        ]
        .into_iter()
        .fold(environment(), |env, (name, type_)| {
            env.add_decl(ConstantInfo::Axiom(AxiomVal {
                base: ConstantVal {
                    name: n(name),
                    level_params: Vec::new(),
                    type_,
                },
                is_unsafe: false,
            }))
            .unwrap()
        })
        .add_decl(ConstantInfo::Defn(DefinitionVal {
            base: ConstantVal {
                name: n("wrap"),
                level_params: Vec::new(),
                type_: pi(nat.clone(), nat.clone(), BinderInfo::Default),
            },
            value: Expr::lam(
                Name::anonymous(),
                nat.clone(),
                Expr::app(c("Nat.succ"), bvar(0)),
                BinderInfo::Default,
            ),
            hints: ReducibilityHints::Regular(1),
            safety: DefinitionSafety::Safe,
            all: vec![n("wrap")],
        }))
        .unwrap();
        let rule = |name: &str| {
            SimpRule::Global(scope::simp::SimpEntry {
                declaration: n(name),
                proof: None,
                priority: 1000,
                reverse: false,
                order: 0,
            })
        };
        let admitted = |env: &Environment, target: Expr, name: &str| {
            let mut context = Context::new(env, Budget::DEFAULT);
            context
                .txn
                .lctx
                .add_param(FVarId(n("x")), n("x"), nat.clone(), BinderInfo::Default);
            let index = context.simp_target_index(&target).unwrap();
            context.simp_rule_admitted(&rule(name), index.as_ref(), SimpKeySide::Rewrite)
        };
        let x = Expr::fvar(FVarId(n("x")));
        let f = |arg: Expr| Expr::app(c("f"), arg);
        // A numeral argument matches only its own value; `Nat.zero` is the numeral 0.
        assert!(admitted(&base, f(numeral(0)), "fzero"));
        assert!(admitted(&base, f(c("Nat.zero")), "fzero"));
        assert!(!admitted(&base, f(numeral(3)), "fzero"));
        assert!(!admitted(&base, f(x.clone()), "fzero"));
        // A numeral supplies no `Nat.succ` root; a written `Nat.succ` does.
        assert!(!admitted(&base, f(numeral(3)), "succ_rule"));
        assert!(admitted(
            &base,
            f(Expr::app(c("Nat.succ"), x.clone())),
            "succ_rule"
        ));
        // The target closure unfolds a reducible definition, never an instance-reducible one.
        let wrapped = f(Expr::app(c("wrap"), x));
        assert!(!admitted(&base, wrapped.clone(), "succ_rule"));
        for (status, expected) in [
            (crate::reducibility::Reducibility::ImplicitReducible, false),
            (crate::reducibility::Reducibility::Reducible, true),
        ] {
            let env = crate::reducibility::register(&base, &n("wrap"), status).unwrap();
            assert_eq!(
                admitted(&env, wrapped.clone(), "succ_rule"),
                expected,
                "{status:?}"
            );
        }
        // A rule rooted at a reducible head is keyed by its unfolding's head, as the pin's
        // `whnfR` keys it; a plain definition keys itself.
        let pattern = Expr::app(c("wrap"), bvar(0));
        let head = |env: &Environment| {
            let table = crate::reducibility::table(env).unwrap();
            simp_pattern_key(env, &table, &pattern).unwrap()
        };
        let reducible = crate::reducibility::register(
            &base,
            &n("wrap"),
            crate::reducibility::Reducibility::Reducible,
        )
        .unwrap();
        assert_eq!(head(&reducible).head, n("Nat.succ"));
        assert!(head(&reducible).args.is_empty());
        assert_eq!(head(&base).head, n("wrap"));
        // Unfolding substitutes the actual arguments, so the unfolded statement keeps its own
        // keys: `cop m n := f m = n` (like `Nat.Coprime`) is keyed as `Eq Nat (f _) _`.
        let cop = reducible
            .add_decl(ConstantInfo::Defn(DefinitionVal {
                base: ConstantVal {
                    name: n("cop"),
                    level_params: Vec::new(),
                    type_: pi(
                        nat.clone(),
                        pi(nat.clone(), Expr::sort(Level::zero()), BinderInfo::Default),
                        BinderInfo::Default,
                    ),
                },
                value: Expr::lam(
                    Name::anonymous(),
                    nat.clone(),
                    Expr::lam(
                        Name::anonymous(),
                        nat.clone(),
                        eq(nat.clone(), Expr::app(c("f"), bvar(1)), bvar(0)),
                        BinderInfo::Default,
                    ),
                    BinderInfo::Default,
                ),
                hints: ReducibilityHints::Regular(1),
                safety: DefinitionSafety::Safe,
                all: vec![n("cop")],
            }))
            .unwrap();
        let cop = crate::reducibility::register(
            &cop,
            &n("cop"),
            crate::reducibility::Reducibility::Reducible,
        )
        .unwrap();
        let table = crate::reducibility::table(&cop).unwrap();
        let key = simp_pattern_key(&cop, &table, &apps(c("cop"), &[bvar(1), bvar(0)])).unwrap();
        assert_eq!(key.head, n("Eq"));
        assert_eq!(
            key.args,
            [SimpArgKey::Const(n("Nat")), SimpArgKey::Const(n("f"))]
        );
        // Partially applied, the unfolding is a `fun`: left open, as the pin's `.other`.
        assert!(simp_pattern_key(&cop, &table, &Expr::app(c("cop"), bvar(0))).is_none());
        // A rule rooted at a `∀` is keyed `.arrow` and admitted only where the target has a
        // `∀`; one rooted at a `fun` is keyed `.other` and admitted only where the target has
        // a `fun` or a metavariable head.
        let arrow_rule =
            simp_pattern_key(&cop, &table, &pi(c("Nat"), c("Nat"), BinderInfo::Default)).unwrap();
        assert_eq!(arrow_rule.head, simp_arrow_key());
        let other_rule = simp_pattern_key(
            &cop,
            &table,
            &Expr::lam(Name::anonymous(), c("Nat"), bvar(0), BinderInfo::Default),
        )
        .unwrap();
        assert_eq!(other_rule.head, simp_other_key());
        let mut context = Context::new(&base, Budget::DEFAULT);
        let plain = context.simp_target_index(&f(numeral(1))).unwrap().unwrap();
        assert!(!plain.admits(&arrow_rule) && !plain.admits(&other_rule));
        let index = |context: &mut Context, side: Expr| {
            context
                .simp_target_index(&eq(c("Nat"), f(numeral(1)), side))
                .unwrap()
                .unwrap()
        };
        let lambda = index(
            &mut context,
            Expr::lam(Name::anonymous(), c("Nat"), bvar(0), BinderInfo::Default),
        );
        assert!(lambda.admits(&other_rule) && !lambda.admits(&arrow_rule));
        let forall = index(&mut context, pi(c("Nat"), c("Nat"), BinderInfo::Default));
        assert!(forall.admits(&arrow_rule) && !forall.admits(&other_rule));
        let pending = index(
            &mut context,
            Expr::app(Expr::mvar(MVarId(n("pending"))), numeral(1)),
        );
        assert!(pending.admits(&other_rule) && !pending.admits(&arrow_rule));
    }

    #[test]
    fn a_rule_is_tried_only_at_the_nodes_its_key_admits() {
        let env = environment();
        let mut context = Context::new(&env, Budget::DEFAULT);
        for name in ["x", "y"] {
            context
                .txn
                .lctx
                .add_param(FVarId(n(name)), n(name), c("Nat"), BinderInfo::Default);
        }
        context.txn.lctx.add_param(
            FVarId(n("g")),
            n("g"),
            pi(c("Nat"), c("Nat"), BinderInfo::Default),
            BinderInfo::Default,
        );
        context.txn.lctx.add_let(
            FVarId(n("z")),
            n("z"),
            c("Nat"),
            Expr::app(c("f"), Expr::fvar(FVarId(n("x")))),
        );
        let rule = |name: &str| {
            SimpRule::Global(scope::simp::SimpEntry {
                declaration: n(name),
                proof: None,
                priority: 1000,
                reverse: false,
                order: 0,
            })
        };
        let local = |name: &str| Expr::fvar(FVarId(n(name)));
        let f_x = Expr::app(c("f"), local("x"));
        let equation = eq(c("Nat"), f_x.clone(), local("y"));
        let succ = Expr::app(c("Nat.succ"), local("x"));
        let binder = Expr::lam(Name::anonymous(), c("Nat"), bvar(0), BinderInfo::Default);
        // `fx : f a = b` rewrites at `f x` only; `fne : ¬ f a = b` at the equation only.
        let rewrite = context.simp_rule_node_key(&rule("fx")).unwrap().unwrap();
        let refutation = context.simp_rule_node_key(&rule("fne")).unwrap().unwrap();
        for (node, rewrites, refutes) in [
            (f_x, true, false),
            (equation, false, true),
            (succ, false, false),
            // A parameter, alone or applied, is the pin's `.fvar` key and a sort its
            // `.other` key: no constant-rooted rule is retrieved there. A let-bound local
            // may reduce to its value, so it is never filtered. A binder admits only a rule
            // rooted at a binder.
            (local("x"), false, false),
            (Expr::app(local("g"), local("x")), false, false),
            (Expr::sort(Level::zero()), false, false),
            (local("z"), true, true),
            (binder, false, false),
            // A raw literal is a literal key: no constant-rooted rule matches it.
            (
                Expr::lit(fln_core::expr::Literal::Nat(
                    fln_core::expr::NatLit::from_u64(2),
                )),
                false,
                false,
            ),
        ] {
            assert_eq!(
                context.simp_node_admits(&rewrite, &node).unwrap(),
                rewrites,
                "{node:?}"
            );
            assert_eq!(
                context.simp_node_admits(&refutation, &node).unwrap(),
                refutes,
                "{node:?}"
            );
        }
        // Explicit and local rules are unkeyed and try every node.
        assert!(
            context
                .simp_rule_node_key(&SimpRule::Local(FVarId(n("x"))))
                .unwrap()
                .is_none()
        );
    }

    #[test]
    fn keys_compare_the_heads_of_an_arguments_own_arguments() {
        use fln_env::constants::{AxiomVal, ConstantVal};
        let nat = c("Nat");
        let f = |arg: Expr| Expr::app(c("f"), arg);
        // `fff : ∀ a b : Nat, f (f (f a)) = b` rewrites at `f (f (f _))`.
        let env = environment()
            .add_decl(ConstantInfo::Axiom(AxiomVal {
                base: ConstantVal {
                    name: n("fff"),
                    level_params: Vec::new(),
                    type_: pi(
                        nat.clone(),
                        pi(
                            nat.clone(),
                            eq(nat.clone(), f(f(f(bvar(1)))), bvar(0)),
                            BinderInfo::Default,
                        ),
                        BinderInfo::Default,
                    ),
                },
                is_unsafe: false,
            }))
            .unwrap();
        let mut context = Context::new(&env, Budget::DEFAULT);
        for name in ["x", "y"] {
            context
                .txn
                .lctx
                .add_param(FVarId(n(name)), n(name), nat.clone(), BinderInfo::Default);
        }
        let rule = SimpRule::Global(scope::simp::SimpEntry {
            declaration: n("fff"),
            proof: None,
            priority: 1000,
            reverse: false,
            order: 0,
        });
        let key = context.simp_rule_node_key(&rule).unwrap().unwrap();
        assert_eq!(key.head, n("f"));
        assert_eq!(
            key.args,
            [SimpArgKey::App(n("f"), vec![SimpArgKey::Const(n("f"))])]
        );
        let local = |name: &str| Expr::fvar(FVarId(n(name)));
        for (node, admitted) in [
            (f(f(f(local("x")))), true),
            // The argument's head agrees and its own argument is a parameter.
            (f(f(local("x"))), false),
            (f(local("x")), false),
        ] {
            let target = eq(nat.clone(), node.clone(), local("y"));
            let index = context.simp_target_index(&target).unwrap();
            assert_eq!(
                context.simp_rule_admitted(&rule, index.as_ref(), SimpKeySide::Rewrite),
                admitted,
                "{target:?}"
            );
            assert_eq!(
                context.simp_node_admits(&key, &node).unwrap(),
                admitted,
                "{node:?}"
            );
        }
    }

    #[test]
    fn an_explicit_argument_is_keyed_unless_it_is_certainly_a_proof() {
        use fln_env::constants::{AxiomVal, ConstantVal};
        let nat = c("Nat");
        let u = Level::param(n("u"));
        // `g {α : Sort u} (x : α) : α` returns data or a proof depending on `α`;
        // `k (m : Nat) (h : m = m) : Nat` takes a proof.
        let env = [
            (
                "g",
                vec![n("u")],
                pi(
                    Expr::sort(u.clone()),
                    pi(bvar(0), bvar(1), BinderInfo::Default),
                    BinderInfo::Implicit,
                ),
            ),
            (
                "k",
                Vec::new(),
                pi(
                    nat.clone(),
                    pi(
                        eq(nat.clone(), bvar(0), bvar(0)),
                        nat.clone(),
                        BinderInfo::Default,
                    ),
                    BinderInfo::Default,
                ),
            ),
        ]
        .into_iter()
        .fold(environment(), |env, (name, level_params, type_)| {
            env.add_decl(ConstantInfo::Axiom(AxiomVal {
                base: ConstantVal {
                    name: n(name),
                    level_params,
                    type_,
                },
                is_unsafe: false,
            }))
            .unwrap()
        });
        let table = crate::reducibility::table(&env).unwrap();
        let key = |pattern: Expr| simp_pattern_key(&env, &table, &pattern).unwrap();
        let sort_eq = |type_: Expr, left: Expr, right: Expr| {
            apps(
                Expr::const_(n("Eq"), vec![u.clone()]),
                &[type_, left, right],
            )
        };
        let g = |type_: Expr, arg: Expr| apps(Expr::const_(n("g"), vec![u.clone()]), &[type_, arg]);
        // At a `Sort u` the pin's `isProof` cannot see a proposition, so `g α x` is keyed.
        let undecided = key(sort_eq(bvar(2), g(bvar(2), bvar(1)), bvar(1)));
        assert_eq!(undecided.args, [SimpArgKey::Any, SimpArgKey::Const(n("g"))]);
        // A proof argument (`h : m = m`) is never keyed, even when it is a constant.
        let proof = key(apps(c("k"), &[bvar(1), c("fx")]));
        assert_eq!(proof.head, n("k"));
        assert!(proof.args.is_empty(), "{proof:?}");
    }

    #[test]
    fn a_reducible_target_node_is_keyed_by_its_unfolding() {
        use fln_env::constants::{DefinitionSafety, DefinitionVal};
        let nat = c("Nat");
        let prop = Expr::sort(Level::zero());
        let abbrev = |name: &str, type_: Expr, value: Expr| {
            ConstantInfo::Defn(DefinitionVal {
                base: ConstantVal {
                    name: n(name),
                    level_params: Vec::new(),
                    type_,
                },
                value,
                hints: ReducibilityHints::Abbrev,
                safety: DefinitionSafety::Safe,
                all: vec![n(name)],
            })
        };
        // `wrap a := f a` unfolds to an application of `f`; `imp p q := p → q` to an arrow.
        let env = environment()
            .add_decl(abbrev(
                "wrap",
                pi(nat.clone(), nat.clone(), BinderInfo::Default),
                Expr::lam(
                    Name::anonymous(),
                    nat.clone(),
                    Expr::app(c("f"), bvar(0)),
                    BinderInfo::Default,
                ),
            ))
            .unwrap()
            .add_decl(abbrev(
                "imp",
                pi(
                    prop.clone(),
                    pi(prop.clone(), prop.clone(), BinderInfo::Default),
                    BinderInfo::Default,
                ),
                Expr::lam(
                    Name::anonymous(),
                    prop.clone(),
                    Expr::lam(
                        Name::anonymous(),
                        prop.clone(),
                        pi(bvar(1), bvar(1), BinderInfo::Default),
                        BinderInfo::Default,
                    ),
                    BinderInfo::Default,
                ),
            ))
            .unwrap()
            // `apply g a := g a` unfolds to an application of a local, as `dsimp2`'s `eval`.
            .add_decl(abbrev(
                "apply",
                pi(
                    pi(nat.clone(), nat.clone(), BinderInfo::Default),
                    pi(nat.clone(), nat.clone(), BinderInfo::Default),
                    BinderInfo::Default,
                ),
                Expr::lam(
                    Name::anonymous(),
                    pi(nat.clone(), nat.clone(), BinderInfo::Default),
                    Expr::lam(
                        Name::anonymous(),
                        nat.clone(),
                        Expr::app(bvar(1), bvar(0)),
                        BinderInfo::Default,
                    ),
                    BinderInfo::Default,
                ),
            ))
            .unwrap();
        let mut context = Context::new(&env, Budget::DEFAULT);
        context
            .txn
            .lctx
            .add_param(FVarId(n("x")), n("x"), nat.clone(), BinderInfo::Default);
        context.txn.lctx.add_param(
            FVarId(n("g")),
            n("g"),
            pi(nat.clone(), nat.clone(), BinderInfo::Default),
            BinderInfo::Default,
        );
        for name in ["p", "q"] {
            context
                .txn
                .lctx
                .add_param(FVarId(n(name)), n(name), prop.clone(), BinderInfo::Default);
        }
        let rule = SimpRule::Global(scope::simp::SimpEntry {
            declaration: n("fx"),
            proof: None,
            priority: 1000,
            reverse: false,
            order: 0,
        });
        let key = context.simp_rule_node_key(&rule).unwrap().unwrap();
        let local = |name: &str| Expr::fvar(FVarId(n(name)));
        let binder = SimpKey {
            head: simp_arrow_key(),
            arity: 0,
            args: Vec::new(),
        };
        let other = SimpKey {
            head: simp_other_key(),
            arity: 0,
            args: Vec::new(),
        };
        let wrapped = Expr::app(c("wrap"), local("x"));
        let implication = apps(c("imp"), &[local("p"), local("q")]);
        assert!(context.simp_node_admits(&key, &wrapped).unwrap());
        assert!(!context.simp_node_admits(&binder, &wrapped).unwrap());
        assert!(!context.simp_node_admits(&key, &implication).unwrap());
        assert!(context.simp_node_admits(&binder, &implication).unwrap());
        assert!(!context.simp_node_admits(&other, &implication).unwrap());
        // A pending proof `?h x` is the pin's `.other` key: neither `fx`'s rule nor a rule
        // rooted at a `∀` is retrieved there.
        let pending = Expr::app(Expr::mvar(MVarId(n("pending"))), local("x"));
        assert!(!context.simp_node_admits(&key, &pending).unwrap());
        assert!(!context.simp_node_admits(&binder, &pending).unwrap());
        assert!(context.simp_node_admits(&other, &pending).unwrap());
        // `apply g x` is keyed as `g x`, the pin's `.fvar g 1`: neither rule is retrieved.
        let applied = apps(c("apply"), &[local("g"), local("x")]);
        assert!(!context.simp_node_admits(&key, &applied).unwrap());
        assert!(!context.simp_node_admits(&binder, &applied).unwrap());
        // `apply` and `apply g` unfold to lambdas, which the pin does not key: it keys them
        // by `apply` itself, where no rule key here is rooted.
        for short in [c("apply"), Expr::app(c("apply"), local("g"))] {
            assert!(!context.simp_node_admits(&key, &short).unwrap());
            assert!(!context.simp_node_admits(&binder, &short).unwrap());
            assert!(context.simp_root_index(&short).unwrap().is_some());
        }
        // Unfolding into `f x` still admits `f`'s rule: the filter follows the unfolding.
        let unfolds_to_f = apps(
            c("apply"),
            &[
                Expr::lam(
                    Name::anonymous(),
                    nat.clone(),
                    Expr::app(c("f"), bvar(0)),
                    BinderInfo::Default,
                ),
                local("x"),
            ],
        );
        assert!(context.simp_node_admits(&key, &unfolds_to_f).unwrap());
    }

    /// The source seed, which declares the structure `And` (`And.intro (left : a) (right : b)`).
    fn seeded_context() -> Context {
        use fln_env::environment::{DeclarationBudget, DeclarationCommitted};
        use fln_env::pmap::CollisionBudget;
        use fln_kernel::capability::{Published, admit};
        use fln_kernel::council::{Council, CouncilOutcome, convene};
        let mut env = Environment::new();
        let budget = Budget::for_stack_bytes(2 * 1024 * 1024);
        for declaration in crate::seed::source_seed_declarations() {
            let Outcome::Complete(admitted) = admit(&env, declaration, budget) else {
                panic!("seed nonanswer")
            };
            let CouncilOutcome::Agreed(checked) = convene(&Council::nobody_was_asked(), admitted)
            else {
                panic!("seed rejected")
            };
            env = match checked.publish(
                DeclarationBudget::default(),
                CollisionBudget::default(),
                None,
            ) {
                Outcome::Complete(Published::Committed(DeclarationCommitted::Published(
                    result,
                ))) => result.environment,
                Outcome::Complete(Published::BlockCommitted(result)) => result.environment,
                other => panic!("seed publication {other:?}"),
            };
        }
        Context::new(&env, budget)
    }

    /// A primitive projection `h.1` is keyed by its projection function, `And.left`, so a
    /// rule keyed by another head is not tried there. Unindexed, every rule was: each
    /// `*.sizeOf_spec` rule was tried at `hiddenSize.1 a` inside a `termination_by`
    /// measure, some 14,000 heartbeats apiece.
    #[test]
    fn a_primitive_projection_is_keyed_by_its_projection_function() {
        let mut context = seeded_context();
        let prop = Expr::sort(Level::zero());
        let mut local = |name: &str, type_: Expr| {
            let id = FVarId(n(name));
            context
                .txn
                .lctx
                .add_param(id.clone(), n(name), type_, BinderInfo::Default);
            Expr::fvar(id)
        };
        let p = local("p", prop.clone());
        let q = local("q", prop);
        let h = local("h", Expr::app(Expr::app(c("And"), p), q));
        let node = Expr::proj(n("And"), 0, h);
        let rule = |head: &str| SimpKey {
            head: n(head),
            arity: 3,
            args: Vec::new(),
        };
        assert!(context.simp_node_admits(&rule("And.left"), &node).unwrap());
        assert!(!context.simp_node_admits(&rule("Nat.succ"), &node).unwrap());
        assert!(!context.simp_node_admits(&rule("And.right"), &node).unwrap());
        let index = context.simp_target_index(&node).unwrap().unwrap();
        assert!(index.admits(&rule("And.left")));
    }
}
