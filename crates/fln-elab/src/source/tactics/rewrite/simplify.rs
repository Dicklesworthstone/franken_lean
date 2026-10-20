//! Proof-producing simplification with explicit and immutable registered rules.
//! Rules are tried deterministically and re-instantiated for every application.
//! An unsuccessful alternative restores its complete elaboration state while
//! retaining spent work. Every productive step is ordinary Eq.rec transport.

mod binders;
mod dsimp;
mod locations;
mod simpa;
mod unfold;

use super::matching::RigidTypeHead;
use super::*;
use crate::lctx::LocalContext;
use fln_core::expr::BinderInfo;
use fln_env::environment::Environment;
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
}
impl SimpRule<'_> {
    fn reverse(&self) -> bool {
        match self {
            Self::Explicit(rule) => rule.reverse,
            Self::Global(rule) => rule.reverse,
            Self::Local(_) => false,
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
            match self.unfold_simp_term(syntax, false, &current)? {
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
        if self.txn.lctx.find_by_user_name(val).is_some() {
            return Ok(None);
        }
        let resolved = self
            .resolve_source_name(val)?
            .ok_or_else(|| failure(SourceInferenceError::UnknownConstant(val.clone())))?;
        Ok((self.txn.lctx.find_by_user_name(&resolved).is_none()
            && self.txn.env.contains(&resolved))
        .then_some(resolved))
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
    /// and charges nothing: it reads only the rule's admitted type. Explicit and
    /// local rules, unfolded definitions and every shape not keyed here may match.
    fn simp_rule_admitted(
        &self,
        rule: &SimpRule<'_>,
        index: Option<&SimpTargetIndex>,
        side: SimpKeySide,
    ) -> bool {
        let (Some(index), SimpRule::Global(entry)) = (index, rule) else {
            return true;
        };
        let cache = Arc::clone(&self.simp_key_cache.0);
        let mut memo = cache.lock().unwrap_or_else(PoisonError::into_inner);
        if memo.environment.as_ref() != Some(&index.environment) {
            *memo = SimpKeyMemo {
                environment: Some(index.environment),
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
            .or_insert_with(|| simp_rule_keys(&self.txn.env, &index.table, entry));
        keys[side as usize]
            .as_ref()
            .is_none_or(|key| index.admits(key))
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
                        .map(|arg| simp_target_arg_key(env, &table, &self.txn.lctx, arg))
                        .collect();
                    applications.entry(name.clone()).or_default().push(keys);
                    if simp_key_unfolds(env, &table, name)
                        && unfolded.insert(name.clone())
                        && let Some(ConstantInfo::Defn(definition)) = env.find(name)
                    {
                        pending.push(definition.value.clone());
                    }
                }
                ExprNode::Proj {
                    struct_name, idx, ..
                } => {
                    if let Ok(idx) = usize::try_from(*idx)
                        && let Some(projection) = self.simp_projection_function(struct_name, idx)
                    {
                        applications.entry(projection).or_default().push(Vec::new());
                    }
                }
                ExprNode::ForallE { .. } | ExprNode::Lam { .. } | ExprNode::LetE { .. } => {
                    applications
                        .entry(simp_binder_key())
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
    /// may reduce the node: a non-constant or reducible head.
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
        let ExprNode::Const { name, .. } = head.node() else {
            return Ok(None);
        };
        if simp_key_unfolds(env, &table, name) {
            return Ok(None);
        }
        let keys = args
            .iter()
            .map(|arg| simp_target_arg_key(env, &table, &self.txn.lctx, arg))
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
        }
    }

    /// A bare, explicitly selected induction hypothesis can use its checked
    /// companion without changing the public hypothesis's application API.
    /// Both declarations must still be in this branch. Following only direct
    /// local aliases preserves annotations and local shadowing; ordinary term
    /// applications continue to elaborate the full conditional hypothesis.
    fn simp_rule_term(&mut self, syntax: &Syntax) -> Result<Typed, NatDefinitionElabError> {
        if let Some(term) = self.specialized_induction_rule(syntax)? {
            return Ok(term);
        }
        self.term(syntax, None)
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
        expect_default_config(config, "default simplification configuration")?;
        expect_empty_null(discharger, "default simplification discharger")?;
        if !simpa {
            let location = location.ok_or_else(|| error(TacticError::MalformedScript))?;
            self.rewrite_locations(location)?;
        }
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
        } else {
            Vec::new()
        };
        for _ in &defaults {
            self.tick()?;
        }
        let mut arguments = expect_null_args(arguments, "optional simp rule list")?;
        // `simpa`'s rule list is its own `simpArgs` node (`simpaArgsRest`); `simp`'s is inline.
        if let [Syntax::Node { kind, args, .. }] = arguments
            && kind == &parser_kind(&["Tactic", "simpArgs"])
        {
            arguments = args.as_slice();
        }
        if arguments.is_empty() {
            return Ok(defaults);
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
                origin,
                SimpRule::Explicit(RewriteRule {
                    syntax: &parts[2],
                    reverse,
                }),
            ));
        }
        // Explicit arguments have precedence; registered rules follow in their
        // stable priority/registration order. `only` leaves this tail empty.
        Ok(rules
            .into_iter()
            .map(|(_, rule)| rule)
            .chain(defaults)
            .collect())
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
            for rule in &unfoldable {
                self.tick()?;
                if let UnfoldResult::Changed(next) = self.unfold_simp_rule(rule, &target)? {
                    target = next;
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
        if let Some(value) = self.simp_reflexivity(&goal)? {
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
                let Some((next_goal, value)) = self.simp_step(&goal, rule, &[])? else {
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
                None => self.simp_reflexivity(&goal)?,
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
    ) -> Result<Option<(ProofGoal, Expr)>, NatDefinitionElabError> {
        let target = self.instantiate(&goal.target)?;
        if !self.simp_rule_may_rewrite(rule, &target)? {
            return Ok(None);
        }
        match self.unfold_simp_rule(rule, &target)? {
            UnfoldResult::Unchanged => Ok(None),
            UnfoldResult::Changed(next_target) => {
                let (child, next_goal) = self.proof_goal(next_target)?;
                Ok(Some((next_goal, child)))
            }
            UnfoldResult::NotDefinition => {
                let Some((term, occurrence, reverse)) =
                    self.simp_rule_evidence(&target, rule, premise_rules)?
                else {
                    return Ok(None);
                };
                self.rewrite_transport(goal, term, &occurrence, reverse)
                    .map(Some)
            }
        }
    }

    /// Check a candidate only after the shared automatic-closure policy admits
    /// it. Full K1 assignment conversion alone would unfold ordinary definitions
    /// that are absent from this tactic's explicit rule set.
    fn simp_reflexivity(
        &mut self,
        goal: &ProofGoal,
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
        } else if matches!(target.node(), ExprNode::ForallE { .. }) {
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

    pub(in crate::source) fn simplify_proof_goal(
        &mut self,
        proof: &mut ProofState<'_>,
        goal: ProofGoal,
        args: &[Syntax],
    ) -> Result<(), NatDefinitionElabError> {
        if self.simplify_at_locations(proof, &goal, args)? {
            return Ok(());
        }
        let rules = self.simp_rules(args)?;
        self.simplify_goal_with_rules(proof, goal, &rules, 0, None)
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
                let transition = self.simp_step(&goal, rule, rules)?;
                let Some((next_goal, value)) = transition else {
                    self.restore_simp_trial(original);
                    continue;
                };
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
                break;
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
            } else if let Some(value) = self.simp_reflexivity(&goal)? {
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
    /// A numeral, keyed by its value as the pin's `toNatLit?` keys it.
    Lit(fln_core::expr::NatLit),
    Other,
}

impl SimpArgKey {
    fn admits(&self, target: &Self) -> bool {
        match (self, target) {
            (Self::Any, _) | (_, Self::Any) => true,
            (Self::Const(rule), Self::Const(target)) => rule == target,
            (Self::Lit(rule), Self::Lit(target)) => rule == target,
            _ => false,
        }
    }
}

/// A rule's key: its pattern's rigid head and the keys of that head's keyed
/// arguments, in order; positions the pin's key ignores are `Any`.
#[derive(Clone, Debug)]
struct SimpKey {
    head: Name,
    args: Vec<SimpArgKey>,
}

/// A target's applications by rigid head, with the environment they were read in.
pub(super) struct SimpTargetIndex {
    applications: HashMap<Name, Vec<Vec<SimpArgKey>>>,
    environment: SimpKeyEnvironment,
    table: Arc<crate::reducibility::ReducibilityTable>,
}

impl SimpTargetIndex {
    /// Some application of the key's head agrees with every argument key both have.
    fn admits(&self, key: &SimpKey) -> bool {
        self.applications
            .get(&key.head)
            .is_some_and(|applications| {
                applications.iter().any(|args| {
                    key.args
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
    let (head, args) = simp_key_spine(pattern);
    match head.node() {
        // The pin keys a binder as `.arrow` or `.other`: only a binder in the target matches.
        ExprNode::ForallE { .. } | ExprNode::Lam { .. } if args.is_empty() => {
            return Some(SimpKey {
                head: simp_binder_key(),
                args: Vec::new(),
            });
        }
        ExprNode::Const { .. } => {}
        _ => return None,
    }
    let args: Vec<Expr> = args.into_iter().cloned().collect();
    simp_constant_key(env, table, head, &args, 0)
}

/// The pseudo head every binder (`∀`, `fun`, `let`) of a target is indexed under, and a
/// rule rooted at one is keyed by.
fn simp_binder_key() -> Name {
    Name::from_components(["«binder»"])
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
        let mut keys = simp_key_arguments(env, table, name, &arguments);
        while keys.last() == Some(&SimpArgKey::Any) {
            keys.pop();
        }
        return Some(SimpKey {
            head: name.clone(),
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
                        simp_key_is_sort(binder_type)
                            || simp_key_is_data_type(env, binder_type, &binders, args)
                            || simp_key_arg_is_data(env, args[keys.len()])
                    }
                };
                keys.push(if keyed {
                    simp_rule_arg_key(env, table, args[keys.len()])
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

/// Whether an argument is data by its own head, as the pin's `isProof` reads it: the head
/// constant's result is a sort (the argument is a type), a type in a nonzero universe, or one
/// of the head's own type parameters ranging over one.
fn simp_key_arg_is_data(env: &Environment, arg: &Expr) -> bool {
    let ExprNode::Const { name, .. } = simp_key_spine(arg).0.node() else {
        return false;
    };
    let Some(info) = env.find(name) else {
        return false;
    };
    let mut binders: Vec<&Expr> = Vec::new();
    let mut result = &info.constant_val().type_;
    loop {
        match result.node() {
            ExprNode::ForallE {
                binder_type, body, ..
            } => {
                binders.push(binder_type);
                result = body;
            }
            ExprNode::MData { expr, .. } => result = expr,
            _ => break,
        }
    }
    let sort_is_not_zero = |type_: &Expr| {
        matches!(simp_key_spine(simp_key_without_out_param(type_)).0.node(),
            ExprNode::Sort { level } if level.is_not_zero())
    };
    match simp_key_spine(result).0.node() {
        ExprNode::Sort { .. } => true,
        ExprNode::BVar { idx } => usize::try_from(*idx)
            .ok()
            .and_then(|idx| binders.len().checked_sub(idx + 1))
            .is_some_and(|binder| sort_is_not_zero(binders[binder])),
        ExprNode::Const { name, .. } => env.find(name).is_some_and(|info| {
            let mut codomain = &info.constant_val().type_;
            loop {
                match codomain.node() {
                    ExprNode::ForallE { body, .. } => codomain = body,
                    ExprNode::MData { expr, .. } => codomain = expr,
                    _ => break sort_is_not_zero(codomain),
                }
            }
        }),
        _ => false,
    }
}

/// Whether every inhabitant of the binder type `type_` is data, never a proof: its
/// head is a constant whose type ends in a nonzero universe, or an earlier binder
/// whose actual argument is such a type (or, failing that, ranges over one).
fn simp_key_is_data_type(
    env: &Environment,
    type_: &Expr,
    binders: &[&Expr],
    args: &[&Expr],
) -> bool {
    let sort_is_not_zero = |type_: &Expr| {
        matches!(simp_key_spine(simp_key_without_out_param(type_)).0.node(),
            ExprNode::Sort { level } if level.is_not_zero())
    };
    let constant_is_data_type = |name: &Name| {
        env.find(name).is_some_and(|info| {
            let mut result = &info.constant_val().type_;
            loop {
                match result.node() {
                    ExprNode::ForallE { body, .. } => result = body,
                    ExprNode::MData { expr, .. } => result = expr,
                    _ => break sort_is_not_zero(result),
                }
            }
        })
    };
    match simp_key_spine(type_).0.node() {
        ExprNode::BVar { idx } => {
            let Some(binder) = usize::try_from(*idx)
                .ok()
                .and_then(|idx| binders.len().checked_sub(idx + 1))
            else {
                return false;
            };
            match simp_key_spine(args[binder]).0.node() {
                ExprNode::Const { name, .. } => constant_is_data_type(name),
                ExprNode::Sort { .. } => true,
                _ => sort_is_not_zero(binders[binder]),
            }
        }
        ExprNode::Const { name, .. } => constant_is_data_type(name),
        _ => false,
    }
}

/// A rule's argument key: a numeral's value, the rigid constant the pin's key fixes
/// there, or `Any` for a pattern variable, a reducible head, and the `Nat` offsets
/// (`n + 1`, `Nat.succ n`) the pin leaves open as stars.
fn simp_rule_arg_key(
    env: &Environment,
    table: &crate::reducibility::ReducibilityTable,
    arg: &Expr,
) -> SimpArgKey {
    if let Some(value) = simp_key_numeral(arg) {
        return SimpArgKey::Lit(value);
    }
    let (head, args) = simp_key_spine(arg);
    match head.node() {
        ExprNode::Const { name, .. }
            if !simp_key_is_numeral_or_offset(name, &args)
                && !simp_key_unfolds(env, table, name) =>
        {
            SimpArgKey::Const(name.clone())
        }
        _ => SimpArgKey::Any,
    }
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
) -> SimpArgKey {
    if let Some(value) = simp_key_numeral(arg) {
        return SimpArgKey::Lit(value);
    }
    let (head, _) = simp_key_spine(arg);
    match head.node() {
        ExprNode::Const { name, .. } => {
            // A `Nat.succ` whose value is not read here may still be a numeral.
            if *name == Name::from_components(["OfNat", "ofNat"])
                || *name == Name::from_components(["Nat", "succ"])
                || simp_key_unfolds(env, table, name)
            {
                SimpArgKey::Any
            } else {
                SimpArgKey::Const(name.clone())
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
        // A rule rooted at a binder is admitted only where the target has a binder.
        let binder_rule = SimpKey {
            head: simp_binder_key(),
            args: Vec::new(),
        };
        let mut context = Context::new(&base, Budget::DEFAULT);
        let plain = context.simp_target_index(&f(numeral(1))).unwrap().unwrap();
        assert!(!plain.admits(&binder_rule));
        let with_binder = context
            .simp_target_index(&eq(
                c("Nat"),
                f(numeral(1)),
                Expr::lam(Name::anonymous(), c("Nat"), bvar(0), BinderInfo::Default),
            ))
            .unwrap()
            .unwrap();
        assert!(with_binder.admits(&binder_rule));
    }
}
