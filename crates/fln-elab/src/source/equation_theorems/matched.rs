//! The equations of a definition by pattern matching, from its recorded match (`journal`):
//! the pin's `mkEqnTypes` splitting the definition's matcher with its splitter
//! (vendored `Lean/Elab/PreDefinition/Eqns.lean:224-310`, `Lean/Meta/Tactic/Split.lean:243-301`,
//! `Lean/Meta/Match/MatchEqs.lean:153-250`), replayed on the recorded alternatives.
//!
//! One equation per alternative, in order. Its statement:
//! - the names the split gives its locals, with `tactic.hygienic` off (`mkEqns`): the
//!   generalized discriminants are named after the matcher's motive binders, then each
//!   alternative's fields after the matcher's, then its overlap hypotheses `x`, each the first
//!   name the context does not use (`LocalContext.getUnusedName`, Lean/LocalContext.lean:413);
//! - the alternative's overlap hypotheses: for each earlier alternative whose patterns unify
//!   with this one's, `∀ ys, pattern = earlier pattern → … → False`, simplified as
//!   `Match.simpH?` simplifies it (vendored Lean/Meta/Match/SimpH.lean): an equation of equal
//!   sides is dropped, one whose right side is a variable is substituted, one between
//!   constructor applications is replaced by its fields' equations, and a hypothesis whose
//!   constructors differ is dropped;
//! - `Cases.unifyEqs?` on the discriminants' equations: a parameter matched by a constructor
//!   pattern is replaced by it, a variable pattern by the older local (the parameter);
//! - `saveEqn`: the locals the equation mentions, in context order, then the relevant
//!   hypotheses, and the right-hand side with its head `let`s substituted (`expandRHS?`).
//!
//! The proof is this engine's: the definition is unfolded by the kernel, a local the unfolded
//! term is stuck on is split by its recursor, a literal comparison it is stuck on is split by
//! `Bool` cases (`Nat.eq_of_beq_eq_true`), and a case an earlier alternative covers is
//! discharged by its overlap hypothesis. The kernel checks all of it.
//!
//! Refused: a right-hand side that still contains a `match` after the split (the pin's states
//! it with its matcher), and anything the prover does not reach.
use super::super::*;
use super::journal::{self, Record};
use super::{NotGenerated, Unsupported, cleanup_annotations, equation_name};
use fln_core::expr::Literal;
use fln_env::constants::{ConstantInfo, ConstantVal, DefinitionVal, TheoremVal};

/// Splits one proof may make before it is refused: a literal pattern this engine compiles to
/// one `Nat` layer per unit costs one split each.
const MAX_DEPTH: usize = 160;

fn scope_error() -> NatDefinitionElabError {
    failure(SourceInferenceError::Scope)
}

/// `Name.appendIndexAfter`.
fn append_index(name: &Name, index: usize) -> Name {
    match name.leaf_view() {
        LeafView::Str(text) => Name::str(name.parent(), format!("{text}_{index}")),
        _ => Name::str(name.clone(), format!("_{index}")),
    }
}

/// `LocalContext.getUnusedName` over the user names `used`, which it extends.
fn unused_name(used: &mut Vec<Name>, suggestion: &Name) -> Name {
    let suggestion = suggestion.erase_macro_scopes();
    let name = if used.contains(&suggestion) {
        (1..)
            .map(|index| append_index(&suggestion, index))
            .find(|candidate| !used.contains(candidate))
            .expect("an unused name")
    } else {
        suggestion
    };
    used.push(name.clone());
    name
}

fn app_n(head: Expr, args: impl IntoIterator<Item = Expr>) -> Expr {
    args.into_iter().fold(head, Expr::app)
}

fn spine(expr: &Expr) -> (&Expr, Vec<Expr>) {
    let mut args = Vec::new();
    let mut head = expr;
    while let ExprNode::App { f, a } = head.node() {
        args.push(a.clone());
        head = f;
    }
    args.reverse();
    (head, args)
}

fn replace(expr: &Expr, id: &FVarId, value: &Expr) -> Result<Expr, NatDefinitionElabError> {
    expr.abstract_fvar(id, 0)
        .map_err(|_| scope_error())?
        .subst_loose(0, std::slice::from_ref(value))
        .map_err(|_| scope_error())
}

fn mentions(expr: &Expr, id: &FVarId) -> bool {
    let mut pending = vec![expr];
    while let Some(expr) = pending.pop() {
        if !expr.has_fvar() {
            continue;
        }
        match expr.node() {
            ExprNode::FVar { id: found } if found == id => return true,
            ExprNode::App { f, a } => pending.extend([f, a]),
            ExprNode::Lam {
                binder_type, body, ..
            }
            | ExprNode::ForallE {
                binder_type, body, ..
            } => pending.extend([binder_type, body]),
            ExprNode::LetE {
                type_, value, body, ..
            } => pending.extend([type_, value, body]),
            ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => pending.push(expr),
            _ => {}
        }
    }
    false
}

fn as_fvar(expr: &Expr) -> Option<&FVarId> {
    match expr.node() {
        ExprNode::FVar { id } => Some(id),
        _ => None,
    }
}

/// A pattern's head as a constructor: `Nat` literals (raw or `OfNat`) as `zero`/`succ`.
enum Head {
    Constructor {
        name: Name,
        fields: Vec<Expr>,
    },
    /// A natural number literal.
    Nat(u64),
    Other,
}

fn nat_literal(expr: &Expr) -> Option<u64> {
    match expr.node() {
        ExprNode::Lit {
            literal: Literal::Nat(value),
        } => value.to_u64(),
        _ => {
            let (head, args) = spine(expr);
            match (head.node(), args.as_slice()) {
                (ExprNode::Const { name, .. }, [ty, literal, _])
                    if *name == Name::from_components(["OfNat", "ofNat"])
                        && matches!(ty.node(), ExprNode::Const { name, .. }
                            if *name == Name::from_components(["Nat"])) =>
                {
                    nat_literal(literal)
                }
                (ExprNode::Const { name, .. }, [])
                    if *name == Name::from_components(["Nat", "zero"]) =>
                {
                    Some(0)
                }
                _ => None,
            }
        }
    }
}

fn raw_nat(value: u64) -> Expr {
    Expr::lit(Literal::Nat(fln_core::expr::NatLit::from_u64(value)))
}

impl Context {
    fn head(&self, expr: &Expr) -> Head {
        if let Some(value) = nat_literal(expr) {
            return Head::Nat(value);
        }
        let (head, args) = spine(expr);
        let ExprNode::Const { name, .. } = head.node() else {
            return Head::Other;
        };
        let Some(ConstantInfo::Ctor(constructor)) = self.txn.env.find(name) else {
            return Head::Other;
        };
        if args.len() != (constructor.num_params + constructor.num_fields) as usize {
            return Head::Other;
        }
        Head::Constructor {
            name: name.clone(),
            fields: args[constructor.num_params as usize..].to_vec(),
        }
    }

    /// `C a = C b` as its fields' equations, `None` when the constructors differ, and the
    /// equation itself when a side is not a constructor (injection fails). A literal is its
    /// `Nat.succ` when compared with one.
    fn injection(&self, lhs: &Expr, rhs: &Expr) -> Option<Result<Vec<(Expr, Expr)>, ()>> {
        let succ = Name::from_components(["Nat", "succ"]);
        match (self.head(lhs), self.head(rhs)) {
            (Head::Nat(a), Head::Nat(b)) => Some(if a == b { Ok(Vec::new()) } else { Err(()) }),
            (Head::Nat(a), Head::Constructor { name, fields }) => {
                if name != succ {
                    return Some(if a == 0 && fields.is_empty() {
                        Ok(Vec::new())
                    } else {
                        Err(())
                    });
                }
                Some(if a == 0 {
                    Err(())
                } else {
                    Ok(vec![(raw_nat(a - 1), fields[0].clone())])
                })
            }
            (Head::Constructor { name, fields }, Head::Nat(b)) => {
                if name != succ {
                    return Some(if b == 0 && fields.is_empty() {
                        Ok(Vec::new())
                    } else {
                        Err(())
                    });
                }
                Some(if b == 0 {
                    Err(())
                } else {
                    Ok(vec![(fields[0].clone(), raw_nat(b - 1))])
                })
            }
            (
                Head::Constructor {
                    name: left,
                    fields: a,
                },
                Head::Constructor {
                    name: right,
                    fields: b,
                },
            ) => Some(if left == right {
                Ok(a.into_iter().zip(b).collect())
            } else {
                Err(())
            }),
            _ => None,
        }
    }

    /// Whether two patterns can match one value, their variables independent.
    fn patterns_unify(&self, left: &Expr, right: &Expr, variables: &[FVarId]) -> bool {
        let mut pending = vec![(left.clone(), right.clone())];
        while let Some((a, b)) = pending.pop() {
            if as_fvar(&a).is_some_and(|id| variables.contains(id))
                || as_fvar(&b).is_some_and(|id| variables.contains(id))
            {
                continue;
            }
            match self.injection(&a, &b) {
                Some(Ok(fields)) => pending.extend(fields),
                Some(Err(())) => return false,
                None => {
                    if a != b {
                        // Not a pattern shape this compares: assume it may match.
                        continue;
                    }
                }
            }
        }
        true
    }

    /// Whether `a` and `b` are definitionally equal: the kernel, closed over the context.
    fn closed_defeq(
        &mut self,
        a: &Expr,
        b: &Expr,
        level_params: &[Name],
    ) -> Result<bool, NatDefinitionElabError> {
        if a == b {
            return Ok(true);
        }
        let a = self.close_context(a.clone(), false)?;
        let b = self.close_context(b.clone(), false)?;
        Ok(matches!(
            fln_kernel::check_def_eq(&self.txn.env, level_params, &a, &b, self.kernel),
            Outcome::Complete(Verdict::Accepted { .. })
        ))
    }

    /// `expr` closed over the whole local context, as lambdas (or `∀`s).
    fn close_context(
        &mut self,
        mut expr: Expr,
        forall: bool,
    ) -> Result<Expr, NatDefinitionElabError> {
        for local in self.txn.lctx.decls().to_vec().into_iter().rev() {
            self.tick()?;
            let body = expr
                .abstract_fvar(&local.id, 0)
                .map_err(|_| scope_error())?;
            expr = match &local.value {
                Some(value) => {
                    Expr::let_e(local.user_name, local.type_, value.clone(), body, false)
                }
                None if forall => {
                    Expr::forall_e(local.user_name, local.type_, body, local.binder_info)
                }
                None => Expr::lam(local.user_name, local.type_, body, local.binder_info),
            };
        }
        Ok(expr)
    }

    /// `simpH?` (vendored Lean/Meta/Match/SimpH.lean:126-160): `∀ xs, eqs → False`, simplified;
    /// `None` when it holds (two different constructors).
    fn simp_hypothesis(
        &mut self,
        mut variables: Vec<FVarId>,
        equations: Vec<(Expr, Expr)>,
        level_params: &[Name],
    ) -> Result<Option<Expr>, NatDefinitionElabError> {
        let mut pending: std::collections::VecDeque<(Expr, Expr)> = equations.into();
        let mut kept: Vec<(Expr, Expr)> = Vec::new();
        while let Some((lhs, rhs)) = pending.pop_front() {
            self.tick()?;
            if self.closed_defeq(&lhs, &rhs, level_params)? {
                continue;
            }
            if let Some(id) = as_fvar(&rhs).cloned()
                && variables.contains(&id)
                && !mentions(&lhs, &id)
            {
                let substitute = |cx: &mut Self,
                                  (a, b): (Expr, Expr)|
                 -> Result<(Expr, Expr), NatDefinitionElabError> {
                    cx.tick()?;
                    Ok((replace(&a, &id, &lhs)?, replace(&b, &id, &lhs)?))
                };
                pending = pending
                    .into_iter()
                    .map(|eq| substitute(self, eq))
                    .collect::<Result<_, _>>()?;
                kept = kept
                    .into_iter()
                    .map(|eq| substitute(self, eq))
                    .collect::<Result<_, _>>()?;
                variables.retain(|variable| variable != &id);
                continue;
            }
            match self.injection(&lhs, &rhs) {
                Some(Err(())) => return Ok(None),
                Some(Ok(fields)) => {
                    for field in fields.into_iter().rev() {
                        pending.push_front(field);
                    }
                }
                None => kept.push((lhs, rhs)),
            }
        }
        let mut body = Expr::const_(Name::from_components(["False"]), Vec::new());
        for (lhs, rhs) in kept.into_iter().rev() {
            let equality = self.equation_type(&lhs, &rhs)?;
            body = Expr::forall_e(Name::anonymous(), equality, body, BinderInfo::Default);
        }
        for id in variables.iter().rev() {
            if !mentions(&body, id) {
                continue;
            }
            let local = self.txn.lctx.find(id).cloned().ok_or_else(scope_error)?;
            body = Expr::forall_e(
                local.user_name,
                local.type_,
                body.abstract_fvar(id, 0).map_err(|_| scope_error())?,
                BinderInfo::Default,
            );
        }
        Ok(Some(body))
    }

    /// `@Eq α a b`, `α` the type of `a`.
    fn equation_type(&mut self, a: &Expr, b: &Expr) -> Result<Expr, NatDefinitionElabError> {
        let Some(type_) = self.known_type(a)? else {
            return Err(failure(SourceInferenceError::ExpectedType));
        };
        let level = self.sort_level_of(&type_)?;
        Ok(app_n(
            Expr::const_(Name::from_components(["Eq"]), vec![level]),
            [type_, a.clone(), b.clone()],
        ))
    }

    fn sort_level_of(&mut self, type_: &Expr) -> Result<Level, NatDefinitionElabError> {
        let Some(sort) = self.known_type(type_)? else {
            return Err(failure(SourceInferenceError::ExpectedType));
        };
        let sort = self.whnf(&sort)?;
        match sort.node() {
            ExprNode::Sort { level } => Ok(level.clone()),
            _ => Err(failure(SourceInferenceError::ExpectedType)),
        }
    }

    /// The equation theorems of `definition`, from `record`, in order.
    pub(super) fn matched_equations(
        &mut self,
        definition: &DefinitionVal,
        record: &Record,
    ) -> Result<Vec<Declaration>, NatDefinitionElabError> {
        let refuse = |reason| {
            failure(SourceInferenceError::EquationTheorem(Box::new(
                NotGenerated {
                    name: equation_name(&definition.base.name, 1),
                    declaration: definition.base.name.clone(),
                    reason,
                },
            )))
        };
        let levels: Vec<Level> = definition
            .base
            .level_params
            .iter()
            .cloned()
            .map(Level::param)
            .collect();
        let level_params = definition.base.level_params.clone();
        // The definition's parameters, as `lambdaTelescope` opens its value. The generated
        // binders of equations are the pin's `x✝`.
        let saved = self.txn.lctx.clone();
        let mut value = definition.value.clone();
        let mut type_ = definition.base.type_.clone();
        let mut parameters = Vec::new();
        let mut used: Vec<Name> = Vec::new();
        while parameters.len() < record.arity {
            let ExprNode::Lam {
                binder_name,
                binder_type,
                body,
                binder_info,
            } = value.node()
            else {
                return Err(refuse(Unsupported::CompiledMatch));
            };
            let name = if matches!(binder_name.leaf_view(), LeafView::Num(_))
                || binder_name.to_display_string().starts_with("_fln")
                || binder_name.is_anonymous()
            {
                // The pin's generated binders: `inst✝` for an anonymous instance, else `x✝`.
                let stem = if *binder_info == BinderInfo::InstImplicit {
                    "inst"
                } else {
                    "x"
                };
                self.fresh_inaccessible(&Name::from_components([stem]))?
            } else {
                binder_name.clone()
            };
            let id = FVarId(self.fresh_name()?);
            self.txn.lctx.add_param(
                id.clone(),
                name.clone(),
                cleanup_annotations(binder_type.clone()),
                *binder_info,
            );
            used.push(name);
            let local = Expr::fvar(id.clone());
            if !matches!(type_.node(), ExprNode::ForallE { .. }) {
                type_ = self.whnf(&type_)?;
            }
            let ExprNode::ForallE { body: codomain, .. } = type_.node() else {
                return Err(refuse(Unsupported::CompiledMatch));
            };
            type_ = self.substitute(codomain, &local)?;
            value = self.substitute(body, &local)?;
            parameters.push(id);
        }
        // The generalized discriminants (`generalizeTargetsEq`, then `introN`).
        for name in &record.motive_names {
            unused_name(&mut used, name);
        }
        let base = self.txn.lctx.len();
        let mut declarations = Vec::new();
        for (index, alternative) in record.alternatives.iter().enumerate() {
            self.tick()?;
            self.txn.lctx.truncate(base);
            let mut used = used.clone();
            // Earlier alternatives' patterns over their own fresh fields, for the hypotheses.
            let (fields, patterns, rhs) =
                self.open_alternative(alternative, &parameters, record, Some(&mut used))?;
            let mut hypotheses = Vec::new();
            for earlier in 0..index {
                let (variables, others, _) = self.open_alternative(
                    &record.alternatives[earlier],
                    &parameters,
                    record,
                    None,
                )?;
                if !self.patterns_unify_columns(&patterns, &others, &fields, &variables) {
                    continue;
                }
                let equations: Vec<(Expr, Expr)> = patterns
                    .iter()
                    .cloned()
                    .zip(others.iter().cloned())
                    .collect();
                if let Some(hypothesis) =
                    self.simp_hypothesis(variables, equations, &level_params)?
                {
                    hypotheses.push(hypothesis);
                }
            }
            let mut hypothesis_locals = Vec::new();
            for hypothesis in hypotheses {
                let name = unused_name(&mut used, &Name::from_components(["x"]));
                let id = FVarId(self.fresh_name()?);
                self.txn
                    .lctx
                    .add_param(id.clone(), name, hypothesis, BinderInfo::Default);
                hypothesis_locals.push(id);
            }
            // `Cases.unifyEqs?` on the discriminants' equations.
            let mut substitution: Vec<(FVarId, Expr)> = Vec::new();
            let apply = |cx: &mut Self, expr: &Expr, substitution: &[(FVarId, Expr)]| {
                let mut expr = expr.clone();
                for (id, value) in substitution {
                    cx.tick()?;
                    expr = replace(&expr, id, value)?;
                }
                Ok::<Expr, NatDefinitionElabError>(expr)
            };
            let mut equations: std::collections::VecDeque<(Expr, Expr)> = record
                .discriminants
                .iter()
                .zip(&patterns)
                .map(|(position, pattern)| {
                    (Expr::fvar(parameters[*position].clone()), pattern.clone())
                })
                .collect();
            while let Some((lhs, rhs)) = equations.pop_front() {
                self.tick()?;
                let lhs = apply(self, &lhs, &substitution)?;
                let rhs = apply(self, &rhs, &substitution)?;
                match (as_fvar(&lhs).cloned(), as_fvar(&rhs).cloned()) {
                    (Some(a), Some(b)) => {
                        if a == b {
                            continue;
                        }
                        let index = |id: &FVarId| self.txn.lctx.find(id).map(|local| local.index);
                        let (older, newer) = if index(&a) < index(&b) {
                            (a, b)
                        } else {
                            (b, a)
                        };
                        substitution.push((newer, Expr::fvar(older)));
                    }
                    (Some(a), None) if !mentions(&rhs, &a) => substitution.push((a, rhs)),
                    (None, Some(b)) if !mentions(&lhs, &b) => substitution.push((b, lhs)),
                    _ => match self.injection(&lhs, &rhs) {
                        Some(Ok(fields)) => {
                            for field in fields.into_iter().rev() {
                                equations.push_front(field);
                            }
                        }
                        _ if self.closed_defeq(&lhs, &rhs, &level_params)? => {}
                        _ => return Err(refuse(Unsupported::CompiledMatch)),
                    },
                }
            }
            let arguments: Vec<Expr> = parameters
                .iter()
                .map(|id| apply(self, &Expr::fvar(id.clone()), &substitution))
                .collect::<Result<_, _>>()?;
            let lhs = app_n(
                Expr::const_(definition.base.name.clone(), levels.clone()),
                arguments,
            );
            let mut rhs = apply(self, &rhs, &substitution)?;
            loop {
                rhs = match rhs.node() {
                    ExprNode::LetE { value, body, .. } => self.substitute(body, value)?,
                    ExprNode::MData { expr, .. } => expr.clone(),
                    _ => break,
                };
            }
            if super::compiled_match(&self.txn.env, &rhs) {
                self.txn.lctx = saved;
                return Err(refuse(Unsupported::MatchInStatement));
            }
            for id in &hypothesis_locals {
                let local = self.txn.lctx.find(id).cloned().ok_or_else(scope_error)?;
                let type_ = apply(self, &local.type_, &substitution)?;
                self.retype_local(id, type_);
            }
            // `saveEqn`: the locals the equation mentions, with their types' locals, in context
            // order, then the hypotheses that mention one of them.
            let statement = self.equation_type(&lhs, &rhs)?;
            let mut selected: Vec<FVarId> = Vec::new();
            let mut pending = vec![statement.clone()];
            while let Some(expr) = pending.pop() {
                self.tick()?;
                for local in self.txn.lctx.decls().to_vec() {
                    if !selected.contains(&local.id)
                        && !hypothesis_locals.contains(&local.id)
                        && mentions(&expr, &local.id)
                    {
                        selected.push(local.id.clone());
                        pending.push(local.type_.clone());
                    }
                }
            }
            let mut changed = true;
            while changed {
                changed = false;
                for id in &hypothesis_locals {
                    if selected.contains(id) {
                        continue;
                    }
                    let local = self.txn.lctx.find(id).cloned().ok_or_else(scope_error)?;
                    if selected
                        .iter()
                        .any(|selected| mentions(&local.type_, selected))
                    {
                        selected.push(id.clone());
                        changed = true;
                    }
                }
            }
            let mut order: Vec<FVarId> = self
                .txn
                .lctx
                .decls()
                .iter()
                .filter(|local| selected.contains(&local.id))
                .map(|local| local.id.clone())
                .collect();
            order.dedup();
            // The proof, in a context of exactly these locals.
            let context = self.txn.lctx.clone();
            let mut lctx = LocalContext::new();
            for id in &order {
                let local = context.find(id).cloned().ok_or_else(scope_error)?;
                lctx.add_param(local.id, local.user_name, local.type_, local.binder_info);
            }
            self.txn.lctx = lctx;
            let hypotheses_in_scope: Vec<FVarId> = order
                .iter()
                .filter(|id| hypothesis_locals.contains(id))
                .cloned()
                .collect();
            let proof = self.prove(&lhs, &rhs, &hypotheses_in_scope, &level_params, 0)?;
            let Some(proof) = proof else {
                self.txn.lctx = saved;
                return Err(refuse(Unsupported::Unproved));
            };
            let type_ = self.close_context(statement, true)?;
            let value = self.close_context(proof, false)?;
            self.txn.lctx = context;
            if type_.has_fvar() || value.has_fvar() || type_.has_loose_bvars() {
                self.txn.lctx = saved;
                return Err(scope_error());
            }
            let name = equation_name(&definition.base.name, index + 1);
            declarations.push(Declaration::Thm(TheoremVal {
                base: ConstantVal {
                    name: name.clone(),
                    level_params: level_params.clone(),
                    type_,
                },
                value,
                all: vec![name],
            }));
        }
        self.txn.lctx = saved;
        Ok(declarations)
    }

    fn retype_local(&mut self, id: &FVarId, type_: Expr) {
        let decls = self.txn.lctx.decls().to_vec();
        let mut lctx = LocalContext::new();
        for mut local in decls {
            if &local.id == id {
                local.type_ = type_.clone();
            }
            match local.value {
                Some(value) => {
                    lctx.add_let(local.id, local.user_name, local.type_, value);
                }
                None => {
                    lctx.add_param(local.id, local.user_name, local.type_, local.binder_info);
                }
            }
        }
        self.txn.lctx = lctx;
    }

    fn patterns_unify_columns(
        &self,
        patterns: &[Expr],
        others: &[Expr],
        fields: &[FVarId],
        variables: &[FVarId],
    ) -> bool {
        let all: Vec<FVarId> = fields.iter().chain(variables).cloned().collect();
        patterns
            .iter()
            .zip(others)
            .all(|(a, b)| self.patterns_unify(a, b, &all))
    }

    /// An alternative's fields as locals, named by `used` when it is given (and otherwise by
    /// the matcher), and its patterns and right-hand side over them.
    fn open_alternative(
        &mut self,
        alternative: &Expr,
        parameters: &[FVarId],
        record: &Record,
        mut used: Option<&mut Vec<Name>>,
    ) -> Result<(Vec<FVarId>, Vec<Expr>, Expr), NatDefinitionElabError> {
        let mut body = alternative.clone();
        for id in parameters {
            let ExprNode::Lam { body: inner, .. } = body.node() else {
                return Err(scope_error());
            };
            body = self.substitute(inner, &Expr::fvar(id.clone()))?;
        }
        let mut fields = Vec::new();
        while let ExprNode::Lam {
            binder_name,
            binder_type,
            body: inner,
            ..
        } = body.node()
        {
            let name = match used.as_deref_mut() {
                Some(used) => unused_name(used, binder_name),
                None => binder_name.clone(),
            };
            let id = FVarId(self.fresh_name()?);
            self.txn
                .lctx
                .add_param(id.clone(), name, binder_type.clone(), BinderInfo::Default);
            body = self.substitute(inner, &Expr::fvar(id.clone()))?;
            fields.push(id);
        }
        let parts = journal::unpack(&body).ok_or_else(scope_error)?;
        let columns = record.discriminants.len();
        if parts.len() != columns + 1 {
            return Err(scope_error());
        }
        Ok((fields, parts[..columns].to_vec(), parts[columns].clone()))
    }

    /// A proof of `lhs = rhs` in the current context, `None` when it is not found.
    fn prove(
        &mut self,
        lhs: &Expr,
        rhs: &Expr,
        hypotheses: &[FVarId],
        level_params: &[Name],
        depth: usize,
    ) -> Result<Option<Expr>, NatDefinitionElabError> {
        self.tick()?;
        if self.closed_defeq(lhs, rhs, level_params)? {
            let Some(type_) = self.known_type(lhs)? else {
                return Ok(None);
            };
            let level = self.sort_level_of(&type_)?;
            return Ok(Some(app_n(
                Expr::const_(Name::from_components(["Eq", "refl"]), vec![level]),
                [type_, lhs.clone()],
            )));
        }
        let goal = self.equation_type(lhs, rhs)?;
        if let Some(contradiction) = self.refute(hypotheses, level_params)? {
            return Ok(Some(app_n(
                Expr::const_(
                    Name::from_components(["False", "elim"]),
                    vec![Level::zero()],
                ),
                [goal, contradiction],
            )));
        }
        if depth >= MAX_DEPTH {
            return Ok(None);
        }
        let unfolded = self.unfold_head(lhs)?;
        let stuck = self.stuck(&unfolded)?;
        match stuck {
            Some(Stuck::Variable(id)) => {
                self.split_variable(&id, lhs, rhs, hypotheses, level_params, depth)
            }
            Some(Stuck::Comparison(comparison)) => {
                self.split_comparison(&comparison, &unfolded, rhs, hypotheses, level_params, depth)
            }
            None => Ok(None),
        }
    }

    /// `term` in weak head normal form, its head definition unfolded once by delta even where
    /// smart unfolding keeps a stuck recursive application folded.
    fn unfold_head(&mut self, term: &Expr) -> Result<Expr, NatDefinitionElabError> {
        let (head, args) = spine(term);
        if let ExprNode::Const { name, levels } = head.node()
            && let Some(ConstantInfo::Defn(definition)) = self.txn.env.find(name).cloned()
            && definition.base.level_params.len() == levels.len()
        {
            let value =
                self.instantiate_params(&definition.value, &definition.base.level_params, levels)?;
            let mut value = value;
            let mut rest = args.as_slice();
            while let (ExprNode::Lam { body, .. }, Some((first, tail))) =
                (value.node(), rest.split_first())
            {
                value = self.substitute(body, first)?;
                rest = tail;
            }
            return self.whnf(&app_n(value, rest.iter().cloned()));
        }
        self.whnf(term)
    }

    /// A hypothesis `∀ ys, a = b → … → False` whose equations hold here by reflexivity, applied:
    /// a proof of `False`.
    fn refute(
        &mut self,
        hypotheses: &[FVarId],
        level_params: &[Name],
    ) -> Result<Option<Expr>, NatDefinitionElabError> {
        for id in hypotheses {
            self.tick()?;
            let Some(local) = self.txn.lctx.find(id).cloned() else {
                continue;
            };
            // Open the `∀ ys` as holes to be matched, then the equations.
            let mut type_ = local.type_.clone();
            let mut holes: Vec<(FVarId, Option<Expr>)> = Vec::new();
            let mut equations = Vec::new();
            let saved = self.txn.lctx.len();
            while let ExprNode::ForallE {
                binder_name,
                binder_type,
                body,
                ..
            } = type_.node()
            {
                if body.has_loose_bvar(0) {
                    let hole = FVarId(self.fresh_name()?);
                    self.txn.lctx.add_param(
                        hole.clone(),
                        binder_name.clone(),
                        binder_type.clone(),
                        BinderInfo::Default,
                    );
                    holes.push((hole.clone(), None));
                    type_ = self.substitute(body, &Expr::fvar(hole))?;
                } else {
                    equations.push(binder_type.clone());
                    type_ = self.substitute(body, &Expr::const_(Name::anonymous(), Vec::new()))?;
                }
            }
            let mut matched = true;
            for equation in &equations {
                let (head, args) = spine(equation);
                let (ExprNode::Const { name, .. }, [_, a, b]) = (head.node(), args.as_slice())
                else {
                    matched = false;
                    break;
                };
                if *name != Name::from_components(["Eq"]) {
                    matched = false;
                    break;
                }
                if !self.match_pattern(b, a, &mut holes)? {
                    matched = false;
                    break;
                }
            }
            let assignments: Option<Vec<Expr>> = holes.iter().map(|(_, v)| v.clone()).collect();
            let hole_ids: Vec<FVarId> = holes.iter().map(|(id, _)| id.clone()).collect();
            self.txn.lctx.truncate(saved);
            let (true, Some(assignments)) = (matched, assignments) else {
                continue;
            };
            // Every equation, instantiated, must hold by reflexivity.
            let mut proofs = Vec::new();
            let mut ok = true;
            for equation in &equations {
                let mut equation = equation.clone();
                for (hole, value) in hole_ids.iter().zip(&assignments) {
                    equation = replace(&equation, hole, value)?;
                }
                let (_, args) = spine(&equation);
                let [type_, a, b] = args.as_slice() else {
                    ok = false;
                    break;
                };
                if !self.closed_defeq(a, b, level_params)? {
                    ok = false;
                    break;
                }
                let level = self.sort_level_of(type_)?;
                proofs.push(app_n(
                    Expr::const_(Name::from_components(["Eq", "refl"]), vec![level]),
                    [type_.clone(), a.clone()],
                ));
            }
            if ok {
                return Ok(Some(app_n(
                    Expr::fvar(id.clone()),
                    assignments.into_iter().chain(proofs),
                )));
            }
        }
        Ok(None)
    }

    /// First-order matching of `pattern` (over `holes`) against `term`.
    fn match_pattern(
        &mut self,
        pattern: &Expr,
        term: &Expr,
        holes: &mut [(FVarId, Option<Expr>)],
    ) -> Result<bool, NatDefinitionElabError> {
        self.tick()?;
        if let Some(id) = as_fvar(pattern)
            && let Some(slot) = holes.iter_mut().find(|(hole, _)| hole == id)
        {
            return Ok(match &slot.1 {
                Some(value) => value == term,
                None => {
                    slot.1 = Some(term.clone());
                    true
                }
            });
        }
        match self.injection(pattern, term) {
            Some(Ok(fields)) => {
                for (a, b) in fields {
                    if !self.match_pattern(&a, &b, holes)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            Some(Err(())) => Ok(false),
            None => Ok(pattern == term),
        }
    }

    /// What `term` (in weak head normal form) is stuck on: a local a recursor eliminates, or a
    /// `Nat.beq` comparison with a literal.
    fn stuck(&mut self, term: &Expr) -> Result<Option<Stuck>, NatDefinitionElabError> {
        let mut current = term.clone();
        for _ in 0..MAX_DEPTH {
            self.tick()?;
            let (head, args) = spine(&current);
            if let ExprNode::Proj { expr, .. } = head.node() {
                current = self.whnf(expr)?;
                continue;
            }
            let ExprNode::Const { name, .. } = head.node() else {
                return Ok(None);
            };
            if let Some(comparison) = self.literal_comparison(&current)? {
                return Ok(Some(self.comparison_or_variable(comparison)?));
            }
            let Some(ConstantInfo::Rec(recursor)) = self.txn.env.find(name).cloned() else {
                return Ok(None);
            };
            let major = (recursor.num_params
                + recursor.num_motives
                + recursor.num_minors
                + recursor.num_indices) as usize;
            let Some(major) = args.get(major) else {
                return Ok(None);
            };
            if let Some(comparison) = self.literal_comparison(major)? {
                return Ok(Some(self.comparison_or_variable(comparison)?));
            }
            let major = self.whnf(major)?;
            if let Some(id) = as_fvar(&major) {
                return Ok(Some(Stuck::Variable(id.clone())));
            }
            current = major;
        }
        Ok(None)
    }

    /// A comparison split by `Bool` cases when `Nat.eq_of_beq_eq_true` is declared, and by cases
    /// on its local otherwise.
    fn comparison_or_variable(
        &mut self,
        comparison: Expr,
    ) -> Result<Stuck, NatDefinitionElabError> {
        if self
            .txn
            .env
            .contains(&Name::from_components(["Nat", "eq_of_beq_eq_true"]))
        {
            return Ok(Stuck::Comparison(comparison));
        }
        let (_, args) = spine(&comparison);
        let left = self.whnf(&args[0])?;
        match as_fvar(&left) {
            Some(id) => Ok(Stuck::Variable(id.clone())),
            None => Err(scope_error()),
        }
    }

    /// `term` as `Nat.beq x n`, `x` a local and `n` a literal, when it is one.
    fn literal_comparison(&mut self, term: &Expr) -> Result<Option<Expr>, NatDefinitionElabError> {
        let (head, args) = spine(term);
        let ExprNode::Const { name, .. } = head.node() else {
            return Ok(None);
        };
        if *name != Name::from_components(["Nat", "beq"]) {
            return Ok(None);
        }
        let [left, right] = args.as_slice() else {
            return Ok(None);
        };
        let left = self.whnf(left)?;
        let right = self.whnf(right)?;
        Ok(match (as_fvar(&left), nat_literal(&right)) {
            (Some(_), Some(_)) => Some(term.clone()),
            _ => None,
        })
    }

    /// Cases on the local `id` by its type's recursor: each case proved with `id` replaced by
    /// the constructor applied to its fields, the hypotheses that mention it generalized.
    fn split_variable(
        &mut self,
        id: &FVarId,
        lhs: &Expr,
        rhs: &Expr,
        hypotheses: &[FVarId],
        level_params: &[Name],
        depth: usize,
    ) -> Result<Option<Expr>, NatDefinitionElabError> {
        let Some(local) = self.txn.lctx.find(id).cloned() else {
            return Ok(None);
        };
        // Only a variable nothing else's type depends on, except the hypotheses.
        let dependents: Vec<FVarId> = self
            .txn
            .lctx
            .decls()
            .iter()
            .filter(|other| other.index > local.index && mentions(&other.type_, id))
            .map(|other| other.id.clone())
            .collect();
        if dependents.iter().any(|other| !hypotheses.contains(other)) {
            return Ok(None);
        }
        let type_ = self.whnf(&local.type_)?;
        let (head, params) = spine(&type_);
        let ExprNode::Const {
            name: inductive_name,
            levels,
        } = head.node()
        else {
            return Ok(None);
        };
        let Some(ConstantInfo::Induct(inductive)) = self.txn.env.find(inductive_name).cloned()
        else {
            return Ok(None);
        };
        if inductive.num_indices != 0 || params.len() != inductive.num_params as usize {
            return Ok(None);
        }
        let recursor_name = Name::str(inductive_name.clone(), "rec");
        let Some(ConstantInfo::Rec(recursor)) = self.txn.env.find(&recursor_name).cloned() else {
            return Ok(None);
        };
        if recursor.num_motives != 1 {
            return Ok(None);
        }
        // The motive: `fun y => ∀ hyps[y], lhs[y] = rhs[y]`.
        let generalized: Vec<LocalDecl> = dependents
            .iter()
            .map(|other| self.txn.lctx.find(other).cloned().ok_or_else(scope_error))
            .collect::<Result<_, _>>()?;
        let mut goal = self.equation_type(lhs, rhs)?;
        for hypothesis in generalized.iter().rev() {
            goal = Expr::forall_e(
                hypothesis.user_name.clone(),
                hypothesis.type_.clone(),
                goal.abstract_fvar(&hypothesis.id, 0)
                    .map_err(|_| scope_error())?,
                BinderInfo::Default,
            );
        }
        let motive = Expr::lam(
            local.user_name.clone(),
            local.type_.clone(),
            goal.abstract_fvar(id, 0).map_err(|_| scope_error())?,
            BinderInfo::Default,
        );
        // `T.rec.{0, us}`: the motive's universe first, when the recursor has one.
        let mut recursor_levels = levels.clone();
        if recursor.base.level_params.len() == levels.len() + 1 {
            recursor_levels.insert(0, Level::zero());
        } else if recursor.base.level_params.len() != levels.len() {
            return Ok(None);
        }
        let mut recursor_type = self.instantiate_params(
            &recursor.base.type_,
            &recursor.base.level_params,
            &recursor_levels,
        )?;
        let mut term = Expr::const_(recursor_name, recursor_levels);
        for argument in params.iter().chain(std::iter::once(&motive)) {
            let ExprNode::ForallE { body, .. } = recursor_type.node() else {
                return Ok(None);
            };
            recursor_type = self.substitute(body, argument)?;
            term = Expr::app(term, argument.clone());
        }
        for rule in &recursor.rules {
            let ExprNode::ForallE {
                binder_type: minor_type,
                body,
                ..
            } = recursor_type.node()
            else {
                return Ok(None);
            };
            let (minor_type, body) = (minor_type.clone(), body.clone());
            let Some(minor) = self.minor_premise(
                &minor_type,
                rule.nfields as usize,
                id,
                &generalized,
                lhs,
                rhs,
                hypotheses,
                level_params,
                depth,
            )?
            else {
                return Ok(None);
            };
            recursor_type = self.substitute(&body, &minor)?;
            term = Expr::app(term, minor);
        }
        term = Expr::app(term, Expr::fvar(id.clone()));
        Ok(Some(app_n(
            term,
            generalized
                .iter()
                .map(|hypothesis| Expr::fvar(hypothesis.id.clone())),
        )))
    }

    /// One recursor minor premise: `fun fields ihs hyps => proof`.
    #[allow(clippy::too_many_arguments)]
    fn minor_premise(
        &mut self,
        minor_type: &Expr,
        fields: usize,
        id: &FVarId,
        generalized: &[LocalDecl],
        lhs: &Expr,
        rhs: &Expr,
        hypotheses: &[FVarId],
        level_params: &[Name],
        depth: usize,
    ) -> Result<Option<Expr>, NatDefinitionElabError> {
        let saved = self.txn.lctx.clone();
        // The generalized hypotheses are replaced in the case by their instances.
        let mut lctx = LocalContext::new();
        for local in saved.decls() {
            if generalized
                .iter()
                .any(|hypothesis| hypothesis.id == local.id)
            {
                continue;
            }
            match &local.value {
                Some(value) => {
                    lctx.add_let(
                        local.id.clone(),
                        local.user_name.clone(),
                        local.type_.clone(),
                        value.clone(),
                    );
                }
                None => {
                    lctx.add_param(
                        local.id.clone(),
                        local.user_name.clone(),
                        local.type_.clone(),
                        local.binder_info,
                    );
                }
            }
        }
        self.txn.lctx = lctx;
        let mut type_ = minor_type.clone();
        let mut binders: Vec<LocalDecl> = Vec::new();
        let mut field_values = Vec::new();
        let mut inductive_hypotheses = Vec::new();
        while let ExprNode::ForallE {
            binder_name,
            binder_type,
            body,
            binder_info,
        } = type_.node()
        {
            let field = field_values.len() < fields;
            let name = if field {
                binder_name.clone()
            } else {
                Name::from_components(["ih"])
            };
            let local = FVarId(self.fresh_name()?);
            self.txn
                .lctx
                .add_param(local.clone(), name, binder_type.clone(), *binder_info);
            binders.push(
                self.txn
                    .lctx
                    .find(&local)
                    .cloned()
                    .ok_or_else(scope_error)?,
            );
            if field {
                field_values.push(Expr::fvar(local.clone()));
            } else {
                inductive_hypotheses.push(local.clone());
            }
            type_ = self.substitute(body, &Expr::fvar(local))?;
        }
        // The proof uses no induction hypothesis: out of the context, nothing depends on them.
        let kept: Vec<LocalDecl> = self
            .txn
            .lctx
            .decls()
            .iter()
            .filter(|local| !inductive_hypotheses.contains(&local.id))
            .cloned()
            .collect();
        let mut lctx = LocalContext::new();
        for local in kept {
            lctx.add_param(local.id, local.user_name, local.type_, local.binder_info);
        }
        self.txn.lctx = lctx;
        // `type_` is `motive (C params fields)`: beta it to the goal at the constructor.
        let (_, args) = spine(&type_);
        let Some(value) = args.last().cloned() else {
            self.txn.lctx = saved;
            return Ok(None);
        };
        let lhs = replace(lhs, id, &value)?;
        let rhs = replace(rhs, id, &value)?;
        let mut new_hypotheses: Vec<FVarId> = hypotheses
            .iter()
            .filter(|other| !generalized.iter().any(|g| &g.id == *other))
            .cloned()
            .collect();
        for hypothesis in generalized {
            let local = FVarId(self.fresh_name()?);
            let type_ = replace(&hypothesis.type_, id, &value)?;
            self.txn.lctx.add_param(
                local.clone(),
                hypothesis.user_name.clone(),
                type_,
                BinderInfo::Default,
            );
            binders.push(
                self.txn
                    .lctx
                    .find(&local)
                    .cloned()
                    .ok_or_else(scope_error)?,
            );
            new_hypotheses.push(local);
        }
        let proof = self.prove(&lhs, &rhs, &new_hypotheses, level_params, depth + 1)?;
        let result = match proof {
            Some(mut proof) => {
                for local in binders.iter().rev() {
                    proof = Expr::lam(
                        local.user_name.clone(),
                        local.type_.clone(),
                        proof
                            .abstract_fvar(&local.id, 0)
                            .map_err(|_| scope_error())?,
                        local.binder_info,
                    );
                }
                Some(proof)
            }
            None => None,
        };
        self.txn.lctx = saved;
        Ok(result)
    }

    /// `Bool` cases on a literal comparison `Nat.beq x n` the unfolded left side is stuck on:
    /// `true` gives `x = n` (`Nat.eq_of_beq_eq_true`), which a hypothesis refutes or which is
    /// substituted; `false` reduces the comparison.
    fn split_comparison(
        &mut self,
        comparison: &Expr,
        unfolded: &Expr,
        rhs: &Expr,
        hypotheses: &[FVarId],
        level_params: &[Name],
        depth: usize,
    ) -> Result<Option<Expr>, NatDefinitionElabError> {
        let (_, args) = spine(comparison);
        let [variable, literal] = args.as_slice() else {
            return Ok(None);
        };
        let variable = self.whnf(variable)?;
        let literal = self.whnf(literal)?;
        let (variable, literal) = (&variable, &literal);
        let Some(id) = as_fvar(variable).cloned() else {
            return Ok(None);
        };
        let bool_type = Expr::const_(Name::from_components(["Bool"]), Vec::new());
        let bool_value =
            |text: &str| Expr::const_(Name::from_components(["Bool", text]), Vec::new());
        // Generalize the comparison in the unfolded goal.
        let hole = FVarId(self.fresh_name()?);
        let saved = self.txn.lctx.clone();
        self.txn.lctx.add_param(
            hole.clone(),
            Name::from_components(["b"]),
            bool_type.clone(),
            BinderInfo::Default,
        );
        let abstracted = abstract_term(unfolded, comparison, &Expr::fvar(hole.clone()));
        let goal = self.equation_type(&abstracted, rhs)?;
        let one = Level::zero().succ().map_err(|_| scope_error())?;
        let equation = app_n(
            Expr::const_(Name::from_components(["Eq"]), vec![one.clone()]),
            [
                bool_type.clone(),
                comparison.clone(),
                Expr::fvar(hole.clone()),
            ],
        );
        let motive_body = Expr::forall_e(
            Name::from_components(["h"]),
            equation,
            goal,
            BinderInfo::Default,
        );
        let motive = Expr::lam(
            Name::from_components(["b"]),
            bool_type.clone(),
            motive_body
                .abstract_fvar(&hole, 0)
                .map_err(|_| scope_error())?,
            BinderInfo::Default,
        );
        self.txn.lctx = saved.clone();
        let mut cases = Vec::new();
        for value in ["false", "true"] {
            let constant = bool_value(value);
            let h = FVarId(self.fresh_name()?);
            let equation = app_n(
                Expr::const_(Name::from_components(["Eq"]), vec![one.clone()]),
                [bool_type.clone(), comparison.clone(), constant.clone()],
            );
            self.txn.lctx.add_param(
                h.clone(),
                Name::from_components(["h"]),
                equation,
                BinderInfo::Default,
            );
            let lhs = abstract_term(unfolded, comparison, &constant);
            let proof = if value == "true" {
                // `x = n`, then the hypotheses with `x` replaced by `n`.
                let equal = app_n(
                    Expr::const_(
                        Name::from_components(["Nat", "eq_of_beq_eq_true"]),
                        Vec::new(),
                    ),
                    [variable.clone(), literal.clone(), Expr::fvar(h.clone())],
                );
                self.prove_with_equation(
                    &id,
                    literal,
                    &equal,
                    &lhs,
                    rhs,
                    hypotheses,
                    level_params,
                    depth,
                )?
            } else {
                self.prove(&lhs, rhs, hypotheses, level_params, depth + 1)?
            };
            let Some(proof) = proof else {
                self.txn.lctx = saved;
                return Ok(None);
            };
            cases.push(Expr::lam(
                Name::from_components(["h"]),
                self.txn
                    .lctx
                    .find(&h)
                    .map(|l| l.type_.clone())
                    .ok_or_else(scope_error)?,
                proof.abstract_fvar(&h, 0).map_err(|_| scope_error())?,
                BinderInfo::Default,
            ));
            self.txn.lctx = saved.clone();
        }
        let refl = app_n(
            Expr::const_(Name::from_components(["Eq", "refl"]), vec![one]),
            [bool_type, comparison.clone()],
        );
        let recursor = app_n(
            Expr::const_(Name::from_components(["Bool", "rec"]), vec![Level::zero()]),
            [
                motive,
                cases[0].clone(),
                cases[1].clone(),
                comparison.clone(),
                refl,
            ],
        );
        Ok(Some(recursor))
    }

    /// With `equal : x = n`, a hypothesis instantiated at `n` refutes the case, or the goal at
    /// `n` is proved and transported back along `equal`.
    #[allow(clippy::too_many_arguments)]
    fn prove_with_equation(
        &mut self,
        id: &FVarId,
        literal: &Expr,
        equal: &Expr,
        lhs: &Expr,
        rhs: &Expr,
        hypotheses: &[FVarId],
        level_params: &[Name],
        depth: usize,
    ) -> Result<Option<Expr>, NatDefinitionElabError> {
        // Each hypothesis at `x := n`, as `h (eq ▸ …)`: refute with the specialized types.
        let saved = self.txn.lctx.clone();
        let mut specialized = Vec::new();
        let mut definitions = Vec::new();
        for hypothesis in hypotheses {
            let Some(local) = self.txn.lctx.find(hypothesis).cloned() else {
                continue;
            };
            if !mentions(&local.type_, id) {
                specialized.push(hypothesis.clone());
                continue;
            }
            let type_ = replace(&local.type_, id, literal)?;
            // `Eq.mpr`-free: `@Eq.rec Nat x (fun y _ => T[y]) h n equal : T[n]`.
            let motive = {
                let y = FVarId(self.fresh_name()?);
                self.txn.lctx.add_param(
                    y.clone(),
                    Name::from_components(["y"]),
                    nat_type(),
                    BinderInfo::Default,
                );
                let body = replace(&local.type_, id, &Expr::fvar(y.clone()))?;
                let one = Level::zero().succ().map_err(|_| scope_error())?;
                let eq_type = app_n(
                    Expr::const_(Name::from_components(["Eq"]), vec![one]),
                    [nat_type(), Expr::fvar(id.clone()), Expr::fvar(y.clone())],
                );
                let inner = Expr::lam(
                    Name::from_components(["h"]),
                    eq_type,
                    body.lift_loose(0, 1).map_err(|_| scope_error())?,
                    BinderInfo::Default,
                );
                let motive = Expr::lam(
                    Name::from_components(["y"]),
                    nat_type(),
                    inner.abstract_fvar(&y, 0).map_err(|_| scope_error())?,
                    BinderInfo::Default,
                );
                self.txn.lctx.truncate(self.txn.lctx.len() - 1);
                motive
            };
            let value = app_n(
                Expr::const_(
                    Name::from_components(["Eq", "rec"]),
                    vec![
                        Level::zero(),
                        Level::zero().succ().map_err(|_| scope_error())?,
                    ],
                ),
                [
                    nat_type(),
                    Expr::fvar(id.clone()),
                    motive,
                    Expr::fvar(hypothesis.clone()),
                    literal.clone(),
                    equal.clone(),
                ],
            );
            let new = FVarId(self.fresh_name()?);
            self.txn
                .lctx
                .add_let(new.clone(), local.user_name.clone(), type_, value);
            definitions.push(new.clone());
            specialized.push(new);
        }
        let refuted = self.refute(&specialized, level_params)?;
        let result = match refuted {
            Some(contradiction) => {
                let goal = self.equation_type(lhs, rhs)?;
                let mut proof = app_n(
                    Expr::const_(
                        Name::from_components(["False", "elim"]),
                        vec![Level::zero()],
                    ),
                    [goal, contradiction],
                );
                for definition in definitions.iter().rev() {
                    let local = self
                        .txn
                        .lctx
                        .find(definition)
                        .cloned()
                        .ok_or_else(scope_error)?;
                    proof = Expr::let_e(
                        local.user_name,
                        local.type_,
                        local
                            .value
                            .unwrap_or_else(|| Expr::fvar(definition.clone())),
                        proof
                            .abstract_fvar(definition, 0)
                            .map_err(|_| scope_error())?,
                        false,
                    );
                }
                Some(proof)
            }
            None => {
                let _ = depth;
                None
            }
        };
        self.txn.lctx = saved;
        Ok(result)
    }
}

enum Stuck {
    Variable(FVarId),
    /// `Nat.beq x n`, `x` a local and `n` a literal.
    Comparison(Expr),
}

fn nat_type() -> Expr {
    Expr::const_(Name::from_components(["Nat"]), Vec::new())
}

/// `expr` with each occurrence of `term` (outside binders that capture its locals) replaced.
fn abstract_term(expr: &Expr, term: &Expr, replacement: &Expr) -> Expr {
    if expr == term {
        return replacement.clone();
    }
    match expr.node() {
        ExprNode::App { f, a } => Expr::app(
            abstract_term(f, term, replacement),
            abstract_term(a, term, replacement),
        ),
        ExprNode::Lam {
            binder_name,
            binder_type,
            body,
            binder_info,
        } => Expr::lam(
            binder_name.clone(),
            abstract_term(binder_type, term, replacement),
            abstract_term(body, term, replacement),
            *binder_info,
        ),
        ExprNode::ForallE {
            binder_name,
            binder_type,
            body,
            binder_info,
        } => Expr::forall_e(
            binder_name.clone(),
            abstract_term(binder_type, term, replacement),
            abstract_term(body, term, replacement),
            *binder_info,
        ),
        ExprNode::LetE {
            decl_name,
            type_,
            value,
            body,
            non_dep,
        } => Expr::let_e(
            decl_name.clone(),
            abstract_term(type_, term, replacement),
            abstract_term(value, term, replacement),
            abstract_term(body, term, replacement),
            *non_dep,
        ),
        ExprNode::MData { data, expr } => {
            Expr::mdata(data.clone(), abstract_term(expr, term, replacement))
        }
        ExprNode::Proj {
            struct_name,
            idx,
            expr,
        } => Expr::proj(
            struct_name.clone(),
            *idx,
            abstract_term(expr, term, replacement),
        ),
        _ => expr.clone(),
    }
}
