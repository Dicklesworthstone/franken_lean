//! Bounded insertion and matching paths for `symmExt`, under reducible
//! transparency. Unlike the instance index, matching never treats a goal
//! metavariable as a wildcard: the pin's `getMatch` keys it as `Other`.
use super::*;
use crate::instances::discr_tree::Key;
use fln_core::expr::NatLit;
use fln_env::constants::{ConstantInfo, DefinitionSafety, ReducibilityHints};

const MAX_KEYS: usize = 4_096;

fn unsupported() -> NatDefinitionElabError {
    NatDefinitionElabError::UnexpectedSyntax {
        expected: "a symmetry discrimination path supported by native normalization",
    }
}

impl Context {
    fn symm_spine(
        &mut self,
        expression: &Expr,
    ) -> Result<(Expr, Vec<Expr>), NatDefinitionElabError> {
        let mut head = expression;
        let mut arguments = Vec::new();
        loop {
            self.tick()?;
            match head.node() {
                ExprNode::App { f, a } => {
                    arguments.push(a.clone());
                    head = f;
                }
                ExprNode::MData { expr, .. } => head = expr,
                _ => break,
            }
        }
        arguments.reverse();
        Ok((head.clone(), arguments))
    }

    fn symm_eta(&mut self, expression: &Expr) -> Result<Option<Expr>, NatDefinitionElabError> {
        let mut body = expression;
        let mut binders = 0u32;
        while let ExprNode::Lam { body: next, .. } = body.node() {
            self.tick()?;
            binders = binders
                .checked_add(1)
                .ok_or_else(|| failure(SourceInferenceError::ResourceLimit))?;
            body = next;
        }
        if binders == 0 {
            return Ok(None);
        }
        for expected in 0..binders {
            self.tick()?;
            let ExprNode::App { f, a } = body.node() else {
                return Ok(None);
            };
            if !matches!(a.node(), ExprNode::BVar { idx } if *idx == expected) {
                return Ok(None);
            }
            body = f;
        }
        Ok((!body.has_loose_bvars()).then(|| body.clone()))
    }

    /// The root keeps its last useful key if delta would expose a lambda or
    /// metavariable. This is `reduceUntilBadKey`, not ordinary WHNF.
    fn symm_reduce_key(
        &mut self,
        expression: &Expr,
        root: bool,
    ) -> Result<Expr, NatDefinitionElabError> {
        let mut current = expression.clone();
        loop {
            self.tick()?;
            current = self.whnf_with_transparency(&current, UnificationTransparency::None, true)?;
            let (head, arguments) = self.symm_spine(&current)?;
            if let ExprNode::Const { name, levels } = head.node()
                && let Some(ConstantInfo::Defn(definition)) = self.txn.env.find(name).cloned()
            {
                if !arguments.is_empty() {
                    let env = self.txn.env.clone();
                    if let Some(projection) =
                        crate::records::projection::class_projection(&env, &definition, || {
                            self.tick()
                        })?
                        && self.instance_registry()?.is_class(&projection.structure)
                    {
                        // `backward.whnf.reducibleClassField` uses a separate
                        // instances-transparency receiver step. Keeping its
                        // ordinary constant key would guess the pin's path.
                        return Err(unsupported());
                    }
                }
                let status = crate::reducibility::table(&self.txn.env)
                    .map_err(|error| {
                        failure(SourceInferenceError::Unification(Box::new(
                            UnificationError::Reducibility(error),
                        )))
                    })?
                    .get(name);
                let reducible = status
                    .map_or(definition.hints == ReducibilityHints::Abbrev, |status| {
                        status == crate::reducibility::Reducibility::Reducible
                    });
                if reducible {
                    if definition.safety != DefinitionSafety::Safe {
                        return Err(unsupported());
                    }
                    if self.txn.env.contains(&Name::str(name.clone(), "_sunfold")) {
                        if !arguments.is_empty() {
                            return Err(unsupported());
                        }
                    } else {
                        let mut unfolded = self.instantiate_params(
                            &definition.value,
                            &definition.base.level_params,
                            levels,
                        )?;
                        for argument in arguments {
                            unfolded = Expr::app(unfolded, argument);
                        }
                        unfolded = self.whnf_with_transparency(
                            &unfolded,
                            UnificationTransparency::None,
                            true,
                        )?;
                        let (unfolded_head, _) = self.symm_spine(&unfolded)?;
                        let bad = !matches!(
                            unfolded_head.node(),
                            ExprNode::Lit { .. }
                                | ExprNode::Const { .. }
                                | ExprNode::FVar { .. }
                                | ExprNode::Proj { .. }
                                | ExprNode::ForallE { .. }
                        );
                        if !root || !bad {
                            current = unfolded;
                            continue;
                        }
                    }
                }
            }
            if let Some(eta) = self.symm_eta(&current)? {
                current = eta;
                continue;
            }
            return Ok(current);
        }
    }

    fn symm_numeral(
        &mut self,
        expression: &Expr,
    ) -> Result<Option<NatLit>, NatDefinitionElabError> {
        let mut expression = expression.clone();
        let mut successors = 0u64;
        let base = loop {
            let (head, arguments) = self.symm_spine(&expression)?;
            match head.node() {
                ExprNode::Lit {
                    literal: Literal::Nat(n),
                } if arguments.is_empty() => break n.clone(),
                ExprNode::Const { name, .. }
                    if *name == Name::from_components(["Nat", "zero"]) && arguments.is_empty() =>
                {
                    break NatLit::from_u64(0);
                }
                ExprNode::Const { name, .. }
                    if *name == Name::from_components(["Nat", "succ"]) && arguments.len() == 1 =>
                {
                    successors = successors
                        .checked_add(1)
                        .ok_or_else(|| failure(SourceInferenceError::ResourceLimit))?;
                    expression = arguments[0].clone();
                }
                ExprNode::Const { name, .. }
                    if *name == Name::from_components(["OfNat", "ofNat"])
                        && arguments.len() == 3 =>
                {
                    expression = arguments[1].clone()
                }
                _ => return Ok(None),
            }
        };
        for _ in 0..base.limbs_le().len() {
            self.tick()?;
        }
        if successors == 0 {
            return Ok(Some(base));
        }
        let n = fln_bignum::interop::bignat_from_literal(&base)
            .add(&fln_bignum::nat::BigNat::from_u64(successors));
        Ok(Some(fln_bignum::interop::literal_from_bignat(&n)))
    }

    fn symm_offset(
        &mut self,
        name: &Name,
        arguments: &[Expr],
    ) -> Result<bool, NatDefinitionElabError> {
        if *name == Name::from_components(["Nat", "succ"]) && arguments.len() == 1 {
            return Ok(true);
        }
        let carrier = if *name == Name::from_components(["Nat", "add"]) && arguments.len() == 2 {
            None
        } else if *name == Name::from_components(["Add", "add"]) && arguments.len() == 4 {
            Some(0)
        } else if *name == Name::from_components(["HAdd", "hAdd"]) && arguments.len() == 6 {
            Some(1)
        } else {
            return Ok(false);
        };
        if let Some(carrier) = carrier {
            let carrier = self.symm_reduce_key(&arguments[carrier], false)?;
            if !matches!(carrier.node(), ExprNode::Const { name, .. } if *name == Name::from_components(["Nat"]))
            {
                return Ok(false);
            }
        }
        self.symm_numeral(arguments.last().ok_or_else(unsupported)?)
            .map(|value| value.is_some())
    }

    fn symm_is_type(&mut self, expression: &Expr) -> Result<bool, NatDefinitionElabError> {
        let type_ = self.known_type(expression)?.ok_or_else(unsupported)?;
        Ok(matches!(
            self.whnf_with_transparency(&type_, UnificationTransparency::Abbreviations, true)?
                .node(),
            ExprNode::Sort { .. }
        ))
    }

    fn symm_is_proof(&mut self, expression: &Expr) -> Result<bool, NatDefinitionElabError> {
        let type_ = self.known_type(expression)?.ok_or_else(unsupported)?;
        let sort = self.known_type(&type_)?.ok_or_else(unsupported)?;
        Ok(
            matches!(self.whnf_with_transparency(&sort, UnificationTransparency::Abbreviations, true)?.node(), ExprNode::Sort { level } if level.normalize_fixpoint().is_zero()),
        )
    }

    fn symm_index_arguments(
        &mut self,
        head: &Expr,
        arguments: &[Expr],
    ) -> Result<Vec<Option<Expr>>, NatDefinitionElabError> {
        let mut type_ = self.known_type(head)?.ok_or_else(unsupported)?;
        let mut indexed = Vec::new();
        for argument in arguments {
            self.tick()?;
            type_ =
                self.whnf_with_transparency(&type_, UnificationTransparency::Abbreviations, true)?;
            let ignored = if let ExprNode::ForallE {
                binder_info, body, ..
            } = type_.node()
            {
                let body = body.clone();
                let ignored = match binder_info {
                    BinderInfo::InstImplicit => true,
                    BinderInfo::Implicit | BinderInfo::StrictImplicit => {
                        !self.symm_is_type(argument)?
                    }
                    BinderInfo::Default => self.symm_is_proof(argument)?,
                };
                type_ = self.substitute(&body, argument)?;
                ignored
            } else {
                self.symm_is_proof(argument)?
            };
            indexed.push((!ignored).then(|| argument.clone()));
        }
        Ok(indexed)
    }

    pub(super) fn symm_path(
        &mut self,
        expression: &Expr,
        insert: bool,
    ) -> Result<Vec<Key>, NatDefinitionElabError> {
        let mut todo = vec![(Some(expression.clone()), true)];
        let mut keys = Vec::new();
        while let Some((expression, root)) = todo.pop() {
            self.tick()?;
            if keys.len() >= MAX_KEYS {
                return Err(failure(SourceInferenceError::ResourceLimit));
            }
            let Some(expression) = expression else {
                keys.push(Key::Star);
                continue;
            };
            if insert
                && matches!(expression.node(), ExprNode::MData { data, .. } if data.len() == 1 && data.get_bool(&Name::from_components(["noindex"]), false))
            {
                keys.push(Key::Star);
                continue;
            }
            let expression = self.symm_reduce_key(&expression, root)?;
            if !root && let Some(n) = self.symm_numeral(&expression)? {
                keys.push(Key::Lit(Literal::Nat(n)));
                continue;
            }
            let (head, arguments) = self.symm_spine(&expression)?;
            let arity = u32::try_from(arguments.len())
                .map_err(|_| failure(SourceInferenceError::ResourceLimit))?;
            let key = match head.node() {
                ExprNode::Const { name, .. } => {
                    if insert && !root && self.symm_offset(name, &arguments)? {
                        keys.push(Key::Star);
                        continue;
                    }
                    Key::Const(name.clone(), arity)
                }
                ExprNode::FVar { id } => Key::FVar(id.clone(), arity),
                ExprNode::Proj {
                    struct_name,
                    idx,
                    expr,
                } => {
                    // The pin ignores a class projection's dictionary when
                    // inserting; matching inspects the receiver normally.
                    let ignored = insert && self.instance_registry()?.is_class(struct_name);
                    todo.push(((!ignored).then(|| expr.clone()), false));
                    Key::Proj(
                        struct_name.clone(),
                        u32::try_from(*idx)
                            .map_err(|_| failure(SourceInferenceError::ResourceLimit))?,
                        arity,
                    )
                }
                ExprNode::ForallE { binder_type, .. } if arguments.is_empty() => {
                    todo.push((Some(binder_type.clone()), false));
                    keys.push(Key::Arrow);
                    continue;
                }
                ExprNode::MVar { .. } => {
                    keys.push(if insert { Key::Star } else { Key::Other });
                    continue;
                }
                ExprNode::Lit { literal } if arguments.is_empty() => {
                    keys.push(Key::Lit(literal.clone()));
                    continue;
                }
                _ => {
                    keys.push(Key::Other);
                    continue;
                }
            };
            let arguments = if insert {
                self.symm_index_arguments(&head, &arguments)?
            } else {
                arguments.into_iter().map(Some).collect()
            };
            todo.extend(
                arguments
                    .into_iter()
                    .rev()
                    .map(|argument| (argument, false)),
            );
            keys.push(key);
        }
        Ok(keys)
    }

    pub(super) fn symm_path_matches(
        &mut self,
        stored: &[Key],
        query: &[Key],
    ) -> Result<bool, NatDefinitionElabError> {
        let mut at = 0usize;
        for key in stored {
            self.tick()?;
            let Some(actual) = query.get(at) else {
                return Ok(false);
            };
            if *key != Key::Star {
                if key != actual {
                    return Ok(false);
                }
                at += 1;
                continue;
            }
            let mut pending = 1usize;
            while pending != 0 {
                self.tick()?;
                let Some(actual) = query.get(at) else {
                    return Ok(false);
                };
                pending = pending
                    .checked_sub(1)
                    .and_then(|pending| pending.checked_add(actual.arity()))
                    .ok_or_else(|| failure(SourceInferenceError::ResourceLimit))?;
                at += 1;
            }
        }
        Ok(at == query.len())
    }
}

/// Matching paths can first differ only at a wildcard/exact edge. Stable
/// sorting therefore gives `getMatch`'s wildcard-first DFS and preserves leaf
/// insertion order without any dependence on declaration-name ordering.
pub(super) fn match_order(left: &[Key], right: &[Key]) -> std::cmp::Ordering {
    for (left, right) in left.iter().zip(right) {
        if left != right {
            return if *left == Key::Star {
                std::cmp::Ordering::Less
            } else if *right == Key::Star {
                std::cmp::Ordering::Greater
            } else {
                std::cmp::Ordering::Equal
            };
        }
    }
    std::cmp::Ordering::Equal
}
