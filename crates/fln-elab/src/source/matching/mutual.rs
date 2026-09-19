//! Specialize an admitted mutual recursor to an ordinary single-family match.
//!
//! Other families use the constant motive `R -> R`, inhabited by identity at
//! exactly the same universe as R (including Prop). This needs no new axiom,
//! default instance, trusted evaluator or universe-cumulative coercion. The
//! selected family's supplied branches remain the actual recursor minors.
use super::*;
use fln_env::constants::{InductiveVal, RecursorVal};

impl Context {
    /// Build lambdas over a checked telescope until its result is the constant's
    /// type. Every fresh binder is private and closed capture-avoidantly. A
    /// malformed or differently returning telescope fails rather than erasing
    /// a premise. This is term construction, never declaration admission.
    fn mutual_constant_function(
        &mut self,
        type_: Expr,
        constant: &Typed,
    ) -> Result<Typed, NatDefinitionElabError> {
        let saved = self.txn.lctx.clone();
        let result = (|| {
            let expected = self.whnf(&constant.type_)?;
            let mut current = type_.clone();
            let mut locals = Vec::new();
            loop {
                self.tick()?;
                current = self.whnf(&current)?;
                if current == expected {
                    break;
                }
                let ExprNode::ForallE {
                    binder_name,
                    binder_type,
                    body,
                    binder_info,
                } = current.node()
                else {
                    return Err(error(MatchError::UnsupportedFamily));
                };
                let id = FVarId(self.fresh_name()?);
                self.txn.lctx.add_param(
                    id.clone(),
                    binder_name.clone(),
                    binder_type.clone(),
                    *binder_info,
                );
                locals.push(
                    self.txn
                        .lctx
                        .find(&id)
                        .expect("private mutual binder")
                        .clone(),
                );
                current = self.substitute(body, &Expr::fvar(id))?;
            }
            let mut value = constant.value.clone();
            for local in locals.into_iter().rev() {
                self.tick()?;
                value = Expr::lam(
                    local.user_name,
                    local.type_,
                    value
                        .abstract_fvar(&local.id, 0)
                        .map_err(|_| failure(SourceInferenceError::Scope))?,
                    local.binder_info,
                );
            }
            Ok(Typed { value, type_ })
        })();
        self.txn.lctx = saved;
        result
    }

    pub(in crate::source) fn specialize_mutual_match(
        &mut self,
        mut recursor: Typed,
        family: &InductiveVal,
        rec: &RecursorVal,
        motive: Typed,
        target: &Expr,
        universe: Level,
    ) -> Result<Typed, NatDefinitionElabError> {
        let mut constructors = Vec::new();
        let mut names = HashSet::new();
        for name in &family.all {
            self.tick()?;
            let Some(ConstantInfo::Induct(member)) = self.txn.env.find(name) else {
                return Err(error(MatchError::UnsupportedFamily));
            };
            if !names.insert(name.clone())
                || member.all != family.all
                || member.is_unsafe
                || member.num_nested != 0
                || member.num_params != family.num_params
                || member.base.level_params != family.base.level_params
            {
                return Err(error(MatchError::UnsupportedFamily));
            }
            for ctor in &member.ctors {
                if constructors.len() >= 256 {
                    return Err(failure(SourceInferenceError::ResourceLimit));
                }
                constructors.push((name.clone(), ctor.clone()));
            }
        }
        if constructors.len() != rec.num_minors as usize
            || rec.rules.iter().map(|r| &r.ctor).ne(family.ctors.iter())
            || target.has_loose_bvars()
        {
            return Err(error(MatchError::UnsupportedFamily));
        }
        let neutral_type = Expr::forall_e(
            Name::anonymous(),
            target.clone(),
            target.clone(),
            BinderInfo::Default,
        );
        let neutral = Typed {
            value: Expr::lam(
                Name::anonymous(),
                target.clone(),
                Expr::bvar(0).map_err(|_| failure(SourceInferenceError::Scope))?,
                BinderInfo::Default,
            ),
            type_: neutral_type.clone(),
        };
        let saved = self.txn.lctx.clone();
        let result = (|| {
            for name in &family.all {
                self.tick()?;
                let argument = if name == &family.base.name {
                    motive.clone()
                } else {
                    let type_ = self.whnf(&recursor.type_)?;
                    let ExprNode::ForallE { binder_type, .. } = type_.node() else {
                        return Err(error(MatchError::UnsupportedFamily));
                    };
                    self.mutual_constant_function(
                        binder_type.clone(),
                        &Typed {
                            value: neutral_type.clone(),
                            type_: Expr::sort(universe.clone()),
                        },
                    )?
                };
                recursor = self.match_apply(recursor, argument)?;
            }
            let mut selected = Vec::new();
            for (owner, _) in &constructors {
                self.tick()?;
                let type_ = self.whnf(&recursor.type_)?;
                let ExprNode::ForallE {
                    binder_name,
                    binder_type,
                    binder_info,
                    ..
                } = type_.node()
                else {
                    return Err(error(MatchError::UnsupportedFamily));
                };
                let argument = if owner == &family.base.name {
                    let id = FVarId(self.fresh_name()?);
                    self.txn.lctx.add_param(
                        id.clone(),
                        binder_name.clone(),
                        binder_type.clone(),
                        *binder_info,
                    );
                    selected.push(self.txn.lctx.find(&id).expect("selected minor").clone());
                    Typed {
                        value: Expr::fvar(id),
                        type_: binder_type.clone(),
                    }
                } else {
                    self.mutual_constant_function(binder_type.clone(), &neutral)?
                };
                recursor = self.match_apply(recursor, argument)?;
            }
            for local in selected.into_iter().rev() {
                self.tick()?;
                recursor.value = Expr::lam(
                    local.user_name.clone(),
                    local.type_.clone(),
                    recursor
                        .value
                        .abstract_fvar(&local.id, 0)
                        .map_err(|_| failure(SourceInferenceError::Scope))?,
                    local.binder_info,
                );
                recursor.type_ = Expr::forall_e(
                    local.user_name,
                    local.type_,
                    recursor
                        .type_
                        .abstract_fvar(&local.id, 0)
                        .map_err(|_| failure(SourceInferenceError::Scope))?,
                    local.binder_info,
                );
            }
            Ok(recursor)
        })();
        self.txn.lctx = saved;
        result
    }
}
