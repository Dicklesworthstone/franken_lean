//! Native `SizeOf` instance and `sizeOf_spec` theorem generation for source
//! inductive types and structures, following vendored `Lean/Meta/SizeOf.lean`.
//!
//! Candidate generation carries no admission authority: every generated
//! `<first>._sizeOf_<k>`, `<I>._sizeOf_inst`, and `<ctor>.sizeOf_spec` passes
//! through both checking seats before publication or attribute registration.
use super::*;
use crate::lctx::{LocalContext, LocalDecl};
use fln_core::expr::{BinderInfo, Expr, ExprNode, FVarId, Literal, NatLit};
use fln_core::level::Level;
use fln_core::name::Name;
use fln_env::constants::{
    ConstantInfo, ConstantVal, DefinitionSafety, DefinitionVal, InductiveVal, ReducibilityHints,
    TheoremVal,
};
use fln_env::environment::Environment;
use fln_kernel::verdict::Budget;

/// Generated `_sizeOf_<k>` helpers and `_sizeOf_inst` dictionaries, ordered so
/// every function precedes the instance that references it.
pub struct GeneratedSizeOfDefs {
    pub declarations: Vec<Declaration>,
    pub functions: Vec<Name>,
    pub instances: Vec<Name>,
}

/// Generated `<ctor>.sizeOf_spec` equational theorems to admit and register
/// with `@[simp]`.
pub struct GeneratedSizeOfSpecs {
    pub declarations: Vec<Declaration>,
    pub theorems: Vec<Name>,
}

const REQUIRED_PRELUDE: &[&[&str]] = &[
    &["SizeOf"],
    &["SizeOf", "mk"],
    &["SizeOf", "sizeOf"],
    &["Nat"],
    &["HAdd", "hAdd"],
    &["instHAdd"],
    &["instAddNat"],
    &["OfNat", "ofNat"],
    &["instOfNatNat"],
    &["Eq"],
    &["Eq", "refl"],
];

fn has_required_prelude(env: &Environment) -> bool {
    REQUIRED_PRELUDE
        .iter()
        .all(|parts| env.contains(&Name::from_components(parts.iter().copied())))
}

fn is_prop_former(inductive: &InductiveVal) -> bool {
    let mut cursor = &inductive.base.type_;
    loop {
        match cursor.node() {
            ExprNode::ForallE { body, .. } => cursor = body,
            ExprNode::MData { expr, .. } => cursor = expr,
            ExprNode::Sort { level } => return level.is_zero(),
            _ => return true,
        }
    }
}

fn eligible_block(env: &Environment, block: &[InductiveVal]) -> bool {
    if block.is_empty() || !has_required_prelude(env) {
        return false;
    }
    let Some(first) = block.first() else {
        return false;
    };
    if first.num_nested > 0 {
        return false;
    }
    for inductive in block {
        if inductive.is_unsafe || inductive.num_nested > 0 || is_prop_former(inductive) {
            return false;
        }
        let rec_name = Name::str(inductive.base.name.clone(), "rec");
        let Some(ConstantInfo::Rec(rec)) = env.find(&rec_name) else {
            return false;
        };
        if rec.base.level_params.len() != inductive.base.level_params.len() + 1
            || rec.base.level_params[1..] != inductive.base.level_params[..]
        {
            return false;
        }
    }
    true
}

fn apply_all(mut f: Expr, args: impl IntoIterator<Item = Expr>) -> Expr {
    for arg in args {
        f = Expr::app(f, arg);
    }
    f
}

fn nat_const() -> Expr {
    Expr::const_(Name::from_components(["Nat"]), Vec::new())
}

fn nat_one() -> Expr {
    let one = Expr::lit(Literal::Nat(NatLit::from_u64(1)));
    let nat = nat_const();
    let inst = Expr::app(
        Expr::const_(Name::from_components(["instOfNatNat"]), Vec::new()),
        one.clone(),
    );
    apply_all(
        Expr::const_(
            Name::from_components(["OfNat", "ofNat"]),
            vec![Level::zero()],
        ),
        [nat, one, inst],
    )
}

fn nat_add(lhs: Expr, rhs: Expr) -> Expr {
    let nat = nat_const();
    let inst_hadd = apply_all(
        Expr::const_(Name::from_components(["instHAdd"]), vec![Level::zero()]),
        [
            nat.clone(),
            Expr::const_(Name::from_components(["instAddNat"]), Vec::new()),
        ],
    );
    apply_all(
        Expr::const_(
            Name::from_components(["HAdd", "hAdd"]),
            vec![Level::zero(), Level::zero(), Level::zero()],
        ),
        [nat.clone(), nat.clone(), nat, inst_hadd, lhs, rhs],
    )
}

fn size_of_fn_name(first_name: &Name, one_based_index: usize) -> Name {
    Name::str(first_name.clone(), format!("_sizeOf_{one_based_index}"))
}

fn size_of_inst_name(type_name: &Name) -> Name {
    Name::str(type_name.clone(), "_sizeOf_inst")
}

fn size_of_spec_name(ctor_name: &Name) -> Name {
    Name::str(ctor_name.clone(), "sizeOf_spec")
}

fn params_with_inst_as_implicit(params: &[LocalDecl]) -> Vec<LocalDecl> {
    params
        .iter()
        .cloned()
        .map(|mut param| {
            if param.binder_info == BinderInfo::InstImplicit {
                param.binder_info = BinderInfo::Implicit;
            }
            param
        })
        .collect()
}

impl Context {
    fn open_forall_telescope(
        &mut self,
        type_: &Expr,
        limit: Option<usize>,
    ) -> Result<(Vec<LocalDecl>, Expr), NatDefinitionElabError> {
        let mut current = type_.clone();
        let mut locals = Vec::new();
        while limit.is_none_or(|max| locals.len() < max) {
            self.tick()?;
            if !matches!(current.node(), ExprNode::ForallE { .. }) {
                current = self.whnf(&current)?;
            }
            let ExprNode::ForallE {
                binder_name,
                binder_type,
                body,
                binder_info,
            } = current.node()
            else {
                break;
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
                    .ok_or_else(|| failure(SourceInferenceError::Scope))?
                    .clone(),
            );
            current = self.substitute(body, &Expr::fvar(id))?;
        }
        Ok((locals, current))
    }

    fn close_binders(
        &mut self,
        locals: &[LocalDecl],
        body: Expr,
        lambda: bool,
    ) -> Result<Expr, NatDefinitionElabError> {
        let mut result = self.instantiate(&body)?;
        for local in locals.iter().rev() {
            self.tick()?;
            let domain = self.instantiate(&local.type_)?;
            let abstracted = result
                .abstract_fvar(&local.id, 0)
                .map_err(|_| failure(SourceInferenceError::Scope))?;
            result = if lambda {
                Expr::lam(
                    local.user_name.clone(),
                    domain,
                    abstracted,
                    local.binder_info,
                )
            } else {
                Expr::forall_e(
                    local.user_name.clone(),
                    domain,
                    abstracted,
                    local.binder_info,
                )
            };
        }
        Ok(result)
    }

    /// `mkLocalInstances` (vendored `Lean/Meta/SizeOf.lean:16-38`): synthesize a
    /// local `[inst : ∀ xs, SizeOf (param xs)]` for each type-valued parameter.
    fn size_of_local_instances(
        &mut self,
        params: &[LocalDecl],
    ) -> Result<Vec<LocalDecl>, NatDefinitionElabError> {
        let mut instances = Vec::new();
        for param in params {
            self.tick()?;
            let saved = self.txn.lctx.clone();
            let inst_type = (|| {
                let (xs, tail) = self.open_forall_telescope(&param.type_, None)?;
                let tail = self.whnf(&tail)?;
                let ExprNode::Sort { level } = tail.node() else {
                    return Ok(None);
                };
                let applied = apply_all(
                    Expr::fvar(param.id.clone()),
                    xs.iter().map(|local| Expr::fvar(local.id.clone())),
                );
                let size_of = Expr::app(
                    Expr::const_(Name::from_components(["SizeOf"]), vec![level.clone()]),
                    applied,
                );
                let closed = self.close_binders(&xs, size_of, false)?;
                Ok(Some(closed))
            })();
            self.txn.lctx = saved;
            if let Some(inst_type) = inst_type? {
                let id = FVarId(self.fresh_name()?);
                self.txn.lctx.add_param(
                    id.clone(),
                    Name::from_components(["inst"]),
                    inst_type,
                    BinderInfo::InstImplicit,
                );
                instances.push(
                    self.txn
                        .lctx
                        .find(&id)
                        .ok_or_else(|| failure(SourceInferenceError::Scope))?
                        .clone(),
                );
            }
        }
        Ok(instances)
    }

    /// `isInductiveHypothesis?` (vendored `Lean/Meta/SizeOf.lean:44-49`).
    fn size_of_ih_target(
        &mut self,
        motive_ids: &[FVarId],
        local: &LocalDecl,
    ) -> Result<Option<Expr>, NatDefinitionElabError> {
        let saved = self.txn.lctx.clone();
        let outcome = (|| {
            let (_, tail) = self.open_forall_telescope(&local.type_, None)?;
            let ExprNode::App { a, .. } = tail.node() else {
                return Ok(None);
            };
            let (head, _) = operators::spine(&tail);
            if let ExprNode::FVar { id } = head.node()
                && motive_ids.contains(id)
            {
                return Ok(Some(a.clone()));
            }
            Ok(None)
        })();
        self.txn.lctx = saved;
        outcome
    }

    /// `isRecField?` (vendored `Lean/Meta/SizeOf.lean:58-65`).
    fn size_of_rec_field_ih_index(
        &mut self,
        motive_ids: &[FVarId],
        minor_fvars: &[LocalDecl],
        field: &LocalDecl,
    ) -> Result<Option<usize>, NatDefinitionElabError> {
        for (idx, candidate) in minor_fvars.iter().enumerate() {
            self.tick()?;
            if let Some(target) = self.size_of_ih_target(motive_ids, candidate)? {
                let (head, _) = operators::spine(&target);
                if matches!(head.node(), ExprNode::FVar { id } if id == &field.id) {
                    return Ok(Some(idx));
                }
            }
        }
        Ok(None)
    }

    /// `ignoreFieldType` (vendored `Lean/Meta/SizeOf.lean:80-89`).
    fn size_of_ignore_field_type(&mut self, type_: &Expr) -> Result<bool, NatDefinitionElabError> {
        let mut current = type_.clone();
        loop {
            self.tick()?;
            current = self.whnf(&current)?;
            let ExprNode::ForallE {
                binder_type, body, ..
            } = current.node()
            else {
                return Ok(false);
            };
            let is_unit_arrow = !body.has_loose_bvars()
                && matches!(
                    binder_type.node(),
                    ExprNode::Const { name, .. }
                        if name == &Name::from_components(["Unit"])
                            || name == &Name::from_components(["PUnit"])
                );
            if is_unit_arrow {
                current = body.clone();
            } else {
                return Ok(true);
            }
        }
    }

    /// `mkSizeOfRecFieldFormIH` (vendored `Lean/Meta/SizeOf.lean:96-100`).
    fn size_of_rec_field_from_ih(&mut self, mut ih: Expr) -> Result<Expr, NatDefinitionElabError> {
        loop {
            self.tick()?;
            let Some(ty) = self.known_type(&ih)? else {
                return Ok(ih);
            };
            let ty = self.whnf(&ty)?;
            if !matches!(ty.node(), ExprNode::ForallE { .. }) {
                return Ok(ih);
            }
            let unit = Expr::const_(Name::from_components(["PUnit", "unit"]), vec![Level::one()]);
            ih = Expr::app(ih, unit);
        }
    }

    fn size_of_field_term(
        &mut self,
        field: &LocalDecl,
    ) -> Result<Option<Expr>, NatDefinitionElabError> {
        let Some(sort) = self.known_type(&field.type_)? else {
            return Ok(None);
        };
        let sort = self.whnf(&sort)?;
        let ExprNode::Sort { level } = sort.node() else {
            return Ok(None);
        };
        let goal = Expr::app(
            Expr::const_(Name::from_components(["SizeOf"]), vec![level.clone()]),
            field.type_.clone(),
        );
        let Some(inst) = self.coercion_instance(goal)? else {
            return Ok(None);
        };
        let inst = self.instantiate(&inst)?;
        if inst.has_expr_mvar() || inst.has_level_mvar() {
            return Ok(None);
        }
        Ok(Some(apply_all(
            Expr::const_(
                Name::from_components(["SizeOf", "sizeOf"]),
                vec![level.clone()],
            ),
            [field.type_.clone(), inst, Expr::fvar(field.id.clone())],
        )))
    }

    /// `mkSizeOfFn` (vendored `Lean/Meta/SizeOf.lean:126-160`).
    fn build_size_of_fn(
        &mut self,
        inductive: &InductiveVal,
        decl_name: Name,
    ) -> Result<Option<DefinitionVal>, NatDefinitionElabError> {
        let rec_name = Name::str(inductive.base.name.clone(), "rec");
        let Some(ConstantInfo::Rec(rec_info)) = self.txn.env.find(&rec_name).cloned() else {
            return Ok(None);
        };
        let level_params = inductive.base.level_params.clone();
        self.level_params = level_params.clone();
        self.explicit_levels = level_params.len();
        let saved = self.txn.lctx.clone();
        let built = (|| {
            self.txn.lctx = LocalContext::new();
            let (xs, _) = self.open_forall_telescope(&rec_info.base.type_, None)?;
            let num_params = rec_info.num_params as usize;
            let num_motives = rec_info.num_motives as usize;
            let num_minors = rec_info.num_minors as usize;
            let num_indices = rec_info.num_indices as usize;
            let first_minor = num_params + num_motives;
            let first_index = first_minor + num_minors;
            let major_idx = first_index + num_indices;
            if xs.len() <= major_idx {
                return Ok(None);
            }
            let params = &xs[..num_params];
            let motive_fvars = &xs[num_params..first_minor];
            let minor_fvars = &xs[first_minor..first_index];
            let indices = &xs[first_index..major_idx];
            let major = &xs[major_idx];
            let motive_ids: Vec<_> = motive_fvars.iter().map(|m| m.id.clone()).collect();
            let local_insts = self.size_of_local_instances(params)?;

            let mut motives = Vec::with_capacity(num_motives);
            for motive in motive_fvars {
                let before = self.txn.lctx.clone();
                let (m_xs, _) = self.open_forall_telescope(&motive.type_, None)?;
                let motive_val = self.close_binders(&m_xs, nat_const(), true)?;
                self.txn.lctx = before;
                motives.push(motive_val);
            }

            let mut us = Vec::with_capacity(level_params.len() + 1);
            us.push(Level::one());
            us.extend(level_params.iter().cloned().map(Level::param));
            let rec_fn = Expr::const_(rec_name, us);
            let mut val = apply_all(
                rec_fn,
                params
                    .iter()
                    .map(|p| Expr::fvar(p.id.clone()))
                    .chain(motives),
            );
            let Some(val_type) = self.known_type(&val)? else {
                return Ok(None);
            };
            let before_minors = self.txn.lctx.clone();
            let (minor_fvars_prime, _) = self.open_forall_telescope(&val_type, Some(num_minors))?;
            if minor_fvars_prime.len() != num_minors {
                self.txn.lctx = before_minors;
                return Ok(None);
            }
            let mut minors = Vec::with_capacity(num_minors);
            for (minor_fvar, minor_fvar_prime) in minor_fvars.iter().zip(&minor_fvars_prime) {
                let before_minor = self.txn.lctx.clone();
                let (m_xs, _) = self.open_forall_telescope(&minor_fvar.type_, None)?;
                let (m_xs_prime, _) =
                    self.open_forall_telescope(&minor_fvar_prime.type_, Some(m_xs.len()))?;
                if m_xs_prime.len() != m_xs.len() {
                    self.txn.lctx = before_minor;
                    return Ok(None);
                }
                let mut minor_body = nat_one();
                for (x, x_prime) in m_xs.iter().zip(&m_xs_prime) {
                    if self.size_of_ih_target(&motive_ids, x)?.is_some() {
                        continue;
                    }
                    if self.size_of_ignore_field_type(&x.type_)? {
                        continue;
                    }
                    if let Some(ih_idx) = self.size_of_rec_field_ih_index(&motive_ids, &m_xs, x)? {
                        let ih = self
                            .size_of_rec_field_from_ih(Expr::fvar(m_xs_prime[ih_idx].id.clone()))?;
                        minor_body = nat_add(minor_body, ih);
                    } else {
                        let Some(field_size) = self.size_of_field_term(x_prime)? else {
                            self.txn.lctx = before_minor;
                            return Ok(None);
                        };
                        minor_body = nat_add(minor_body, field_size);
                    }
                }
                let minor = self.close_binders(&m_xs_prime, minor_body, true)?;
                self.txn.lctx = before_minor;
                minors.push(minor);
            }
            self.txn.lctx = before_minors;

            val = apply_all(
                val,
                minors
                    .into_iter()
                    .chain(indices.iter().map(|i| Expr::fvar(i.id.clone())))
                    .chain(std::iter::once(Expr::fvar(major.id.clone()))),
            );
            let mut size_of_params = params_with_inst_as_implicit(params);
            size_of_params.extend(local_insts);
            size_of_params.extend(indices.iter().cloned());
            size_of_params.push(major.clone());
            let type_ = self.close_binders(&size_of_params, nat_const(), false)?;
            let value = self.close_binders(&size_of_params, val, true)?;
            if type_.has_fvar()
                || type_.has_loose_bvars()
                || type_.has_expr_mvar()
                || type_.has_level_mvar()
                || value.has_fvar()
                || value.has_loose_bvars()
                || value.has_expr_mvar()
                || value.has_level_mvar()
            {
                return Ok(None);
            }
            Ok(Some(DefinitionVal {
                base: ConstantVal {
                    name: decl_name.clone(),
                    level_params,
                    type_,
                },
                value,
                hints: ReducibilityHints::Abbrev,
                safety: DefinitionSafety::Safe,
                all: vec![decl_name],
            }))
        })();
        self.txn.lctx = saved;
        built
    }

    /// `mkSizeOfInstances` instance dictionary (vendored `Lean/Meta/SizeOf.lean:500-528`).
    fn build_size_of_inst(
        &mut self,
        inductive: &InductiveVal,
        fn_name: &Name,
    ) -> Result<Option<DefinitionVal>, NatDefinitionElabError> {
        let level_params = inductive.base.level_params.clone();
        self.level_params = level_params.clone();
        self.explicit_levels = level_params.len();
        let saved = self.txn.lctx.clone();
        let built = (|| {
            self.txn.lctx = LocalContext::new();
            let (xs, sort) = self.open_forall_telescope(&inductive.base.type_, None)?;
            let sort = self.whnf(&sort)?;
            let ExprNode::Sort { level } = sort.node() else {
                return Ok(None);
            };
            let num_params = inductive.num_params as usize;
            if xs.len() < num_params {
                return Ok(None);
            }
            let params = &xs[..num_params];
            let indices = &xs[num_params..];
            let local_insts = self.size_of_local_instances(params)?;
            let us: Vec<_> = level_params.iter().cloned().map(Level::param).collect();
            let ind_type = apply_all(
                Expr::const_(inductive.base.name.clone(), us.clone()),
                xs.iter().map(|x| Expr::fvar(x.id.clone())),
            );
            let size_of_ind_type = Expr::app(
                Expr::const_(Name::from_components(["SizeOf"]), vec![level.clone()]),
                ind_type.clone(),
            );
            let m_id = FVarId(self.fresh_name()?);
            let m_name = Name::from_components(["m"]);
            self.txn.lctx.add_param(
                m_id.clone(),
                m_name.clone(),
                ind_type.clone(),
                BinderInfo::Default,
            );
            let fn_app = apply_all(
                Expr::const_(fn_name.clone(), us),
                params
                    .iter()
                    .map(|p| Expr::fvar(p.id.clone()))
                    .chain(local_insts.iter().map(|i| Expr::fvar(i.id.clone())))
                    .chain(indices.iter().map(|i| Expr::fvar(i.id.clone())))
                    .chain(std::iter::once(Expr::fvar(m_id.clone()))),
            );
            let fn_lam = Expr::lam(
                m_name,
                ind_type.clone(),
                fn_app
                    .abstract_fvar(&m_id, 0)
                    .map_err(|_| failure(SourceInferenceError::Scope))?,
                BinderInfo::Default,
            );
            let size_of_mk = apply_all(
                Expr::const_(Name::from_components(["SizeOf", "mk"]), vec![level.clone()]),
                [ind_type, fn_lam],
            );
            let mut binders = params_with_inst_as_implicit(params);
            binders.extend(indices.iter().cloned());
            binders.extend(local_insts);
            let type_ = self.close_binders(&binders, size_of_ind_type, false)?;
            let value = self.close_binders(&binders, size_of_mk, true)?;
            if type_.has_fvar()
                || type_.has_loose_bvars()
                || type_.has_expr_mvar()
                || type_.has_level_mvar()
                || value.has_fvar()
                || value.has_loose_bvars()
                || value.has_expr_mvar()
                || value.has_level_mvar()
            {
                return Ok(None);
            }
            let inst_name = size_of_inst_name(&inductive.base.name);
            Ok(Some(DefinitionVal {
                base: ConstantVal {
                    name: inst_name.clone(),
                    level_params,
                    type_,
                },
                value,
                hints: ReducibilityHints::Abbrev,
                safety: DefinitionSafety::Safe,
                all: vec![inst_name],
            }))
        })();
        self.txn.lctx = saved;
        built
    }

    /// `mkSizeOfSpecTheorem` (vendored `Lean/Meta/SizeOf.lean:424-473`).
    fn build_size_of_spec(
        &mut self,
        inductive: &InductiveVal,
        ctor_name: &Name,
    ) -> Result<Option<TheoremVal>, NatDefinitionElabError> {
        let Some(ConstantInfo::Ctor(ctor_info)) = self.txn.env.find(ctor_name).cloned() else {
            return Ok(None);
        };
        let level_params = ctor_info.base.level_params.clone();
        self.level_params = level_params.clone();
        self.explicit_levels = level_params.len();
        let saved = self.txn.lctx.clone();
        let built = (|| {
            self.txn.lctx = LocalContext::new();
            let (xs, _) = self.open_forall_telescope(&ctor_info.base.type_, None)?;
            let num_params = ctor_info.num_params as usize;
            if xs.len() < num_params {
                return Ok(None);
            }
            let params = &xs[..num_params];
            let fields = &xs[num_params..];
            let us: Vec<_> = level_params.iter().cloned().map(Level::param).collect();
            let ctor_app = apply_all(
                Expr::const_(ctor_name.clone(), us.clone()),
                xs.iter().map(|x| Expr::fvar(x.id.clone())),
            );
            let local_insts = self.size_of_local_instances(params)?;
            let Some(ctor_app_type) = self.known_type(&ctor_app)? else {
                return Ok(None);
            };
            let (_, ctor_app_type_args) = operators::spine(&ctor_app_type);
            let ind_num_params = inductive.num_params as usize;
            if ctor_app_type_args.len() < ind_num_params {
                return Ok(None);
            }
            let indices_from_type = &ctor_app_type_args[ind_num_params..];
            let Some(sort) = self.known_type(&ctor_app_type)? else {
                return Ok(None);
            };
            let sort = self.whnf(&sort)?;
            let ExprNode::Sort { level } = sort.node() else {
                return Ok(None);
            };
            let inst = apply_all(
                Expr::const_(size_of_inst_name(&inductive.base.name), us),
                params
                    .iter()
                    .map(|p| Expr::fvar(p.id.clone()))
                    .chain(indices_from_type.iter().cloned())
                    .chain(local_insts.iter().map(|i| Expr::fvar(i.id.clone()))),
            );
            let lhs = apply_all(
                Expr::const_(
                    Name::from_components(["SizeOf", "sizeOf"]),
                    vec![level.clone()],
                ),
                [ctor_app_type, inst, ctor_app],
            );
            let mut rhs = nat_one();
            for field in fields {
                if self.size_of_ignore_field_type(&field.type_)? {
                    continue;
                }
                let Some(field_size) = self.size_of_field_term(field)? else {
                    return Ok(None);
                };
                rhs = nat_add(rhs, field_size);
            }
            let target = apply_all(
                Expr::const_(Name::from_components(["Eq"]), vec![Level::one()]),
                [nat_const(), lhs, rhs.clone()],
            );
            let proof = apply_all(
                Expr::const_(Name::from_components(["Eq", "refl"]), vec![Level::one()]),
                [nat_const(), rhs],
            );
            let mut thm_params = params.to_vec();
            thm_params.extend(local_insts);
            thm_params.extend(fields.iter().cloned());
            let type_ = self.close_binders(&thm_params, target, false)?;
            let value = self.close_binders(&thm_params, proof, true)?;
            if type_.has_fvar()
                || type_.has_loose_bvars()
                || type_.has_expr_mvar()
                || type_.has_level_mvar()
                || value.has_fvar()
                || value.has_loose_bvars()
                || value.has_expr_mvar()
                || value.has_level_mvar()
            {
                return Ok(None);
            }
            let thm_name = size_of_spec_name(ctor_name);
            Ok(Some(TheoremVal {
                base: ConstantVal {
                    name: thm_name.clone(),
                    level_params,
                    type_,
                },
                value,
                all: vec![thm_name],
            }))
        })();
        self.txn.lctx = saved;
        built
    }
}

/// Generate `<first>._sizeOf_<k>` and `<I>._sizeOf_inst` declarations for a
/// newly admitted non-Prop, non-nested safe inductive block.
pub fn generate_inductive_size_of_defs(
    env: &Environment,
    block: &[InductiveVal],
    kernel: Budget,
) -> Result<Option<GeneratedSizeOfDefs>, NatDefinitionElabError> {
    if !eligible_block(env, block) {
        return Ok(None);
    }
    let first_name = &block[0].base.name;
    let mut fn_names = Vec::with_capacity(block.len());
    for (index, inductive) in block.iter().enumerate() {
        let fn_name = size_of_fn_name(first_name, index + 1);
        let inst_name = size_of_inst_name(&inductive.base.name);
        if env.contains(&fn_name) || env.contains(&inst_name) {
            return Ok(None);
        }
        fn_names.push(fn_name);
    }
    let mut context = Context::new(env, kernel);
    let mut declarations = Vec::with_capacity(block.len() * 2);
    let mut functions = Vec::with_capacity(block.len());
    let mut instances = Vec::with_capacity(block.len());
    for (inductive, fn_name) in block.iter().zip(&fn_names) {
        let Some(definition) = context.build_size_of_fn(inductive, fn_name.clone())? else {
            return Ok(None);
        };
        functions.push(fn_name.clone());
        declarations.push(Declaration::Defn(definition));
    }
    for (inductive, fn_name) in block.iter().zip(&fn_names) {
        let Some(instance) = context.build_size_of_inst(inductive, fn_name)? else {
            return Ok(None);
        };
        instances.push(instance.base.name.clone());
        declarations.push(Declaration::Defn(instance));
    }
    Ok(Some(GeneratedSizeOfDefs {
        declarations,
        functions,
        instances,
    }))
}

/// Generate `<ctor>.sizeOf_spec` theorems after `_sizeOf_<k>` and
/// `_sizeOf_inst` have been admitted and registered as instances.
pub fn generate_inductive_size_of_specs(
    env: &Environment,
    block: &[InductiveVal],
    kernel: Budget,
) -> Result<Option<GeneratedSizeOfSpecs>, NatDefinitionElabError> {
    if !eligible_block(env, block) {
        return Ok(None);
    }
    for inductive in block {
        if !env.contains(&size_of_inst_name(&inductive.base.name)) {
            return Ok(None);
        }
        for ctor_name in &inductive.ctors {
            if env.contains(&size_of_spec_name(ctor_name)) {
                return Ok(None);
            }
        }
    }
    let mut context = Context::new(env, kernel);
    let mut declarations = Vec::new();
    let mut theorems = Vec::new();
    for inductive in block {
        for ctor_name in &inductive.ctors {
            let Some(theorem) = context.build_size_of_spec(inductive, ctor_name)? else {
                return Ok(None);
            };
            theorems.push(theorem.base.name.clone());
            declarations.push(Declaration::Thm(theorem));
        }
    }
    Ok(Some(GeneratedSizeOfSpecs {
        declarations,
        theorems,
    }))
}
