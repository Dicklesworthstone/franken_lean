//! Conv navigation: `congr`, `arg i`, `lhs`/`rhs`, `fun`, `ext`/`intro` and `enter`
//! (vendored `Lean/Elab/Tactic/Conv/Congr.lean`), over the congruence theorems the pin
//! generates (`mkCongrSimpCore?`, `getCongrSimpKinds`, `getCongrSimpKindsForArgZero`, vendored
//! `Lean/Meta/CongrTheorems.lean`; `getFunInfoNArgs`, `Lean/Meta/FunInfo.lean`).
use super::*;

/// `ParamInfo`'s fields the congruence kinds read.
#[derive(Clone)]
pub(super) struct ParamInfo {
    binder_info: BinderInfo,
    back_deps: Vec<usize>,
    pub(super) has_fwd_deps: bool,
    is_prop: bool,
    is_dec_inst: bool,
}

impl ParamInfo {
    fn is_explicit(&self) -> bool {
        self.binder_info == BinderInfo::Default
    }
    fn is_instance(&self) -> bool {
        self.binder_info == BinderInfo::InstImplicit
    }
}

#[derive(Clone)]
pub(super) struct FunInfo {
    pub(super) params: Vec<ParamInfo>,
    result_deps: Vec<usize>,
}

/// `CongrArgKind`, without the kinds congr-simp theorems never use.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(super) enum ArgKind {
    Fixed,
    Eq,
    Cast,
    SubsingletonInst,
}

/// A generated congruence theorem: its statement, its proof (a closed lambda), its kinds.
struct CongrTheorem {
    type_: Expr,
    proof: Expr,
    kinds: Vec<ArgKind>,
}

/// The equation a `.cast` argument is transported along.
#[derive(Clone)]
enum EqInfo {
    Hyp {
        equation: FVarId,
        lhs: FVarId,
        rhs: FVarId,
    },
    DecSubsingleton,
}

/// What a congruence theorem applied to a goal's arguments gives (`mkCongrThm`).
struct Applied {
    proof: Expr,
    rhs: Expr,
    goals: Vec<Option<ProofGoal>>,
    instances: Vec<ProofGoal>,
}

impl Context {
    /// `getFunInfoNArgs f n`: the parameters of `f`'s type, at most `n`, each with the earlier
    /// parameters its type reads, and those the result type reads.
    pub(super) fn conv_fun_info(
        &mut self,
        f: &Expr,
        max: usize,
    ) -> Result<FunInfo, NatDefinitionElabError> {
        let saved = self.txn.lctx.clone();
        let result = self.conv_fun_info_in(f, max);
        self.txn.lctx = saved;
        result
    }

    fn conv_fun_info_in(
        &mut self,
        f: &Expr,
        max: usize,
    ) -> Result<FunInfo, NatDefinitionElabError> {
        // `inferType` instantiates with `instantiateBetaRevRange`: an instance's `fun _ => Int`
        // substituted for `β` leaves `β a` as `Int`, which then reads no parameter.
        let mut type_ = self.conv_type(f)?;
        type_ = self.conv_beta_all(&type_)?;
        let mut locals: Vec<FVarId> = Vec::new();
        let mut params: Vec<ParamInfo> = Vec::new();
        while locals.len() < max {
            self.tick()?;
            if !matches!(type_.node(), ExprNode::ForallE { .. }) {
                type_ = self.whnf(&type_)?;
            }
            let ExprNode::ForallE {
                binder_name,
                binder_type,
                body,
                binder_info,
            } = type_.node()
            else {
                break;
            };
            let domain = self.instantiate(binder_type)?;
            let domain = self.conv_beta_all(&domain)?;
            let reads = self.elimination_reads(&domain)?;
            let back_deps: Vec<usize> = locals
                .iter()
                .enumerate()
                .filter(|(_, id)| reads.contains(id))
                .map(|(index, _)| index)
                .collect();
            for &dep in &back_deps {
                params[dep].has_fwd_deps = true;
            }
            let is_prop = self.conv_is_prop(&domain)?;
            let is_dec_inst = self.conv_concludes_in(&domain, &["Decidable"])?;
            params.push(ParamInfo {
                binder_info: *binder_info,
                back_deps,
                has_fwd_deps: false,
                is_prop,
                is_dec_inst,
            });
            let local = self.conv_local(binder_name.clone(), domain, *binder_info)?;
            locals.push(local.id.clone());
            type_ = self.substitute(body, &Expr::fvar(local.id))?;
        }
        let type_ = self.conv_beta_all(&type_)?;
        let reads = self.elimination_reads(&type_)?;
        let result_deps: Vec<usize> = locals
            .iter()
            .enumerate()
            .filter(|(_, id)| reads.contains(id))
            .map(|(index, _)| index)
            .collect();
        for &dep in &result_deps {
            params[dep].has_fwd_deps = true;
        }
        Ok(FunInfo {
            params,
            result_deps,
        })
    }

    /// `forallTelescopeReducing type fun _ type => type.isAppOf c`.
    fn conv_concludes_in(
        &mut self,
        type_: &Expr,
        name: &[&str],
    ) -> Result<bool, NatDefinitionElabError> {
        let mut type_ = type_.clone();
        let mut depth = 0u32;
        loop {
            self.tick()?;
            while let ExprNode::ForallE { body, .. } = type_.node() {
                type_ = body.clone();
                depth += 1;
            }
            if is_app_of(&type_, name) {
                return Ok(true);
            }
            if depth != 0 || type_.has_loose_bvars() {
                return Ok(false);
            }
            let reduced = self.whnf(&type_)?;
            if !matches!(reduced.node(), ExprNode::ForallE { .. }) {
                return Ok(is_app_of(&reduced, name));
            }
            type_ = reduced;
        }
    }

    /// `getClassSubobjectMask?` is `some` only for a class's constructor, whose subobject
    /// fields the pin treats as ordinary parameters; this engine does not build that case.
    fn conv_is_class_constructor(&mut self, f: &Expr) -> Result<bool, NatDefinitionElabError> {
        let ExprNode::Const { name, .. } = f.node() else {
            return Ok(false);
        };
        let Some(fln_env::constants::ConstantInfo::Ctor(ctor)) = self.txn.env.find(name).cloned()
        else {
            return Ok(false);
        };
        let registry = crate::instances::InstanceRegistry::read(&self.txn.env)
            .map_err(crate::source::instances::registry_error)?;
        Ok(registry.is_class(&ctor.induct))
    }

    /// `getCongrSimpKinds f info`.
    pub(super) fn conv_congr_simp_kinds(
        &mut self,
        f: &Expr,
        info: &FunInfo,
    ) -> Result<Vec<ArgKind>, NatDefinitionElabError> {
        if self.conv_is_class_constructor(f)? {
            return Err(error(TacticError::ConvUnsupported(
                "congruence through a class constructor",
            )));
        }
        let mut result = Vec::new();
        for (i, param) in info.params.iter().enumerate() {
            let kind = if info.result_deps.contains(&i) {
                ArgKind::Fixed
            } else if param.is_prop {
                ArgKind::Cast
            } else if param.is_instance() {
                if should_use_subsingleton_inst(info, &result, i) {
                    ArgKind::SubsingletonInst
                } else {
                    ArgKind::Fixed
                }
            } else {
                ArgKind::Eq
            };
            result.push(kind);
        }
        Ok(fix_kinds_for_dependencies(info, result))
    }

    /// `getCongrSimpKindsForArgZero info`.
    fn conv_congr_simp_kinds_arg_zero(&self, info: &FunInfo) -> Vec<ArgKind> {
        let mut result = Vec::new();
        for (i, param) in info.params.iter().enumerate() {
            let kind = if info.result_deps.contains(&i) {
                ArgKind::Fixed
            } else if i == 0 {
                ArgKind::Eq
            } else if param.is_prop {
                ArgKind::Cast
            } else if param.is_instance() {
                if should_use_subsingleton_inst(info, &result, i) {
                    ArgKind::SubsingletonInst
                } else {
                    ArgKind::Fixed
                }
            } else {
                ArgKind::Fixed
            };
            result.push(kind);
        }
        fix_kinds_for_dependencies(info, result)
    }

    /// `mkCongrSimpCore? f info kinds (subsingletonInstImplicitRhs := false)`: the theorem, or
    /// `None` where the pin's `mk?` fails for both its tries.
    fn conv_congr_simp_core(
        &mut self,
        f: &Expr,
        info: &FunInfo,
        kinds: Vec<ArgKind>,
    ) -> Result<Option<CongrTheorem>, NatDefinitionElabError> {
        let saved = self.txn.lctx.clone();
        let result = self.conv_congr_simp_mk(f, info, &kinds);
        self.txn.lctx = saved;
        match result? {
            Some(theorem) => Ok(Some(theorem)),
            None if kinds
                .iter()
                .any(|kind| matches!(kind, ArgKind::Cast | ArgKind::SubsingletonInst)) =>
            {
                Err(error(TacticError::ConvUnsupported(
                    "a congruence theorem whose casts cannot be built",
                )))
            }
            None => Ok(None),
        }
    }

    /// `mkCongrSimpCore?.mk?`.
    fn conv_congr_simp_mk(
        &mut self,
        f: &Expr,
        info: &FunInfo,
        kinds: &[ArgKind],
    ) -> Result<Option<CongrTheorem>, NatDefinitionElabError> {
        let mut type_ = self.conv_type(f)?;
        let mut lhss: Vec<LocalDecl> = Vec::new();
        while lhss.len() < kinds.len() {
            self.tick()?;
            if !matches!(type_.node(), ExprNode::ForallE { .. }) {
                type_ = self.whnf(&type_)?;
            }
            let ExprNode::ForallE {
                binder_name,
                binder_type,
                body,
                binder_info,
            } = type_.node()
            else {
                return Ok(None);
            };
            let domain = cleanup(&self.instantiate(binder_type)?);
            let local = self.conv_local(binder_name.clone(), domain, *binder_info)?;
            type_ = self.substitute(body, &Expr::fvar(local.id.clone()))?;
            lhss.push(local);
        }
        let mut hyps: Vec<LocalDecl> = Vec::new();
        let mut rhss: Vec<Expr> = Vec::new();
        let mut eqs: Vec<Option<EqInfo>> = Vec::new();
        for (i, kind) in kinds.iter().enumerate() {
            self.tick()?;
            let lhs = lhss[i].clone();
            match kind {
                ArgKind::Eq => {
                    hyps.push(lhs.clone());
                    let rhs =
                        self.conv_local(lhs.user_name.clone(), lhs.type_.clone(), lhs.binder_info)?;
                    let level = self.conv_level(&lhs.type_)?;
                    let equation = equality::equation(
                        level,
                        lhs.type_.clone(),
                        Expr::fvar(lhs.id.clone()),
                        Expr::fvar(rhs.id.clone()),
                    );
                    let eq = self.conv_local(
                        append_before(&lhs.user_name, "e_"),
                        equation,
                        BinderInfo::Default,
                    )?;
                    rhss.push(Expr::fvar(rhs.id.clone()));
                    eqs.push(Some(EqInfo::Hyp {
                        equation: eq.id.clone(),
                        lhs: lhs.id.clone(),
                        rhs: rhs.id.clone(),
                    }));
                    hyps.push(rhs);
                    hyps.push(eq);
                }
                ArgKind::Fixed => {
                    hyps.push(lhs.clone());
                    rhss.push(Expr::fvar(lhs.id.clone()));
                    eqs.push(None);
                }
                ArgKind::Cast => {
                    hyps.push(lhs.clone());
                    let rhs =
                        self.conv_cast(&lhs, &info.params[i].back_deps, &eqs, &lhss, &rhss)?;
                    rhss.push(rhs);
                    eqs.push(None);
                }
                ArgKind::SubsingletonInst => {
                    // `withImplicitBinderInfos #[lhs]`.
                    let mut implicit = lhs.clone();
                    implicit.binder_info = BinderInfo::Implicit;
                    hyps.push(implicit);
                    let rhs_type = self.conv_replace_locals(&lhs.type_, &lhss[..i], &rhss)?;
                    let rhs =
                        self.conv_local(lhs.user_name.clone(), rhs_type, BinderInfo::Implicit)?;
                    rhss.push(Expr::fvar(rhs.id.clone()));
                    eqs.push(Some(EqInfo::DecSubsingleton));
                    hyps.push(rhs);
                }
            }
        }
        let lhs = lhss.iter().fold(f.clone(), |e, local| {
            Expr::app(e, Expr::fvar(local.id.clone()))
        });
        let rhs = rhss.iter().cloned().fold(f.clone(), Expr::app);
        let alpha = self.conv_type(&lhs)?;
        let level = self.conv_level(&alpha)?;
        let statement =
            self.conv_close_binders(&hyps, equality::equation(level, alpha, lhs, rhs), false)?;
        let proof = self.conv_congr_proof(&statement, kinds)?;
        Ok(Some(CongrTheorem {
            type_: statement,
            proof,
            kinds: kinds.to_vec(),
        }))
    }

    /// `type_` with the locals `from` replaced by `to` (`replaceFVars`).
    fn conv_replace_locals(
        &mut self,
        type_: &Expr,
        from: &[LocalDecl],
        to: &[Expr],
    ) -> Result<Expr, NatDefinitionElabError> {
        let mut result = type_.clone();
        for (local, replacement) in from.iter().zip(to) {
            self.tick()?;
            let abstracted = result
                .abstract_fvar(&local.id, 0)
                .map_err(|_| failure(SourceInferenceError::Scope))?;
            result = self.substitute(&abstracted, replacement)?;
        }
        Ok(result)
    }

    /// `mkCast`: `lhs`, a proof, transported to its type over the right-hand sides, along the
    /// equations among its dependencies, each by `Eq.ndrec`.
    fn conv_cast(
        &mut self,
        lhs: &LocalDecl,
        deps: &[usize],
        eqs: &[Option<EqInfo>],
        lhss: &[LocalDecl],
        rhss: &[Expr],
    ) -> Result<Expr, NatDefinitionElabError> {
        let mut value = Expr::fvar(lhs.id.clone());
        let mut type_ = lhs.type_.clone();
        for &dep in deps {
            self.tick()?;
            let Some(info) = eqs.get(dep).cloned().flatten() else {
                continue;
            };
            let EqInfo::Hyp {
                equation,
                lhs: from,
                rhs: to,
            } = info
            else {
                return Err(error(TacticError::ConvUnsupported(
                    "a proof cast along a decidability instance",
                )));
            };
            let from_decl = lhss[dep].clone();
            let alpha = from_decl.type_.clone();
            let u2 = self.conv_level(&alpha)?;
            let u1 = self.conv_level(&type_)?;
            let abstracted = type_
                .abstract_fvar(&from, 0)
                .map_err(|_| failure(SourceInferenceError::Scope))?;
            let motive = Expr::lam(
                from_decl.user_name.clone(),
                alpha.clone(),
                abstracted.clone(),
                BinderInfo::Default,
            );
            value = app(
                self.conv_constant(&["Eq", "ndrec"], vec![u1, u2])?,
                [
                    alpha,
                    Expr::fvar(from.clone()),
                    motive,
                    value,
                    Expr::fvar(to.clone()),
                    Expr::fvar(equation),
                ],
            );
            type_ = self.substitute(&abstracted, &Expr::fvar(to))?;
        }
        let _ = rhss;
        Ok(value)
    }

    /// `mkCongrSimpCore?.mkProof`: the statement's proof, by `Eq.rec` on each equation and
    /// `Eq.ndrec` on each `Subsingleton.elim`, down to `Eq.refl`.
    fn conv_congr_proof(
        &mut self,
        statement: &Expr,
        kinds: &[ArgKind],
    ) -> Result<Expr, NatDefinitionElabError> {
        // An explicit worklist: open binders going down, close lambdas coming up.
        enum Frame {
            Lambdas(Vec<LocalDecl>),
            Rec {
                locals: Vec<LocalDecl>,
                motive: Expr,
                equation: Expr,
                alpha: Expr,
                lhs: Expr,
                rhs: Expr,
                levels: Vec<Level>,
                dependent: bool,
            },
        }
        let mut frames = Vec::new();
        let mut type_ = statement.clone();
        let mut proof = None;
        for kind in kinds.iter().chain(std::iter::once(&ArgKind::Fixed)) {
            self.tick()?;
            if frames.len() == kinds.len() {
                let (_, _, lhs, _) =
                    equality_target(&type_).ok_or_else(|| failure(SourceInferenceError::Scope))?;
                proof = Some(self.conv_eq_refl(&lhs)?);
                break;
            }
            let lhs = self.conv_open_binder(&mut type_)?;
            match kind {
                ArgKind::Fixed | ArgKind::Cast => frames.push(Frame::Lambdas(vec![lhs])),
                ArgKind::Eq => {
                    // `type.bindingBody!.bindingBody!.instantiate #[Eq.refl lhs, lhs]`.
                    let refl = self.conv_eq_refl(&Expr::fvar(lhs.id.clone()))?;
                    let rest = match type_.node() {
                        ExprNode::ForallE { body, .. } => match body.node() {
                            ExprNode::ForallE { body, .. } => body.clone(),
                            _ => return Err(failure(SourceInferenceError::Scope)),
                        },
                        _ => return Err(failure(SourceInferenceError::Scope)),
                    };
                    let sub = rest
                        .subst_loose(0, &[Expr::fvar(lhs.id.clone()), refl])
                        .map_err(|_| failure(SourceInferenceError::Scope))?;
                    let rhs = self.conv_open_binder(&mut type_)?;
                    let equation = self.conv_open_binder(&mut type_)?;
                    let motive = self.conv_close_binders(
                        &[rhs.clone(), equation.clone()],
                        type_.clone(),
                        true,
                    )?;
                    let alpha = lhs.type_.clone();
                    let u2 = self.conv_level(&alpha)?;
                    let u1 = self.conv_level(&type_)?;
                    frames.push(Frame::Rec {
                        locals: vec![lhs.clone(), rhs.clone(), equation.clone()],
                        motive,
                        equation: Expr::fvar(equation.id.clone()),
                        alpha,
                        lhs: Expr::fvar(lhs.id.clone()),
                        rhs: Expr::fvar(rhs.id.clone()),
                        levels: vec![u1, u2],
                        dependent: true,
                    });
                    type_ = sub;
                }
                ArgKind::SubsingletonInst => {
                    let rest = match type_.node() {
                        ExprNode::ForallE { body, .. } => body.clone(),
                        _ => return Err(failure(SourceInferenceError::Scope)),
                    };
                    let sub = self.substitute(&rest, &Expr::fvar(lhs.id.clone()))?;
                    let rhs = self.conv_open_binder(&mut type_)?;
                    let motive =
                        self.conv_close_binders(std::slice::from_ref(&rhs), type_.clone(), true)?;
                    let alpha = lhs.type_.clone();
                    let u2 = self.conv_level(&alpha)?;
                    let u1 = self.conv_level(&type_)?;
                    // `mkAppM ``Subsingleton.elim #[lhs, rhs]`, the instance `Decidable`'s.
                    let proposition = match spine(&cleanup(&alpha)).1.as_slice() {
                        [p] => p.clone(),
                        _ => {
                            return Err(error(TacticError::ConvUnsupported(
                                "a subsingleton instance other than `Decidable p`",
                            )));
                        }
                    };
                    let instance = Expr::app(
                        self.conv_constant(&["instSubsingletonDecidable"], Vec::new())?,
                        proposition,
                    );
                    let equation = app(
                        self.conv_constant(&["Subsingleton", "elim"], vec![u2.clone()])?,
                        [
                            alpha.clone(),
                            instance,
                            Expr::fvar(lhs.id.clone()),
                            Expr::fvar(rhs.id.clone()),
                        ],
                    );
                    frames.push(Frame::Rec {
                        locals: vec![lhs.clone(), rhs.clone()],
                        motive,
                        equation,
                        alpha,
                        lhs: Expr::fvar(lhs.id.clone()),
                        rhs: Expr::fvar(rhs.id.clone()),
                        levels: vec![u1, u2],
                        dependent: false,
                    });
                    type_ = sub;
                }
            }
        }
        let mut proof = proof.ok_or_else(|| failure(SourceInferenceError::Scope))?;
        while let Some(frame) = frames.pop() {
            self.tick()?;
            match frame {
                Frame::Lambdas(locals) => {
                    proof = self.conv_close_binders(&locals, proof, true)?;
                }
                Frame::Rec {
                    locals,
                    motive,
                    equation,
                    alpha,
                    lhs,
                    rhs,
                    levels,
                    dependent,
                } => {
                    let recursor = if dependent {
                        self.conv_constant(&["Eq", "rec"], levels)?
                    } else {
                        self.conv_constant(&["Eq", "ndrec"], levels)?
                    };
                    let body = app(recursor, [alpha, lhs, motive, proof, rhs, equation]);
                    proof = self.conv_close_binders(&locals, body, true)?;
                }
            }
        }
        Ok(proof)
    }

    /// The first binder of `*type_` as a fresh local of the current context; `*type_` becomes
    /// its body over that local (`withNext`).
    fn conv_open_binder(&mut self, type_: &mut Expr) -> Result<LocalDecl, NatDefinitionElabError> {
        let ExprNode::ForallE {
            binder_name,
            binder_type,
            body,
            binder_info,
        } = type_.node()
        else {
            return Err(failure(SourceInferenceError::Scope));
        };
        let (name, domain, body, info) = (
            binder_name.clone(),
            cleanup(binder_type),
            body.clone(),
            *binder_info,
        );
        let local = self.conv_local(name, domain, info)?;
        *type_ = self.substitute(&body, &Expr::fvar(local.id.clone()))?;
        Ok(local)
    }

    /// `Meta.mkCongrFun h a` for `h : f = g`: `congrFun h a : f a = g a`.
    pub(super) fn conv_congr_fun(
        &mut self,
        proof: Expr,
        f: &Expr,
        g: &Expr,
        argument: &Expr,
    ) -> Result<Expr, NatDefinitionElabError> {
        if is_app_of(&proof, &["Eq", "refl"]) {
            return self.conv_eq_refl(&Expr::app(f.clone(), argument.clone()));
        }
        let rho = self.conv_type(f)?;
        let rho = self.whnf(&rho)?;
        let ExprNode::ForallE {
            binder_name,
            binder_type,
            body,
            ..
        } = rho.node()
        else {
            return Err(error(TacticError::ConvFailure(
                "equality proof between functions expected".to_owned(),
            )));
        };
        let u = self.conv_level(binder_type)?;
        let codomain = self.substitute(body, argument)?;
        let v = self.conv_level(&codomain)?;
        let beta = Expr::lam(
            binder_name.clone(),
            binder_type.clone(),
            body.clone(),
            BinderInfo::Default,
        );
        Ok(app(
            self.conv_constant(&["congrFun"], vec![u, v])?,
            [
                binder_type.clone(),
                beta,
                f.clone(),
                g.clone(),
                proof,
                argument.clone(),
            ],
        ))
    }

    /// The statement `type_` instantiated by `arguments` (`instantiateForall`).
    fn conv_instantiate_forall(
        &mut self,
        mut type_: Expr,
        arguments: &[Expr],
    ) -> Result<Expr, NatDefinitionElabError> {
        for argument in arguments {
            self.tick()?;
            let ExprNode::ForallE { body, .. } = type_.node() else {
                return Err(failure(SourceInferenceError::Scope));
            };
            let body = body.clone();
            type_ = self.substitute(&body, argument)?;
        }
        Ok(type_)
    }

    /// `mkCongrThm origTag f args addImplicitArgs nameSubgoals` (`Conv/Congr.lean`), with
    /// `addImplicitArgs := false` and `nameSubgoals := true`.
    fn conv_congr_theorem(
        &mut self,
        tag: &Name,
        f: &Expr,
        args: &[Expr],
    ) -> Result<Applied, NatDefinitionElabError> {
        let info = self.conv_fun_info(f, args.len())?;
        let kinds = self.conv_congr_simp_kinds(f, &info)?;
        let theorem = self.conv_congr_simp_core(f, &info, kinds)?.ok_or_else(|| {
            error(TacticError::ConvFailure(
                "'congr' conv tactic failed to create congruence theorem".to_owned(),
            ))
        })?;
        let arity = theorem.kinds.len();
        let mut e_new = f.clone();
        let mut proof = theorem.proof.clone();
        let mut type_ = theorem.type_.clone();
        let mut goals = Vec::new();
        let mut instances = Vec::new();
        let mut applied = Vec::new();
        for i in 0..arity {
            self.tick()?;
            let arg = args[i].clone();
            let explicit = info.params[i].is_explicit();
            match theorem.kinds[i] {
                ArgKind::Fixed | ArgKind::Cast => {
                    e_new = Expr::app(e_new, arg.clone());
                    proof = Expr::app(proof, arg.clone());
                    applied.push(arg);
                    if explicit {
                        goals.push(None);
                    }
                }
                ArgKind::Eq => {
                    if explicit {
                        let binder = match type_.node() {
                            ExprNode::ForallE { binder_name, .. } => binder_name.clone(),
                            _ => return Err(failure(SourceInferenceError::Scope)),
                        };
                        // `appendTag origTag n` erases `n`'s macro scopes.
                        let child_tag =
                            crate::source::trace::append_tag(tag, &binder.erase_macro_scopes());
                        let (rhs, hole, goal) = self.conv_goal_for(&arg, &child_tag)?;
                        e_new = Expr::app(e_new, rhs.clone());
                        proof = app(proof, [arg.clone(), rhs.clone(), hole.clone()]);
                        applied.extend([arg, rhs, hole]);
                        goals.push(Some(goal));
                    } else {
                        let refl = self.conv_eq_refl(&arg)?;
                        e_new = Expr::app(e_new, arg.clone());
                        proof = app(proof, [arg.clone(), arg.clone(), refl.clone()]);
                        applied.extend([arg.clone(), arg, refl]);
                    }
                }
                ArgKind::SubsingletonInst => {
                    proof = Expr::app(proof, arg.clone());
                    applied.push(arg);
                    let partial = self.conv_instantiate_forall(type_.clone(), &applied)?;
                    let domain = match partial.node() {
                        ExprNode::ForallE { binder_type, .. } => binder_type.clone(),
                        _ => return Err(failure(SourceInferenceError::Scope)),
                    };
                    let (hole, goal) = self.proof_goal(domain)?;
                    e_new = Expr::app(e_new, hole.clone());
                    proof = Expr::app(proof, hole.clone());
                    applied.push(hole);
                    instances.push(goal);
                }
            }
            // Keep `type_` positioned at the next lhs binder (for its name).
            type_ = self.conv_instantiate_forall(theorem.type_.clone(), &applied)?;
        }
        let statement = self.conv_instantiate_forall(theorem.type_.clone(), &applied)?;
        let (level, alpha, mut lhs_now, mut rhs_now) =
            equality_target(&statement).ok_or_else(|| failure(SourceInferenceError::Scope))?;
        if arity < args.len() {
            if arity == 0 {
                return Err(error(TacticError::ConvFailure(
                    "'congr' conv tactic failed to create congruence theorem".to_owned(),
                )));
            }
            let rest = &args[info.params.len()..];
            let inner = self.conv_congr_theorem(tag, &e_new, rest)?;
            for arg in rest {
                self.tick()?;
                proof = self.conv_congr_fun(proof, &lhs_now, &rhs_now, arg)?;
                lhs_now = Expr::app(lhs_now, arg.clone());
                rhs_now = Expr::app(rhs_now, arg.clone());
            }
            let alpha = self.conv_type(&lhs_now)?;
            let level = self.conv_level(&alpha)?;
            proof = self.conv_eq_trans(
                &level,
                &alpha,
                [&lhs_now, &rhs_now, &inner.rhs],
                proof,
                inner.proof,
            )?;
            goals.extend(inner.goals);
            instances.extend(inner.instances);
            rhs_now = inner.rhs;
        }
        let _ = (level, alpha);
        Ok(Applied {
            proof,
            rhs: rhs_now,
            goals,
            instances,
        })
    }

    /// The conv navigation tactics on `goal`.
    pub(super) fn conv_navigate(
        &mut self,
        proof: &mut ProofState<'_>,
        goal: ProofGoal,
        tactic: &str,
        args: &[Syntax],
    ) -> Result<(), NatDefinitionElabError> {
        let mut deferred = Vec::new();
        let goals = match tactic {
            "lhs" | "convLeft" => self.conv_arg(goal, "lhs", -2, false, &mut deferred)?,
            "rhs" | "convRight" => self.conv_arg(goal, "rhs", -1, false, &mut deferred)?,
            "arg" => {
                let [keyword, argument] = args else {
                    return Err(error(TacticError::MalformedScript));
                };
                expect_atom(keyword, "arg", "arg keyword")?;
                let (index, explicit) = arg_index(argument)?;
                self.conv_arg(goal, "arg", index, explicit, &mut deferred)?
            }
            "congr" | "convArgs" => self.conv_congr(goal)?,
            "fun" => self.conv_fun(goal)?,
            "ext" | "convIntro___" => {
                let [_, names] = args else {
                    return Err(error(TacticError::MalformedScript));
                };
                let names = expect_null_args(names, "ext names")?;
                let mut goal = goal;
                if names.is_empty() {
                    goal = self.conv_ext(goal, None, &mut deferred)?;
                } else {
                    for name in names {
                        self.tick()?;
                        goal = self.conv_ext(goal, binder_name(name)?, &mut deferred)?;
                    }
                }
                vec![goal]
            }
            "enter" => {
                let [keyword, open, entries, close] = args else {
                    return Err(error(TacticError::MalformedScript));
                };
                expect_atom(keyword, "enter", "enter keyword")?;
                expect_atom(open, "[", "enter bracket")?;
                expect_atom(close, "]", "enter bracket")?;
                let mut goals = vec![goal];
                for (index, entry) in expect_null_args(entries, "enter arguments")?
                    .iter()
                    .enumerate()
                {
                    self.tick()?;
                    if index % 2 == 1 {
                        expect_atom(entry, ",", "enter separator")?;
                        continue;
                    }
                    let [inner] = expect_node(entry, &conv_kind("enterArg"), 1, "enter argument")?
                    else {
                        return Err(error(TacticError::MalformedScript));
                    };
                    let mut rest = goals.split_off(1);
                    let main = goals.pop().ok_or_else(|| no_goals(Some(inner)))?;
                    let mut produced = if inner.kind() == Some(&conv_kind("argArg")) {
                        let (index, explicit) = arg_index(inner)?;
                        self.conv_arg(main, "arg", index, explicit, &mut deferred)?
                    } else if inner.kind() == Some(&Name::from_components(["Lean", "binderIdent"]))
                    {
                        vec![self.conv_ext(main, binder_name(inner)?, &mut deferred)?]
                    } else if inner.kind() == Some(&conv_kind("enterPattern")) {
                        let [keyword, occs, term] =
                            expect_node(inner, &conv_kind("enterPattern"), 3, "enter pattern")?
                        else {
                            return Err(error(TacticError::MalformedScript));
                        };
                        expect_atom(keyword, "in", "enter pattern keyword")?;
                        // `pattern`'s own work: its goals, then its deferred closes.
                        let mut work = self.conv_pattern(main, occs, term)?;
                        let split = work
                            .iter()
                            .position(|w| !matches!(w, Work::Goal(_)))
                            .unwrap_or(work.len());
                        let closes = work.split_off(split);
                        deferred.extend(closes.into_iter().map(|w| match w {
                            Work::Close(goal, value) => Work::Close(goal, value),
                            _ => unreachable!("pattern defers closes only"),
                        }));
                        work.into_iter()
                            .map(|w| match w {
                                Work::Goal(goal) => goal,
                                _ => unreachable!("pattern goals"),
                            })
                            .collect()
                    } else {
                        return Err(error(TacticError::MalformedScript));
                    };
                    produced.append(&mut rest);
                    goals = produced;
                }
                goals
            }
            _ => return Err(error(TacticError::MalformedScript)),
        };
        // Deferred closes run after every goal above them, the latest (innermost) first: an
        // outer close abstracts its binder over what an inner one assigns.
        proof.work.extend(deferred);
        proof.work.extend(goals.into_iter().rev().map(Work::Goal));
        Ok(())
    }

    /// `congr` (`Conv.congr`): one goal per explicit argument the congruence theorem rewrites,
    /// then its instance goals; an implication splits by `implies_congr`.
    fn conv_congr(&mut self, goal: ProofGoal) -> Result<Vec<ProofGoal>, NatDefinitionElabError> {
        let tag = self
            .goal_tags
            .get(&goal.id)
            .cloned()
            .unwrap_or_else(Name::anonymous);
        let (_, _, lhs, rhs) = self.conv_sides(&goal)?;
        self.txn.lctx = goal.lctx.clone();
        let lhs = cleanup(&self.instantiate(&lhs)?);
        if self.conv_is_implies(&lhs)? {
            return self.conv_congr_implies(goal, &lhs, &rhs);
        }
        if !matches!(lhs.node(), ExprNode::App { .. }) {
            return Err(error(TacticError::ConvFailure(
                "invalid 'congr' conv tactic, application or implication expected".to_owned(),
            )));
        }
        let (f, args) = spine(&lhs);
        let applied = self.conv_congr_theorem(&tag, &f, &args)?;
        if !self.conv_resolve_rhs(&rhs, &applied.rhs)? {
            return Err(error(TacticError::ConvFailure(
                "invalid `congr` conv tactic, failed to resolve".to_owned(),
            )));
        }
        self.conv_goals.remove(&goal.id);
        self.conv_close(goal, applied.proof)?;
        let mut goals: Vec<ProofGoal> = applied.goals.into_iter().flatten().collect();
        goals.extend(applied.instances);
        Ok(goals)
    }

    /// `isImplies e`: a non-dependent arrow between propositions.
    fn conv_is_implies(&mut self, lhs: &Expr) -> Result<bool, NatDefinitionElabError> {
        let ExprNode::ForallE {
            binder_type, body, ..
        } = lhs.node()
        else {
            return Ok(false);
        };
        if body.has_loose_bvar(0) {
            return Ok(false);
        }
        let body = body
            .subst_loose(0, &[Expr::sort(Level::zero())])
            .map_err(|_| failure(SourceInferenceError::Scope))?;
        Ok(self.conv_is_prop(binder_type)? && self.conv_is_prop(&body)?)
    }

    /// `congrImplies`: `apply implies_congr`, its two equations marked as conv goals.
    fn conv_congr_implies(
        &mut self,
        goal: ProofGoal,
        lhs: &Expr,
        rhs: &Expr,
    ) -> Result<Vec<ProofGoal>, NatDefinitionElabError> {
        let ExprNode::ForallE {
            binder_type, body, ..
        } = lhs.node()
        else {
            return Err(error(TacticError::ConvInvalidGoal));
        };
        let premise = binder_type.clone();
        let conclusion = body
            .subst_loose(0, &[Expr::sort(Level::zero())])
            .map_err(|_| failure(SourceInferenceError::Scope))?;
        let u = self.conv_level(&premise)?;
        let v = self.conv_level(&conclusion)?;
        let (p2, h1_hole, h1) = self.conv_goal_for(&premise, &Name::from_components(["h₁"]))?;
        let (q2, h2_hole, h2) = self.conv_goal_for(&conclusion, &Name::from_components(["h₂"]))?;
        let arrow = Expr::forall_e(
            Name::anonymous(),
            p2.clone(),
            q2.clone()
                .lift_loose(0, 1)
                .map_err(|_| failure(SourceInferenceError::Scope))?,
            BinderInfo::Default,
        );
        if !self.conv_resolve_rhs(rhs, &arrow)? {
            return Err(error(TacticError::ConvFailure(
                "'apply implies_congr' unexpected result".to_owned(),
            )));
        }
        // `markAsConvGoal` gives each its `id` type hint.
        let hint1 = self.conv_id_hint(&h1, h1_hole)?;
        let hint2 = self.conv_id_hint(&h2, h2_hole)?;
        let value = app(
            self.conv_constant(&["implies_congr"], vec![u, v])?,
            [premise, p2, conclusion, q2, hint1, hint2],
        );
        self.conv_goals.remove(&goal.id);
        self.conv_close(goal, value)?;
        Ok(vec![h1, h2])
    }

    /// `@id T hole`, `T` the goal's target (`mkExpectedTypeHint`, as `replaceTargetDefEq`).
    fn conv_id_hint(
        &mut self,
        goal: &ProofGoal,
        hole: Expr,
    ) -> Result<Expr, NatDefinitionElabError> {
        let target = self.instantiate(&goal.target)?;
        Ok(app(
            self.conv_constant(&["id"], vec![Level::zero()])?,
            [target, hole],
        ))
    }

    /// `arg i`, `arg @i`, `lhs` (`arg -2`) and `rhs` (`arg -1`) (`Conv.evalArg`).
    fn conv_arg<'w>(
        &mut self,
        goal: ProofGoal,
        tactic: &str,
        index: i64,
        explicit: bool,
        deferred: &mut Vec<Work<'w>>,
    ) -> Result<Vec<ProofGoal>, NatDefinitionElabError> {
        if index == 0 {
            return Ok(vec![self.conv_arg_zero(goal)?]);
        }
        let tag = self
            .goal_tags
            .get(&goal.id)
            .cloned()
            .unwrap_or_else(Name::anonymous);
        let (_, _, lhs, rhs) = self.conv_sides(&goal)?;
        self.txn.lctx = goal.lctx.clone();
        let lhs = cleanup(&self.instantiate(&lhs)?);
        if matches!(lhs.node(), ExprNode::ForallE { .. }) {
            if !(-2..=2).contains(&index) {
                return Err(error(TacticError::ConvFailure(format!(
                    "invalid `{tactic}` conv tactic, index is out of bounds for pi type"
                ))));
            }
            let domain = index == 1 || index == -2;
            return self.conv_arg_forall(goal, tactic, domain, &lhs, &rhs, &tag, deferred);
        }
        if !matches!(lhs.node(), ExprNode::App { .. }) {
            return Err(error(TacticError::ConvFailure(format!(
                "invalid `{tactic}` conv tactic, application or implication expected"
            ))));
        }
        let (f, xs) = spine(&lhs);
        let (f, xs) = self.conv_apply_args(tactic, &f, &xs, index, explicit)?;
        // `mkCongrArgZeroThm`.
        let info = self.conv_fun_info(&f, xs.len())?;
        let kinds = self.conv_congr_simp_kinds_arg_zero(&info);
        let theorem = self
            .conv_congr_simp_core(&f, &info, kinds)?
            .ok_or_else(|| {
                error(TacticError::ConvFailure(format!(
                    "`{tactic}` conv tactic failed to create congruence theorem"
                )))
            })?;
        if theorem.kinds.first() != Some(&ArgKind::Eq) {
            return Err(error(TacticError::ConvFailure(format!(
                "`{tactic}` conv tactic failed, cannot select argument"
            ))));
        }
        let mut proof = theorem.proof.clone();
        let mut applied = Vec::new();
        let mut selected = None;
        let mut instances = Vec::new();
        for (i, kind) in theorem.kinds.iter().enumerate() {
            self.tick()?;
            let arg = xs[i].clone();
            match kind {
                ArgKind::Fixed | ArgKind::Cast => {
                    proof = Expr::app(proof, arg.clone());
                    applied.push(arg);
                }
                ArgKind::Eq => {
                    if selected.is_some() {
                        return Err(error(TacticError::ConvFailure(format!(
                            "`{tactic}` conv tactic failed, cannot select argument"
                        ))));
                    }
                    let (rhs, hole, child) = self.conv_goal_for(&arg, &tag)?;
                    proof = app(proof, [arg.clone(), rhs.clone(), hole.clone()]);
                    applied.extend([arg, rhs, hole]);
                    selected = Some(child);
                }
                ArgKind::SubsingletonInst => {
                    proof = Expr::app(proof, arg.clone());
                    applied.push(arg);
                    let partial = self.conv_instantiate_forall(theorem.type_.clone(), &applied)?;
                    let domain = match partial.node() {
                        ExprNode::ForallE { binder_type, .. } => binder_type.clone(),
                        _ => return Err(failure(SourceInferenceError::Scope)),
                    };
                    let (hole, instance) = self.proof_goal(domain)?;
                    proof = Expr::app(proof, hole.clone());
                    applied.push(hole);
                    instances.push(instance);
                }
            }
        }
        let statement = self.conv_instantiate_forall(theorem.type_.clone(), &applied)?;
        let (_, _, mut lhs_now, mut rhs_now) =
            equality_target(&statement).ok_or_else(|| failure(SourceInferenceError::Scope))?;
        for arg in &xs[theorem.kinds.len()..] {
            self.tick()?;
            proof = self.conv_congr_fun(proof, &lhs_now, &rhs_now, arg)?;
            lhs_now = Expr::app(lhs_now, arg.clone());
            rhs_now = Expr::app(rhs_now, arg.clone());
        }
        if !self.conv_resolve_rhs(&rhs, &rhs_now)? {
            return Err(error(TacticError::ConvFailure(format!(
                "invalid `{tactic}` conv tactic, failed to resolve"
            ))));
        }
        self.conv_goals.remove(&goal.id);
        self.conv_close(goal, proof)?;
        let mut goals = vec![selected.ok_or_else(|| failure(SourceInferenceError::Scope))?];
        goals.extend(instances);
        Ok(goals)
    }

    /// `congrArgN.applyArgs`: the function and the arguments from the selected one on.
    fn conv_apply_args(
        &mut self,
        tactic: &str,
        f: &Expr,
        xs: &[Expr],
        index: i64,
        explicit: bool,
    ) -> Result<(Expr, Vec<Expr>), NatDefinitionElabError> {
        let size =
            i64::try_from(xs.len()).map_err(|_| failure(SourceInferenceError::ResourceLimit))?;
        let position = if explicit {
            let position = if index > 0 { index - 1 } else { index + size };
            if position < 0 || position >= size {
                return Err(error(TacticError::ConvFailure(format!(
                    "invalid `{tactic}` tactic, application has {} argument(s) but the index is out of bounds",
                    xs.len()
                ))));
            }
            usize::try_from(position).map_err(|_| failure(SourceInferenceError::Scope))?
        } else {
            let mut type_ = self.conv_type(f)?;
            let mut explicit_positions = Vec::new();
            for (k, x) in xs.iter().enumerate() {
                self.tick()?;
                if !matches!(type_.node(), ExprNode::ForallE { .. }) {
                    type_ = self.whnf_with_transparency(
                        &type_,
                        UnificationTransparency::SafeDefinitions,
                        true,
                    )?;
                }
                let ExprNode::ForallE {
                    body, binder_info, ..
                } = type_.node()
                else {
                    return Err(error(TacticError::ConvInvalidGoal));
                };
                if *binder_info == BinderInfo::Default {
                    explicit_positions.push(k);
                }
                let body = body.clone();
                type_ = self.substitute(&body, x)?;
            }
            let count = i64::try_from(explicit_positions.len())
                .map_err(|_| failure(SourceInferenceError::ResourceLimit))?;
            let position = if index > 0 { index - 1 } else { index + count };
            if position < 0 || position >= count {
                return Err(error(TacticError::ConvFailure(format!(
                    "invalid `{tactic}` tactic, application has {} explicit argument(s) but the index is out of bounds",
                    explicit_positions.len()
                ))));
            }
            explicit_positions
                [usize::try_from(position).map_err(|_| failure(SourceInferenceError::Scope))?]
        };
        let head = xs[..position].iter().cloned().fold(f.clone(), Expr::app);
        Ok((head, xs[position..].to_vec()))
    }

    /// `arg i` on a `∀` (`congrArgForall`): its domain by `implies_congr` or
    /// `forall_prop_congr_dom`, its codomain by `pi_congr`.
    #[allow(clippy::too_many_arguments)]
    fn conv_arg_forall<'w>(
        &mut self,
        goal: ProofGoal,
        tactic: &str,
        domain: bool,
        lhs: &Expr,
        rhs: &Expr,
        tag: &Name,
        deferred: &mut Vec<Work<'w>>,
    ) -> Result<Vec<ProofGoal>, NatDefinitionElabError> {
        let ExprNode::ForallE {
            binder_name,
            binder_type,
            body,
            binder_info,
        } = lhs.node()
        else {
            return Err(error(TacticError::ConvInvalidGoal));
        };
        let (name, t, b, bi) = (
            binder_name.clone(),
            binder_type.clone(),
            body.clone(),
            *binder_info,
        );
        if domain {
            if !b.has_loose_bvars() {
                let (t2, hole, child) = self.conv_goal_for(&t, tag)?;
                let body_level = self.conv_level(&b)?;
                let u = self.conv_level(&t)?;
                let refl = self.conv_eq_refl(&b)?;
                let value = app(
                    self.conv_constant(&["implies_congr"], vec![u, body_level])?,
                    [t.clone(), t2.clone(), b.clone(), b.clone(), hole, refl],
                );
                if !self.conv_resolve_rhs(rhs, &Expr::forall_e(name, t2, b, bi))? {
                    return Err(error(TacticError::ConvFailure(format!(
                        "invalid `{tactic}` conv tactic, failed to resolve"
                    ))));
                }
                self.conv_goals.remove(&goal.id);
                self.conv_close(goal, value)?;
                return Ok(vec![child]);
            }
            let local = self.conv_local(name.clone(), t.clone(), bi)?;
            let opened = self.substitute(&b, &Expr::fvar(local.id.clone()))?;
            let body_is_prop = self.conv_is_prop(&opened)?;
            self.txn.lctx = goal.lctx.clone();
            if body_is_prop && self.conv_is_prop(lhs)? {
                let (t2, hole, child) = self.conv_goal_for(&t, tag)?;
                let family = Expr::lam(name, t.clone(), b, BinderInfo::Default);
                let theorem = self.conv_constant(&["forall_prop_congr_dom"], Vec::new())?;
                let statement = self.conv_constant_type(&["forall_prop_congr_dom"], &[])?;
                let arguments = [t.clone(), t2, hole, family];
                let instantiated = self.conv_instantiate_forall_beta(statement, &arguments)?;
                let value = arguments.into_iter().fold(theorem, Expr::app);
                let (_, _, _, rhs_new) = equality_target(&instantiated)
                    .ok_or_else(|| failure(SourceInferenceError::Scope))?;
                if !self.conv_resolve_rhs(rhs, &rhs_new)? {
                    return Err(error(TacticError::ConvFailure(format!(
                        "invalid `{tactic}` conv tactic, failed to resolve"
                    ))));
                }
                self.conv_goals.remove(&goal.id);
                self.conv_close(goal, value)?;
                return Ok(vec![child]);
            }
            return Err(error(TacticError::ConvFailure(format!(
                "`{tactic}` conv tactic failed, cannot select domain"
            ))));
        }
        // The codomain, under a fresh `n✝` (`mkFreshUserName n`).
        let u = self.conv_level(&t)?;
        let fresh = self.fresh_inaccessible(&name)?;
        let parent_lctx = self.txn.lctx.clone();
        let local = self.conv_local(fresh, t.clone(), BinderInfo::Default)?;
        let extended = self.txn.lctx.clone();
        let q = self.substitute(&b, &Expr::fvar(local.id.clone()))?;
        let v = self.conv_level(&q)?;
        let (q2, hole, child) = self.conv_goal_for(&q, tag)?;
        // `q' := fun x => ?q` and `h := fun x => ?goal`, both once the goal is solved.
        let q2_type =
            self.conv_close_binders(std::slice::from_ref(&local), Expr::sort(v.clone()), false)?;
        let family = self.conv_lift(
            deferred,
            &extended,
            std::slice::from_ref(&local),
            q2,
            q2_type,
        )?;
        let applied = Expr::app(family.clone(), Expr::fvar(local.id.clone()));
        let equation = equality::equation(
            v.clone()
                .succ()
                .map_err(|_| failure(SourceInferenceError::Scope))?,
            Expr::sort(v.clone()),
            q.clone(),
            applied,
        );
        let h_type = self.conv_close_binders(std::slice::from_ref(&local), equation, false)?;
        let h = self.conv_lift(
            deferred,
            &extended,
            std::slice::from_ref(&local),
            hole,
            h_type,
        )?;
        self.txn.lctx = parent_lctx;
        let original = Expr::lam(name, t.clone(), b, BinderInfo::Default);
        let theorem = self.conv_constant(&["pi_congr"], vec![u.clone(), v.clone()])?;
        let statement = self.conv_constant_type(&["pi_congr"], &[u, v])?;
        let arguments = [t, original, family, h];
        let instantiated = self.conv_instantiate_forall_beta(statement, &arguments)?;
        let value = arguments.into_iter().fold(theorem, Expr::app);
        let (_, _, _, rhs_new) =
            equality_target(&instantiated).ok_or_else(|| failure(SourceInferenceError::Scope))?;
        if !self.conv_resolve_rhs(rhs, &rhs_new)? {
            return Err(error(TacticError::ConvFailure(format!(
                "invalid `{tactic}` conv tactic, failed to resolve"
            ))));
        }
        self.conv_goals.remove(&goal.id);
        self.conv_close(goal, value)?;
        Ok(vec![child])
    }

    /// A theorem's statement at the universe `levels`.
    fn conv_constant_type(
        &mut self,
        name: &[&str],
        levels: &[Level],
    ) -> Result<Expr, NatDefinitionElabError> {
        let constant = Name::from_components(name.iter().copied());
        let info = self
            .txn
            .env
            .find(&constant)
            .cloned()
            .ok_or_else(|| failure(SourceInferenceError::UnknownConstant(constant.clone())))?;
        let base = info.constant_val();
        self.instantiate_params(&base.type_, &base.level_params, levels)
    }

    /// `instantiateForall` with the beta-reduction of `inferType` (`instantiateBetaRevRange`):
    /// an argument that is a `fun`, substituted at the head of an application, is reduced.
    fn conv_instantiate_forall_beta(
        &mut self,
        statement: Expr,
        arguments: &[Expr],
    ) -> Result<Expr, NatDefinitionElabError> {
        let mut type_ = statement;
        for argument in arguments {
            self.tick()?;
            let ExprNode::ForallE { body, .. } = type_.node() else {
                return Err(failure(SourceInferenceError::Scope));
            };
            let body = body.clone();
            type_ = self.substitute(&body, argument)?;
            if matches!(argument.node(), ExprNode::Lam { .. }) {
                type_ = self.conv_beta_at(&type_, argument)?;
            }
        }
        Ok(type_)
    }

    /// Every beta-redex of `root` reduced (`root` instantiated).
    fn conv_beta_all(&mut self, root: &Expr) -> Result<Expr, NatDefinitionElabError> {
        let root = self.instantiate(root)?;
        self.conv_beta_where(&root, None)
    }

    /// Every application in `root` whose head is (the allocation of) `function` beta-reduced.
    fn conv_beta_at(
        &mut self,
        root: &Expr,
        function: &Expr,
    ) -> Result<Expr, NatDefinitionElabError> {
        self.conv_beta_where(root, Some(function.allocation_identity()))
    }

    /// The redexes of `root` whose head is the allocation `target` (any, for `None`) reduced.
    fn conv_beta_where(
        &mut self,
        root: &Expr,
        target: Option<usize>,
    ) -> Result<Expr, NatDefinitionElabError> {
        let mut done = std::collections::HashMap::<usize, Expr>::new();
        let mut keep = Vec::new();
        let mut work = vec![(root.clone(), false)];
        while let Some((term, exit)) = work.pop() {
            let key = term.allocation_identity();
            if done.contains_key(&key) {
                continue;
            }
            self.tick()?;
            let children: Vec<Expr> = match term.node() {
                ExprNode::App { f, a } => vec![f.clone(), a.clone()],
                ExprNode::Lam {
                    binder_type, body, ..
                }
                | ExprNode::ForallE {
                    binder_type, body, ..
                } => vec![binder_type.clone(), body.clone()],
                ExprNode::LetE {
                    type_, value, body, ..
                } => vec![type_.clone(), value.clone(), body.clone()],
                ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => vec![expr.clone()],
                _ => Vec::new(),
            };
            if !exit
                && children
                    .iter()
                    .any(|c| !done.contains_key(&c.allocation_identity()))
            {
                work.push((term.clone(), true));
                for child in children.into_iter().rev() {
                    work.push((child, false));
                }
                continue;
            }
            let get = |e: &Expr| done[&e.allocation_identity()].clone();
            let result = match term.node() {
                ExprNode::App { f, a } => {
                    let (head, _) = spine(&term);
                    let rebuilt = Expr::app(get(f), get(a));
                    let reduce = match target {
                        Some(target) => head.allocation_identity() == target,
                        None => {
                            let (rebuilt_head, _) = spine(&rebuilt);
                            matches!(rebuilt_head.node(), ExprNode::Lam { .. })
                        }
                    };
                    if reduce {
                        self.head_beta(rebuilt)?
                    } else {
                        rebuilt
                    }
                }
                ExprNode::Lam {
                    binder_name,
                    binder_type,
                    body,
                    binder_info,
                } => Expr::lam(
                    binder_name.clone(),
                    get(binder_type),
                    get(body),
                    *binder_info,
                ),
                ExprNode::ForallE {
                    binder_name,
                    binder_type,
                    body,
                    binder_info,
                } => Expr::forall_e(
                    binder_name.clone(),
                    get(binder_type),
                    get(body),
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
                    get(type_),
                    get(value),
                    get(body),
                    *non_dep,
                ),
                ExprNode::MData { data, expr } => Expr::mdata(data.clone(), get(expr)),
                ExprNode::Proj {
                    struct_name,
                    idx,
                    expr,
                } => Expr::proj(struct_name.clone(), *idx, get(expr)),
                _ => term.clone(),
            };
            done.insert(key, result);
            keep.push(term);
        }
        Ok(done[&root.allocation_identity()].clone())
    }

    /// `arg 0` (`congrFunN`): the function of the application.
    fn conv_arg_zero(&mut self, goal: ProofGoal) -> Result<ProofGoal, NatDefinitionElabError> {
        let (_, _, lhs, rhs) = self.conv_sides(&goal)?;
        self.txn.lctx = goal.lctx.clone();
        let lhs = cleanup(&self.instantiate(&lhs)?);
        if !matches!(lhs.node(), ExprNode::App { .. }) {
            return Err(error(TacticError::ConvFailure(
                "invalid 'arg 0' conv tactic, application expected".to_owned(),
            )));
        }
        let (f, xs) = spine(&lhs);
        let (g, hole, child) = self.conv_goal_for(&f, &Name::anonymous())?;
        let mut proof = hole;
        let mut left = f.clone();
        let mut right = g.clone();
        for x in &xs {
            self.tick()?;
            proof = self.conv_congr_fun(proof, &left, &right, x)?;
            left = Expr::app(left, x.clone());
            right = Expr::app(right, x.clone());
        }
        if !self.conv_resolve_rhs(&rhs, &right)? {
            return Err(error(TacticError::ConvFailure(
                "invalid `arg 0` conv tactic, failed to resolve".to_owned(),
            )));
        }
        self.conv_goals.remove(&goal.id);
        self.conv_close(goal, proof)?;
        Ok(child)
    }

    /// `fun` (`Conv.evalFun`): `f a` becomes `f`.
    fn conv_fun(&mut self, goal: ProofGoal) -> Result<Vec<ProofGoal>, NatDefinitionElabError> {
        let (_, _, lhs, rhs) = self.conv_sides(&goal)?;
        self.txn.lctx = goal.lctx.clone();
        let lhs = cleanup(&self.instantiate(&lhs)?);
        let ExprNode::App { f, a } = lhs.node() else {
            return Err(error(TacticError::ConvFailure(
                "invalid 'fun' conv tactic, application expected".to_owned(),
            )));
        };
        let (f, a) = (f.clone(), a.clone());
        let (g, hole, child) = self.conv_goal_for(&f, &Name::anonymous())?;
        let proof = self.conv_congr_fun(hole, &f, &g, &a)?;
        if !self.conv_resolve_rhs(&rhs, &Expr::app(g, a))? {
            return Err(error(TacticError::ConvFailure(
                "invalid `fun` conv tactic, failed to resolve".to_owned(),
            )));
        }
        self.conv_goals.remove(&goal.id);
        self.conv_close(goal, proof)?;
        Ok(vec![child])
    }

    /// `ext x` (`extCore`): into a `∀` by `forall_congr`, into a `let` by `let_body_congr`, into
    /// a function by `funext`.
    fn conv_ext<'w>(
        &mut self,
        goal: ProofGoal,
        name: Option<Name>,
        deferred: &mut Vec<Work<'w>>,
    ) -> Result<ProofGoal, NatDefinitionElabError> {
        let (_, _, lhs, rhs) = self.conv_sides(&goal)?;
        self.txn.lctx = goal.lctx.clone();
        let parent_lctx = goal.lctx.clone();
        let lhs = cleanup(&self.instantiate(&lhs)?);
        let rhs = self.instantiate(&rhs)?;
        if !matches!(rhs.node(), ExprNode::MVar { id } if !self.txn.mvars.is_assigned(id)) {
            return Err(error(TacticError::ConvUnsupported(
                "`ext` on a conv goal whose right-hand side is already known",
            )));
        }
        if let ExprNode::ForallE {
            binder_name,
            binder_type,
            body,
            binder_info,
        } = lhs.node()
        {
            let (n, d, b, bi) = (
                binder_name.clone(),
                binder_type.clone(),
                body.clone(),
                *binder_info,
            );
            // `forall_congr` is about propositions; the pin's term for any other `∀` fails.
            if !self.conv_is_prop(&lhs)? {
                return Err(error(TacticError::ConvUnsupported(
                    "`ext` into a `∀` that is not a proposition",
                )));
            }
            let u = self.conv_level(&d)?;
            let user = match name {
                Some(name) => name,
                None => self.fresh_inaccessible(&n)?,
            };
            let local = self.conv_local(user, d.clone(), bi)?;
            let extended = self.txn.lctx.clone();
            let pa = self.substitute(&b, &Expr::fvar(local.id.clone()))?;
            let (qa, hole, child) = self.conv_goal_for(&pa, &Name::anonymous())?;
            let q_type = self.conv_close_binders(
                std::slice::from_ref(&local),
                Expr::sort(Level::zero()),
                false,
            )?;
            let q = self.conv_lift(
                deferred,
                &extended,
                std::slice::from_ref(&local),
                qa,
                q_type,
            )?;
            let applied = Expr::app(q.clone(), Expr::fvar(local.id.clone()));
            let equation = equality::equation(
                Level::zero()
                    .succ()
                    .map_err(|_| failure(SourceInferenceError::Scope))?,
                Expr::sort(Level::zero()),
                pa,
                applied.clone(),
            );
            let h_type = self.conv_close_binders(std::slice::from_ref(&local), equation, false)?;
            let h = self.conv_lift(
                deferred,
                &extended,
                std::slice::from_ref(&local),
                hole,
                h_type,
            )?;
            // `resolveRhs "ext" rhs (∀ a, qa)`.
            let rhs_new = self.conv_close_binders(std::slice::from_ref(&local), applied, false)?;
            self.txn.lctx = parent_lctx;
            if !self.conv_resolve_rhs(&rhs, &rhs_new)? {
                return Err(error(TacticError::ConvFailure(
                    "invalid `ext` conv tactic, failed to resolve".to_owned(),
                )));
            }
            let p = Expr::lam(n, d.clone(), b, bi);
            let value = app(
                self.conv_constant(&["forall_congr"], vec![u])?,
                [d, p, q, h],
            );
            self.conv_goals.remove(&goal.id);
            self.conv_close(goal, value)?;
            return Ok(child);
        }
        if let ExprNode::LetE {
            decl_name,
            type_,
            value,
            body,
            ..
        } = lhs.node()
        {
            // `extLetBodyCongr?`.
            let (n, t, v, b) = (
                decl_name.clone(),
                type_.clone(),
                value.clone(),
                body.clone(),
            );
            let u1 = self.conv_level(&t)?;
            let f = Expr::lam(n.clone(), t.clone(), b.clone(), BinderInfo::Default);
            let local = self.conv_local(n.clone(), t.clone(), BinderInfo::Default)?;
            let extended = self.txn.lctx.clone();
            let eq_lhs = self.substitute(&b, &Expr::fvar(local.id.clone()))?;
            let body_type = self.conv_type(&eq_lhs)?;
            let u2 = self.conv_level(&body_type)?;
            let beta =
                self.conv_close_binders(std::slice::from_ref(&local), body_type.clone(), true)?;
            let (r, hole, child) = self.conv_goal_for(&eq_lhs, &Name::anonymous())?;
            let f2_type =
                self.conv_close_binders(std::slice::from_ref(&local), body_type.clone(), false)?;
            let f2 = self.conv_lift(
                deferred,
                &extended,
                std::slice::from_ref(&local),
                r,
                f2_type,
            )?;
            let applied = Expr::app(f2.clone(), Expr::fvar(local.id.clone()));
            let hint = self.conv_id_hint(&child, hole)?;
            let equation = equality::equation(u2.clone(), body_type, eq_lhs, applied.clone());
            let h_type = self.conv_close_binders(std::slice::from_ref(&local), equation, false)?;
            let h = self.conv_lift(
                deferred,
                &extended,
                std::slice::from_ref(&local),
                hint,
                h_type,
            )?;
            let rhs_body = applied
                .abstract_fvar(&local.id, 0)
                .map_err(|_| failure(SourceInferenceError::Scope))?;
            self.txn.lctx = parent_lctx;
            let rhs_new = Expr::let_e(n, t.clone(), v.clone(), rhs_body, false);
            if !self.conv_resolve_rhs(&rhs, &rhs_new)? {
                return Err(error(TacticError::ConvFailure(
                    "failed to go inside let-declaration, type error".to_owned(),
                )));
            }
            let value = app(
                self.conv_constant(&["let_body_congr"], vec![u1, u2])?,
                [t, beta, f, f2, v, h],
            );
            self.conv_goals.remove(&goal.id);
            self.conv_close(goal, value)?;
            return Ok(child);
        }
        // `apply funext; intro x; markAsConvGoal`.
        let lhs_type = self.conv_type(&lhs)?;
        let lhs_type = self.whnf(&lhs_type)?;
        let ExprNode::ForallE {
            binder_name,
            binder_type,
            body,
            ..
        } = lhs_type.node()
        else {
            return Err(error(TacticError::ConvFailure(
                "invalid 'ext' conv tactic, function or arrow expected".to_owned(),
            )));
        };
        let (alpha, codomain) = (binder_type.clone(), body.clone());
        let _ = binder_name;
        let u = self.conv_level(&alpha)?;
        let user = match name {
            Some(name) => name,
            // `introN 1` names it after `funext`'s binder `x`, inaccessibly.
            None => self.fresh_inaccessible(&Name::from_components(["x"]))?,
        };
        let local = self.conv_local(user, alpha.clone(), BinderInfo::Default)?;
        let extended = self.txn.lctx.clone();
        let codomain_at = self.substitute(&codomain, &Expr::fvar(local.id.clone()))?;
        let v = self.conv_level(&codomain_at)?;
        let applied_lhs = self.head_beta(Expr::app(lhs.clone(), Expr::fvar(local.id.clone())))?;
        let (r, hole, child) = self.conv_goal_for(&applied_lhs, &Name::anonymous())?;
        if let Some(tag) = self.goal_tags.get(&goal.id).cloned() {
            self.goal_tags.insert(child.id.clone(), tag);
        }
        let g_type =
            self.conv_close_binders(std::slice::from_ref(&local), codomain_at.clone(), false)?;
        let g = self.conv_lift(deferred, &extended, std::slice::from_ref(&local), r, g_type)?;
        let hint = self.conv_id_hint(&child, hole)?;
        let equation = equality::equation(
            v.clone(),
            codomain_at,
            applied_lhs,
            Expr::app(g.clone(), Expr::fvar(local.id.clone())),
        );
        let h_type = self.conv_close_binders(std::slice::from_ref(&local), equation, false)?;
        let h = self.conv_lift(
            deferred,
            &extended,
            std::slice::from_ref(&local),
            hint,
            h_type,
        )?;
        self.txn.lctx = parent_lctx;
        if !self.conv_resolve_rhs(&rhs, &g)? {
            return Err(error(TacticError::ConvFailure(
                "'apply funext' unexpected result".to_owned(),
            )));
        }
        let beta = Expr::lam(
            Name::from_components(["x"]),
            alpha.clone(),
            codomain,
            BinderInfo::Default,
        );
        let value = app(
            self.conv_constant(&["funext"], vec![u, v])?,
            [alpha, beta, lhs, g, h],
        );
        self.conv_goals.remove(&goal.id);
        self.conv_close(goal, value)?;
        Ok(child)
    }
}

/// `shouldUseSubsingletonInst info kinds i`.
fn should_use_subsingleton_inst(info: &FunInfo, kinds: &[ArgKind], i: usize) -> bool {
    info.params[i].is_dec_inst
        && info.params[i]
            .back_deps
            .iter()
            .any(|&j| kinds.get(j) == Some(&ArgKind::Eq))
}

/// `fixKindsForDependencies`: every parameter an `.eq` or `.fixed` one depends on is `.fixed`.
fn fix_kinds_for_dependencies(info: &FunInfo, mut kinds: Vec<ArgKind>) -> Vec<ArgKind> {
    for i in 0..info.params.len() {
        for j in i + 1..info.params.len() {
            if info.params[j].back_deps.contains(&i)
                && matches!(kinds[j], ArgKind::Eq | ArgKind::Fixed)
            {
                kinds[i] = ArgKind::Fixed;
                break;
            }
        }
    }
    kinds
}

/// `argArg := "@"? "-"? num`: the index and whether it counts every argument.
fn arg_index(syntax: &Syntax) -> Result<(i64, bool), NatDefinitionElabError> {
    let [explicit, negative, number] = expect_node(syntax, &conv_kind("argArg"), 3, "arg index")?
    else {
        return Err(error(TacticError::MalformedScript));
    };
    let explicit = match expect_null_args(explicit, "arg @")? {
        [] => false,
        [at] => {
            expect_atom(at, "@", "arg @")?;
            true
        }
        _ => return Err(error(TacticError::MalformedScript)),
    };
    let negative = match expect_null_args(negative, "arg -")? {
        [] => false,
        [minus] => {
            expect_atom(minus, "-", "arg -")?;
            true
        }
        _ => return Err(error(TacticError::MalformedScript)),
    };
    let [Syntax::Atom { val, .. }] = expect_node(
        number,
        &Name::str(Name::anonymous(), "num"),
        1,
        "arg numeral",
    )?
    else {
        return Err(error(TacticError::MalformedScript));
    };
    let value: i64 = val
        .parse()
        .map_err(|_| error(TacticError::MalformedScript))?;
    Ok((if negative { -value } else { value }, explicit))
}

/// `binderIdent := ident <|> hole`: the name, or `None` for `_`.
fn binder_name(syntax: &Syntax) -> Result<Option<Name>, NatDefinitionElabError> {
    let [inner] = expect_node(
        syntax,
        &Name::from_components(["Lean", "binderIdent"]),
        1,
        "binder name",
    )?
    else {
        return Err(error(TacticError::MalformedScript));
    };
    match inner {
        Syntax::Ident { val, .. } => Ok(Some(val.clone())),
        hole if hole.kind() == Some(&parser_kind(&["Term", "hole"])) => Ok(None),
        _ => Err(error(TacticError::MalformedScript)),
    }
}
