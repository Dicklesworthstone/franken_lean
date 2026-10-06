//! The pin's eliminator elaboration for recursor heads (`elabAsElim`, vendored at
//! `vendor/lean4-src/src/Lean/Elab/App.lean:976-1420`), bead
//! `fln-recursor-motive-elab-as-elim-3jsg`.
//!
//! An application of a recursor whose motive is not supplied does not infer the
//! motive by unification. The pin
//! - postpones the whole application while the expected type is unknown
//!   (`tryPostponeIfNoneOrMVar`), and refuses it if that type never arrives;
//! - elaborates the major premises (the motive's arguments and, transitively,
//!   the parameters their types mention) first, against their binder types;
//! - builds the motive by abstracting the major premises out of the expected type
//!   (`mkMotive`, which `kabstract`s each one) and assigns it;
//! - only then elaborates the remaining explicit arguments, whose expected types
//!   now mention the known motive.
//!
//! Without this, `Chain.rec 0 (fun _ _ ih => ih + 1) c` made the motive a
//! unification problem (`?motive Chain.nil =?= ?α` from the numeral), which was
//! solved out of scope and refused at the declaration's final scope check.
//!
//! What is implemented, mapped to the pin:
//! - `shouldElabAsElim` for recursor constants (`isRec`). `casesOn`/`recOn`/
//!   `brecOn` and `@[elab_as_elim]` are not wired here.
//! - `elabAsElim?`: not under `@`, and not when the motive is supplied. An
//!   application with any named argument keeps the ordinary elaborator.
//! - `getElabElimExprInfo` (motive position and major positions, including the
//!   transitive closure and the "first-order" rule), `ElabElim.main`,
//!   `finalize` with under-application (expected type specialized) and
//!   over-application (`revertArgs`), and `mkMotive`.
//!
//! One deviation, stated: `kabstract` here replaces subterms that are
//! structurally equal to the major premise after metavariable instantiation.
//! The pin also abstracts subterms that are only definitionally equal to it
//! with the same head symbol and arity.
use super::*;
use fln_env::constants::ConstantInfo;

/// `ElabElimInfo`: the motive's parameter position and the major positions.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct ElimInfo {
    motive_pos: usize,
    majors: Vec<usize>,
}

/// An eliminator application waiting for its expected type. `hole` stands for
/// the application where it was written; its type is `expected`.
#[derive(Clone)]
pub(super) struct PostponedEliminator {
    hole: Expr,
    expected: Expr,
    function: Typed,
    arguments: Vec<Syntax>,
    info: ElimInfo,
    lctx: LocalContext,
}

fn eliminator(reason: &'static str) -> NatDefinitionElabError {
    failure(SourceInferenceError::Eliminator(reason))
}

/// Positions (0-based, outermost binder first) of the loose bound variables of
/// `expr`, which sits under `depth` telescope binders.
fn loose_positions(expr: &Expr, depth: usize, out: &mut Vec<usize>) {
    let mut work = vec![(expr.clone(), 0usize)];
    while let Some((e, offset)) = work.pop() {
        if !e.has_loose_bvars() {
            continue;
        }
        match e.node() {
            ExprNode::BVar { idx } => {
                let idx = *idx as usize;
                if idx >= offset {
                    let k = idx - offset;
                    if k < depth {
                        out.push(depth - 1 - k);
                    }
                }
            }
            ExprNode::App { f, a } => {
                work.push((f.clone(), offset));
                work.push((a.clone(), offset));
            }
            ExprNode::Lam {
                binder_type, body, ..
            }
            | ExprNode::ForallE {
                binder_type, body, ..
            } => {
                work.push((binder_type.clone(), offset));
                work.push((body.clone(), offset + 1));
            }
            ExprNode::LetE {
                type_, value, body, ..
            } => {
                work.push((type_.clone(), offset));
                work.push((value.clone(), offset));
                work.push((body.clone(), offset + 1));
            }
            ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => {
                work.push((expr.clone(), offset));
            }
            _ => {}
        }
    }
}

/// The pin's "first-order" test: every application is headed by a constant.
fn first_order(expr: &Expr) -> bool {
    let mut work = vec![expr.clone()];
    while let Some(e) = work.pop() {
        match e.node() {
            ExprNode::App { .. } => {
                let mut head = e.clone();
                while let ExprNode::App { f, a } = head.node() {
                    work.push(a.clone());
                    head = f.clone();
                }
                if !matches!(head.node(), ExprNode::Const { .. }) {
                    return false;
                }
            }
            ExprNode::Lam {
                binder_type, body, ..
            }
            | ExprNode::ForallE {
                binder_type, body, ..
            } => {
                work.push(binder_type.clone());
                work.push(body.clone());
            }
            ExprNode::LetE {
                type_, value, body, ..
            } => {
                work.push(type_.clone());
                work.push(value.clone());
                work.push(body.clone());
            }
            ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => work.push(expr.clone()),
            _ => {}
        }
    }
    true
}

/// `getElabElimExprInfo` over an eliminator's declared type.
fn elim_info(type_: &Expr) -> Option<ElimInfo> {
    let mut binders = Vec::new();
    let mut result = type_.clone();
    while let ExprNode::ForallE {
        binder_type, body, ..
    } = result.node()
    {
        binders.push(binder_type.clone());
        result = body.clone();
    }
    let depth = binders.len();
    let mut head = result.clone();
    let mut args = Vec::new();
    while let ExprNode::App { f, a } = head.node() {
        args.push(a.clone());
        head = f.clone();
    }
    let ExprNode::BVar { idx } = head.node() else {
        return None;
    };
    let idx = *idx as usize;
    if args.is_empty() || idx >= depth {
        return None;
    }
    let motive_pos = depth - 1 - idx;
    // The motive's type takes exactly its arguments and returns a sort.
    let mut motive_type = binders.get(motive_pos)?.clone();
    let mut params = 0;
    while let ExprNode::ForallE { body, .. } = motive_type.node() {
        params += 1;
        motive_type = body.clone();
    }
    if params != args.len() || !matches!(motive_type.node(), ExprNode::Sort { .. }) {
        return None;
    }
    let mut set = Vec::new();
    for arg in &args {
        loose_positions(arg, depth, &mut set);
    }
    for (i, binder) in binders.iter().enumerate().rev() {
        if set.contains(&i) {
            let mut more = Vec::new();
            loose_positions(binder, i, &mut more);
            set.extend(more);
        }
    }
    let mut majors = Vec::new();
    for (i, binder) in binders.iter().enumerate() {
        if i == motive_pos {
            continue;
        }
        let mut mentioned = Vec::new();
        loose_positions(binder, i, &mut mentioned);
        if set.contains(&i) || (first_order(binder) && mentioned.iter().any(|p| set.contains(p))) {
            majors.push(i);
        }
    }
    Some(ElimInfo { motive_pos, majors })
}

fn is_hole_syntax(syntax: &Syntax) -> bool {
    syntax.kind() == Some(&parser_kind(&["Term", "hole"]))
}

impl Context {
    /// `elabAsElim?`: the eliminator information when this application should
    /// be elaborated as an eliminator, and `None` for the ordinary elaborator.
    pub(super) fn eliminator_info(
        &mut self,
        function: &Typed,
        arguments: &[Syntax],
        explicit: bool,
    ) -> Result<Option<ElimInfo>, NatDefinitionElabError> {
        if explicit || application::has_named(arguments) {
            return Ok(None);
        }
        let ExprNode::Const { name, .. } = function.value.node() else {
            return Ok(None);
        };
        let Some(ConstantInfo::Rec(recursor)) = self.txn.env.find(name) else {
            return Ok(None);
        };
        let declared = recursor.base.type_.clone();
        let Some(info) = elim_info(&declared) else {
            return Ok(None);
        };
        // A motive written positionally is supplied unless it is `_`.
        let mut explicit_before = 0;
        let mut binder = declared;
        for position in 0..=info.motive_pos {
            self.tick()?;
            let ExprNode::ForallE {
                body, binder_info, ..
            } = binder.node()
            else {
                return Ok(None);
            };
            let explicit_binder = *binder_info == BinderInfo::Default;
            if position == info.motive_pos {
                if explicit_binder
                    && let Some(written) = arguments.get(explicit_before)
                    && !is_hole_syntax(written)
                {
                    return Ok(None);
                }
                break;
            }
            if explicit_binder {
                explicit_before += 1;
            }
            binder = body.clone();
        }
        Ok(Some(info))
    }

    /// `elabAppArgs` for an eliminator: postpone while the expected type is
    /// unknown, otherwise run `ElabElim.main`.
    pub(super) fn eliminator_application(
        &mut self,
        function: Typed,
        arguments: &[Syntax],
        info: ElimInfo,
        expected: Option<Expr>,
    ) -> Result<Typed, NatDefinitionElabError> {
        let expected = match expected {
            Some(expected) => Some(self.instantiate(&expected)?),
            None => None,
        };
        match expected {
            Some(expected) if !expected_unavailable(&expected) => {
                self.elaborate_eliminator(function, arguments, &info, expected)
            }
            expected => {
                // `tryPostponeIfNoneOrMVar`: a placeholder stands for the
                // application until the surroundings determine its type.
                let expected = match expected {
                    Some(expected) => expected,
                    None => {
                        let sort = self.type_expected()?;
                        self.hole(sort)?
                    }
                };
                let hole = self.hole(expected.clone())?;
                self.postponed_eliminators.push(PostponedEliminator {
                    hole: hole.clone(),
                    expected: expected.clone(),
                    function,
                    arguments: arguments.to_vec(),
                    info,
                    lctx: self.txn.lctx.clone(),
                });
                Ok(Typed {
                    value: hole,
                    type_: expected,
                })
            }
        }
    }

    /// Resume postponed eliminators whose expected type is now known, in their
    /// own local context. On the final pass, one whose type never became
    /// available is the pin's "expected type is not available" refusal.
    pub(super) fn resume_postponed_eliminators(
        &mut self,
        final_pass: bool,
    ) -> Result<(), NatDefinitionElabError> {
        loop {
            self.tick()?;
            let pending = std::mem::take(&mut self.postponed_eliminators);
            if pending.is_empty() {
                return Ok(());
            }
            let mut waiting = Vec::new();
            let mut progressed = false;
            for record in pending {
                let expected = self.instantiate(&record.expected)?;
                if expected_unavailable(&expected) {
                    waiting.push(record);
                    continue;
                }
                let saved = std::mem::replace(&mut self.txn.lctx, record.lctx.clone());
                let result = self.elaborate_eliminator(
                    record.function.clone(),
                    &record.arguments,
                    &record.info,
                    expected,
                );
                self.txn.lctx = saved;
                let term = result?;
                self.constrain(&record.hole, &term.value)?;
                progressed = true;
            }
            // Resuming may postpone nested eliminators; keep both.
            self.postponed_eliminators.extend(waiting);
            if !progressed {
                if final_pass && !self.postponed_eliminators.is_empty() {
                    return Err(eliminator("expected type is not available"));
                }
                return Ok(());
            }
            self.resolve_instances(final_pass)?;
        }
    }

    /// `ElabElim.main` and `finalize`.
    fn elaborate_eliminator(
        &mut self,
        function: Typed,
        arguments: &[Syntax],
        info: &ElimInfo,
        expected: Expr,
    ) -> Result<Typed, NatDefinitionElabError> {
        let mut f = function.value;
        let mut f_type = self.instantiate(&function.type_)?;
        let mut args: std::collections::VecDeque<&Syntax> = arguments.iter().collect();
        let mut motive = None;
        let mut postponed: Vec<(Expr, &Syntax, Expr)> = Vec::new();
        let mut index = 0usize;
        loop {
            self.tick()?;
            if !matches!(f_type.node(), ExprNode::ForallE { .. }) {
                f_type = self.whnf(&f_type)?;
            }
            let ExprNode::ForallE {
                binder_type,
                body,
                binder_info,
                ..
            } = f_type.node()
            else {
                break;
            };
            let (binder_type, body, binder_info) =
                (binder_type.clone(), body.clone(), *binder_info);
            let explicit_binder = binder_info == BinderInfo::Default;
            let argument = if index == info.motive_pos {
                // A positional motive is `_` (checked by `eliminator_info`).
                if explicit_binder {
                    args.pop_front();
                }
                let value = self.hole(binder_type)?;
                motive = Some(value.clone());
                value
            } else if explicit_binder {
                let Some(syntax) = args.pop_front() else {
                    break;
                };
                if info.majors.contains(&index) {
                    self.term(syntax, Some(binder_type))?.value
                } else {
                    // `postponeElabTerm`: elaborated once the motive is known.
                    let hole = self.hole(binder_type.clone())?;
                    postponed.push((hole.clone(), syntax, binder_type));
                    hole
                }
            } else if binder_info == BinderInfo::InstImplicit {
                self.instance_hole(binder_type)?
            } else {
                self.hole(binder_type)?
            };
            f = Expr::app(f, argument.clone());
            f_type = self.substitute(&body, &argument)?;
            index += 1;
        }
        let Some(motive) = motive else {
            return Err(eliminator("insufficient number of arguments"));
        };
        let saved = self.txn.lctx.clone();
        let result = self.finalize_eliminator(f, f_type, args, motive, postponed, expected);
        self.txn.lctx = saved;
        result
    }

    fn finalize_eliminator(
        &mut self,
        mut f: Expr,
        mut f_type: Expr,
        args: std::collections::VecDeque<&Syntax>,
        motive: Expr,
        postponed: Vec<(Expr, &Syntax, Expr)>,
        result_type: Expr,
    ) -> Result<Typed, NatDefinitionElabError> {
        // Known dictionaries in the majors first, so the motive abstracts
        // their final form.
        self.resolve_instances(false)?;
        let mut expected = self.instantiate(&result_type)?;
        let mut locals = Vec::new();
        f_type = self.instantiate(&f_type)?;
        while let ExprNode::ForallE {
            binder_name,
            binder_type,
            body,
            binder_info,
        } = f_type.node()
        {
            // Under-application: specialize the expected type at a fresh local.
            self.tick()?;
            if !args.is_empty() {
                return Err(eliminator("insufficient number of arguments"));
            }
            let expected_head = self.whnf(&expected)?;
            let ExprNode::ForallE {
                binder_type: expected_domain,
                body: expected_body,
                ..
            } = expected_head.node()
            else {
                return Err(eliminator("insufficient number of arguments"));
            };
            self.constrain_type(binder_type, expected_domain)?;
            let id = FVarId(self.fresh_name()?);
            self.txn.lctx.add_param(
                id.clone(),
                binder_name.clone(),
                binder_type.clone(),
                *binder_info,
            );
            let local = Expr::fvar(id.clone());
            expected = self.substitute(expected_body, &local)?;
            f = Expr::app(f, local.clone());
            let next = self.substitute(body, &local)?;
            locals.push((id, binder_name.clone(), binder_type.clone(), *binder_info));
            f_type = next;
        }
        // Over-application: `revertArgs` generalizes each extra argument.
        let mut extra = Vec::new();
        for syntax in &args {
            extra.push(self.term(syntax, None)?);
        }
        let mut generalized = expected.clone();
        for value in extra.iter().rev() {
            let value_expr = self.instantiate(&value.value)?;
            let value_type = self.instantiate(&value.type_)?;
            let body = self.kabstract(&generalized, &value_expr)?;
            let name = self.fresh_name()?;
            generalized = Expr::forall_e(name, value_type, body, BinderInfo::Default);
        }
        // The target type must be the motive applied to the discriminants.
        let target = self.instantiate(&f_type)?;
        let mut head = target.clone();
        let mut discrs = Vec::new();
        while let ExprNode::App { f: g, a } = head.node() {
            discrs.push(a.clone());
            head = g.clone();
        }
        discrs.reverse();
        if self.instantiate(&head)? != self.instantiate(&motive)? {
            return Err(eliminator(
                "eliminator target type isn't an application of the motive",
            ));
        }
        // `mkMotive`.
        let mut motive_value = generalized;
        for discr in discrs.iter().rev() {
            let discr = self.instantiate(discr)?;
            let body = self.kabstract(&motive_value, &discr)?;
            let discr_type = self
                .known_type(&discr)?
                .ok_or_else(|| eliminator("motive is not type correct"))?;
            let discr_type = self.instantiate(&discr_type)?;
            let name = self.fresh_name()?;
            motive_value = Expr::lam(name, discr_type, body, BinderInfo::Default);
        }
        self.constrain(&motive, &motive_value)
            .map_err(|_| eliminator("invalid motive"))?;
        // The postponed arguments now see the motive.
        for (hole, syntax, binder_type) in postponed {
            let binder_type = self.instantiate(&binder_type)?;
            let value = self.term(syntax, Some(binder_type))?;
            self.constrain(&hole, &value.value)?;
        }
        for value in extra {
            f = Expr::app(f, value.value);
        }
        let mut value = self.instantiate(&f)?;
        let mut type_ = self.instantiate(&expected)?;
        for (id, name, domain, style) in locals.into_iter().rev() {
            let domain = self.instantiate(&domain)?;
            value = Expr::lam(
                name.clone(),
                domain.clone(),
                value
                    .abstract_fvar(&id, 0)
                    .map_err(|_| failure(SourceInferenceError::Scope))?,
                style,
            );
            type_ = Expr::forall_e(
                name,
                domain,
                type_
                    .abstract_fvar(&id, 0)
                    .map_err(|_| failure(SourceInferenceError::Scope))?,
                style,
            );
        }
        Ok(Typed { value, type_ })
    }

    /// `kabstract`: every subterm structurally equal to `pattern` (after
    /// instantiation) becomes the variable of a new enclosing binder.
    pub(super) fn kabstract(
        &mut self,
        expr: &Expr,
        pattern: &Expr,
    ) -> Result<Expr, NatDefinitionElabError> {
        let expr = self.instantiate(expr)?;
        if expr.has_loose_bvars() {
            return Err(failure(SourceInferenceError::Scope));
        }
        enum Work {
            Visit(Expr, u32),
            App,
            Binder(bool, Name, BinderInfo),
            Let(Name, bool),
            MData(KVMap),
            Proj(Name, u64),
        }
        let mut work = vec![Work::Visit(expr, 0)];
        let mut values: Vec<Expr> = Vec::new();
        while let Some(item) = work.pop() {
            self.tick()?;
            match item {
                Work::Visit(e, offset) => {
                    // A subterm under binders that mentions them cannot be the
                    // closed pattern.
                    if !e.has_loose_bvars() && &e == pattern {
                        values.push(
                            Expr::bvar(offset).map_err(|_| failure(SourceInferenceError::Scope))?,
                        );
                        continue;
                    }
                    match e.node() {
                        ExprNode::App { f, a } => {
                            work.push(Work::App);
                            work.push(Work::Visit(a.clone(), offset));
                            work.push(Work::Visit(f.clone(), offset));
                        }
                        ExprNode::Lam {
                            binder_name,
                            binder_type,
                            body,
                            binder_info,
                        } => {
                            work.push(Work::Binder(true, binder_name.clone(), *binder_info));
                            work.push(Work::Visit(body.clone(), offset + 1));
                            work.push(Work::Visit(binder_type.clone(), offset));
                        }
                        ExprNode::ForallE {
                            binder_name,
                            binder_type,
                            body,
                            binder_info,
                        } => {
                            work.push(Work::Binder(false, binder_name.clone(), *binder_info));
                            work.push(Work::Visit(body.clone(), offset + 1));
                            work.push(Work::Visit(binder_type.clone(), offset));
                        }
                        ExprNode::LetE {
                            decl_name,
                            type_,
                            value,
                            body,
                            non_dep,
                        } => {
                            work.push(Work::Let(decl_name.clone(), *non_dep));
                            work.push(Work::Visit(body.clone(), offset + 1));
                            work.push(Work::Visit(value.clone(), offset));
                            work.push(Work::Visit(type_.clone(), offset));
                        }
                        ExprNode::MData { data, expr } => {
                            work.push(Work::MData(data.clone()));
                            work.push(Work::Visit(expr.clone(), offset));
                        }
                        ExprNode::Proj {
                            struct_name,
                            idx,
                            expr,
                        } => {
                            work.push(Work::Proj(struct_name.clone(), *idx));
                            work.push(Work::Visit(expr.clone(), offset));
                        }
                        _ => values.push(e.clone()),
                    }
                }
                Work::App => {
                    let a = values
                        .pop()
                        .ok_or_else(|| failure(SourceInferenceError::Scope))?;
                    let f = values
                        .pop()
                        .ok_or_else(|| failure(SourceInferenceError::Scope))?;
                    values.push(Expr::app(f, a));
                }
                Work::Binder(lambda, name, style) => {
                    let body = values
                        .pop()
                        .ok_or_else(|| failure(SourceInferenceError::Scope))?;
                    let domain = values
                        .pop()
                        .ok_or_else(|| failure(SourceInferenceError::Scope))?;
                    values.push(if lambda {
                        Expr::lam(name, domain, body, style)
                    } else {
                        Expr::forall_e(name, domain, body, style)
                    });
                }
                Work::Let(name, non_dep) => {
                    let body = values
                        .pop()
                        .ok_or_else(|| failure(SourceInferenceError::Scope))?;
                    let value = values
                        .pop()
                        .ok_or_else(|| failure(SourceInferenceError::Scope))?;
                    let type_ = values
                        .pop()
                        .ok_or_else(|| failure(SourceInferenceError::Scope))?;
                    values.push(Expr::let_e(name, type_, value, body, non_dep));
                }
                Work::MData(data) => {
                    let inner = values
                        .pop()
                        .ok_or_else(|| failure(SourceInferenceError::Scope))?;
                    values.push(Expr::mdata(data, inner));
                }
                Work::Proj(name, idx) => {
                    let inner = values
                        .pop()
                        .ok_or_else(|| failure(SourceInferenceError::Scope))?;
                    values.push(Expr::proj(name, idx, inner));
                }
            }
        }
        match values.as_slice() {
            [single] => Ok(single.clone()),
            _ => Err(failure(SourceInferenceError::Scope)),
        }
    }
}

/// The pin's `expectedType.getAppFn.isMVar`.
fn expected_unavailable(expected: &Expr) -> bool {
    let mut head = expected;
    while let ExprNode::App { f, .. } = head.node() {
        head = f;
    }
    matches!(head.node(), ExprNode::MVar { .. })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn n(s: &str) -> Name {
        Name::from_components(s.split('.'))
    }

    #[test]
    fn a_recursor_type_yields_the_pin_motive_and_major_positions() {
        // Chain.rec : {motive : Chain → Sort u} → motive nil →
        //   ((head : Nat) → (tail : Chain) → motive tail → motive (cons head tail)) →
        //   (t : Chain) → motive t
        let chain = Expr::const_(n("Chain"), vec![]);
        let nat = Expr::const_(n("Nat"), vec![]);
        let b = |i| Expr::bvar(i).unwrap();
        let motive_type = Expr::forall_e(
            n("t"),
            chain.clone(),
            Expr::sort(Level::zero()),
            BinderInfo::Default,
        );
        let nil_case = Expr::app(b(0), Expr::const_(n("Chain.nil"), vec![]));
        let cons_case = Expr::forall_e(
            n("head"),
            nat,
            Expr::forall_e(
                n("tail"),
                chain.clone(),
                Expr::forall_e(
                    n("ih"),
                    Expr::app(b(3), b(0)),
                    Expr::app(
                        b(4),
                        Expr::app(Expr::app(Expr::const_(n("Chain.cons"), vec![]), b(2)), b(1)),
                    ),
                    BinderInfo::Default,
                ),
                BinderInfo::Default,
            ),
            BinderInfo::Default,
        );
        let type_ = Expr::forall_e(
            n("motive"),
            motive_type,
            Expr::forall_e(
                n("nil"),
                nil_case,
                Expr::forall_e(
                    n("cons"),
                    cons_case,
                    Expr::forall_e(n("t"), chain, Expr::app(b(3), b(0)), BinderInfo::Default),
                    BinderInfo::Default,
                ),
                BinderInfo::Default,
            ),
            BinderInfo::Implicit,
        );
        assert_eq!(
            elim_info(&type_),
            Some(ElimInfo {
                motive_pos: 0,
                majors: vec![3]
            })
        );
    }
}
