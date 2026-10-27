//! Insertion paths, not approximate instance-query keys. The contract is
//! `DiscrTree.mkPath` under `simpGlobalConfig` in the pinned Lean sources:
//! beta/zeta and reducible delta, no iota/projection/local-let reduction; the
//! root stops before an unfolding would lose its useful key. Every theorem
//! telescope local supplied by the caller stands for a fresh assignable mvar.
//! Unsupported smart-unfolding cases fail closed rather than widening a path.
use super::{Meter, SimpSetError};
use crate::instances::{InstanceRegistry, InstanceRegistryError, discr_tree::Key};
use crate::lctx::LocalContext;
use crate::reducibility::{Reducibility, ReducibilityError, ReducibilityTable};
use fln_core::expr::{BinderInfo, Expr, ExprNode, FVarId, Literal, NatLit};
use fln_core::level::Level;
use fln_core::name::{LeafView, Name};
use fln_env::constants::{ConstantInfo, DefinitionSafety, ReducibilityHints};
use fln_env::environment::Environment;
use std::collections::HashSet;
use std::sync::Arc;

const MAX_KEYS: usize = 4096;
const MAX_TYPE_DEPTH: usize = 128;

fn unsupported() -> SimpSetError {
    // The owning export attaches the declaration identity to this shape error.
    SimpSetError::UnsupportedDeclaration(Name::anonymous())
}

fn registry_error(error: InstanceRegistryError) -> SimpSetError {
    match error {
        InstanceRegistryError::Limit => SimpSetError::Limit,
        _ => SimpSetError::Malformed,
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Transparency {
    Reducible,
    Default,
}

struct Indexer<'a> {
    env: &'a Environment,
    locals: LocalContext,
    telescope: HashSet<FVarId>,
    meter: &'a mut Meter,
    reducibility: Option<Arc<ReducibilityTable>>,
    registry: Option<InstanceRegistry>,
    next_local: u64,
}

pub(super) fn keys(
    env: &Environment,
    lhs: &Expr,
    locals: &LocalContext,
    meter: &mut Meter,
) -> Result<Vec<Key>, SimpSetError> {
    Indexer::new(env, locals, meter)?.path(lhs)
}

/// The reducing telescope/conclusion used by SimpTheorems.mkSimpTheoremKeys.
/// Unlike path roots, type heads have no stop-before-a-bad-key rule.
pub(super) fn reduce_type(
    env: &Environment,
    expr: &Expr,
    locals: &LocalContext,
    meter: &mut Meter,
) -> Result<Expr, SimpSetError> {
    Indexer::new(env, locals, meter)?.reduce(expr, false, Transparency::Reducible)
}

/// shouldPreprocess/checkBadRewrite opens its telescope with rigid fvars.
/// Unlike the subsequent mkSimpTheoremKeys mvars, these are good root keys.
pub(super) fn reduce_lhs_for_check(
    env: &Environment,
    lhs: &Expr,
    locals: &LocalContext,
    meter: &mut Meter,
) -> Result<Expr, SimpSetError> {
    let mut indexer = Indexer::new(env, locals, meter)?;
    indexer.telescope.clear();
    indexer.reduce(lhs, true, Transparency::Reducible)
}

/// Classify a closed declaration type by its inferred sort. A failed
/// sufficient-only syntactic proposition check is not evidence of data.
pub(super) fn is_proposition(
    env: &Environment,
    type_expr: &Expr,
    meter: &mut Meter,
) -> Result<bool, SimpSetError> {
    if type_expr.has_fvar()
        || type_expr.has_expr_mvar()
        || type_expr.has_level_mvar()
        || type_expr.has_loose_bvars()
    {
        return Err(SimpSetError::Malformed);
    }
    Indexer::new(env, &LocalContext::new(), meter)?.is_proposition(type_expr)
}

impl<'a> Indexer<'a> {
    fn new(
        env: &'a Environment,
        locals: &LocalContext,
        meter: &'a mut Meter,
    ) -> Result<Self, SimpSetError> {
        meter.work(locals.len())?;
        if locals.decls().iter().any(|local| local.is_let()) {
            return Err(unsupported());
        }
        Ok(Self {
            env,
            locals: locals.clone(),
            telescope: locals
                .decls()
                .iter()
                .map(|local| local.id.clone())
                .collect(),
            meter,
            reducibility: None,
            registry: None,
            next_local: 0,
        })
    }

    fn tick(&mut self) -> Result<(), SimpSetError> {
        self.meter.work(1)
    }

    fn literal_payload(&mut self, literal: &Literal) -> Result<(), SimpSetError> {
        let bytes = match literal {
            Literal::Nat(value) => value
                .limbs_le()
                .len()
                .checked_mul(std::mem::size_of::<u64>())
                .ok_or(SimpSetError::Limit)?,
            Literal::Str(value) => value.len(),
        };
        self.meter.work(bytes)?;
        self.meter.bytes(bytes)
    }

    fn scan(&mut self, root: &Expr) -> Result<(), SimpSetError> {
        let mut todo = vec![root];
        let mut seen = HashSet::new();
        while let Some(expr) = todo.pop() {
            self.tick()?;
            if !seen.insert(expr.allocation_identity()) {
                continue;
            }
            match expr.node() {
                ExprNode::App { f, a } => todo.extend([f, a]),
                ExprNode::Lam {
                    binder_type, body, ..
                }
                | ExprNode::ForallE {
                    binder_type, body, ..
                } => todo.extend([binder_type, body]),
                ExprNode::LetE {
                    type_, value, body, ..
                } => todo.extend([type_, value, body]),
                ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => todo.push(expr),
                _ => {}
            }
        }
        Ok(())
    }

    fn substitute(&mut self, body: &Expr, value: &Expr) -> Result<Expr, SimpSetError> {
        self.scan(body)?;
        body.subst_loose(0, std::slice::from_ref(value))
            .map_err(|_| SimpSetError::Limit)
    }

    fn instantiate(
        &mut self,
        expr: &Expr,
        parameters: &[Name],
        levels: &[Level],
    ) -> Result<Expr, SimpSetError> {
        self.meter.work(parameters.len())?;
        crate::universe::parameters::instantiate(
            || self.meter.work(1),
            unsupported,
            expr,
            parameters,
            levels,
        )
    }

    fn spine(&mut self, expr: &Expr) -> Result<(Expr, Vec<Expr>), SimpSetError> {
        let mut head = expr;
        let mut args = Vec::new();
        loop {
            self.tick()?;
            match head.node() {
                ExprNode::App { f, a } => {
                    args.push(a.clone());
                    head = f;
                }
                _ => {
                    args.reverse();
                    return Ok((head.clone(), args));
                }
            }
        }
    }

    fn apply(&mut self, mut head: Expr, args: Vec<Expr>) -> Result<Expr, SimpSetError> {
        for arg in args {
            self.tick()?;
            head = Expr::app(head, arg);
        }
        Ok(head)
    }

    /// Expr.betaRev's default (useZeta=false, preserveMData=false), not
    /// whnfCore. Root indexing examines this exact result before performing
    /// another reduction, so reducing a let or metadata body here loses keys.
    fn delta_beta(&mut self, body: Expr, args: Vec<Expr>) -> Result<Expr, SimpSetError> {
        if args.is_empty() {
            return Ok(body);
        }
        let mut current = body;
        let mut consumed = 0;
        while consumed < args.len() {
            self.tick()?;
            match current.node() {
                ExprNode::Lam { body, .. } => {
                    current = body.clone();
                    consumed += 1;
                }
                ExprNode::MData { expr, .. } => current = expr.clone(),
                _ => break,
            }
        }
        if consumed != 0 {
            self.scan(&current)?;
            self.meter.work(consumed)?;
            current = current
                // subst_loose takes declaration/binder order and internally
                // maps bvar j to substitutions[n - 1 - j].
                .subst_loose(0, &args[..consumed])
                .map_err(|_| SimpSetError::Limit)?;
        }
        self.apply(current, args.into_iter().skip(consumed).collect())
    }

    /// whnfCore with simpGlobalConfig. In particular a projection or recursor
    /// application does not reduce even with a constructor major argument.
    fn core(&mut self, expr: &Expr) -> Result<Expr, SimpSetError> {
        let mut head = expr.clone();
        let mut args = Vec::new();
        loop {
            self.tick()?;
            match head.node() {
                ExprNode::App { f, a } => {
                    args.push(a.clone());
                    head = f.clone();
                }
                ExprNode::MData { expr, .. } => head = expr.clone(),
                ExprNode::LetE { value, body, .. } => head = self.substitute(body, value)?,
                ExprNode::Lam { body, .. } if !args.is_empty() => {
                    let arg = args.pop().expect("nonempty beta spine");
                    head = self.substitute(body, &arg)?;
                }
                ExprNode::MVar { .. } | ExprNode::BVar { .. } => return Err(unsupported()),
                _ => break,
            }
        }
        args.reverse();
        self.apply(head, args)
    }

    fn status(
        &mut self,
        name: &Name,
        hints: ReducibilityHints,
    ) -> Result<Reducibility, SimpSetError> {
        if self.reducibility.is_none() {
            // The cached table reads both journals. Charge their complete rows
            // before obtaining it, independently of whether a prior call cached it.
            for (name, version) in [
                ("sourceReducibility", "v1"),
                ("sourceInstances", "v1"),
                ("importedInstances", "v2"),
            ] {
                if let Some(state) =
                    self.env
                        .extension(&Name::from_components(["FrankenLean", name, version]))
                {
                    for row in state.entries() {
                        self.meter.work(1 + row.payload.len())?;
                        self.meter.bytes(row.payload.len())?;
                    }
                }
            }
            self.reducibility =
                Some(
                    crate::reducibility::table(self.env).map_err(|error| match error {
                        ReducibilityError::Limit => SimpSetError::Limit,
                        ReducibilityError::Instances(error) => registry_error(error),
                        _ => SimpSetError::Malformed,
                    })?,
                );
        }
        Ok(self
            .reducibility
            .as_ref()
            .expect("loaded table")
            .get(name)
            .unwrap_or(if hints == ReducibilityHints::Abbrev {
                Reducibility::Reducible
            } else {
                Reducibility::Semireducible
            }))
    }

    fn class(&mut self, name: &Name) -> Result<bool, SimpSetError> {
        if self.registry.is_none() {
            for (journal, version) in [("sourceInstances", "v1"), ("importedInstances", "v2")] {
                if let Some(state) =
                    self.env
                        .extension(&Name::from_components(["FrankenLean", journal, version]))
                {
                    for row in state.entries() {
                        self.meter.work(1 + row.payload.len())?;
                        self.meter.bytes(row.payload.len())?;
                    }
                }
            }
            self.registry = Some(InstanceRegistry::read(self.env).map_err(registry_error)?);
        }
        Ok(self
            .registry
            .as_ref()
            .expect("loaded registry")
            .is_class(name))
    }

    fn delta(
        &mut self,
        expr: &Expr,
        transparency: Transparency,
    ) -> Result<Option<Expr>, SimpSetError> {
        let (head, args) = self.spine(expr)?;
        let ExprNode::Const { name, levels } = head.node() else {
            return Ok(None);
        };
        let Some(info) = self.env.find(name) else {
            return Err(SimpSetError::UnknownDeclaration(name.clone()));
        };
        let ConstantInfo::Defn(definition) = info else {
            return Ok(None);
        };
        if definition.safety != DefinitionSafety::Safe {
            return Err(unsupported());
        }
        let definition = definition.clone();
        let status = self.status(name, definition.hints)?;
        if !(status == Reducibility::Reducible
            || transparency == Transparency::Default && status != Reducibility::Irreducible)
        {
            return Ok(None);
        }
        if self.env.contains(&Name::str(name.clone(), "_sunfold")) {
            // The pin never unfolds a bare smart-unfolded constant. Applications
            // require its matcher metadata and structural-major checks.
            return if args.is_empty() {
                Ok(None)
            } else {
                Err(unsupported())
            };
        }
        if matches!(name.leaf_view(), LeafView::Str(text) if text.strip_prefix("match_").is_some_and(|suffix| !suffix.is_empty() && suffix.bytes().all(|byte| byte.is_ascii_digit())))
        {
            return Err(unsupported());
        }
        let projection =
            crate::records::projection::class_projection(self.env, &definition, || {
                self.meter.work(1)
            })?;
        if transparency == Transparency::Reducible
            && !args.is_empty()
            && let Some(projection) = projection
            && self.class(&projection.structure)?
        {
            // backward.whnf.reducibleClassField also reduces the receiver at
            // instance transparency. A raw projection key would be incorrect.
            return Err(unsupported());
        }
        let body = self.instantiate(&definition.value, &definition.base.level_params, levels)?;
        self.delta_beta(body, args).map(Some)
    }

    fn bad_key(&mut self, expr: &Expr) -> Result<bool, SimpSetError> {
        let (head, _) = self.spine(expr)?;
        if let ExprNode::FVar { id } = head.node()
            && self.telescope.contains(id)
        {
            // The pin opened theorem binders as mvars, not fvars. An unfolding
            // to one would lose the root's constant key and must be stopped.
            return Ok(true);
        }
        Ok(!matches!(
            head.node(),
            ExprNode::Lit { .. }
                | ExprNode::Const { .. }
                | ExprNode::FVar { .. }
                | ExprNode::Proj { .. }
                | ExprNode::ForallE { .. }
        ))
    }

    fn eta(&mut self, expr: &Expr) -> Result<Option<Expr>, SimpSetError> {
        let mut body = expr;
        let mut count = 0u32;
        while let ExprNode::Lam { body: inner, .. } = body.node() {
            self.tick()?;
            count = count.checked_add(1).ok_or(SimpSetError::Limit)?;
            body = inner;
        }
        if count == 0 {
            return Ok(None);
        }
        for expected in 0..count {
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

    fn reduce(
        &mut self,
        expr: &Expr,
        root: bool,
        transparency: Transparency,
    ) -> Result<Expr, SimpSetError> {
        let mut current = expr.clone();
        loop {
            current = self.core(&current)?;
            if let Some(unfolded) = self.delta(&current, transparency)?
                && (!root || !self.bad_key(&unfolded)?)
            {
                current = unfolded;
                continue;
            }
            if let Some(contracted) = self.eta(&current)? {
                current = contracted;
                continue;
            }
            return Ok(current);
        }
    }

    fn local(&mut self, domain: Expr, binder: BinderInfo) -> Result<FVarId, SimpSetError> {
        loop {
            self.tick()?;
            let id = FVarId(Name::num(
                Name::from_components(["FrankenLean", "simpExportIndex"]),
                self.next_local,
            ));
            self.next_local = self.next_local.checked_add(1).ok_or(SimpSetError::Limit)?;
            self.meter.work(self.locals.len())?;
            if !self.locals.contains(&id) {
                self.locals
                    .add_param(id.clone(), Name::anonymous(), domain, binder);
                return Ok(id);
            }
        }
    }

    fn infer(&mut self, expr: &Expr, depth: usize) -> Result<Expr, SimpSetError> {
        self.tick()?;
        if depth >= MAX_TYPE_DEPTH {
            return Err(SimpSetError::Limit);
        }
        match expr.node() {
            ExprNode::Sort { level } => Ok(Expr::sort(
                level.clone().succ().map_err(|_| SimpSetError::Limit)?,
            )),
            ExprNode::FVar { id } => {
                self.meter.work(self.locals.len())?;
                self.locals
                    .find(id)
                    .map(|local| local.type_.clone())
                    .ok_or_else(unsupported)
            }
            ExprNode::Const { name, levels } => {
                let info = self
                    .env
                    .find(name)
                    .ok_or_else(|| SimpSetError::UnknownDeclaration(name.clone()))?;
                let base = info.constant_val();
                self.instantiate(&base.type_, &base.level_params, levels)
            }
            ExprNode::Lit { literal } => Ok(Expr::const_(
                Name::from_components([match literal {
                    Literal::Nat(_) => "Nat",
                    Literal::Str(_) => "String",
                }]),
                Vec::new(),
            )),
            ExprNode::MData { expr, .. } => self.infer(expr, depth + 1),
            ExprNode::LetE { body, value, .. } => {
                let value = self.substitute(body, value)?;
                self.infer(&value, depth + 1)
            }
            ExprNode::App { .. } => {
                let (head, args) = self.spine(expr)?;
                let mut type_ = self.infer(&head, depth + 1)?;
                for arg in args {
                    let reduced = self.reduce(&type_, false, Transparency::Default)?;
                    let ExprNode::ForallE { body, .. } = reduced.node() else {
                        return Err(unsupported());
                    };
                    type_ = self.substitute(body, &arg)?;
                }
                Ok(type_)
            }
            ExprNode::Lam {
                binder_name,
                binder_type,
                body,
                binder_info,
            }
            | ExprNode::ForallE {
                binder_name,
                binder_type,
                body,
                binder_info,
            } => {
                let saved = self.locals.len();
                let id = self.local(binder_type.clone(), *binder_info)?;
                let opened = self.substitute(body, &Expr::fvar(id.clone()))?;
                let body_type = self.infer(&opened, depth + 1);
                self.locals.truncate(saved);
                let body_type = body_type?;
                if matches!(expr.node(), ExprNode::Lam { .. }) {
                    self.scan(&body_type)?;
                    let body_type = body_type
                        .abstract_fvar(&id, 0)
                        .map_err(|_| SimpSetError::Limit)?;
                    Ok(Expr::forall_e(
                        binder_name.clone(),
                        binder_type.clone(),
                        body_type,
                        *binder_info,
                    ))
                } else {
                    let domain_sort = self.infer(binder_type, depth + 1)?;
                    let domain_sort = self.reduce(&domain_sort, false, Transparency::Reducible)?;
                    let range_sort = self.reduce(&body_type, false, Transparency::Reducible)?;
                    let (ExprNode::Sort { level: domain }, ExprNode::Sort { level: range }) =
                        (domain_sort.node(), range_sort.node())
                    else {
                        return Err(unsupported());
                    };
                    Ok(Expr::sort(
                        Level::try_kernel_imax(domain.clone(), range.clone())
                            .map_err(|_| SimpSetError::Limit)?,
                    ))
                }
            }
            ExprNode::Proj {
                struct_name,
                idx,
                expr,
            } => self.projection_type(struct_name, *idx, expr, depth + 1),
            ExprNode::BVar { .. } | ExprNode::MVar { .. } => Err(unsupported()),
        }
    }

    fn projection_type(
        &mut self,
        structure: &Name,
        index: u64,
        receiver: &Expr,
        depth: usize,
    ) -> Result<Expr, SimpSetError> {
        let receiver_type = self.infer(receiver, depth)?;
        let receiver_type = self.reduce(&receiver_type, false, Transparency::Default)?;
        let (head, args) = self.spine(&receiver_type)?;
        let ExprNode::Const { name, levels } = head.node() else {
            return Err(unsupported());
        };
        if name != structure {
            return Err(unsupported());
        }
        let Some(ConstantInfo::Induct(family)) = self.env.find(name) else {
            return Err(unsupported());
        };
        let family_arity = u64::from(family.num_params) + u64::from(family.num_indices);
        if family.ctors.len() != 1 || args.len() as u64 != family_arity {
            return Err(unsupported());
        }
        let Some(ConstantInfo::Ctor(constructor)) = self.env.find(&family.ctors[0]) else {
            return Err(unsupported());
        };
        if constructor.induct != *structure || index >= u64::from(constructor.num_fields) {
            return Err(unsupported());
        }
        let parameters = family.num_params as usize;
        let mut telescope = self.instantiate(
            &constructor.base.type_,
            &constructor.base.level_params,
            levels,
        )?;
        for argument in args.iter().take(parameters).cloned().chain(
            (0..index).map(|previous| Expr::proj(structure.clone(), previous, receiver.clone())),
        ) {
            let reduced = self.reduce(&telescope, false, Transparency::Default)?;
            let ExprNode::ForallE { body, .. } = reduced.node() else {
                return Err(unsupported());
            };
            telescope = self.substitute(body, &argument)?;
        }
        let reduced = self.reduce(&telescope, false, Transparency::Default)?;
        let ExprNode::ForallE { binder_type, .. } = reduced.node() else {
            return Err(unsupported());
        };
        // inferProjType returns consumeTypeAnnotations, independently of the
        // reducibility status of these elaborator-only wrappers.
        let mut domain = binder_type.clone();
        loop {
            self.tick()?;
            let ExprNode::App { f, a } = domain.node() else {
                return Ok(domain);
            };
            domain = match f.node() {
                ExprNode::Const { name, .. }
                    if name.parent().is_anonymous()
                        && matches!(
                            name.leaf_view(),
                            LeafView::Str("outParam" | "semiOutParam")
                        ) =>
                {
                    a.clone()
                }
                ExprNode::App { f, a } => match f.node() {
                    ExprNode::Const { name, .. }
                        if name.parent().is_anonymous()
                            && matches!(
                                name.leaf_view(),
                                LeafView::Str("optParam" | "autoParam")
                            ) =>
                    {
                        a.clone()
                    }
                    _ => return Ok(domain),
                },
                _ => return Ok(domain),
            };
        }
    }

    fn is_class_type(&mut self, expr: &Expr) -> Result<bool, SimpSetError> {
        let saved = self.locals.len();
        let result = (|| {
            let mut current = expr.clone();
            loop {
                let reduced = self.reduce(&current, false, Transparency::Reducible)?;
                if let ExprNode::ForallE {
                    binder_type,
                    body,
                    binder_info,
                    ..
                } = reduced.node()
                {
                    let id = self.local(binder_type.clone(), *binder_info)?;
                    current = self.substitute(body, &Expr::fvar(id))?;
                    continue;
                }
                let (head, _) = self.spine(&reduced)?;
                return match head.node() {
                    ExprNode::Const { name, .. } => self.class(name),
                    _ => Ok(false),
                };
            }
        })();
        self.locals.truncate(saved);
        result
    }

    fn is_type(&mut self, expr: &Expr) -> Result<bool, SimpSetError> {
        let type_ = self.infer(expr, 0)?;
        // Lean's isType fallback explicitly uses whnfD, even when the caller
        // indexes under reducible transparency.
        Ok(matches!(
            self.reduce(&type_, false, Transparency::Default)?.node(),
            ExprNode::Sort { .. }
        ))
    }

    fn is_proof(&mut self, expr: &Expr) -> Result<bool, SimpSetError> {
        let type_ = self.infer(expr, 0)?;
        self.is_proposition(&type_)
    }

    fn is_proposition(&mut self, expr: &Expr) -> Result<bool, SimpSetError> {
        let sort = self.infer(expr, 0)?;
        let sort = self.reduce(&sort, false, Transparency::Default)?;
        let ExprNode::Sort { level } = sort.node() else {
            return Err(unsupported());
        };
        super::super::always_zero(level, &[], &[], &mut || self.meter.work(1))
    }

    fn ignored_arguments(&mut self, head: &Expr, args: &[Expr]) -> Result<Vec<bool>, SimpSetError> {
        let mut type_ = self.infer(head, 0)?;
        let saved = self.locals.len();
        let result = (|| {
            let mut ignored = Vec::with_capacity(args.len());
            for arg in args {
                self.tick()?;
                let reduced = self.reduce(&type_, false, Transparency::Default)?;
                let ExprNode::ForallE {
                    binder_type,
                    binder_info,
                    body,
                    ..
                } = reduced.node()
                else {
                    return Err(unsupported());
                };
                let ignore =
                    if *binder_info != BinderInfo::Default && self.is_class_type(binder_type)? {
                        true
                    } else if matches!(
                        binder_info,
                        BinderInfo::Implicit | BinderInfo::StrictImplicit
                    ) {
                        !self.is_type(arg)?
                    } else {
                        self.is_proof(arg)?
                    };
                ignored.push(ignore);
                // FunInfo uses fresh formals, not actual preceding arguments.
                let id = self.local(binder_type.clone(), *binder_info)?;
                type_ = self.substitute(body, &Expr::fvar(id))?;
            }
            Ok(ignored)
        })();
        self.locals.truncate(saved);
        result
    }

    fn numeral(&mut self, expr: &Expr) -> Result<Option<NatLit>, SimpSetError> {
        let mut current = expr.clone();
        let mut successors = 0u64;
        let base = loop {
            let (head, args) = self.spine(&current)?;
            match head.node() {
                ExprNode::Lit {
                    literal: literal @ Literal::Nat(value),
                } if args.is_empty() => {
                    self.literal_payload(literal)?;
                    break value.clone();
                }
                ExprNode::Const { name, .. }
                    if *name == Name::from_components(["Nat", "zero"]) && args.is_empty() =>
                {
                    break NatLit::from_u64(0);
                }
                ExprNode::Const { name, .. }
                    if *name == Name::from_components(["Nat", "succ"]) && args.len() == 1 =>
                {
                    successors = successors.checked_add(1).ok_or(SimpSetError::Limit)?;
                    current = args[0].clone();
                }
                ExprNode::Const { name, .. }
                    if *name == Name::from_components(["OfNat", "ofNat"]) && args.len() == 3 =>
                {
                    current = args[1].clone()
                }
                _ => return Ok(None),
            }
        };
        self.meter.work(base.limbs_le().len() + 1)?;
        if successors == 0 {
            return Ok(Some(base));
        }
        // Addition can grow by at most one limb. Charge its owned result
        // before constructing the arithmetic temporary or literal payload.
        let output_bytes = base
            .limbs_le()
            .len()
            .checked_add(1)
            .and_then(|limbs| limbs.checked_mul(std::mem::size_of::<u64>()))
            .ok_or(SimpSetError::Limit)?;
        self.meter.work(output_bytes)?;
        self.meter.bytes(output_bytes)?;
        let result = fln_bignum::interop::bignat_from_literal(&base)
            .add(&fln_bignum::nat::BigNat::from_u64(successors));
        Ok(Some(fln_bignum::interop::literal_from_bignat(&result)))
    }

    fn offset(&mut self, name: &Name, args: &[Expr]) -> Result<bool, SimpSetError> {
        if *name == Name::from_components(["Nat", "succ"]) && args.len() == 1 {
            return Ok(true);
        }
        let type_index = if *name == Name::from_components(["Nat", "add"]) && args.len() == 2 {
            None
        } else if *name == Name::from_components(["Add", "add"]) && args.len() == 4 {
            Some(0)
        } else if *name == Name::from_components(["HAdd", "hAdd"]) && args.len() == 6 {
            Some(1)
        } else {
            return Ok(false);
        };
        if let Some(index) = type_index {
            let type_ = self.reduce(&args[index], false, Transparency::Reducible)?;
            if !matches!(type_.node(), ExprNode::Const { name, .. } if *name == Name::from_components(["Nat"]))
            {
                return Ok(false);
            }
        }
        self.numeral(args.last().expect("matched offset arity"))
            .map(|value| value.is_some())
    }

    fn path(&mut self, lhs: &Expr) -> Result<Vec<Key>, SimpSetError> {
        let mut keys = Vec::new();
        let mut todo = vec![(Some(lhs.clone()), true)];
        while let Some((expr, root)) = todo.pop() {
            self.tick()?;
            if keys.len() >= MAX_KEYS {
                return Err(SimpSetError::Limit);
            }
            self.meter.bytes(std::mem::size_of::<Key>())?;
            let Some(expr) = expr else {
                keys.push(Key::Star);
                continue;
            };
            if matches!(expr.node(), ExprNode::MData { data, .. } if data.len() == 1 && data.get_bool(&Name::from_components(["noindex"]), false))
            {
                keys.push(Key::Star);
                continue;
            }
            let expr = self.reduce(&expr, root, Transparency::Reducible)?;
            let (head, args) = self.spine(&expr)?;
            let arity = u32::try_from(args.len()).map_err(|_| SimpSetError::Limit)?;
            let key = match head.node() {
                ExprNode::Lit { literal } if args.is_empty() => {
                    self.literal_payload(literal)?;
                    Key::Lit(literal.clone())
                }
                ExprNode::Const { name, .. } => {
                    if !root {
                        if let Some(value) = self.numeral(&expr)? {
                            keys.push(Key::Lit(Literal::Nat(value)));
                            continue;
                        }
                        if self.offset(name, &args)? {
                            keys.push(Key::Star);
                            continue;
                        }
                    }
                    let ignored = self.ignored_arguments(&head, &args)?;
                    for (argument, ignore) in args.into_iter().zip(ignored).rev() {
                        todo.push(((!ignore).then_some(argument), false));
                    }
                    Key::Const(name.clone(), arity)
                }
                ExprNode::FVar { id } if self.telescope.contains(id) => Key::Star,
                ExprNode::ForallE { binder_type, .. } if args.is_empty() => {
                    todo.push((Some(binder_type.clone()), false));
                    Key::Arrow
                }
                ExprNode::Proj {
                    struct_name,
                    idx,
                    expr,
                } => {
                    // pushArgs adds the receiver first to its LIFO worklist;
                    // application arguments are therefore visited before it.
                    let receiver = if self.class(struct_name)? {
                        None
                    } else {
                        Some(expr.clone())
                    };
                    todo.push((receiver, false));
                    let ignored = self.ignored_arguments(&head, &args)?;
                    for (argument, ignore) in args.into_iter().zip(ignored).rev() {
                        todo.push(((!ignore).then_some(argument), false));
                    }
                    Key::Proj(
                        struct_name.clone(),
                        u32::try_from(*idx).map_err(|_| SimpSetError::Limit)?,
                        arity,
                    )
                }
                ExprNode::Lam { .. } | ExprNode::Sort { .. } if args.is_empty() => Key::Other,
                _ => return Err(unsupported()),
            };
            keys.push(key);
        }
        Ok(keys)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use fln_core::options::{DataValue, KVMap};
    use fln_env::constants::{AxiomVal, ConstantVal, ConstructorVal, DefinitionVal, InductiveVal};
    use fln_kernel::Declaration;

    fn n(text: &str) -> Name {
        Name::from_components(text.split('.'))
    }

    fn c(text: &str) -> Expr {
        Expr::const_(n(text), vec![])
    }

    fn nat(value: u64) -> Expr {
        Expr::lit(Literal::Nat(NatLit::from_u64(value)))
    }

    fn arrow(domain: Expr, range: Expr, binder: BinderInfo) -> Expr {
        Expr::forall_e(n("a"), domain, range, binder)
    }

    fn app(head: Expr, args: &[Expr]) -> Expr {
        args.iter().cloned().fold(head, Expr::app)
    }

    fn axiom(env: &Environment, name: &str, type_: Expr) -> Environment {
        env.add_decl(ConstantInfo::Axiom(AxiomVal {
            base: ConstantVal {
                name: n(name),
                level_params: vec![],
                type_,
            },
            is_unsafe: false,
        }))
        .unwrap()
    }

    fn definition(
        env: &Environment,
        name: &str,
        type_: Expr,
        value: Expr,
        hints: ReducibilityHints,
    ) -> Environment {
        env.add_decl(ConstantInfo::Defn(DefinitionVal {
            base: ConstantVal {
                name: n(name),
                level_params: vec![],
                type_,
            },
            value,
            hints,
            safety: DefinitionSafety::Safe,
            all: vec![n(name)],
        }))
        .unwrap()
    }

    // These are explicit metadata models, not a declaration-admission bypass.
    // Their expected paths follow the pin's DiscrTree/Main.lean pushArgs cases.
    fn environment() -> Environment {
        let env = axiom(&Environment::new(), "Nat", Expr::sort(Level::one()));
        let env = axiom(&env, "Nat.zero", c("Nat"));
        let env = axiom(
            &env,
            "Nat.succ",
            arrow(c("Nat"), c("Nat"), BinderInfo::Default),
        );
        let env = axiom(
            &env,
            "Nat.add",
            arrow(
                c("Nat"),
                arrow(c("Nat"), c("Nat"), BinderInfo::Default),
                BinderInfo::Default,
            ),
        );
        let env = axiom(&env, "f", arrow(c("Nat"), c("Nat"), BinderInfo::Default));
        let env = axiom(&env, "P", Expr::sort(Level::zero()));
        axiom(&env, "p", c("P"))
    }

    fn indexed(env: &Environment, term: &Expr, locals: &LocalContext) -> Vec<Key> {
        keys(
            env,
            term,
            locals,
            &mut Meter {
                remaining: 100_000,
                bytes: 0,
            },
        )
        .expect("bounded insertion path")
    }

    fn telescope() -> (LocalContext, Expr) {
        let mut locals = LocalContext::new();
        let id = FVarId(n("theorem.x"));
        locals.add_param(id.clone(), n("x"), c("Nat"), BinderInfo::Default);
        (locals, Expr::fvar(id))
    }

    #[test]
    fn reducible_root_preserves_a_constant_before_an_assignable_mvar() {
        let env = definition(
            &environment(),
            "identity",
            arrow(c("Nat"), c("Nat"), BinderInfo::Default),
            Expr::lam(
                n("x"),
                c("Nat"),
                Expr::bvar(0).unwrap(),
                BinderInfo::Default,
            ),
            ReducibilityHints::Abbrev,
        );
        let (locals, x) = telescope();
        let identity_x = Expr::app(c("identity"), x.clone());
        assert_eq!(
            indexed(&env, &identity_x, &locals),
            vec![Key::Const(n("identity"), 1), Key::Star]
        );
        assert_eq!(
            indexed(&env, &Expr::app(c("f"), identity_x.clone()), &locals),
            vec![Key::Const(n("f"), 1), Key::Star]
        );
        assert_eq!(
            reduce_type(
                &env,
                &identity_x,
                &locals,
                &mut Meter {
                    remaining: 100_000,
                    bytes: 0
                }
            )
            .unwrap(),
            x
        );

        let env = definition(
            &env,
            "alias",
            arrow(c("Nat"), c("Nat"), BinderInfo::Default),
            c("f"),
            ReducibilityHints::Abbrev,
        );
        assert_eq!(
            indexed(&env, &Expr::app(c("alias"), nat(7)), &locals),
            vec![
                Key::Const(n("f"), 1),
                Key::Lit(Literal::Nat(NatLit::from_u64(7)))
            ]
        );
        let env = definition(
            &env,
            "ordinary",
            arrow(c("Nat"), c("Nat"), BinderInfo::Default),
            c("f"),
            ReducibilityHints::Regular(1),
        );
        assert_eq!(
            indexed(&env, &Expr::app(c("ordinary"), nat(7)), &locals)[0],
            Key::Const(n("ordinary"), 1)
        );
    }

    #[test]
    fn root_guard_sees_raw_delta_beta_before_zeta_or_further_beta() {
        let env = definition(
            &environment(),
            "letAlias",
            c("Nat"),
            Expr::let_e(
                n("x"),
                c("Nat"),
                c("Nat.zero"),
                Expr::bvar(0).unwrap(),
                false,
            ),
            ReducibilityHints::Abbrev,
        );
        let locals = LocalContext::new();
        assert_eq!(
            indexed(&env, &c("letAlias"), &locals),
            vec![Key::Const(n("letAlias"), 0)]
        );
        assert_eq!(
            indexed(&env, &Expr::app(c("f"), c("letAlias")), &locals),
            vec![
                Key::Const(n("f"), 1),
                Key::Lit(Literal::Nat(NatLit::from_u64(0)))
            ]
        );

        // betaRev stops at the original body head after consuming its lambdas.
        // Substitution may expose another beta redex, whose lambda is still a
        // bad root until the next whnfCore iteration.
        let fn_type = arrow(c("Nat"), c("Nat"), BinderInfo::Default);
        let env = definition(
            &env,
            "apply",
            arrow(fn_type.clone(), c("Nat"), BinderInfo::Default),
            Expr::lam(
                n("g"),
                fn_type,
                Expr::app(Expr::bvar(0).unwrap(), nat(3)),
                BinderInfo::Default,
            ),
            ReducibilityHints::Abbrev,
        );
        let identity = Expr::lam(
            n("x"),
            c("Nat"),
            Expr::bvar(0).unwrap(),
            BinderInfo::Default,
        );
        assert_eq!(
            indexed(&env, &Expr::app(c("apply"), identity), &locals),
            vec![Key::Const(n("apply"), 1), Key::Other]
        );
    }

    #[test]
    fn bad_rewrite_check_uses_rigid_locals_before_indexing_fresh_mvars() {
        let value = Expr::lam(
            n("x"),
            c("Nat"),
            Expr::bvar(0).unwrap(),
            BinderInfo::Default,
        );
        let type_ = arrow(c("Nat"), c("Nat"), BinderInfo::Default);
        let env = definition(
            &environment(),
            "identity",
            type_.clone(),
            value.clone(),
            ReducibilityHints::Abbrev,
        );
        let env = definition(
            &env,
            "ordinaryIdentity",
            type_,
            value,
            ReducibilityHints::Regular(1),
        );
        let (locals, x) = telescope();
        let lhs = Expr::app(c("identity"), x.clone());
        let reduced = reduce_lhs_for_check(
            &env,
            &lhs,
            &locals,
            &mut Meter {
                remaining: 100_000,
                bytes: 0,
            },
        )
        .unwrap();
        assert_eq!(reduced, x);
        assert!(matches!(reduced.node(), ExprNode::FVar { .. }));
        // checkBadRewrite rejects identity x = x. The later insertion pass
        // alone would preserve a constant key, so it cannot replace this check.
        assert_eq!(
            indexed(&env, &lhs, &locals),
            vec![Key::Const(n("identity"), 1), Key::Star]
        );
        let ordinary = Expr::app(c("ordinaryIdentity"), x);
        assert_eq!(
            reduce_lhs_for_check(
                &env,
                &ordinary,
                &locals,
                &mut Meter {
                    remaining: 100_000,
                    bytes: 0
                }
            )
            .unwrap(),
            ordinary
        );
    }

    #[test]
    fn delta_beta_keeps_binder_order_for_partial_full_and_over_applications() {
        let choose_value = Expr::lam(
            n("x"),
            c("Nat"),
            Expr::lam(
                n("y"),
                c("Nat"),
                Expr::bvar(1).unwrap(),
                BinderInfo::Default,
            ),
            BinderInfo::Default,
        );
        let env = definition(
            &environment(),
            "choose",
            arrow(
                c("Nat"),
                arrow(c("Nat"), c("Nat"), BinderInfo::Default),
                BinderInfo::Default,
            ),
            choose_value,
            ReducibilityHints::Abbrev,
        );
        let locals = LocalContext::new();
        let full = app(
            c("choose"),
            &[c("Nat.zero"), Expr::app(c("Nat.succ"), c("Nat.zero"))],
        );
        assert_eq!(
            indexed(&env, &Expr::app(c("f"), full), &locals),
            vec![
                Key::Const(n("f"), 1),
                Key::Lit(Literal::Nat(NatLit::from_u64(0)))
            ]
        );
        let partial = Expr::app(c("choose"), nat(5));
        assert_eq!(
            reduce_type(
                &env,
                &partial,
                &locals,
                &mut Meter {
                    remaining: 100_000,
                    bytes: 0
                }
            )
            .unwrap(),
            Expr::lam(n("y"), c("Nat"), nat(5), BinderInfo::Default)
        );

        let function_type = arrow(c("Nat"), c("Nat"), BinderInfo::Default);
        let env = definition(
            &env,
            "chooseFn",
            arrow(
                function_type.clone(),
                arrow(
                    function_type.clone(),
                    function_type.clone(),
                    BinderInfo::Default,
                ),
                BinderInfo::Default,
            ),
            Expr::lam(
                n("f"),
                function_type.clone(),
                Expr::lam(
                    n("g"),
                    function_type,
                    Expr::bvar(1).unwrap(),
                    BinderInfo::Default,
                ),
                BinderInfo::Default,
            ),
            ReducibilityHints::Abbrev,
        );
        let identity = Expr::lam(
            n("x"),
            c("Nat"),
            Expr::bvar(0).unwrap(),
            BinderInfo::Default,
        );
        assert_eq!(
            indexed(
                &env,
                &app(c("chooseFn"), &[c("f"), identity, nat(3)]),
                &locals
            ),
            vec![
                Key::Const(n("f"), 1),
                Key::Lit(Literal::Nat(NatLit::from_u64(3)))
            ]
        );
    }

    #[test]
    fn proposition_classification_infers_beta_heads_and_refuses_unknown_sorts() {
        let env = environment();
        let beta_prop = Expr::app(
            Expr::lam(
                n("P"),
                Expr::sort(Level::zero()),
                Expr::bvar(0).unwrap(),
                BinderInfo::Default,
            ),
            c("P"),
        );
        assert_eq!(
            is_proposition(
                &env,
                &beta_prop,
                &mut Meter {
                    remaining: 100_000,
                    bytes: 0
                }
            ),
            Ok(true)
        );
        assert_eq!(
            is_proposition(
                &env,
                &c("Nat"),
                &mut Meter {
                    remaining: 100_000,
                    bytes: 0
                }
            ),
            Ok(false)
        );
        let universal_proof = arrow(c("Nat"), beta_prop, BinderInfo::Default);
        assert_eq!(
            is_proposition(
                &env,
                &universal_proof,
                &mut Meter {
                    remaining: 100_000,
                    bytes: 0
                }
            ),
            Ok(true)
        );
        // Only an inferred Sort can justify false. This explicit malformed
        // metadata model exercises a stuck sort without publishing it.
        let env = axiom(&env, "unknownType", c("opaqueSort"));
        let env = axiom(&env, "opaqueSort", Expr::sort(Level::one()));
        assert!(matches!(
            is_proposition(
                &env,
                &c("unknownType"),
                &mut Meter {
                    remaining: 100_000,
                    bytes: 0
                }
            ),
            Err(SimpSetError::UnsupportedDeclaration(_))
        ));
    }

    #[test]
    fn implicit_types_survive_while_values_proofs_and_instances_are_stars() {
        let env = environment();
        let env = axiom(
            &env,
            "choose",
            arrow(
                Expr::sort(Level::one()),
                arrow(
                    c("Nat"),
                    arrow(c("Nat"), c("Nat"), BinderInfo::Default),
                    BinderInfo::StrictImplicit,
                ),
                BinderInfo::Implicit,
            ),
        );
        let locals = LocalContext::new();
        assert_eq!(
            indexed(
                &env,
                &app(c("choose"), &[c("Nat"), nat(4), nat(9)]),
                &locals
            ),
            vec![
                Key::Const(n("choose"), 3),
                Key::Const(n("Nat"), 0),
                Key::Star,
                Key::Lit(Literal::Nat(NatLit::from_u64(9)))
            ]
        );
        let env = axiom(
            &env,
            "useProof",
            arrow(c("P"), c("Nat"), BinderInfo::Default),
        );
        assert_eq!(
            indexed(&env, &Expr::app(c("useProof"), c("p")), &locals),
            vec![Key::Const(n("useProof"), 1), Key::Star]
        );

        let env = axiom(&env, "C", Expr::sort(Level::one()));
        let env = axiom(&env, "instanceC", c("C"));
        let env = crate::instances::register_class(&env, &n("C")).unwrap();
        let env = axiom(
            &env,
            "implicitClass",
            arrow(c("C"), c("Nat"), BinderInfo::Implicit),
        );
        let env = axiom(
            &env,
            "explicitClass",
            arrow(c("C"), c("Nat"), BinderInfo::Default),
        );
        assert_eq!(
            indexed(
                &env,
                &Expr::app(c("implicitClass"), c("instanceC")),
                &locals
            ),
            vec![Key::Const(n("implicitClass"), 1), Key::Star]
        );
        assert_eq!(
            indexed(
                &env,
                &Expr::app(c("explicitClass"), c("instanceC")),
                &locals
            ),
            vec![
                Key::Const(n("explicitClass"), 1),
                Key::Const(n("instanceC"), 0)
            ]
        );
        // An instance binder alone is insufficient: FunInfo also checks the
        // domain's registered class, unlike the approximate goal-query path.
        let env = axiom(
            &env,
            "notAClass",
            arrow(c("Nat"), c("Nat"), BinderInfo::InstImplicit),
        );
        assert_eq!(
            indexed(&env, &Expr::app(c("notAClass"), nat(2)), &locals),
            vec![
                Key::Const(n("notAClass"), 1),
                Key::Lit(Literal::Nat(NatLit::from_u64(2)))
            ]
        );
    }

    #[test]
    fn proof_arguments_recognize_structurally_unsimplified_zero_universes() {
        let env = environment();
        let zero = Level::max(
            Level::zero(),
            Level::imax(Level::one(), Level::zero()).unwrap(),
        )
        .unwrap();
        assert!(!zero.is_zero(), "the test needs raw level constructors");
        let env = axiom(&env, "RawProp", Expr::sort(zero));
        let env = axiom(&env, "rawProof", c("RawProp"));
        let env = axiom(
            &env,
            "useRawProof",
            arrow(c("RawProp"), c("Nat"), BinderInfo::Default),
        );
        assert_eq!(
            indexed(
                &env,
                &Expr::app(c("useRawProof"), c("rawProof")),
                &LocalContext::new()
            ),
            vec![Key::Const(n("useRawProof"), 1), Key::Star]
        );
    }

    #[test]
    fn nested_numerals_and_offsets_have_different_root_rules() {
        let env = environment();
        let (locals, x) = telescope();
        let one = Expr::app(c("Nat.succ"), c("Nat.zero"));
        assert_eq!(
            indexed(&env, &one, &locals),
            vec![
                Key::Const(n("Nat.succ"), 1),
                Key::Lit(Literal::Nat(NatLit::from_u64(0)))
            ]
        );
        assert_eq!(
            indexed(&env, &Expr::app(c("f"), one), &locals),
            vec![
                Key::Const(n("f"), 1),
                Key::Lit(Literal::Nat(NatLit::from_u64(1)))
            ]
        );
        let offset = app(c("Nat.add"), &[x, nat(3)]);
        assert_eq!(
            indexed(&env, &offset, &locals),
            vec![
                Key::Const(n("Nat.add"), 2),
                Key::Star,
                Key::Lit(Literal::Nat(NatLit::from_u64(3)))
            ]
        );
        assert_eq!(
            indexed(&env, &Expr::app(c("f"), offset), &locals),
            vec![Key::Const(n("f"), 1), Key::Star]
        );
    }

    #[test]
    fn eta_arrow_and_applied_telescope_heads_match_insertion_semantics() {
        let env = environment();
        let locals = LocalContext::new();
        let eta = Expr::lam(
            n("x"),
            c("Nat"),
            Expr::app(c("f"), Expr::bvar(0).unwrap()),
            BinderInfo::Default,
        );
        assert_eq!(indexed(&env, &eta, &locals), vec![Key::Const(n("f"), 0)]);
        assert_eq!(
            indexed(
                &env,
                &arrow(c("Nat"), c("Nat"), BinderInfo::Default),
                &locals
            ),
            vec![Key::Arrow, Key::Const(n("Nat"), 0)]
        );
        let id = FVarId(n("theorem.fn"));
        let mut locals = locals;
        locals.add_param(
            id.clone(),
            n("fn"),
            arrow(c("Nat"), c("Nat"), BinderInfo::Default),
            BinderInfo::Default,
        );
        assert_eq!(
            indexed(&env, &Expr::app(Expr::fvar(id), nat(3)), &locals),
            vec![Key::Star]
        );
        let lambda = Expr::lam(
            n("x"),
            c("Nat"),
            Expr::bvar(0).unwrap(),
            BinderInfo::Default,
        );
        assert_eq!(indexed(&env, &lambda, &locals), vec![Key::Other]);
    }

    #[test]
    fn projection_arguments_precede_receiver_and_class_receivers_are_ignored() {
        let env = environment()
            .add_decl(ConstantInfo::Induct(InductiveVal {
                base: ConstantVal {
                    name: n("Box"),
                    level_params: vec![],
                    type_: Expr::sort(Level::one()),
                },
                num_params: 0,
                num_indices: 0,
                all: vec![n("Box")],
                ctors: vec![n("Box.mk")],
                num_nested: 0,
                is_rec: false,
                is_unsafe: false,
                is_reflexive: false,
            }))
            .unwrap()
            .add_decl(ConstantInfo::Ctor(ConstructorVal {
                base: ConstantVal {
                    name: n("Box.mk"),
                    level_params: vec![],
                    type_: arrow(
                        arrow(c("Nat"), c("Nat"), BinderInfo::Default),
                        c("Box"),
                        BinderInfo::Default,
                    ),
                },
                induct: n("Box"),
                cidx: 0,
                num_params: 0,
                num_fields: 1,
                is_unsafe: false,
            }))
            .unwrap();
        let env = axiom(&env, "box", c("Box"));
        let term = Expr::app(Expr::proj(n("Box"), 0, c("box")), nat(3));
        let locals = LocalContext::new();
        assert_eq!(
            indexed(&env, &term, &locals),
            vec![
                Key::Proj(n("Box"), 0, 1),
                Key::Lit(Literal::Nat(NatLit::from_u64(3))),
                Key::Const(n("box"), 0)
            ]
        );
        let env = crate::instances::register_class(&env, &n("Box")).unwrap();
        assert_eq!(
            indexed(&env, &term, &locals),
            vec![
                Key::Proj(n("Box"), 0, 1),
                Key::Lit(Literal::Nat(NatLit::from_u64(3))),
                Key::Star
            ]
        );
    }

    #[test]
    fn source_no_index_survives_and_only_exact_annotation_is_a_wildcard() {
        let env = environment();
        let parsed =
            // This model's `Nat.zero` is an axiom, so a definition over it is
            // noncomputable here as at the pin.
            fln_parse::parse_definition(b"noncomputable def flagged : Nat := no_index Nat.zero")
                .unwrap();
        let Declaration::Defn(definition) =
            crate::elaborate_definition_in(parsed.syntax(), &env).unwrap()
        else {
            panic!("definition")
        };
        let ExprNode::MData { data, expr } = definition.value.node() else {
            panic!("source no_index annotation must survive")
        };
        assert_eq!(data.len(), 1);
        assert!(data.get_bool(&n("noindex"), false));
        assert_eq!(*expr, c("Nat.zero"));
        let locals = LocalContext::new();
        assert_eq!(indexed(&env, &definition.value, &locals), vec![Key::Star]);

        let mut mixed = KVMap::new();
        mixed.insert(n("noindex"), DataValue::OfBool(true));
        mixed.insert(n("anotherAnnotation"), DataValue::OfBool(true));
        assert_eq!(
            indexed(&env, &Expr::mdata(mixed, c("Nat.zero")), &locals),
            vec![Key::Const(n("Nat.zero"), 0)]
        );
    }

    #[test]
    fn literal_payloads_consume_work_before_owned_key_allocation() {
        let env = environment();
        let large_nat = Expr::lit(Literal::Nat(NatLit::from_limbs_le(vec![1; 512])));
        for term in [
            Expr::lit(Literal::Str("x".repeat(4096))),
            large_nat.clone(),
            Expr::app(c("f"), Expr::app(c("Nat.succ"), large_nat)),
        ] {
            assert_eq!(
                keys(
                    &env,
                    &term,
                    &LocalContext::new(),
                    &mut Meter {
                        remaining: 512,
                        bytes: 0
                    },
                ),
                Err(SimpSetError::Limit)
            );
        }
    }

    #[test]
    fn resource_exhaustion_and_smart_unfolding_are_explicit_failures() {
        let env = environment();
        assert_eq!(
            keys(
                &env,
                &c("f"),
                &LocalContext::new(),
                &mut Meter {
                    remaining: 0,
                    bytes: 0
                }
            ),
            Err(SimpSetError::Limit)
        );
        let env = definition(
            &env,
            "smart",
            arrow(c("Nat"), c("Nat"), BinderInfo::Default),
            c("f"),
            ReducibilityHints::Abbrev,
        );
        let env = axiom(
            &env,
            "smart._sunfold",
            arrow(c("Nat"), c("Nat"), BinderInfo::Default),
        );
        assert_eq!(
            indexed(&env, &c("smart"), &LocalContext::new()),
            vec![Key::Const(n("smart"), 0)]
        );
        assert!(matches!(
            keys(
                &env,
                &Expr::app(c("smart"), nat(1)),
                &LocalContext::new(),
                &mut Meter {
                    remaining: 100_000,
                    bytes: 0
                }
            ),
            Err(SimpSetError::UnsupportedDeclaration(_))
        ));
    }
}
