//! Candidate generation for nonrecursive Type-valued records and classes.
//!
//! This module owns no admission authority. The generated block (including its
//! proposed eliminator) and each projection must pass the ordinary kernel and
//! the caller's independent-checker policy before any successor is exposed.
use crate::lctx::LocalDecl;
use fln_core::expr::{BinderInfo, Expr, ExprNode, FVarId};
use fln_core::level::Level;
use fln_core::name::{LeafView, Name};
use fln_env::constants::{
    ConstantVal, ConstructorVal, DefinitionSafety, DefinitionVal, InductiveVal, RecursorRule,
    RecursorVal, ReducibilityHints,
};
use fln_kernel::{Declaration, InductiveBlock};
use std::collections::HashSet;

/// Field domains refer to parameters and earlier fields by their local IDs.
/// Universe parameters belong to the record, not to its eliminator.
#[derive(Debug, Clone)]
pub struct RecordSpec {
    pub name: Name,
    pub level_params: Vec<Name>,
    pub parameters: Vec<LocalDecl>,
    pub fields: Vec<LocalDecl>,
    pub result_level: Level,
    pub is_class: bool,
}

#[derive(Debug, Clone, Copy)]
pub struct RecordBudget {
    pub max_binders: usize,
    pub max_nodes: usize,
}
impl Default for RecordBudget {
    fn default() -> Self {
        Self {
            max_binders: 256,
            max_nodes: 100_000,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RecordError {
    InvalidName,
    DuplicateField,
    InvalidTelescope,
    UnsupportedSort,
    ResourceLimit,
}
impl std::fmt::Display for RecordError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Self::InvalidName => "record or field has an invalid or reserved name",
            Self::DuplicateField => "duplicate record field",
            Self::InvalidTelescope => {
                "record field escapes its preceding telescope or remains unresolved"
            }
            Self::UnsupportedSort => "record generation requires a Type-valued result sort",
            Self::ResourceLimit => "record generation resource limit reached",
        })
    }
}
impl std::error::Error for RecordError {}

pub(crate) struct Builder {
    pub(crate) remaining: usize,
}
impl Builder {
    pub(crate) fn tick(&mut self) -> Result<(), RecordError> {
        self.remaining = self
            .remaining
            .checked_sub(1)
            .ok_or(RecordError::ResourceLimit)?;
        Ok(())
    }
    pub(crate) fn scan(
        &mut self,
        expr: &Expr,
        allowed: &HashSet<FVarId>,
        record: &Name,
    ) -> Result<(), RecordError> {
        if expr.has_loose_bvars() || expr.has_expr_mvar() || expr.has_level_mvar() {
            return Err(RecordError::InvalidTelescope);
        }
        let mut work = vec![expr];
        let mut seen = HashSet::new();
        while let Some(term) = work.pop() {
            if !seen.insert(term.allocation_identity()) {
                continue;
            }
            self.tick()?;
            match term.node() {
                ExprNode::FVar { id } if !allowed.contains(id) => {
                    return Err(RecordError::InvalidTelescope);
                }
                ExprNode::Const { name, .. } if name == record => {
                    return Err(RecordError::InvalidTelescope);
                }
                ExprNode::App { f, a } => {
                    work.push(a);
                    work.push(f);
                }
                ExprNode::Lam {
                    binder_type, body, ..
                }
                | ExprNode::ForallE {
                    binder_type, body, ..
                } => {
                    work.push(body);
                    work.push(binder_type);
                }
                ExprNode::LetE {
                    type_, value, body, ..
                } => {
                    work.push(body);
                    work.push(value);
                    work.push(type_);
                }
                ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => work.push(expr),
                _ => {}
            }
        }
        Ok(())
    }
    pub(crate) fn close(
        &mut self,
        locals: &[LocalDecl],
        mut body: Expr,
        lambda: bool,
        implicit: bool,
    ) -> Result<Expr, RecordError> {
        for local in locals.iter().rev() {
            self.tick()?;
            body = body
                .abstract_fvar(&local.id, 0)
                .map_err(|_| RecordError::InvalidTelescope)?;
            let style = if implicit && local.binder_info == BinderInfo::Default {
                BinderInfo::Implicit
            } else {
                local.binder_info
            };
            body = if lambda {
                Expr::lam(local.user_name.clone(), local.type_.clone(), body, style)
            } else {
                Expr::forall_e(local.user_name.clone(), local.type_.clone(), body, style)
            };
        }
        Ok(body)
    }
}
pub(crate) fn fresh(
    used: &mut HashSet<FVarId>,
    user_name: &str,
    type_: Expr,
    style: BinderInfo,
) -> LocalDecl {
    let mut ordinal = 0;
    let id = loop {
        let id = FVarId(Name::num(Name::from_components(["_fln_record"]), ordinal));
        if used.insert(id.clone()) {
            break id;
        }
        ordinal += 1;
    };
    LocalDecl {
        id,
        user_name: Name::from_components([user_name]),
        type_,
        value: None,
        binder_info: style,
        index: 0,
    }
}
pub(crate) fn fv(local: &LocalDecl) -> Expr {
    Expr::fvar(local.id.clone())
}
pub(crate) fn app(head: Expr, arguments: impl IntoIterator<Item = Expr>) -> Expr {
    arguments.into_iter().fold(head, Expr::app)
}

/// Generate one block followed by its projections, in field order. Parameters
/// become implicit constructor/projection arguments; class projections additionally
/// take an instance-implicit receiver. Source inheritance/defaults are separate
/// elaboration features, not silently simulated by this builder.
pub fn record_declarations(
    spec: &RecordSpec,
    budget: RecordBudget,
) -> Result<Vec<Declaration>, RecordError> {
    if spec.name.is_anonymous() {
        return Err(RecordError::InvalidName);
    }
    if spec.parameters.len().saturating_add(spec.fields.len()) > budget.max_binders
        || spec.level_params.len() > budget.max_binders
    {
        return Err(RecordError::ResourceLimit);
    }
    if spec.result_level.has_mvar() || !spec.result_level.is_never_zero() {
        return Err(RecordError::UnsupportedSort);
    }
    let mut builder = Builder {
        remaining: budget.max_nodes,
    };
    let mut used = HashSet::new();
    let mut labels = HashSet::new();
    for local in spec.parameters.iter().chain(&spec.fields) {
        builder.tick()?;
        if local.is_let() || used.contains(&local.id) {
            return Err(RecordError::InvalidTelescope);
        }
        builder.scan(&local.type_, &used, &spec.name)?;
        used.insert(local.id.clone());
    }
    for field in &spec.fields {
        let LeafView::Str(label) = field.user_name.leaf_view() else {
            return Err(RecordError::InvalidName);
        };
        if !field.user_name.parent().is_anonymous()
            || label.is_empty()
            || matches!(label, "mk" | "rec")
        {
            return Err(RecordError::InvalidName);
        }
        if !labels.insert(field.user_name.clone()) {
            return Err(RecordError::DuplicateField);
        }
    }
    let params = u32::try_from(spec.parameters.len()).map_err(|_| RecordError::ResourceLimit)?;
    let fields = u32::try_from(spec.fields.len()).map_err(|_| RecordError::ResourceLimit)?;
    let ctor = Name::str(spec.name.clone(), "mk");
    let rec = Name::str(spec.name.clone(), "rec");
    let levels: Vec<_> = spec
        .level_params
        .iter()
        .cloned()
        .map(Level::param)
        .collect();
    // This is the kernel's fresh elimination-universe naming convention.
    let mut elim = Name::from_components(["u"]);
    let mut ordinal = 1;
    while spec.level_params.contains(&elim) {
        builder.tick()?;
        elim = Name::from_components([format!("u_{ordinal}").as_str()]);
        ordinal += 1;
    }
    let record_type = app(
        Expr::const_(spec.name.clone(), levels.clone()),
        spec.parameters.iter().map(fv),
    );
    let constructor = app(
        Expr::const_(ctor.clone(), levels),
        spec.parameters.iter().chain(&spec.fields).map(fv),
    );
    let major = fresh(&mut used, "t", record_type.clone(), BinderInfo::Default);
    let motive_type = builder.close(
        std::slice::from_ref(&major),
        Expr::sort(Level::param(elim.clone())),
        false,
        false,
    )?;
    let motive = fresh(&mut used, "motive", motive_type, BinderInfo::Default);
    let minor_type = builder.close(
        &spec.fields,
        Expr::app(fv(&motive), constructor),
        false,
        false,
    )?;
    let minor = fresh(&mut used, "mk", minor_type, BinderInfo::Default);
    let rec_type = builder.close(
        std::slice::from_ref(&major),
        Expr::app(fv(&motive), fv(&major)),
        false,
        false,
    )?;
    let rec_type = builder.close(std::slice::from_ref(&minor), rec_type, false, false)?;
    let rec_type = builder.close(std::slice::from_ref(&motive), rec_type, false, true)?;
    let rec_type = builder.close(&spec.parameters, rec_type, false, true)?;
    let rhs = app(fv(&minor), spec.fields.iter().map(fv));
    let rhs = builder.close(&spec.fields, rhs, true, false)?;
    let rhs = builder.close(std::slice::from_ref(&minor), rhs, true, false)?;
    let rhs = builder.close(std::slice::from_ref(&motive), rhs, true, false)?;
    let rhs = builder.close(&spec.parameters, rhs, true, false)?;
    let ctor_type = builder.close(&spec.fields, record_type.clone(), false, false)?;
    let ctor_type = builder.close(&spec.parameters, ctor_type, false, true)?;
    let mut rec_levels = vec![elim];
    rec_levels.extend(spec.level_params.iter().cloned());
    let mut declarations = vec![Declaration::Inductive(InductiveBlock {
        types: vec![InductiveVal {
            base: ConstantVal {
                name: spec.name.clone(),
                level_params: spec.level_params.clone(),
                type_: builder.close(
                    &spec.parameters,
                    Expr::sort(spec.result_level.clone()),
                    false,
                    false,
                )?,
            },
            num_params: params,
            num_indices: 0,
            all: vec![spec.name.clone()],
            ctors: vec![ctor.clone()],
            num_nested: 0,
            is_rec: false,
            is_unsafe: false,
            is_reflexive: false,
        }],
        ctors: vec![ConstructorVal {
            base: ConstantVal {
                name: ctor.clone(),
                level_params: spec.level_params.clone(),
                type_: ctor_type,
            },
            induct: spec.name.clone(),
            cidx: 0,
            num_params: params,
            num_fields: fields,
            is_unsafe: false,
        }],
        recursors: vec![RecursorVal {
            base: ConstantVal {
                name: rec,
                level_params: rec_levels,
                type_: rec_type,
            },
            all: vec![spec.name.clone()],
            num_params: params,
            num_indices: 0,
            num_motives: 1,
            num_minors: 1,
            rules: vec![RecursorRule {
                ctor,
                nfields: fields,
                rhs,
            }],
            k: false,
            is_unsafe: false,
        }],
    })];
    let receiver = fresh(
        &mut used,
        "self",
        record_type,
        if spec.is_class {
            BinderInfo::InstImplicit
        } else {
            BinderInfo::Default
        },
    );
    for (index, field) in spec.fields.iter().enumerate() {
        builder.tick()?;
        let mut domain = field.type_.clone();
        // Later domains refer to earlier fields via projections of the same
        // receiver, not dangling telescope locals or independently chosen values.
        for (prior, prior_field) in spec.fields[..index].iter().enumerate() {
            builder.tick()?;
            domain = domain
                .abstract_fvar(&prior_field.id, 0)
                .map_err(|_| RecordError::InvalidTelescope)?;
            domain = domain
                .subst_loose(
                    0,
                    &[Expr::proj(spec.name.clone(), prior as u64, fv(&receiver))],
                )
                .map_err(|_| RecordError::InvalidTelescope)?;
        }
        let type_ = builder.close(std::slice::from_ref(&receiver), domain, false, false)?;
        let type_ = builder.close(&spec.parameters, type_, false, true)?;
        let value = Expr::proj(spec.name.clone(), index as u64, fv(&receiver));
        let value = builder.close(std::slice::from_ref(&receiver), value, true, false)?;
        let value = builder.close(&spec.parameters, value, true, true)?;
        let name = spec.name.append_core(&field.user_name);
        declarations.push(Declaration::Defn(DefinitionVal {
            base: ConstantVal {
                name: name.clone(),
                level_params: spec.level_params.clone(),
                type_,
            },
            value,
            hints: ReducibilityHints::Abbrev,
            safety: DefinitionSafety::Safe,
            all: vec![name],
        }));
    }
    Ok(declarations)
}

/// Reduction of a projection after its major's application spine is in WHNF.
/// `arguments` is reverse application order, as used by both elaborator machines.
/// Only an admitted, saturated constructor of the requested one-constructor
/// family can reduce; malformed fields never get an arbitrary argument.
pub(crate) fn constructor_field(
    environment: &fln_env::environment::Environment,
    structure: &Name,
    index: u64,
    head: &Expr,
    arguments: &[Expr],
) -> Option<Expr> {
    use fln_env::constants::ConstantInfo;
    let ConstantInfo::Induct(family) = environment.find(structure)? else {
        return None;
    };
    if family.is_unsafe || family.num_indices != 0 || family.ctors.len() != 1 {
        return None;
    }
    let ExprNode::Const { name, levels } = head.node() else {
        return None;
    };
    if &family.ctors[0] != name {
        return None;
    }
    let ConstantInfo::Ctor(constructor) = environment.find(name)? else {
        return None;
    };
    if constructor.is_unsafe
        || &constructor.induct != structure
        || constructor.num_params != family.num_params
        || levels.len() != constructor.base.level_params.len()
        || index >= u64::from(constructor.num_fields)
    {
        return None;
    }
    let arity =
        usize::try_from(u64::from(constructor.num_params) + u64::from(constructor.num_fields))
            .ok()?;
    if arguments.len() != arity {
        return None;
    }
    let position = usize::try_from(u64::from(constructor.num_params) + index).ok()?;
    arguments.get(arity.checked_sub(position + 1)?).cloned()
}
