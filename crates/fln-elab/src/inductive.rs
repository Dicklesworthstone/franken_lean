//! Candidate construction for a single, non-indexed algebraic data type.
//!
//! Both checking engines must validate the block. This generator handles
//! dependent constructor fields and direct uniform recursive fields; it never
//! infers positivity from a flag or publishes a candidate into an environment.
use crate::lctx::LocalDecl;
use crate::records::{Builder, RecordBudget, RecordError, app, fresh, fv};
use fln_core::expr::{BinderInfo, Expr, ExprNode, FVarId};
use fln_core::level::Level;
use fln_core::name::{LeafView, Name};
use fln_env::constants::{ConstantVal, ConstructorVal, InductiveVal, RecursorRule, RecursorVal};
use fln_kernel::{Declaration, InductiveBlock};
use std::collections::HashSet;

#[derive(Debug, Clone)]
pub struct ConstructorSpec {
    /// A single constructor-name component, relative to the family.
    pub name: Name,
    /// Domains may read parameters and preceding fields of this constructor.
    pub fields: Vec<LocalDecl>,
}

#[derive(Debug, Clone)]
pub struct InductiveSpec {
    pub name: Name,
    pub level_params: Vec<Name>,
    pub parameters: Vec<LocalDecl>,
    pub constructors: Vec<ConstructorSpec>,
    pub result_level: Level,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InductiveError {
    InvalidName,
    DuplicateConstructor,
    InvalidTelescope,
    UnsupportedSort,
    UnsupportedRecursion,
    ResourceLimit,
}
impl std::fmt::Display for InductiveError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Self::InvalidName => "invalid algebraic data type or constructor name",
            Self::DuplicateConstructor => "duplicate constructor name",
            Self::InvalidTelescope => "constructor escapes its telescope or has unresolved types",
            Self::UnsupportedSort => "algebraic data type requires a positive result universe",
            Self::UnsupportedRecursion => {
                "only direct uniform recursive constructor fields are supported"
            }
            Self::ResourceLimit => "algebraic data type generation work limit reached",
        })
    }
}
impl std::error::Error for InductiveError {}
impl From<RecordError> for InductiveError {
    fn from(error: RecordError) -> Self {
        match error {
            RecordError::InvalidName => Self::InvalidName,
            RecordError::DuplicateField => Self::DuplicateConstructor,
            RecordError::InvalidTelescope => Self::InvalidTelescope,
            RecordError::UnsupportedSort => Self::UnsupportedSort,
            RecordError::ResourceLimit => Self::ResourceLimit,
        }
    }
}

fn append_ih(name: &Name) -> Name {
    match name.leaf_view() {
        LeafView::Str(text) => Name::str(name.parent().clone(), format!("{text}_ih")),
        _ => Name::str(name.clone(), "_ih"),
    }
}

/// Construct a proposed family, constructors and its dependent recursor. The
/// result is untrusted; kernel regeneration and the independent veto still run.
pub fn inductive_declaration(
    spec: &InductiveSpec,
    budget: RecordBudget,
) -> Result<Declaration, InductiveError> {
    if spec.name.is_anonymous() {
        return Err(InductiveError::InvalidName);
    }
    let count = spec
        .constructors
        .iter()
        .try_fold(spec.parameters.len(), |sum, ctor| {
            sum.checked_add(ctor.fields.len())
                .and_then(|n| n.checked_add(1))
        })
        .ok_or(InductiveError::ResourceLimit)?;
    if count > budget.max_binders || spec.level_params.len() > budget.max_binders {
        return Err(InductiveError::ResourceLimit);
    }
    if spec.result_level.has_mvar() || !spec.result_level.is_never_zero() {
        return Err(InductiveError::UnsupportedSort);
    }
    let mut builder = Builder {
        remaining: budget.max_nodes,
    };
    let mut used = HashSet::<FVarId>::new();
    for param in &spec.parameters {
        builder.tick()?;
        if param.is_let() || used.contains(&param.id) {
            return Err(InductiveError::InvalidTelescope);
        }
        builder.scan(&param.type_, &used, &spec.name)?;
        used.insert(param.id.clone());
    }
    let levels: Vec<_> = spec
        .level_params
        .iter()
        .cloned()
        .map(Level::param)
        .collect();
    let family = app(
        Expr::const_(spec.name.clone(), levels.clone()),
        spec.parameters.iter().map(fv),
    );
    let mut names = HashSet::new();
    let mut recursive = Vec::new();
    for constructor in &spec.constructors {
        let LeafView::Str(label) = constructor.name.leaf_view() else {
            return Err(InductiveError::InvalidName);
        };
        if !constructor.name.parent().is_anonymous() || label.is_empty() || label == "rec" {
            return Err(InductiveError::InvalidName);
        }
        if !names.insert(constructor.name.clone()) {
            return Err(InductiveError::DuplicateConstructor);
        }
        let mut allowed: HashSet<_> = spec.parameters.iter().map(|p| p.id.clone()).collect();
        let mut fields = Vec::new();
        for field in &constructor.fields {
            builder.tick()?;
            if field.is_let() || !allowed.insert(field.id.clone()) {
                return Err(InductiveError::InvalidTelescope);
            }
            allowed.remove(&field.id);
            let mut domain = &field.type_;
            while let ExprNode::MData { expr, .. } = domain.node() {
                builder.tick()?;
                domain = expr;
            }
            let direct = domain == &family;
            if !direct {
                // This scan forbids every occurrence of the family. In
                // particular negative, nested, changed-parameter and higher-
                // order recursion never slips through as a nonrecursive field.
                builder.scan(&field.type_, &allowed, &spec.name)?;
            }
            allowed.insert(field.id.clone());
            used.insert(field.id.clone());
            fields.push(direct);
        }
        recursive.push(fields);
    }
    let mut elim = Name::from_components(["u"]);
    let mut ordinal = 1;
    while spec.level_params.contains(&elim) {
        builder.tick()?;
        elim = Name::from_components([format!("u_{ordinal}").as_str()]);
        ordinal += 1;
    }
    let major = fresh(&mut used, "t", family.clone(), BinderInfo::Default);
    let motive_type = builder.close(
        std::slice::from_ref(&major),
        Expr::sort(Level::param(elim.clone())),
        false,
        false,
    )?;
    let motive = fresh(&mut used, "motive", motive_type, BinderInfo::Default);
    let ctor_names: Vec<_> = spec
        .constructors
        .iter()
        .map(|c| spec.name.append_core(&c.name))
        .collect();
    let mut minors = Vec::new();
    let mut constructors = Vec::new();
    for (index, ctor) in spec.constructors.iter().enumerate() {
        builder.tick()?;
        let constructor = app(
            Expr::const_(ctor_names[index].clone(), levels.clone()),
            spec.parameters.iter().chain(&ctor.fields).map(fv),
        );
        let mut ihs = Vec::new();
        for (field, direct) in ctor.fields.iter().zip(&recursive[index]) {
            if *direct {
                let mut ih = fresh(
                    &mut used,
                    "ih",
                    Expr::app(fv(&motive), fv(field)),
                    BinderInfo::Default,
                );
                ih.user_name = append_ih(&field.user_name);
                ihs.push(ih);
            }
        }
        let body = Expr::app(fv(&motive), constructor);
        let body = builder.close(&ihs, body, false, false)?;
        let minor_type = builder.close(&ctor.fields, body, false, false)?;
        let mut minor = fresh(&mut used, "minor", minor_type, BinderInfo::Default);
        minor.user_name = ctor.name.clone();
        minors.push(minor);
        let type_ = builder.close(&ctor.fields, family.clone(), false, false)?;
        let type_ = builder.close(&spec.parameters, type_, false, true)?;
        constructors.push(ConstructorVal {
            base: ConstantVal {
                name: ctor_names[index].clone(),
                level_params: spec.level_params.clone(),
                type_,
            },
            induct: spec.name.clone(),
            cidx: u32::try_from(index).map_err(|_| InductiveError::ResourceLimit)?,
            num_params: u32::try_from(spec.parameters.len())
                .map_err(|_| InductiveError::ResourceLimit)?,
            num_fields: u32::try_from(ctor.fields.len())
                .map_err(|_| InductiveError::ResourceLimit)?,
            is_unsafe: false,
        });
    }
    let mut rec_levels = vec![Level::param(elim.clone())];
    rec_levels.extend(levels);
    let rec_name = Name::str(spec.name.clone(), "rec");
    let rec_prefix = app(
        Expr::const_(rec_name.clone(), rec_levels),
        spec.parameters
            .iter()
            .chain(std::iter::once(&motive))
            .chain(&minors)
            .map(fv),
    );
    let mut rules = Vec::new();
    for (index, ctor) in spec.constructors.iter().enumerate() {
        builder.tick()?;
        let mut rhs = app(fv(&minors[index]), ctor.fields.iter().map(fv));
        for (field, direct) in ctor.fields.iter().zip(&recursive[index]) {
            if *direct {
                rhs = Expr::app(rhs, Expr::app(rec_prefix.clone(), fv(field)));
            }
        }
        rhs = builder.close(&ctor.fields, rhs, true, false)?;
        rhs = builder.close(&minors, rhs, true, false)?;
        rhs = builder.close(std::slice::from_ref(&motive), rhs, true, false)?;
        rhs = builder.close(&spec.parameters, rhs, true, false)?;
        rules.push(RecursorRule {
            ctor: ctor_names[index].clone(),
            nfields: constructors[index].num_fields,
            rhs,
        });
    }
    let rec_type = builder.close(
        std::slice::from_ref(&major),
        Expr::app(fv(&motive), fv(&major)),
        false,
        false,
    )?;
    let rec_type = builder.close(&minors, rec_type, false, false)?;
    let rec_type = builder.close(std::slice::from_ref(&motive), rec_type, false, true)?;
    let rec_type = builder.close(&spec.parameters, rec_type, false, true)?;
    let mut lparams = vec![elim];
    lparams.extend(spec.level_params.iter().cloned());
    let params = u32::try_from(spec.parameters.len()).map_err(|_| InductiveError::ResourceLimit)?;
    Ok(Declaration::Inductive(InductiveBlock {
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
            ctors: ctor_names,
            num_nested: 0,
            is_rec: recursive.iter().flatten().any(|x| *x),
            is_unsafe: false,
            is_reflexive: false,
        }],
        ctors: constructors,
        recursors: vec![RecursorVal {
            base: ConstantVal {
                name: rec_name,
                level_params: lparams,
                type_: rec_type,
            },
            all: vec![spec.name.clone()],
            num_params: params,
            num_indices: 0,
            num_motives: 1,
            num_minors: u32::try_from(minors.len()).map_err(|_| InductiveError::ResourceLimit)?,
            rules,
            k: false,
            is_unsafe: false,
        }],
    }))
}
