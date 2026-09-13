//! Candidate construction for a single algebraic or indexed data family.
//!
//! Both checking engines must validate the block. This generator handles
//! dependent constructor fields and strictly positive uniform recursive fields; it never
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
    /// Constructor result indices, scoped over parameters and its own fields.
    pub result_indices: Vec<Expr>,
}

#[derive(Debug, Clone)]
pub struct InductiveSpec {
    pub name: Name,
    pub level_params: Vec<Name>,
    pub parameters: Vec<LocalDecl>,
    /// The family index telescope, scoped over parameters and earlier indices.
    pub indices: Vec<LocalDecl>,
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
            Self::UnsupportedSort => {
                "inductive result sort or field elimination universes are unresolved"
            }
            Self::UnsupportedRecursion => {
                "recursive fields must be strictly positive functions returning the uniform family"
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

/// A recursive field can be a dependent function returning this family. Its
/// domains cannot mention the family; result indices may use its arguments.
struct RecursiveField {
    arguments: Vec<LocalDecl>,
    indices: Vec<Expr>,
}

fn recursive_field(
    builder: &mut Builder,
    domain: &Expr,
    spec: &InductiveSpec,
    levels: &[Level],
    allowed: &HashSet<FVarId>,
    used: &mut HashSet<FVarId>,
) -> Result<Option<RecursiveField>, InductiveError> {
    let mut current = domain.clone();
    let mut scope = allowed.clone();
    let mut arguments = Vec::new();
    loop {
        builder.tick()?;
        match current.node() {
            ExprNode::MData { expr, .. } => current = expr.clone(),
            ExprNode::ForallE {
                binder_name,
                binder_type,
                body,
                binder_info,
            } => {
                // Strict positivity is not inferred from metadata: an occurrence
                // in even one argument domain prevents this construction.
                builder.scan(binder_type, &scope, &spec.name)?;
                let mut local = fresh(used, "arg", binder_type.clone(), *binder_info);
                local.user_name = binder_name.clone();
                current = body
                    .subst_loose(0, &[fv(&local)])
                    .map_err(|_| InductiveError::InvalidTelescope)?;
                scope.insert(local.id.clone());
                arguments.push(local);
            }
            _ => break,
        }
    }
    Ok(recursive_indices(builder, &current, spec, levels, &scope)?
        .map(|indices| RecursiveField { arguments, indices }))
}

/// A direct recursive occurrence may change indices, but not parameters or
/// universes. Index terms themselves must not mention the family.
fn recursive_indices(
    builder: &mut Builder,
    domain: &Expr,
    spec: &InductiveSpec,
    levels: &[Level],
    allowed: &HashSet<FVarId>,
) -> Result<Option<Vec<Expr>>, InductiveError> {
    let mut head = domain;
    let mut args = Vec::new();
    loop {
        builder.tick()?;
        match head.node() {
            ExprNode::MData { expr, .. } => head = expr,
            ExprNode::App { f, a } => {
                args.push(a.clone());
                head = f;
            }
            _ => break,
        }
    }
    args.reverse();
    if !matches!(head.node(), ExprNode::Const { name, levels: us } if name == &spec.name && us == levels)
        || args.len() != spec.parameters.len() + spec.indices.len()
        || args
            .iter()
            .zip(&spec.parameters)
            .any(|(arg, param)| *arg != fv(param))
    {
        return Ok(None);
    }
    let indices = args[spec.parameters.len()..].to_vec();
    for index in &indices {
        builder.scan(index, allowed, &spec.name)?;
    }
    Ok(Some(indices))
}

/// Construct a proposed family, constructors and its dependent recursor. The
/// result is untrusted; kernel regeneration and the independent veto still run.
pub fn inductive_declaration(
    spec: &InductiveSpec,
    budget: RecordBudget,
) -> Result<Declaration, InductiveError> {
    build_inductive(spec, budget, None)
}

/// Field universes inform candidate generation only. Both admission engines
/// independently infer them and reconstruct the permitted elimination level.
/// Source elaboration supplies these before replacing its provisional family.
pub(crate) fn inductive_with_field_universes(
    spec: &InductiveSpec,
    budget: RecordBudget,
    field_universes: &[Vec<Level>],
) -> Result<Declaration, InductiveError> {
    build_inductive(spec, budget, Some(field_universes))
}

fn build_inductive(
    spec: &InductiveSpec,
    budget: RecordBudget,
    field_universes: Option<&[Vec<Level>]>,
) -> Result<Declaration, InductiveError> {
    if spec.name.is_anonymous() {
        return Err(InductiveError::InvalidName);
    }
    let count = spec
        .constructors
        .iter()
        .try_fold(
            spec.parameters.len().saturating_add(spec.indices.len()),
            |sum, ctor| {
                sum.checked_add(ctor.fields.len())
                    .and_then(|n| n.checked_add(ctor.result_indices.len()))
                    .and_then(|n| n.checked_add(1))
            },
        )
        .ok_or(InductiveError::ResourceLimit)?;
    if count > budget.max_binders || spec.level_params.len() > budget.max_binders {
        return Err(InductiveError::ResourceLimit);
    }
    let proposition = spec.result_level.normalize_fixpoint().is_zero();
    if spec.result_level.has_mvar() || (!proposition && !spec.result_level.is_never_zero()) {
        return Err(InductiveError::UnsupportedSort);
    }
    if let Some(universes) = field_universes
        && (universes.len() != spec.constructors.len()
            || universes
                .iter()
                .zip(&spec.constructors)
                .any(|(us, ctor)| us.len() != ctor.fields.len() || us.iter().any(Level::has_mvar)))
    {
        return Err(InductiveError::InvalidTelescope);
    }
    // KR-700/701: data and empty predicates eliminate large. A singleton
    // predicate does too iff every data field occurs verbatim in its indices.
    // Proof fields need not appear there; an existential witness cannot be
    // recovered merely because it occurs inside a compound index expression.
    let large = if !proposition || spec.constructors.is_empty() {
        true
    } else if let [ctor] = spec.constructors.as_slice() {
        let mut allowed = true;
        for (i, field) in ctor.fields.iter().enumerate() {
            if ctor.result_indices.iter().any(|index| *index == fv(field)) {
                continue;
            }
            let universe = field_universes
                .and_then(|us| us.first())
                .and_then(|us| us.get(i))
                .ok_or(InductiveError::UnsupportedSort)?;
            allowed &= universe.normalize_fixpoint().is_zero();
        }
        allowed
    } else {
        false
    };
    let k_target =
        proposition && spec.constructors.len() == 1 && spec.constructors[0].fields.is_empty();
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
    for index in &spec.indices {
        builder.tick()?;
        if index.is_let() || used.contains(&index.id) {
            return Err(InductiveError::InvalidTelescope);
        }
        builder.scan(&index.type_, &used, &spec.name)?;
        used.insert(index.id.clone());
    }
    let levels: Vec<_> = spec
        .level_params
        .iter()
        .cloned()
        .map(Level::param)
        .collect();
    // Reserve every caller-supplied identity before introducing function
    // arguments, including fields of constructors visited later.
    for constructor in &spec.constructors {
        for field in &constructor.fields {
            used.insert(field.id.clone());
        }
    }
    let family_prefix = app(
        Expr::const_(spec.name.clone(), levels.clone()),
        spec.parameters.iter().map(fv),
    );
    let family = app(family_prefix.clone(), spec.indices.iter().map(fv));
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
            let direct = recursive_field(
                &mut builder,
                &field.type_,
                spec,
                &levels,
                &allowed,
                &mut used,
            )?;
            if direct.is_none() {
                // This scan forbids every occurrence of the family. In
                // particular negative, nested and changed-parameter recursion
                // never slips through as a nonrecursive field.
                builder.scan(&field.type_, &allowed, &spec.name)?;
            }
            allowed.insert(field.id.clone());
            used.insert(field.id.clone());
            fields.push(direct);
        }
        if constructor.result_indices.len() != spec.indices.len() {
            return Err(InductiveError::InvalidTelescope);
        }
        for index in &constructor.result_indices {
            builder.scan(index, &allowed, &spec.name)?;
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
        Expr::sort(if large {
            Level::param(elim.clone())
        } else {
            Level::zero()
        }),
        false,
        false,
    )?;
    let motive_type = builder.close(&spec.indices, motive_type, false, false)?;
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
            if let Some(recursive) = direct {
                let child = app(fv(field), recursive.arguments.iter().map(fv));
                let result = Expr::app(app(fv(&motive), recursive.indices.iter().cloned()), child);
                let type_ = builder.close(&recursive.arguments, result, false, false)?;
                let mut ih = fresh(&mut used, "ih", type_, BinderInfo::Default);
                ih.user_name = append_ih(&field.user_name);
                ihs.push(ih);
            }
        }
        let body = Expr::app(
            app(fv(&motive), ctor.result_indices.iter().cloned()),
            constructor,
        );
        let body = builder.close(&ihs, body, false, false)?;
        let minor_type = builder.close(&ctor.fields, body, false, false)?;
        let mut minor = fresh(&mut used, "minor", minor_type, BinderInfo::Default);
        minor.user_name = ctor.name.clone();
        minors.push(minor);
        let result = app(family_prefix.clone(), ctor.result_indices.iter().cloned());
        let type_ = builder.close(&ctor.fields, result, false, false)?;
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
    let mut rec_levels = if large {
        vec![Level::param(elim.clone())]
    } else {
        Vec::new()
    };
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
            if let Some(recursive) = direct {
                let call = app(rec_prefix.clone(), recursive.indices.iter().cloned());
                let child = app(fv(field), recursive.arguments.iter().map(fv));
                let call =
                    builder.close(&recursive.arguments, Expr::app(call, child), true, false)?;
                rhs = Expr::app(rhs, call);
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
        Expr::app(app(fv(&motive), spec.indices.iter().map(fv)), fv(&major)),
        false,
        false,
    )?;
    let rec_type = builder.close(&spec.indices, rec_type, false, true)?;
    let rec_type = builder.close(&minors, rec_type, false, false)?;
    // With no minor premises, no later binder domain mentions the motive.
    // It stays explicit under the Reference's strict implicit inference rule.
    let rec_type = builder.close(
        std::slice::from_ref(&motive),
        rec_type,
        false,
        !minors.is_empty(),
    )?;
    let rec_type = builder.close(&spec.parameters, rec_type, false, true)?;
    let mut lparams = if large { vec![elim] } else { Vec::new() };
    lparams.extend(spec.level_params.iter().cloned());
    let params = u32::try_from(spec.parameters.len()).map_err(|_| InductiveError::ResourceLimit)?;
    let indices = u32::try_from(spec.indices.len()).map_err(|_| InductiveError::ResourceLimit)?;
    let family_result = builder.close(
        &spec.indices,
        Expr::sort(spec.result_level.clone()),
        false,
        false,
    )?;
    Ok(Declaration::Inductive(InductiveBlock {
        types: vec![InductiveVal {
            base: ConstantVal {
                name: spec.name.clone(),
                level_params: spec.level_params.clone(),
                type_: builder.close(&spec.parameters, family_result, false, false)?,
            },
            num_params: params,
            num_indices: indices,
            all: vec![spec.name.clone()],
            ctors: ctor_names,
            num_nested: 0,
            is_rec: recursive.iter().flatten().any(Option::is_some),
            is_unsafe: false,
            is_reflexive: recursive
                .iter()
                .flatten()
                .flatten()
                .any(|field| !field.arguments.is_empty()),
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
            num_indices: indices,
            num_motives: 1,
            num_minors: u32::try_from(minors.len()).map_err(|_| InductiveError::ResourceLimit)?,
            rules,
            k: k_target,
            is_unsafe: false,
        }],
    }))
}
