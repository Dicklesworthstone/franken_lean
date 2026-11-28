//! Native computed-field candidates and their checked representation contract.
//!
//! Logical getters remain ordinary safe definitions. Constructor caches live in
//! a separate implementation family, selected only by checked replacement edges.
//! Every candidate still requires the caller's ordinary dual admission. A
//! journal claim alone never authorizes casts or a different runtime layout.

use crate::ElabTxn;
use crate::constraint::unify::{UnificationBudget, UnificationError, UnificationTransparency};
use crate::inductive::{ConstructorSpec, InductiveError, InductiveSpec};
use crate::lctx::LocalDecl;
use crate::records::{Builder, RecordBudget, RecordError, app, fv};
use fln_core::expr::{BinderInfo, Expr, ExprNode, FVarId};
use fln_core::level::Level;
use fln_core::name::Name;
use fln_core::options::KVMap;
use fln_env::constants::{
    ConstantInfo, ConstantVal, DefinitionSafety, DefinitionVal, ReducibilityHints,
};
use fln_env::environment::Environment;
use fln_kernel::verdict::Budget;
use fln_kernel::{Declaration, InductiveBlock};
use std::collections::HashSet;

mod journal;
pub use journal::{
    ComputedFieldEntry, decode_entry, families, journal_name, register, register_projected,
    supports, validated_family,
};

/// Consumers can reserve this many `RecordBudget::max_nodes` units before a
/// complete model validation. Each generation, metadata and comparison phase
/// has its own explicit bound; exhaustion never means an absent model.
pub const VALIDATION_PHASES: usize = 6;

#[derive(Debug, Clone, PartialEq)]
pub enum ComputedFieldError {
    ResourceLimit,
    Unsupported(&'static str),
    InvalidField(Name),
    ConstructorReduction { field: Name, constructor: Name },
    InvalidInventory,
    Reduction(Box<UnificationError>),
}

impl ComputedFieldError {
    pub fn is_resource_limit(&self) -> bool {
        matches!(self, Self::ResourceLimit)
    }
}

impl std::fmt::Display for ComputedFieldError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::ResourceLimit => f.write_str("computed-field work limit reached"),
            Self::Unsupported(what) => write!(f, "unsupported computed fields: {what}"),
            Self::InvalidField(name) => write!(f, "invalid computed-field signature: {}", name.to_display_string()),
            Self::ConstructorReduction { field, constructor } => write!(f,
                "computed field {} does not reduce at constructor {}",
                field.to_display_string(), constructor.to_display_string()),
            Self::InvalidInventory => f.write_str("computed-field declarations or executable metadata differ from their checked construction"),
            Self::Reduction(error) => std::fmt::Display::fmt(error, f),
        }
    }
}

impl std::error::Error for ComputedFieldError {}

impl From<RecordError> for ComputedFieldError {
    fn from(error: RecordError) -> Self {
        if error == RecordError::ResourceLimit {
            Self::ResourceLimit
        } else {
            Self::InvalidInventory
        }
    }
}

impl From<InductiveError> for ComputedFieldError {
    fn from(error: InductiveError) -> Self {
        if error == InductiveError::ResourceLimit {
            Self::ResourceLimit
        } else {
            Self::InvalidInventory
        }
    }
}

fn reduction_error(error: UnificationError) -> ComputedFieldError {
    match error {
        UnificationError::StepLimit { .. }
        | UnificationError::NodeLimit { .. }
        | UnificationError::AssignmentLimit { .. }
        | UnificationError::HeartbeatLimit => ComputedFieldError::ResourceLimit,
        other => ComputedFieldError::Reduction(Box::new(other)),
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ComputedField {
    pub name: Name,
    pub result_type: Expr,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ComputedConstructor {
    pub logical: Name,
    pub implementation: Name,
    pub override_: Name,
    pub num_fields: u32,
    pub cached: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ComputedFamily {
    pub family: Name,
    pub implementation: Name,
    pub fields: Vec<ComputedField>,
    pub constructors: Vec<ComputedConstructor>,
    pub cases_on: Name,
    pub cases_on_override: Name,
    pub overrides: Vec<DefinitionVal>,
    pub inline_fields: Vec<Name>,
}

#[derive(Debug, Clone)]
pub struct Generated {
    pub declarations: Vec<Declaration>,
    pub implemented_by: Vec<(Name, Name)>,
}

struct Build<'a> {
    env: &'a Environment,
    kernel: Budget,
    work: Builder,
    binders: usize,
    next: u64,
    txn: ElabTxn,
}

impl<'a> Build<'a> {
    fn new(env: &'a Environment, kernel: Budget, budget: RecordBudget) -> Self {
        Self {
            env,
            kernel,
            work: Builder {
                remaining: budget.max_nodes,
            },
            binders: budget.max_binders,
            next: 0,
            txn: ElabTxn::new(env.clone(), KVMap::new(), 0),
        }
    }

    fn charge(&mut self, amount: usize) -> Result<(), ComputedFieldError> {
        self.work.remaining = self
            .work
            .remaining
            .checked_sub(amount)
            .ok_or(ComputedFieldError::ResourceLimit)?;
        Ok(())
    }

    fn local(
        &mut self,
        name: Name,
        type_: Expr,
        info: BinderInfo,
    ) -> Result<LocalDecl, ComputedFieldError> {
        self.work.tick()?;
        self.binders = self
            .binders
            .checked_sub(1)
            .ok_or(ComputedFieldError::ResourceLimit)?;
        let index = self.next;
        self.next = self
            .next
            .checked_add(1)
            .ok_or(ComputedFieldError::ResourceLimit)?;
        let id = FVarId(Name::num(Name::from_components(["_fln_computed"]), index));
        self.txn
            .lctx
            .add_param(id.clone(), name.clone(), type_.clone(), info);
        Ok(LocalDecl {
            id,
            user_name: name,
            type_,
            value: None,
            binder_info: info,
            index: index as usize,
        })
    }

    fn whnf(&mut self, expression: &Expr) -> Result<Expr, ComputedFieldError> {
        self.reduce(expression, UnificationTransparency::SafeDefinitions)
    }

    fn reduce(
        &mut self,
        expression: &Expr,
        transparency: UnificationTransparency,
    ) -> Result<Expr, ComputedFieldError> {
        self.work.tick()?;
        let mut budget = UnificationBudget::new(self.kernel);
        budget.transparency = transparency;
        budget.max_steps = budget.max_steps.min(self.work.remaining as u64);
        budget.max_visited_nodes = budget.max_visited_nodes.min(self.work.remaining);
        let spent = self.txn.budget.heartbeats_consumed;
        self.txn.budget.max_heartbeats = spent.saturating_add(self.work.remaining as u64);
        let locals = self.txn.lctx.clone();
        let result = self.txn.whnf_with(expression, &locals, budget);
        let used = self.txn.budget.heartbeats_consumed.saturating_sub(spent);
        self.charge(usize::try_from(used).map_err(|_| ComputedFieldError::ResourceLimit)?)?;
        result.map_err(reduction_error)
    }

    fn equal(&mut self, left: &Expr, right: &Expr) -> Result<(), ComputedFieldError> {
        self.work.tick()?;
        let mut budget = UnificationBudget::new(self.kernel);
        budget.transparency = UnificationTransparency::SafeDefinitions;
        budget.max_steps = budget.max_steps.min(self.work.remaining as u64);
        budget.max_visited_nodes = budget.max_visited_nodes.min(self.work.remaining);
        let spent = self.txn.budget.heartbeats_consumed;
        self.txn.budget.max_heartbeats = spent.saturating_add(self.work.remaining as u64);
        let result = self.txn.unify(left, right, budget);
        let used = self.txn.budget.heartbeats_consumed.saturating_sub(spent);
        self.charge(usize::try_from(used).map_err(|_| ComputedFieldError::ResourceLimit)?)?;
        result.map(|_| ()).map_err(reduction_error)
    }

    /// One logical delta step, leaving recursive calls in the chosen equation
    /// named. Full normalization would unfold a child getter into a traversal
    /// and defeat the constructor cache's constant-time child reads.
    fn unfold_head(&mut self, expression: &Expr) -> Result<Option<Expr>, ComputedFieldError> {
        let mut head = expression;
        let mut arguments = Vec::new();
        loop {
            self.work.tick()?;
            match head.node() {
                ExprNode::App { f, a } => {
                    arguments.push(a.clone());
                    head = f;
                }
                ExprNode::MData { expr, .. } => head = expr,
                _ => break,
            }
        }
        let ExprNode::Const { name, levels } = head.node() else {
            return Ok(None);
        };
        let Some(ConstantInfo::Defn(definition)) = self.env.find(name) else {
            return Ok(None);
        };
        if definition.safety != DefinitionSafety::Safe
            || definition.base.level_params.len() != levels.len()
        {
            return Ok(None);
        }
        self.scan_closed(&definition.value)?;
        let body = crate::universe::parameters::instantiate(
            || self.work.tick().map_err(ComputedFieldError::from),
            || ComputedFieldError::InvalidInventory,
            &definition.value,
            &definition.base.level_params,
            levels,
        )?;
        Ok(Some(app(body, arguments.into_iter().rev())))
    }

    fn telescope(
        &mut self,
        expression: &Expr,
    ) -> Result<(Vec<LocalDecl>, Expr), ComputedFieldError> {
        let mut current = expression.clone();
        let mut locals = Vec::new();
        loop {
            current = self.whnf(&current)?;
            let ExprNode::ForallE {
                binder_name,
                binder_type,
                body,
                binder_info,
            } = current.node()
            else {
                break;
            };
            let local = self.local(binder_name.clone(), binder_type.clone(), *binder_info)?;
            current = body
                .subst_loose(0, &[fv(&local)])
                .map_err(|_| ComputedFieldError::ResourceLimit)?;
            locals.push(local);
        }
        Ok((locals, current))
    }

    fn close(
        &mut self,
        locals: &[LocalDecl],
        value: Expr,
        lambda: bool,
    ) -> Result<Expr, ComputedFieldError> {
        Ok(self.work.close(locals, value, lambda, false)?)
    }

    fn scan_closed(&mut self, value: &Expr) -> Result<(), ComputedFieldError> {
        Ok(self.work.scan(value, &HashSet::new(), &Name::anonymous())?)
    }

    fn contains(&mut self, value: &Expr, target: &Expr) -> Result<bool, ComputedFieldError> {
        let mut pending = vec![value];
        let mut seen = HashSet::new();
        while let Some(expr) = pending.pop() {
            self.work.tick()?;
            if !seen.insert(expr.allocation_identity()) {
                continue;
            }
            if expr == target {
                return Ok(true);
            }
            match expr.node() {
                ExprNode::App { f, a } => {
                    pending.push(f);
                    pending.push(a);
                }
                ExprNode::Lam {
                    binder_type, body, ..
                }
                | ExprNode::ForallE {
                    binder_type, body, ..
                } => {
                    pending.push(binder_type);
                    pending.push(body);
                }
                ExprNode::LetE {
                    type_, value, body, ..
                } => {
                    pending.push(type_);
                    pending.push(value);
                    pending.push(body);
                }
                ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => pending.push(expr),
                _ => {}
            }
        }
        Ok(false)
    }

    fn field_value(
        &mut self,
        field: &Name,
        ctor: &Name,
        term: Expr,
    ) -> Result<Expr, ComputedFieldError> {
        let applied = Expr::app(Expr::const_(field.clone(), vec![]), term.clone());
        let smart_name = Name::str(field.clone(), "_sunfold");
        let mut reduced = if let Some(ConstantInfo::Defn(smart)) = self.env.find(&smart_name) {
            let original = self
                .env
                .find(field)
                .ok_or(ComputedFieldError::InvalidInventory)?;
            if smart.safety != DefinitionSafety::Safe
                || !smart.base.level_params.is_empty()
                || smart.base.type_ != original.constant_val().type_
            {
                return Err(ComputedFieldError::InvalidInventory);
            }
            self.scan_closed(&smart.value)?;
            Expr::app(smart.value.clone(), term.clone())
        } else {
            self.unfold_head(&applied)?
                .ok_or(ComputedFieldError::InvalidField(field.clone()))?
        };
        loop {
            // This is the pin's whnfHeadPred boundary: beta/iota first, then
            // delta only while the original constructor still occurs.
            reduced = self.reduce(&reduced, UnificationTransparency::None)?;
            if !self.contains(&reduced, &term)? {
                // A helper's spelling cannot license different equations. The
                // instantiated constructor equation must actually convert to
                // the admitted logical getter under the caller's work budget.
                self.equal(&applied, &reduced)?;
                return Ok(reduced);
            }
            let Some(next) = self.unfold_head(&reduced)? else {
                return Err(ComputedFieldError::ConstructorReduction {
                    field: field.clone(),
                    constructor: ctor.clone(),
                });
            };
            reduced = next;
        }
    }

    fn cache_locals(
        &mut self,
        model: &ComputedFamily,
    ) -> Result<Vec<LocalDecl>, ComputedFieldError> {
        model
            .fields
            .iter()
            .map(|field| {
                self.local(
                    field.name.clone(),
                    field.result_type.clone(),
                    BinderInfo::Default,
                )
            })
            .collect()
    }

    fn definition(
        &mut self,
        name: Name,
        levels: Vec<Name>,
        type_: Expr,
        value: Expr,
    ) -> Result<DefinitionVal, ComputedFieldError> {
        self.scan_closed(&type_)?;
        self.scan_closed(&value)?;
        Ok(DefinitionVal {
            base: ConstantVal {
                name: name.clone(),
                level_params: levels,
                type_,
            },
            value,
            hints: ReducibilityHints::Opaque,
            safety: DefinitionSafety::Unsafe,
            all: vec![name],
        })
    }
}

fn constant(name: &Name) -> Expr {
    Expr::const_(name.clone(), vec![])
}

fn cast(from: Expr, to: Expr, value: Expr, from_level: Level, to_level: Level) -> Expr {
    app(
        Expr::const_(
            Name::from_components(["unsafeCast"]),
            vec![from_level, to_level],
        ),
        [from, to, value],
    )
}

fn profile(
    build: &mut Build<'_>,
    family: &Name,
    fields: &[Name],
) -> Result<ComputedFamily, ComputedFieldError> {
    build.work.tick()?;
    let Some(ConstantInfo::Induct(inductive)) = build.env.find(family) else {
        return Err(ComputedFieldError::InvalidInventory);
    };
    if inductive.is_unsafe
        || inductive.num_params != 0
        || inductive.num_indices != 0
        || inductive.num_nested != 0
        || !inductive.base.level_params.is_empty()
        || inductive.all.as_slice() != std::slice::from_ref(family)
        || inductive.base.type_ != Expr::sort(Level::one())
    {
        return Err(ComputedFieldError::Unsupported(
            "a safe single monomorphic nonindexed Type family is required",
        ));
    }
    if inductive.ctors.len() < 2 || fields.is_empty() {
        return Err(ComputedFieldError::Unsupported(
            "computed fields require at least two constructors and a field",
        ));
    }
    build.charge(inductive.ctors.len().saturating_add(fields.len()))?;
    if inductive.ctors.len().saturating_add(fields.len()) > build.binders {
        return Err(ComputedFieldError::ResourceLimit);
    }
    let family_type = constant(family);
    let mut names = HashSet::new();
    let mut computed = Vec::new();
    for name in fields {
        if name.parent() != *family || !names.insert(name.clone()) {
            return Err(ComputedFieldError::InvalidField(name.clone()));
        }
        let Some(ConstantInfo::Defn(definition)) = build.env.find(name) else {
            return Err(ComputedFieldError::InvalidField(name.clone()));
        };
        if definition.safety != DefinitionSafety::Safe || !definition.base.level_params.is_empty() {
            return Err(ComputedFieldError::InvalidField(name.clone()));
        }
        build.scan_closed(&definition.base.type_)?;
        let (parameters, result) = build.telescope(&definition.base.type_)?;
        if parameters.len() != 1
            || build.whnf(&parameters[0].type_)? != family_type
            || result.has_fvar()
            || result.has_expr_mvar()
            || result.has_level_mvar()
        {
            return Err(ComputedFieldError::InvalidField(name.clone()));
        }
        if !matches!(result.node(), ExprNode::Const { name, levels }
            if levels.is_empty() && ["Nat", "String", "Bool", "UInt64"].iter().any(|s| name == &Name::from_components([*s])))
        {
            return Err(ComputedFieldError::Unsupported(
                "computed cache results currently require Nat, String, Bool or UInt64",
            ));
        }
        computed.push(ComputedField {
            name: name.clone(),
            result_type: result,
        });
    }
    let mut constructors = Vec::new();
    for (index, name) in inductive.ctors.iter().enumerate() {
        let Some(ConstantInfo::Ctor(ctor)) = build.env.find(name) else {
            return Err(ComputedFieldError::InvalidInventory);
        };
        if ctor.induct != *family
            || ctor.cidx as usize != index
            || ctor.num_params != 0
            || ctor.is_unsafe
            || !ctor.base.level_params.is_empty()
        {
            return Err(ComputedFieldError::InvalidInventory);
        }
        build.scan_closed(&ctor.base.type_)?;
        constructors.push(ComputedConstructor {
            logical: name.clone(),
            implementation: Name::str(name.clone(), "_impl"),
            override_: Name::str(name.clone(), "_override"),
            num_fields: ctor.num_fields,
            cached: ctor.num_fields != 0,
        });
    }
    let cases_on = Name::str(family.clone(), "casesOn");
    Ok(ComputedFamily {
        family: family.clone(),
        implementation: Name::str(family.clone(), "_impl"),
        fields: computed,
        constructors,
        cases_on_override: Name::str(cases_on.clone(), "_override"),
        cases_on,
        overrides: vec![],
        inline_fields: vec![],
    })
}

/// Construct the cache-bearing implementation family. Its recursive object
/// fields retain their original logical type, as at the pin; casts are confined
/// to the generated executable replacements, never used for logical checking.
pub fn implementation_family(
    env: &Environment,
    family: &Name,
    fields: &[Name],
    kernel: Budget,
    budget: RecordBudget,
) -> Result<Declaration, ComputedFieldError> {
    let mut build = Build::new(env, kernel, budget);
    let model = profile(&mut build, family, fields)?;
    let mut constructors = Vec::new();
    let mut names = Vec::new();
    for (index, ctor) in model.constructors.iter().enumerate() {
        let original = env
            .find(&ctor.logical)
            .ok_or(ComputedFieldError::InvalidInventory)?;
        let (parameters, result) = build.telescope(&original.constant_val().type_)?;
        if result != constant(family) || parameters.len() != ctor.num_fields as usize {
            return Err(ComputedFieldError::InvalidInventory);
        }
        let mut cached = if ctor.cached {
            build.cache_locals(&model)?
        } else {
            vec![]
        };
        cached.extend(parameters);
        constructors.push(ConstructorSpec {
            name: Name::from_components([format!("ctor{index}").as_str()]),
            fields: cached,
            result_indices: vec![],
        });
        names.push(ctor.implementation.clone());
    }
    let spec = InductiveSpec {
        name: model.implementation,
        level_params: vec![],
        parameters: vec![],
        indices: vec![],
        constructors,
        result_level: Level::one(),
    };
    Ok(crate::inductive::inductive_with_external_constructor_names(
        &spec,
        &names,
        RecordBudget {
            max_nodes: build.work.remaining,
            max_binders: budget.max_binders,
        },
    )?)
}

/// Construct replacement candidates after `_impl` and its ordinary casesOn
/// have passed both checkers. No metadata is installed by this function.
pub fn replacements(
    env: &Environment,
    family: &Name,
    fields: &[Name],
    kernel: Budget,
    budget: RecordBudget,
) -> Result<Generated, ComputedFieldError> {
    let mut build = Build::new(env, kernel, budget);
    let model = profile(&mut build, family, fields)?;
    let family_type = constant(family);
    let impl_type = constant(&model.implementation);
    let impl_cases_name = Name::str(model.implementation.clone(), "casesOn");
    let Some(ConstantInfo::Defn(cases)) = env.find(&model.cases_on) else {
        return Err(ComputedFieldError::InvalidInventory);
    };
    let Some(ConstantInfo::Defn(_)) = env.find(&impl_cases_name) else {
        return Err(ComputedFieldError::InvalidInventory);
    };
    if cases.base.level_params.len() != 1 {
        return Err(ComputedFieldError::InvalidInventory);
    }
    let elimination = Level::param(cases.base.level_params[0].clone());
    let (parameters, result) = build.telescope(&cases.base.type_)?;
    if parameters.len() != model.constructors.len() + 2 || parameters[1].type_ != family_type {
        return Err(ComputedFieldError::InvalidInventory);
    }
    let impl_motive = Expr::let_e(
        Name::from_components(["m"]),
        Expr::sort(elimination.clone()),
        result.clone(),
        Expr::lam(
            Name::from_components(["a"]),
            impl_type.clone(),
            Expr::bvar(1).map_err(|_| ComputedFieldError::ResourceLimit)?,
            BinderInfo::Default,
        ),
        false,
    );
    let mut arguments = vec![
        impl_motive,
        cast(
            family_type.clone(),
            impl_type.clone(),
            fv(&parameters[1]),
            Level::one(),
            Level::one(),
        ),
    ];
    for (ctor, minor) in model.constructors.iter().zip(&parameters[2..]) {
        let (minor_args, minor_result) = build.telescope(&minor.type_)?;
        if minor_args.len() != ctor.num_fields as usize {
            return Err(ComputedFieldError::InvalidInventory);
        }
        let mut lambda_args = if ctor.cached {
            build.cache_locals(&model)?
        } else {
            vec![]
        };
        lambda_args.extend(minor_args.iter().cloned());
        let value = cast(
            minor_result,
            result.clone(),
            app(fv(minor), minor_args.iter().map(fv)),
            elimination.clone(),
            elimination.clone(),
        );
        arguments.push(build.close(&lambda_args, value, true)?);
    }
    let body = app(
        Expr::const_(impl_cases_name.clone(), vec![elimination]),
        arguments,
    );
    let body = build.close(&parameters, body, true)?;
    let mut definitions = vec![build.definition(
        model.cases_on_override.clone(),
        cases.base.level_params.clone(),
        cases.base.type_.clone(),
        body,
    )?];
    let mut edges = vec![(model.cases_on.clone(), model.cases_on_override.clone())];
    for ctor in &model.constructors {
        let original = env
            .find(&ctor.logical)
            .ok_or(ComputedFieldError::InvalidInventory)?;
        let (parameters, result) = build.telescope(&original.constant_val().type_)?;
        let term = app(constant(&ctor.logical), parameters.iter().map(fv));
        let mut arguments = Vec::new();
        if ctor.cached {
            for field in &model.fields {
                arguments.push(build.field_value(&field.name, &ctor.logical, term.clone())?);
            }
        }
        arguments.extend(parameters.iter().map(fv));
        let body = cast(
            impl_type.clone(),
            result,
            app(constant(&ctor.implementation), arguments),
            Level::one(),
            Level::one(),
        );
        let body = build.close(&parameters, body, true)?;
        definitions.push(build.definition(
            ctor.override_.clone(),
            vec![],
            original.constant_val().type_.clone(),
            body,
        )?);
        edges.push((ctor.logical.clone(), ctor.override_.clone()));
    }
    for (field_index, field) in model.fields.iter().enumerate() {
        let major = build.local(
            Name::from_components(["x"]),
            family_type.clone(),
            BinderInfo::Default,
        )?;
        let ignored = build.local(
            Name::from_components(["x"]),
            impl_type.clone(),
            BinderInfo::Default,
        )?;
        let motive = build.close(
            std::slice::from_ref(&ignored),
            field.result_type.clone(),
            true,
        )?;
        let mut arguments = vec![
            motive,
            cast(
                family_type.clone(),
                impl_type.clone(),
                fv(&major),
                Level::one(),
                Level::one(),
            ),
        ];
        for ctor in &model.constructors {
            let original = env
                .find(&ctor.logical)
                .ok_or(ComputedFieldError::InvalidInventory)?;
            let (parameters, _) = build.telescope(&original.constant_val().type_)?;
            let mut caches = if ctor.cached {
                build.cache_locals(&model)?
            } else {
                vec![]
            };
            let result = if ctor.cached {
                fv(&caches[field_index])
            } else {
                build.field_value(
                    &field.name,
                    &ctor.logical,
                    app(constant(&ctor.logical), parameters.iter().map(fv)),
                )?
            };
            caches.extend(parameters);
            arguments.push(build.close(&caches, result, true)?);
        }
        let body = app(
            Expr::const_(impl_cases_name.clone(), vec![Level::one()]),
            arguments,
        );
        let body = build.close(std::slice::from_ref(&major), body, true)?;
        let name = Name::str(field.name.clone(), "_override");
        let original = env
            .find(&field.name)
            .ok_or(ComputedFieldError::InvalidInventory)?;
        definitions.push(build.definition(
            name.clone(),
            vec![],
            original.constant_val().type_.clone(),
            body,
        )?);
        edges.push((field.name.clone(), name));
    }
    Ok(Generated {
        declarations: definitions.into_iter().map(Declaration::Defn).collect(),
        implemented_by: edges,
    })
}

fn compare_block(build: &mut Build<'_>, block: &InductiveBlock) -> Result<(), ComputedFieldError> {
    for value in &block.types {
        build.scan_closed(&value.base.type_)?;
        if build.env.find(&value.base.name) != Some(&ConstantInfo::Induct(value.clone())) {
            return Err(ComputedFieldError::InvalidInventory);
        }
    }
    for value in &block.ctors {
        build.scan_closed(&value.base.type_)?;
        if build.env.find(&value.base.name) != Some(&ConstantInfo::Ctor(value.clone())) {
            return Err(ComputedFieldError::InvalidInventory);
        }
    }
    for value in &block.recursors {
        build.scan_closed(&value.base.type_)?;
        for rule in &value.rules {
            build.scan_closed(&rule.rhs)?;
        }
        if build.env.find(&value.base.name) != Some(&ConstantInfo::Rec(value.clone())) {
            return Err(ComputedFieldError::InvalidInventory);
        }
    }
    Ok(())
}

fn validate_inventory(
    env: &Environment,
    family: &Name,
    fields: &[Name],
    kernel: Budget,
    budget: RecordBudget,
) -> Result<ComputedFamily, ComputedFieldError> {
    let implementation = implementation_family(env, family, fields, kernel, budget)?;
    let Declaration::Inductive(block) = implementation else {
        return Err(ComputedFieldError::InvalidInventory);
    };
    let generated = replacements(env, family, fields, kernel, budget)?;
    let mut build = Build::new(env, kernel, budget);
    let mut model = profile(&mut build, family, fields)?;
    compare_block(&mut build, &block)?;
    // Neither an arbitrary casesOn with a familiar name nor an altered cache
    // recursor can authorize a representation adapter.
    for name in [family, &model.implementation] {
        let Some(ConstantInfo::Induct(inductive)) = env.find(name) else {
            return Err(ComputedFieldError::InvalidInventory);
        };
        let Some(ConstantInfo::Rec(recursor)) = env.find(&Name::str(name.clone(), "rec")) else {
            return Err(ComputedFieldError::InvalidInventory);
        };
        // These two independent generators are phases five and six of the
        // advertised validation allowance; comparison stays in phase four.
        let canonical = crate::inductive::auxiliaries::cases_on_declaration(
            inductive,
            recursor,
            std::slice::from_ref(inductive),
            budget,
        )
        .map_err(|error| {
            if error == crate::inductive::auxiliaries::AuxiliaryError::ResourceLimit {
                ComputedFieldError::ResourceLimit
            } else {
                ComputedFieldError::InvalidInventory
            }
        })?;
        build.scan_closed(&canonical.base.type_)?;
        build.scan_closed(&canonical.value)?;
        if env.find(&canonical.base.name) != Some(&ConstantInfo::Defn(canonical)) {
            return Err(ComputedFieldError::InvalidInventory);
        }
    }
    for declaration in generated.declarations {
        let Declaration::Defn(definition) = declaration else {
            return Err(ComputedFieldError::InvalidInventory);
        };
        build.scan_closed(&definition.base.type_)?;
        build.scan_closed(&definition.value)?;
        if env.find(&definition.base.name) != Some(&ConstantInfo::Defn(definition.clone())) {
            return Err(ComputedFieldError::InvalidInventory);
        }
        model.overrides.push(definition);
    }
    let edges =
        crate::implemented_by::ImplementedByTable::read_metered(env, |amount| build.charge(amount))
            .map_err(|error| match error {
                crate::implemented_by::ImplementedByReadError::Budget(error) => error,
                crate::implemented_by::ImplementedByReadError::Registry(
                    crate::implemented_by::ImplementedByError::Limit,
                ) => ComputedFieldError::ResourceLimit,
                _ => ComputedFieldError::InvalidInventory,
            })?;
    let externs = crate::externs::ExternTable::read_metered(env, |amount| build.charge(amount))
        .map_err(|error| match error {
            crate::externs::ExternReadError::Budget(error) => error,
            crate::externs::ExternReadError::Registry(crate::externs::ExternError::Limit) => {
                ComputedFieldError::ResourceLimit
            }
            _ => ComputedFieldError::InvalidInventory,
        })?;
    for (logical, implementation) in &generated.implemented_by {
        if edges.get(logical) != Some(implementation)
            || edges.get(implementation).is_some()
            || externs.get(logical).is_some()
            || externs.get(implementation).is_some()
        {
            return Err(ComputedFieldError::InvalidInventory);
        }
    }
    for name in model
        .constructors
        .iter()
        .map(|ctor| ctor.implementation.clone())
        .chain([
            Name::str(model.implementation.clone(), "casesOn"),
            Name::from_components(["unsafeCast"]),
        ])
    {
        if edges.get(&name).is_some() || externs.get(&name).is_some() {
            return Err(ComputedFieldError::InvalidInventory);
        }
    }
    Ok(model)
}
