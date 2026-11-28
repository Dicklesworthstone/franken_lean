//! Execute native computed-field declarations through their checked generator
//! provenance. Neither a familiar `_impl` spelling nor an `unsafeCast` call
//! grants representation authority. Logical declarations remain unchanged.
use super::*;
use fln_elab::computed_fields::{self as generated, ComputedFamily, ComputedFieldError};
use fln_elab::records::RecordBudget;
use std::collections::HashMap;
mod cast;

#[derive(Default)]
pub(super) struct Store {
    claims: Option<HashSet<Name>>,
    families: HashMap<Name, ComputedFamily>,
    overrides: HashMap<Name, DefinitionVal>,
    cast_checked: bool,
}

fn metadata_error(error: ComputedFieldError) -> IngressError {
    match error {
        ComputedFieldError::ResourceLimit => IngressError::MetadataResourceExhausted {
            kind: "computed-field provenance validation",
        },
        _ => unsupported("invalid computed-field generation provenance"),
    }
}

impl Preparation<'_> {
    /// Each generator phase has its own bounded traversal. Reserve its whole
    /// allowance before entering it, so validation cannot escape the aggregate
    /// ingress limit even when a failed comparison visits its last node.
    fn computed_validation_budget(
        &mut self,
        phases: usize,
        cap: usize,
    ) -> Result<RecordBudget, IngressError> {
        self.tick()?;
        let remaining = self.limits.max_nodes.saturating_sub(self.visited);
        let nodes = cap.min(remaining / phases.saturating_add(1));
        if nodes == 0 {
            return Err(IngressError::MetadataResourceExhausted {
                kind: "computed-field provenance validation",
            });
        }
        self.visited = self.visited.saturating_add(nodes.saturating_mul(phases));
        Ok(RecordBudget {
            max_binders: self
                .limits
                .max_context_depth
                .min(self.limits.fir.max_constructors),
            max_nodes: nodes,
        })
    }

    fn computed_claims(&mut self) -> Result<&HashSet<Name>, IngressError> {
        if self.computed_fields.claims.is_none() {
            self.tick()?;
            let claims = if self
                .environment
                .extension(&generated::journal_name())
                .is_none()
            {
                Vec::new()
            } else {
                let budget = self.computed_validation_budget(1, 4_096)?;
                generated::families(self.environment, budget).map_err(metadata_error)?
            };
            let mut names = HashSet::new();
            names
                .try_reserve(claims.len())
                .map_err(|_| IngressError::AllocationFailure {
                    resource: IngressResource::ProgramTables,
                    requested: claims.len(),
                })?;
            for claim in claims {
                self.tick()?;
                names.insert(claim);
            }
            self.computed_fields.claims = Some(names);
        }
        Ok(self
            .computed_fields
            .claims
            .as_ref()
            .expect("complete computed-field claims"))
    }

    fn computed_family(&mut self, family: &Name) -> Result<Option<ComputedFamily>, IngressError> {
        if !self.computed_claims()?.contains(family) {
            return Ok(None);
        }
        if let Some(model) = self.computed_fields.families.get(family) {
            return Ok(Some(model.clone()));
        }
        let kernel = self.computed_field_kernel.ok_or_else(|| {
            unsupported("computed-field validation requires the caller's calibrated kernel budget")
        })?;
        let budget = self.computed_validation_budget(generated::VALIDATION_PHASES, 100_000)?;
        let model = generated::validated_family(self.environment, family, kernel, budget)
            .map_err(metadata_error)?
            .ok_or_else(|| {
                unsupported("computed-field provenance claim has no validated family")
            })?;
        self.check_computed_cast_primitive()?;
        // The generator has no runtime initializer table. Its exact stored
        // bodies cannot authorize bypassing globals supplied by initialization.
        let initialized = |name: &Name| {
            self.runtime_initializers
                .is_some_and(|names| names.contains(name))
        };
        if initialized(&model.family)
            || initialized(&model.implementation)
            || initialized(&model.cases_on)
            || initialized(&Name::str(model.implementation.clone(), "casesOn"))
            || model.fields.iter().any(|field| initialized(&field.name))
            || model
                .constructors
                .iter()
                .any(|ctor| initialized(&ctor.logical) || initialized(&ctor.implementation))
            || model
                .overrides
                .iter()
                .any(|definition| initialized(&definition.base.name))
        {
            return Err(unsupported(
                "computed-field representation requires runtime initialization",
            ));
        }
        // A private implementation constructor or generated override must run
        // the exact body/layout validated above, with no second dispatch edge.
        // Logical getters may have externs; their ordinary native selection
        // remains authoritative when the getter is actually executed.
        for requested in model
            .constructors
            .iter()
            .map(|ctor| &ctor.implementation)
            .chain(
                model
                    .overrides
                    .iter()
                    .map(|definition| &definition.base.name),
            )
        {
            self.tick()?;
            if self.implementations()?.get(requested).is_some()
                || self.has_extern_attribute(requested)?
                || self
                    .environment
                    .contains(&Name::str(requested.clone(), "_unsafe_rec"))
            {
                return Err(unsupported(
                    "computed-field generated declaration has conflicting execution metadata",
                ));
            }
        }
        self.computed_fields.families.try_reserve(1).map_err(|_| {
            IngressError::AllocationFailure {
                resource: IngressResource::ProgramTables,
                requested: self.computed_fields.families.len().saturating_add(1),
            }
        })?;
        self.computed_fields
            .families
            .insert(family.clone(), model.clone());
        Ok(Some(model))
    }

    /// A namespace prefix selects a candidate only. Successful regeneration,
    /// exact declaration inventory and metadata checks confer all authority.
    fn computed_family_for_name(
        &mut self,
        requested: &Name,
    ) -> Result<Option<ComputedFamily>, IngressError> {
        if self.computed_claims()?.is_empty() {
            return Ok(None);
        }
        let mut candidate = requested.clone();
        while !candidate.is_anonymous() {
            self.tick()?;
            if self.computed_claims()?.contains(&candidate) {
                return self.computed_family(&candidate);
            }
            candidate = candidate.parent();
        }
        Ok(None)
    }

    pub(super) fn computed_family_for_type(
        &mut self,
        requested: &Name,
    ) -> Result<Option<ComputedFamily>, IngressError> {
        Ok(self
            .computed_family_for_name(requested)?
            .filter(|model| model.family == *requested || model.implementation == *requested))
    }

    pub(super) fn native_computed_operation(
        &mut self,
        requested: &Name,
    ) -> Result<bool, IngressError> {
        Ok(self
            .computed_family_for_name(requested)?
            .is_some_and(|model| {
                model.cases_on == *requested
                    || model
                        .constructors
                        .iter()
                        .any(|ctor| ctor.logical == *requested)
                    || model.fields.iter().any(|field| field.name == *requested)
            }))
    }

    /// Rewrite only a generated body with an exact validated provenance entry.
    /// This occurs while its admitted declaration identity is still available,
    /// before generic specialization or inlining loses that origin. Casts in
    /// arbitrary source functions, even between these same types, gain nothing.
    pub(super) fn computed_override_definition(
        &mut self,
        requested: &Name,
    ) -> Result<Option<DefinitionVal>, IngressError> {
        if let Some(definition) = self.computed_fields.overrides.get(requested) {
            return Ok(Some(definition.clone()));
        }
        let Some(model) = self.computed_family_for_name(requested)? else {
            return Ok(None);
        };
        let Some(original) = model
            .overrides
            .iter()
            .find(|definition| definition.base.name == *requested)
        else {
            return Ok(None);
        };
        if self.environment.find(requested) != Some(&ConstantInfo::Defn(original.clone())) {
            return Err(unsupported(
                "computed-field override differs from its generated inventory",
            ));
        }
        let mut definition = original.clone();
        definition.value = self.erase_generated_computed_casts(&definition.value)?;
        self.computed_fields.overrides.try_reserve(1).map_err(|_| {
            IngressError::AllocationFailure {
                resource: IngressResource::ProgramTables,
                requested: self.computed_fields.overrides.len().saturating_add(1),
            }
        })?;
        self.computed_fields
            .overrides
            .insert(requested.clone(), definition.clone());
        Ok(Some(definition))
    }

    fn erase_generated_computed_casts(&mut self, input: &Expr) -> Result<Expr, IngressError> {
        enum Task {
            Visit(Expr),
            Finish(Expr),
            Cast(Expr, Expr),
        }
        let mut tasks = vec![Task::Visit(input.clone())];
        let mut values = HashMap::<Expr, Expr>::new();
        while let Some(task) = tasks.pop() {
            self.tick()?;
            let (original, rewritten) = match task {
                Task::Visit(expr) => {
                    if values.contains_key(&expr) {
                        continue;
                    }
                    if let Some(operand) = generated_cast_operand(&expr) {
                        reserve(&mut tasks, self.limits.max_nodes)?;
                        tasks.push(Task::Cast(expr.clone(), operand.clone()));
                        reserve(&mut tasks, self.limits.max_nodes)?;
                        tasks.push(Task::Visit(operand.clone()));
                        continue;
                    }
                    reserve(&mut tasks, self.limits.max_nodes)?;
                    tasks.push(Task::Finish(expr.clone()));
                    let children: Vec<&Expr> = match expr.node() {
                        ExprNode::App { f, a } => vec![f, a],
                        ExprNode::Lam {
                            binder_type, body, ..
                        }
                        | ExprNode::ForallE {
                            binder_type, body, ..
                        } => vec![binder_type, body],
                        ExprNode::LetE {
                            type_, value, body, ..
                        } => vec![type_, value, body],
                        ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => vec![expr],
                        ExprNode::Const { name: constant, .. }
                            if constant == &name("unsafeCast") =>
                        {
                            return Err(unsupported(
                                "generated computed-field cast is not fully applied",
                            ));
                        }
                        _ => Vec::new(),
                    };
                    for child in children {
                        reserve(&mut tasks, self.limits.max_nodes)?;
                        tasks.push(Task::Visit(child.clone()));
                    }
                    continue;
                }
                Task::Cast(original, operand) => {
                    let rewritten = values
                        .get(&operand)
                        .cloned()
                        .ok_or_else(|| unsupported("computed cast traversal result"))?;
                    (original, rewritten)
                }
                Task::Finish(original) => {
                    let get = |child: &Expr| {
                        values
                            .get(child)
                            .cloned()
                            .ok_or_else(|| unsupported("computed override traversal result"))
                    };
                    let rewritten = match original.node() {
                        ExprNode::App { f, a } => Expr::app(get(f)?, get(a)?),
                        ExprNode::Lam {
                            binder_name,
                            binder_type,
                            body,
                            binder_info,
                        } => Expr::lam(
                            binder_name.clone(),
                            get(binder_type)?,
                            get(body)?,
                            *binder_info,
                        ),
                        ExprNode::ForallE {
                            binder_name,
                            binder_type,
                            body,
                            binder_info,
                        } => Expr::forall_e(
                            binder_name.clone(),
                            get(binder_type)?,
                            get(body)?,
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
                            get(type_)?,
                            get(value)?,
                            get(body)?,
                            *non_dep,
                        ),
                        ExprNode::MData { data, expr } => Expr::mdata(data.clone(), get(expr)?),
                        ExprNode::Proj {
                            struct_name,
                            idx,
                            expr,
                        } => Expr::proj(struct_name.clone(), *idx, get(expr)?),
                        _ => original.clone(),
                    };
                    (original, rewritten)
                }
            };
            values
                .try_reserve(1)
                .map_err(|_| IngressError::AllocationFailure {
                    resource: IngressResource::Nodes,
                    requested: values.len().saturating_add(1),
                })?;
            values.insert(original, rewritten);
        }
        values
            .remove(input)
            .ok_or_else(|| unsupported("computed override traversal result"))
    }
}

fn generated_cast_operand(expr: &Expr) -> Option<&Expr> {
    let ExprNode::App { f, a: operand } = expr.node() else {
        return None;
    };
    let ExprNode::App { f, .. } = f.node() else {
        return None;
    };
    let ExprNode::App { f, .. } = f.node() else {
        return None;
    };
    matches!(f.node(), ExprNode::Const { name: constant, levels }
        if constant == &name("unsafeCast") && levels.len() == 2)
    .then_some(operand)
}
