//! Derive object-field layouts from admitted, closed data families.
//! These are native FIR layouts, not a claim of Reference packed-ABI parity.
//! Closed type parameters are specialized, never stored as runtime fields.
//! Direct and function-valued self- and mutually recursive fields are supported.
//! Proof fields keep inert scalar slots; other value-dependent fields remain
//! refusals unless their checked indices erase to a uniform representation.
//! Nondependent function fields are owned closures with checked interfaces.
//! Type-valued fields are runtime-irrelevant, as in the Reference's compiler:
//! each keeps an inert scalar slot, like a proof. Dependent fields use a boxed
//! leaf through uniform containers and explicitly adapted callback interfaces.
mod adapters;
mod erased;
use super::*;
use fln_comp::ingress::ConstructorBinding;
use fln_core::level::Level;
use fln_env::constants::RecursorVal;

#[derive(Clone)]
pub(super) struct Shape {
    pub source: Expr,
    pub name: Name,
    pub recursive: bool,
    pub constructors: Vec<ShapeConstructor>,
}

#[derive(Clone)]
pub(super) struct ShapeConstructor {
    pub original: Name,
    pub name: Name,
    pub tag: u8,
    pub fields: Vec<Expr>,
    /// Which fields hold a type (or type former) and are erased at runtime.
    pub type_fields: Vec<bool>,
}

/// The layout-only field type of a boxed polymorphic slot. It names no
/// declaration and never reaches a checker. Recognition is enabled only after
/// the immutable environment passes the reserved-name check.
pub(super) fn boxed_slot_type() -> Expr {
    Expr::const_(name("_fln_runtime_boxed"), vec![])
}

impl Shape {
    pub(super) fn projection(&self, constructor: &ShapeConstructor) -> Name {
        if self.constructors.len() == 1 {
            self.name.clone()
        } else {
            // Private post-admission projection keys select the exact variant
            // layout. Only the corresponding tested branch evaluates them.
            constructor.name.clone()
        }
    }
}

impl Preparation<'_> {
    pub(super) fn record_shape(&mut self, source: &Expr) -> Result<Option<Shape>, IngressError> {
        self.tick()?;
        let source = self.erase_data_indices(source)?;
        if source.has_loose_bvars()
            || source.has_fvar()
            || source.has_expr_mvar()
            || source.has_level_mvar()
            || source.has_level_param()
        {
            return Ok(None);
        }
        if let Some(shape) = self.data_shapes.get(&source) {
            return Ok(Some(shape.clone()));
        }
        let (head, parameters) = self.spine(&source)?;
        let ExprNode::Const { name, levels } = head.node() else {
            return Ok(None);
        };
        let Some(ConstantInfo::Induct(family)) = self.environment.find(name) else {
            return Ok(None);
        };
        if family.is_unsafe
            || family.num_params as usize != parameters.len()
            || family.num_nested != 0
            || !family.all.contains(name)
            || family.base.level_params.len() != levels.len()
        {
            return Ok(None);
        }
        let mut family_type =
            self.universe_instance(&family.base.type_, &family.base.level_params, levels)?;
        let erased = self.erased_parameter()?;
        let pending = indexed::pending_parameter();
        let mut values = Vec::new();
        for parameter in &parameters {
            self.tick()?;
            let normal = self.normalize_type(&family_type)?;
            let ExprNode::ForallE {
                binder_type, body, ..
            } = normal.node()
            else {
                return Ok(None);
            };
            // A value parameter is not a field: as in the pinned compiler, a
            // constructor object stores only its fields. One layout serves
            // every value, so only the erased key has one. Whether a field's
            // representation depends on the value is decided below, after
            // erasure, never by guessing from a particular (closed) value.
            let value = !self.type_parameter(binder_type)?;
            if value && parameter != &erased {
                return Ok(None);
            }
            family_type = self.substitution(body, if value { &pending } else { parameter })?;
            reserve(&mut values, self.limits.max_context_depth)?;
            values.push(value);
        }
        if family.num_indices != 0 {
            if self.index_domains(family, levels, &parameters)?.is_none() {
                return Ok(None);
            }
        } else {
            let family_type = self.normalize_type(&family_type)?;
            if !matches!(family_type.node(), ExprNode::Sort { level } if level.is_never_zero()) {
                return Ok(None);
            }
        }
        let specialized = !parameters.is_empty() || !levels.is_empty();
        let layout_name = if specialized {
            if self.data_shapes.len() >= self.limits.fir.max_constructors {
                return Err(IngressError::ResourceLimit {
                    resource: IngressResource::ProgramTables,
                    limit: self.limits.fir.max_constructors,
                    observed: self.data_shapes.len().saturating_add(1),
                });
            }
            let serial = u64::try_from(self.data_shapes.len())
                .map_err(|_| unsupported("data specialization identity"))?;
            let name = Name::num(super::name("_fln_runtime_data"), serial);
            if self.environment.contains(&name) {
                return Err(unsupported("runtime data name collision"));
            }
            name
        } else {
            name.clone()
        };
        let mut constructors = Vec::new();
        for (index, ctor_name) in family.ctors.iter().enumerate() {
            self.tick()?;
            let Some(ConstantInfo::Ctor(ctor)) = self.environment.find(ctor_name) else {
                return Ok(None);
            };
            let Ok(tag) = u8::try_from(index) else {
                return Ok(None);
            };
            // FIR ingress validates the ABI tag ceiling before execution.
            if ctor.is_unsafe
                || ctor.induct != *name
                || ctor.num_params != family.num_params
                || ctor.cidx as usize != index
                || ctor.base.level_params != family.base.level_params
            {
                return Ok(None);
            }
            let mut fields = Vec::new();
            let mut type_ =
                self.universe_instance(&ctor.base.type_, &ctor.base.level_params, levels)?;
            for (parameter, value) in parameters.iter().zip(&values) {
                self.tick()?;
                let ExprNode::ForallE { body, .. } = type_.node() else {
                    return Ok(None);
                };
                type_ = self.substitution(body, if *value { &pending } else { parameter })?;
            }
            // Erase the checked telescope before deciding whether a field's
            // representation depends on an earlier runtime value. A proof may
            // mention that value, but its inert slot never depends on it. The
            // logical field count/order is retained for projections and minors.
            type_ = self.erase_runtime_type(&type_)?;
            // The same holds for a value parameter: a proof about it, or a
            // family taking it as a value parameter or scalar index, erases
            // it. Anything still mentioning it (a type computed from the
            // value) has no uniform representation and is refused.
            if type_.has_fvar() {
                return Ok(None);
            }
            let mut type_fields = Vec::new();
            while let ExprNode::ForallE {
                binder_type, body, ..
            } = type_.node()
            {
                self.tick()?;
                let Some(field) = self.erase_field_dependencies(binder_type, &type_fields)? else {
                    return Ok(None);
                };
                let field = self.normalize_type(&field)?;
                let (field, type_field) = if self.type_parameter(&field)? {
                    (proofs::erased_type(), true)
                } else {
                    let (head, _) = self.spine(&field)?;
                    if !matches!(
                        head.node(),
                        ExprNode::Const { .. } | ExprNode::ForallE { .. }
                    ) {
                        return Ok(None);
                    }
                    (field, false)
                };
                reserve(&mut fields, self.limits.max_context_depth)?;
                fields.push(field);
                reserve(&mut type_fields, self.limits.max_context_depth)?;
                type_fields.push(type_field);
                type_ = body.clone();
            }
            if type_.has_loose_bvars()
                || fields.len() != ctor.num_fields as usize
                || self.normalize_type(&type_)? != source
            {
                return Ok(None);
            }
            let constructor_name = if specialized {
                Name::num(layout_name.clone(), index as u64)
            } else {
                ctor.base.name.clone()
            };
            if specialized && self.environment.contains(&constructor_name) {
                return Err(unsupported("runtime data constructor collision"));
            }
            reserve(&mut constructors, self.limits.fir.max_constructors)?;
            constructors.push(ShapeConstructor {
                original: ctor.base.name.clone(),
                name: constructor_name,
                tag,
                fields,
                type_fields,
            });
        }
        let shape = Shape {
            source: source.clone(),
            name: layout_name,
            recursive: family.is_rec,
            constructors,
        };
        self.data_shapes
            .try_reserve(1)
            .map_err(|_| IngressError::AllocationFailure {
                resource: IngressResource::ProgramTables,
                requested: self.data_shapes.len().saturating_add(1),
            })?;
        self.data_shapes.insert(source, shape.clone());
        Ok(Some(shape))
    }

    /// Resolve one complete admitted mutual block at the same ground type
    /// arguments. All members must have usable layouts, even when the caller
    /// initially reaches only one member. No provisional layout is published.
    pub(super) fn record_group(
        &mut self,
        source: &Expr,
    ) -> Result<Option<Vec<Shape>>, IngressError> {
        let source = self.erase_data_indices(source)?;
        let (head, parameters) = self.spine(&source)?;
        let ExprNode::Const { name, levels } = head.node() else {
            return Ok(None);
        };
        let Some(ConstantInfo::Induct(family)) = self.environment.find(name) else {
            return Ok(None);
        };
        let mut shapes = Vec::new();
        let mut seen = HashSet::new();
        for member in &family.all {
            self.tick()?;
            let Some(ConstantInfo::Induct(info)) = self.environment.find(member) else {
                return Ok(None);
            };
            if info.all != family.all
                || info.num_params != family.num_params
                || info.base.level_params != family.base.level_params
                || !seen.insert(member.clone())
            {
                return Ok(None);
            }
            let mut type_ = Expr::const_(member.clone(), levels.clone());
            for argument in &parameters {
                self.tick()?;
                type_ = Expr::app(type_, argument.clone());
            }
            let Some(shape) = self.record_shape(&type_)? else {
                return Ok(None);
            };
            reserve(&mut shapes, self.limits.max_context_depth)?;
            shapes.push(shape);
        }
        Ok(Some(shapes))
    }

    /// Discover data and function representations in one heap worklist. A
    /// record may contain closures whose arguments/results contain more data;
    /// alternating those types must not alternate recursive Rust calls.
    pub(super) fn value_type(&mut self, source: &Expr) -> Result<Option<ValueType>, IngressError> {
        self.tick()?;
        // These exact keys already passed representation discovery. Repeated
        // capture sites need not re-erase the same registered telescope. Keep
        // scalar name recognition below normalization: a familiar name alone
        // is not a cached record or callback representation.
        if let Some(value) = self.value_types.closures.get(source) {
            return Ok(Some(*value));
        }
        if self.value_types.records.contains(source) {
            return Ok(Some(ValueType::Constructor));
        }
        let source = self.erase_data_indices(source)?;
        if let Some((value, _)) = executable_value_type(&source, &self.value_types) {
            return Ok(Some(value));
        }
        let first_interface = self.interfaces.len();
        let first_constructor = self.constructors.len();
        let mut added_records = Vec::new();
        let result = self.discover_value_type(source, &mut added_records);
        if !matches!(result, Ok(Some(_))) {
            // Data anchors let a callback return its enclosing family without
            // recursively reentering discovery. They are not valid bindings
            // until the entire representation graph has finished. Roll back
            // every dependent interface and constructor on refusal or resource
            // exhaustion; retain spent work and descriptive normalization caches.
            for source in added_records {
                self.value_types.records.remove(&source);
            }
            self.value_types.closures.retain(|_, value| {
                matches!(value, ValueType::Closure(id) if (id.get() as usize) < first_interface)
            });
            self.interfaces.truncate(first_interface);
            while self.constructors.len() > first_constructor {
                let constructor = self.constructors.pop().expect("new constructor");
                self.forget_constructor_type(&constructor.name);
            }
        }
        result
    }

    fn discover_value_type(
        &mut self,
        source: Expr,
        added_records: &mut Vec<Expr>,
    ) -> Result<Option<ValueType>, IngressError> {
        enum Task {
            Enter(Expr),
            Finish(Vec<Shape>),
            Function {
                source: Expr,
                domains: Vec<Expr>,
                result: Expr,
            },
        }
        let mut tasks = vec![Task::Enter(source.clone())];
        let mut active = HashSet::new();
        while let Some(task) = tasks.pop() {
            self.tick()?;
            match task {
                Task::Enter(source) => {
                    if executable_value_type(&source, &self.value_types).is_some() {
                        continue;
                    }
                    if source.has_loose_bvars() || active.contains(&source) {
                        return Ok(None);
                    }
                    let depth = active.len().saturating_add(1);
                    if depth > self.limits.max_context_depth {
                        return Err(IngressError::ResourceLimit {
                            resource: IngressResource::ContextDepth,
                            limit: self.limits.max_context_depth,
                            observed: depth,
                        });
                    }
                    active
                        .try_reserve(1)
                        .map_err(|_| IngressError::AllocationFailure {
                            resource: IngressResource::ContextDepth,
                            requested: depth,
                        })?;
                    active.insert(source.clone());
                    if matches!(source.node(), ExprNode::ForallE { .. }) {
                        let mut remaining = &source;
                        let mut domains = Vec::new();
                        while let ExprNode::ForallE {
                            binder_type, body, ..
                        } = remaining.node()
                        {
                            self.tick()?;
                            if body.has_loose_bvars() {
                                return Ok(None);
                            }
                            reserve(&mut domains, self.limits.max_context_depth)?;
                            domains.push(binder_type.clone());
                            remaining = body;
                        }
                        let result = remaining.clone();
                        reserve(&mut tasks, self.limits.max_nodes)?;
                        tasks.push(Task::Function {
                            source,
                            domains: domains.clone(),
                            result: result.clone(),
                        });
                        reserve(&mut tasks, self.limits.max_nodes)?;
                        tasks.push(Task::Enter(result));
                        for domain in domains.into_iter().rev() {
                            reserve(&mut tasks, self.limits.max_nodes)?;
                            tasks.push(Task::Enter(domain));
                        }
                        continue;
                    }
                    let Some(shapes) = self.record_group(&source)? else {
                        return Ok(None);
                    };
                    for shape in &shapes {
                        self.tick()?;
                        if shape.source == source {
                            continue;
                        }
                        if active.contains(&shape.source) {
                            return Ok(None);
                        }
                        let depth = active.len().saturating_add(1);
                        if depth > self.limits.max_context_depth {
                            return Err(IngressError::ResourceLimit {
                                resource: IngressResource::ContextDepth,
                                limit: self.limits.max_context_depth,
                                observed: depth,
                            });
                        }
                        active
                            .try_reserve(1)
                            .map_err(|_| IngressError::AllocationFailure {
                                resource: IngressResource::ContextDepth,
                                requested: depth,
                            })?;
                        active.insert(shape.source.clone());
                    }
                    for shape in &shapes {
                        self.tick()?;
                        reserve(added_records, self.limits.fir.max_constructors)?;
                        self.value_types.records.try_reserve(1).map_err(|_| {
                            IngressError::AllocationFailure {
                                resource: IngressResource::ProgramTables,
                                requested: self.value_types.records.len().saturating_add(1),
                            }
                        })?;
                        if self.value_types.records.insert(shape.source.clone()) {
                            added_records.push(shape.source.clone());
                        }
                    }
                    let mut dependencies = Vec::new();
                    for field in shapes
                        .iter()
                        .flat_map(|shape| &shape.constructors)
                        .flat_map(|ctor| &ctor.fields)
                    {
                        self.tick()?;
                        // A familiar scalar name is not a representation.
                        // Imported UInt32/UInt64 are checked records; discover
                        // their fields before completing an enclosing record.
                        if executable_value_type(field, &self.value_types).is_none()
                            && field != &boxed_slot_type()
                            && !shapes.iter().any(|shape| &shape.source == field)
                        {
                            reserve(&mut dependencies, self.limits.max_nodes)?;
                            dependencies.push(field.clone());
                        }
                    }
                    reserve(&mut tasks, self.limits.max_nodes)?;
                    tasks.push(Task::Finish(shapes));
                    for dependency in dependencies.into_iter().rev() {
                        reserve(&mut tasks, self.limits.max_nodes)?;
                        tasks.push(Task::Enter(dependency));
                    }
                }
                Task::Function {
                    source,
                    domains,
                    result,
                } => {
                    let Some((result, _)) = executable_value_type(&result, &self.value_types)
                    else {
                        return Ok(None);
                    };
                    let mut parameters = Vec::new();
                    for domain in domains {
                        self.tick()?;
                        let Some((parameter, _)) =
                            executable_value_type(&domain, &self.value_types)
                        else {
                            return Ok(None);
                        };
                        reserve(&mut parameters, self.limits.max_context_depth)?;
                        parameters.push(parameter);
                    }
                    self.register_function_type(source.clone(), parameters, result)?;
                    active.remove(&source);
                }
                Task::Finish(shapes) => {
                    for shape in &shapes {
                        for ctor in &shape.constructors {
                            let mut fields = Vec::new();
                            for field in &ctor.fields {
                                self.tick()?;
                                let value = if shapes.iter().any(|member| field == &member.source) {
                                    ValueType::Constructor
                                } else if field == &boxed_slot_type() {
                                    ValueType::Abi
                                } else if let Some((value, _)) =
                                    executable_value_type(field, &self.value_types)
                                {
                                    value
                                } else {
                                    return Ok(None);
                                };
                                reserve(&mut fields, self.limits.max_context_depth)?;
                                fields.push(value);
                            }
                            reserve(&mut self.constructors, self.limits.fir.max_constructors)?;
                            self.constructors.push(ConstructorBinding {
                                name: ctor.name.clone(),
                                projection_structure: Some(shape.projection(ctor)),
                                universe_arity: 0,
                                tag: ctor.tag,
                                fields,
                                static_scalar_bytes: Vec::new(),
                            });
                            // Preserve the checked ground telescope for a constructor
                            // passed as a function. Its parameters have already been
                            // erased; every remaining domain is an actual field.
                            let mut type_ = shape.source.clone();
                            for field in ctor.fields.iter().rev() {
                                self.tick()?;
                                type_ = Expr::forall_e(
                                    Name::anonymous(),
                                    field.clone(),
                                    type_,
                                    BinderInfo::Default,
                                );
                            }
                            self.remember_constructor_type(ctor.name.clone(), type_)?;
                        }
                        active.remove(&shape.source);
                    }
                }
            }
        }
        Ok(executable_value_type(&source, &self.value_types).map(|(value, _)| value))
    }

    pub(crate) fn signature(
        &mut self,
        definition: &DefinitionVal,
        eta_expand: bool,
    ) -> Result<Option<ExecutableSignature>, IngressError> {
        if !definition.base.level_params.is_empty() {
            return Ok(None);
        }
        let definition = self.normalize_definition_signature(definition)?;
        let mut type_ = &definition.base.type_;
        loop {
            self.tick()?;
            match type_.node() {
                ExprNode::ForallE {
                    binder_type, body, ..
                } => {
                    if self.value_type(binder_type)?.is_none() {
                        return Ok(None);
                    }
                    type_ = body;
                }
                _ => {
                    if self.value_type(type_)?.is_none() {
                        return Ok(None);
                    }
                    break;
                }
            }
        }
        // Register a local stage's callback suffix before deriving metadata.
        // This does not change any global function's flat calling interface.
        let mut result_type = &definition.base.type_;
        let mut value = &definition.value;
        while let (ExprNode::ForallE { body: result, .. }, ExprNode::Lam { body, .. }) =
            (result_type.node(), value.node())
        {
            self.tick()?;
            result_type = result;
            value = body;
        }
        if eta_expand
            && definition.safety == fln_env::constants::DefinitionSafety::Partial
            && matches!(result_type.node(), ExprNode::ForallE { .. })
        {
            // A partial prefix can diverge before it returns a callback.
            // The flat global ABI must not move that work beneath invented
            // lambdas. Until partial producers have an explicit stage ABI,
            // refuse this shape after proof erasure and specialization.
            return Err(unsupported("partial function-producing stage"));
        }
        if !eta_expand && matches!(result_type.node(), ExprNode::ForallE { .. }) {
            self.value_type(result_type)?;
        }
        executable_signature(
            &definition,
            &self.value_types,
            &mut self.visited,
            self.limits,
            eta_expand,
        )
    }

    /// Select a ground layout from the recursor's own admitted parameter and
    /// universe telescope. The motive universe is not a family parameter.
    pub(super) fn recursor_shape(
        &mut self,
        rec: &RecursorVal,
        levels: &[Level],
        args: &[Expr],
    ) -> Result<Option<Shape>, IngressError> {
        if rec.is_unsafe
            || rec.all.len() != 1
            || rec.num_motives != 1
            || rec.base.level_params.len() != levels.len()
            || args.len() < rec.num_params as usize
        {
            return Ok(None);
        }
        let Some(ConstantInfo::Induct(family)) = self.environment.find(&rec.all[0]) else {
            return Ok(None);
        };
        if rec.num_params != family.num_params
            || rec.num_indices != family.num_indices
            || rec.num_minors as usize != family.ctors.len()
        {
            return Ok(None);
        }
        let mut family_levels = Vec::new();
        for parameter in &family.base.level_params {
            self.tick()?;
            let mut selected = None;
            for (index, name) in rec.base.level_params.iter().enumerate() {
                self.tick()?;
                if name == parameter {
                    selected = Some(levels[index].clone());
                    break;
                }
            }
            let Some(level) = selected else {
                return Ok(None);
            };
            reserve(&mut family_levels, self.limits.max_context_depth)?;
            family_levels.push(level);
        }
        // Value-parameter arguments are erased like type arguments: the
        // recursor's layout never depends on them, and they are not evaluated.
        let source =
            self.runtime_family(family, &family_levels, &args[..rec.num_params as usize])?;
        let source = self.normalize_type(&source)?;
        if self.value_type(&source)? != Some(ValueType::Constructor) {
            return Ok(None);
        }
        self.record_shape(&source)
    }

    /// Type parameters and universes choose a private constructor binding;
    /// runtime fields stay in their original order and are never evaluated or
    /// duplicated here. No specialized name enters the logical environment.
    pub(super) fn specialize_constructor(
        &mut self,
        head: &Expr,
        args: &[Expr],
    ) -> Result<Option<Expr>, IngressError> {
        let ExprNode::Const { name, levels } = head.node() else {
            return Ok(None);
        };
        let Some(ConstantInfo::Ctor(ctor)) = self.environment.find(name) else {
            return Ok(None);
        };
        let parameters = ctor.num_params as usize;
        // A nonparametric constructor keeps its own name. It is rewritten only
        // to erase a type-valued field argument that is still present.
        let specialized = parameters != 0 || !levels.is_empty();
        if !specialized && args.is_empty() || args.len() < parameters {
            return Ok(None);
        }
        let Some(ConstantInfo::Induct(inductive)) = self.environment.find(&ctor.induct) else {
            return Ok(None);
        };
        // A value parameter is not stored in the object and, like a type
        // argument, is dropped here without being evaluated.
        let family = self.runtime_family(inductive, levels, &args[..parameters])?;
        let family = self.normalize_type(&family)?;
        if self.value_type(&family)? != Some(ValueType::Constructor) {
            return Ok(None);
        }
        let Some(shape) = self.record_shape(&family)? else {
            return Ok(None);
        };
        let Some(binding) = shape.constructors.iter().find(|c| c.original == *name) else {
            return Ok(None);
        };
        // Recover concrete field types before erasing the carrier arguments.
        // An already-erased application is final: never interpret its inert
        // Boolean type slots as fresh source type arguments on a second visit.
        let adapt = args[parameters..].iter().enumerate().any(|(index, field)| {
            binding.type_fields.get(index) == Some(&true) && field != &proofs::erased_value()
        });
        let mut actual_type = if adapt {
            let mut type_ =
                self.universe_instance(&ctor.base.type_, &ctor.base.level_params, levels)?;
            for parameter in &args[..parameters] {
                self.tick()?;
                let ExprNode::ForallE { body, .. } = type_.node() else {
                    return Err(unsupported("hidden field constructor parameters"));
                };
                type_ = self.substitution(body, parameter)?;
            }
            Some(type_)
        } else {
            None
        };
        let mut rewritten = specialized;
        let mut value = Expr::const_(binding.name.clone(), vec![]);
        for (index, field) in args[parameters..].iter().enumerate() {
            self.tick()?;
            let actual = if let Some(type_) = actual_type.take() {
                let normal = self.type_head(&type_)?;
                let ExprNode::ForallE {
                    binder_type, body, ..
                } = normal.node()
                else {
                    return Err(unsupported("hidden field constructor telescope"));
                };
                actual_type = Some(self.substitution(body, field)?);
                Some(binder_type.clone())
            } else {
                None
            };
            // A type argument has no runtime value; its slot holds the same
            // inert scalar as an erased proof and is never evaluated.
            let field = if binding.type_fields.get(index).copied().unwrap_or(false)
                && field != &proofs::erased_value()
            {
                rewritten = true;
                proofs::erased_value()
            } else if let (Some(actual), Some(expected)) = (actual, binding.fields.get(index)) {
                let adapted = self.adapt_erased_field(field, &actual, expected)?;
                rewritten |= adapted != *field;
                adapted
            } else {
                field.clone()
            };
            value = Expr::app(value, field);
        }
        // A partial constructor is itself a callback. Keep its concrete
        // remaining interface: an incoming callback or container must cross
        // the same real adapter as a field supplied in the original call.
        if let Some(mut type_) = actual_type {
            let remaining = type_.clone();
            let first_remaining = args.len() - parameters;
            let mut needs_adapter = false;
            for expected in binding.fields.iter().skip(first_remaining) {
                self.tick()?;
                let normal = self.type_head(&type_)?;
                let ExprNode::ForallE {
                    binder_type, body, ..
                } = normal.node()
                else {
                    return Err(unsupported("partial hidden constructor telescope"));
                };
                let actual = self.erase_runtime_type(binder_type)?;
                let actual = self.erase_hidden_types(&actual, &[])?;
                if !self.shared_erased_storage(&actual, expected)? {
                    needs_adapter = true;
                }
                type_ = self.substitution(body, &indexed::pending_parameter())?;
            }
            if first_remaining < binding.fields.len() {
                let remaining = self.erase_runtime_type(&remaining)?;
                let remaining = self.erase_hidden_types(&remaining, &[])?;
                let (head, arguments) = self.spine(&value)?;
                if needs_adapter {
                    let mut runtime_remaining = family;
                    for domain in binding.fields[first_remaining..].iter().rev() {
                        self.tick()?;
                        runtime_remaining = Expr::forall_e(
                            Name::anonymous(),
                            domain.clone(),
                            runtime_remaining,
                            BinderInfo::Default,
                        );
                    }
                    let value = self
                        .partial_call_with_remaining(&head, &arguments, Some(&runtime_remaining))?
                        .ok_or_else(|| unsupported("partial hidden constructor interface"))?;
                    return self
                        .adapt_erased_field(&value, &runtime_remaining, &remaining)
                        .map(Some);
                }
                return self.partial_call_with_remaining(&head, &arguments, Some(&remaining));
            }
        }
        Ok(rewritten.then_some(value))
    }

    /// A nonrecursive singleton eliminator becomes one let-bound major and
    /// projections into its checked layout. Keep the major shared even when
    /// several fields or the same field are used by the minor premise.
    pub(super) fn record_recursor(
        &mut self,
        name: &Name,
        levels: &[fln_core::level::Level],
        args: &[Expr],
    ) -> Result<Option<Expr>, IngressError> {
        let Some(ConstantInfo::Rec(rec)) = self.environment.find(name) else {
            return Ok(None);
        };
        if rec.is_unsafe
            || rec.num_indices != 0
            || rec.num_motives != 1
            || rec.num_minors != 1
            || rec.all.len() != 1
            || rec.rules.len() != 1
            || levels.len() != rec.base.level_params.len()
            || args.len() != rec.num_params as usize + 3
        {
            return Ok(None);
        }
        let Some(shape) = self.recursor_shape(rec, levels, args)? else {
            return Ok(None);
        };
        let family = shape.source.clone();
        let args = &args[rec.num_params as usize..];
        if shape.recursive {
            return Ok(None);
        }
        let [ctor] = shape.constructors.as_slice() else {
            return Ok(None);
        };
        if rec.rules[0].ctor != ctor.original || rec.rules[0].nfields as usize != ctor.fields.len()
        {
            return Ok(None);
        }
        let ExprNode::Lam {
            binder_type,
            body: motive,
            ..
        } = args[0].node()
        else {
            return Ok(None);
        };
        // A result may depend on the major's erased Type fields while still
        // having a uniform representation. Resolve those verified projections
        // in the motive's own local context, just as definition signatures and
        // constructor minors use the boxed hidden carrier. Dependence on an
        // ordinary value remains unresolved and is refused by layout discovery.
        let motive = self.erase_hidden_types(motive, std::slice::from_ref(binder_type))?;
        let result = self
            .value_type(&motive)?
            .ok_or_else(|| unsupported("dependent record recursor result"))?;
        let major = Expr::bvar(0).map_err(|_| unsupported("record major scope"))?;
        let mut body = args[1]
            .lift_loose(0, 1)
            .map_err(|_| unsupported("record minor scope"))?;
        for index in 0..ctor.fields.len() {
            self.tick()?;
            let field = Expr::proj(shape.name.clone(), index as u64, major.clone());
            body = self.constructor_minor_apply(body, ctor, index, field)?;
        }
        let body = self.typed_callable_result(body, motive, result)?;
        Ok(Some(Expr::let_e(
            Name::anonymous(),
            family,
            args[2].clone(),
            body,
            false,
        )))
    }

    /// The class a closed root reads when its normalized declared type has a
    /// scalar representation. Ingress uses it only to unbox an ABI root, such
    /// as a field read from a boxed slot; any other root is unchanged.
    pub(crate) fn root_result(&self, runtime_type: &Expr) -> Option<ValueType> {
        scalar_type(runtime_type)
    }

    pub(super) fn constructor(&mut self, name: &Name) -> Result<(), IngressError> {
        let Some(ConstantInfo::Ctor(ctor)) = self.environment.find(name) else {
            return Ok(());
        };
        let family = Expr::const_(ctor.induct.clone(), vec![]);
        // Unsupported constructors remain absent from the catalog and are
        // refused by ingress rather than assigned a made-up layout.
        self.value_type(&family)?;
        Ok(())
    }
}

#[cfg(test)]
mod closure_fields_tests {
    use super::*;

    fn box_engine() -> Engine {
        let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
        Engine::with_source_seed(limits)
            .unwrap()
            .into_complete()
            .unwrap()
            .check_source_files(
                &[b"structure Box (A : Type) where\n  value : A"],
                &KVMap::new(),
                SourceCheckLimits::new(limits),
            )
            .unwrap()
            .into_complete()
            .unwrap()
            .engine
    }

    fn alternating_type(depth: usize) -> Expr {
        let scalar = Expr::const_(name("Nat"), vec![]);
        (0..depth).fold(scalar.clone(), |value, _| {
            Expr::app(
                Expr::const_(name("Box"), vec![]),
                Expr::forall_e(
                    Name::anonymous(),
                    scalar.clone(),
                    value,
                    BinderInfo::Default,
                ),
            )
        })
    }

    #[test]
    fn registered_record_and_callback_lookups_are_exact_and_metered() {
        let engine = box_engine();
        let mut prep = Preparation::new(&engine.environment, IngressLimits::default());
        let record = alternating_type(1);
        assert_eq!(
            prep.value_type(&record).unwrap(),
            Some(ValueType::Constructor)
        );
        let ExprNode::App { a: callback, .. } = record.node() else {
            panic!("Box callback")
        };
        let expected = prep.value_type(callback).unwrap();
        assert!(matches!(expected, Some(ValueType::Closure(_))));
        let constructors = prep.constructors.clone();
        let interfaces = prep.interfaces.clone();
        // Rebuild equal keys, rather than requiring the same allocation.
        for input in [alternating_type(1), callback.clone()] {
            let start = prep.visited;
            prep.limits.max_nodes = start + 1;
            assert_eq!(
                prep.value_type(&input).unwrap(),
                if input == record {
                    Some(ValueType::Constructor)
                } else {
                    expected
                }
            );
            assert_eq!(prep.visited, start + 1);
            assert!(matches!(
                prep.value_type(&input),
                Err(IngressError::ResourceLimit {
                    resource: IngressResource::Nodes,
                    ..
                })
            ));
        }
        assert_eq!(prep.constructors, constructors);
        assert_eq!(prep.interfaces, interfaces);
    }

    #[test]
    fn a_different_callback_telescope_is_not_a_cache_hit_even_after_exhaustion() {
        let engine = box_engine();
        let mut prep = Preparation::new(&engine.environment, IngressLimits::default());
        let callback = |result| {
            Expr::forall_e(
                Name::anonymous(),
                Expr::const_(name("Nat"), vec![]),
                Expr::const_(name(result), vec![]),
                BinderInfo::Default,
            )
        };
        let registered = callback("Nat");
        let changed = callback("String");
        let original = prep.value_type(&registered).unwrap();
        let interfaces = prep.interfaces.clone();
        prep.limits.max_nodes = prep.visited + 1;
        assert!(matches!(
            prep.value_type(&changed),
            Err(IngressError::ResourceLimit {
                resource: IngressResource::Nodes,
                ..
            })
        ));
        assert!(!prep.value_types.closures.contains_key(&changed));
        assert_eq!(prep.interfaces, interfaces);
        prep.limits = IngressLimits::default();
        assert_eq!(prep.value_type(&registered).unwrap(), original);
        let discovered = prep.value_type(&changed).unwrap();
        assert!(matches!(discovered, Some(ValueType::Closure(_))));
        assert_ne!(discovered, original);
    }

    #[test]
    fn mixed_data_function_type_dependencies_are_discovered_on_the_heap() {
        let engine = box_engine();
        std::thread::Builder::new()
            .stack_size(128 * 1024)
            .spawn(move || {
                let type_ = alternating_type(200);
                let limits = IngressLimits {
                    max_context_depth: 16,
                    max_nodes: 500_000,
                    ..IngressLimits::default()
                };
                assert!(matches!(
                    Preparation::new(&engine.environment, limits).value_type(&type_),
                    Err(IngressError::ResourceLimit { .. })
                ));
                let mut normal = Preparation::new(&engine.environment, IngressLimits::default());
                assert_eq!(
                    normal.value_type(&alternating_type(8)).unwrap(),
                    Some(ValueType::Constructor)
                );
                assert_eq!(normal.constructors.len(), 8);
                assert!(
                    normal
                        .constructors
                        .iter()
                        .all(|c| matches!(c.fields.as_slice(), [ValueType::Closure(_)]))
                );
            })
            .unwrap()
            .join()
            .unwrap();
    }

    #[test]
    fn canonicalization_remaps_field_interfaces_not_just_call_sites() {
        let engine = box_engine();
        let mut prep = Preparation::new(&engine.environment, IngressLimits::default());
        let mut fields = Vec::new();
        for (argument, result) in [("String", "String"), ("Nat", "Nat")] {
            let type_ = Expr::forall_e(
                Name::anonymous(),
                Expr::const_(name(argument), vec![]),
                Expr::const_(name(result), vec![]),
                BinderInfo::Default,
            );
            assert_eq!(
                prep.value_type(&Expr::app(Expr::const_(name("Box"), vec![]), type_))
                    .unwrap(),
                Some(ValueType::Constructor)
            );
            fields.push(prep.constructors.last().unwrap().fields[0]);
        }
        assert_ne!(fields[0], fields[1]);
        prep.finalize_callables(&mut []).unwrap();
        assert_eq!(prep.constructors[0].fields[0], fields[1]);
        assert_eq!(prep.constructors[1].fields[0], fields[0]);
    }

    #[test]
    fn provisional_recursive_layouts_roll_back_on_refusal_and_exhaustion() {
        let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
        let engine = Engine::with_source_seed(limits)
            .unwrap()
            .into_complete()
            .unwrap()
            .check_source_files(
                &[b"inductive Good where | leaf | node (f : Nat -> Good)\n\
                    structure Payload where\n  flag : Bool\n  value : if flag then Nat else String\n\
                    inductive Bad where | mk (f : Nat -> Bad) (payload : Payload)\n\
                    inductive ProofChild where | leaf | node (f : Nat -> ProofChild) (h : 0 = 0)"],
                &KVMap::new(),
                SourceCheckLimits::new(limits),
            )
            .unwrap()
            .into_complete()
            .unwrap()
            .engine;
        let mut prep = Preparation::new(&engine.environment, IngressLimits::default());
        let good = Expr::const_(name("Good"), vec![]);
        let bad = Expr::const_(name("Bad"), vec![]);
        assert_eq!(
            prep.value_type(&good).unwrap(),
            Some(ValueType::Constructor)
        );
        // Proof payloads now have a valid representation. Keep a positive
        // counterexample alongside the refusal fixture; the latter must fail
        // after anchoring Bad, when its Payload is discovered. Hidden-type
        // callbacks now have a uniform interface, whereas a field type chosen
        // by an ordinary runtime Boolean still has no supported layout.
        let proof_child = Expr::const_(name("ProofChild"), vec![]);
        assert_eq!(
            prep.value_type(&proof_child).unwrap(),
            Some(ValueType::Constructor)
        );
        assert!(prep.constructors.iter().any(|ctor| {
            ctor.name == name("ProofChild.node")
                && matches!(
                    ctor.fields.as_slice(),
                    [ValueType::Closure(_), ValueType::Bool]
                )
        }));
        let interfaces = prep.interfaces.len();
        let constructors = prep.constructors.len();
        let closures = prep.value_types.closures.len();
        for _ in 0..2 {
            assert_eq!(prep.value_type(&bad).unwrap(), None);
            assert!(!prep.value_types.records.contains(&bad));
            assert_eq!(prep.interfaces.len(), interfaces);
            assert_eq!(prep.constructors.len(), constructors);
            assert_eq!(prep.value_types.closures.len(), closures);
            assert_eq!(
                prep.value_type(&good).unwrap(),
                Some(ValueType::Constructor)
            );
        }
        let small = IngressLimits {
            fir: fln_comp::fir::ValidationLimits {
                max_constructors: 1,
                ..IngressLimits::default().fir
            },
            ..IngressLimits::default()
        };
        let mut stopped = Preparation::new(&engine.environment, small);
        assert!(matches!(
            stopped.value_type(&good),
            Err(IngressError::ResourceLimit { .. })
        ));
        assert!(stopped.value_types.records.is_empty());
        assert!(stopped.value_types.closures.is_empty());
        assert!(stopped.interfaces.is_empty());
        assert!(stopped.constructors.is_empty());
        stopped.limits = IngressLimits::default();
        assert_eq!(
            stopped.value_type(&good).unwrap(),
            Some(ValueType::Constructor)
        );
        let mut clean = Preparation::new(&engine.environment, IngressLimits::default());
        assert_eq!(
            clean.value_type(&good).unwrap(),
            Some(ValueType::Constructor)
        );
        assert_eq!(
            stopped.finalize_callables(&mut []).unwrap(),
            clean.finalize_callables(&mut []).unwrap()
        );
        assert_eq!(stopped.constructors, clean.constructors);
    }
}

#[cfg(test)]
mod type_field_tests {
    use super::*;

    const SOURCE: &str = "structure Package where\n  carrier : Type\n  value : carrier\nstructure Box where\n  carrier : Type\nstructure Mixed where\n  label : String\n  carrier : Type\n  value : carrier\n  count : Nat\n  ok : count = count\nstructure Plain where\n  count : Nat\nstructure Listed where\n  carrier : Type\n  items : List carrier\nstructure Shown where\n  carrier : Type\n  value : carrier\n  display : carrier -> String\ndef packed : Package := Package.mk Nat 7\ndef rebuild (p : Package) : Package := match p with\n  | Package.mk c v => Package.mk c v";

    fn engine() -> Engine {
        let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
        Engine::with_source_seed(limits)
            .unwrap()
            .into_complete()
            .unwrap()
            .check_source_files(
                &[SOURCE.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits),
            )
            .unwrap()
            .into_complete()
            .unwrap()
            .engine
    }

    fn family(name_: &str) -> Expr {
        Expr::const_(name(name_), vec![])
    }

    fn fields<'p>(prep: &'p Preparation<'_>, constructor: &str) -> &'p [ValueType] {
        &prep
            .constructors
            .iter()
            .find(|binding| binding.name == name(constructor))
            .expect("constructor binding")
            .fields
    }

    #[test]
    fn type_fields_take_inert_slots_and_their_values_take_boxed_slots() {
        let engine = engine();
        let mut prep = Preparation::new(&engine.environment, IngressLimits::default());
        for name_ in ["Package", "Box", "Mixed"] {
            assert_eq!(
                prep.value_type(&family(name_)).unwrap(),
                Some(ValueType::Constructor),
                "{name_}"
            );
        }
        assert_eq!(
            fields(&prep, "Package.mk"),
            [ValueType::Bool, ValueType::Abi]
        );
        assert_eq!(fields(&prep, "Box.mk"), [ValueType::Bool]);
        // label, carrier (erased type), value (boxed), count, ok (erased proof)
        assert_eq!(
            fields(&prep, "Mixed.mk"),
            [
                ValueType::String,
                ValueType::Bool,
                ValueType::Abi,
                ValueType::Nat,
                ValueType::Bool
            ]
        );
        let shape = prep.record_shape(&family("Mixed")).unwrap().unwrap();
        let ctor = &shape.constructors[0];
        assert_eq!(ctor.type_fields, [false, true, false, false, false]);
        assert_eq!(ctor.fields[1], proofs::erased_type());
        assert_eq!(ctor.fields[2], boxed_slot_type());
    }

    #[test]
    fn hidden_types_extend_through_data_and_callable_interfaces() {
        let engine = engine();
        let mut prep = Preparation::new(&engine.environment, IngressLimits::default());
        for name_ in ["Listed", "Shown"] {
            assert_eq!(
                prep.value_type(&family(name_)).unwrap(),
                Some(ValueType::Constructor),
                "{name_}"
            );
        }
        assert_eq!(
            fields(&prep, "Listed.mk"),
            [ValueType::Bool, ValueType::Constructor]
        );
        let [ValueType::Bool, ValueType::Abi, ValueType::Closure(id)] = fields(&prep, "Shown.mk")
        else {
            panic!("hidden callback layout");
        };
        let signature = &prep.interfaces[id.get() as usize];
        assert_eq!(signature.parameters, [ValueType::Abi]);
        assert_eq!(signature.result, ValueType::String);
    }

    #[test]
    fn a_user_declaration_cannot_claim_the_private_boxed_representation() {
        let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
        let engine = engine()
            .check_source_files(
                &[b"def _fln_runtime_boxed : Type := Nat"],
                &KVMap::new(),
                SourceCheckLimits::new(limits),
            )
            .unwrap()
            .into_complete()
            .unwrap()
            .engine;
        let mut prep = Preparation::new(&engine.environment, IngressLimits::default());
        assert_ne!(
            prep.value_type(&boxed_slot_type()).unwrap(),
            Some(ValueType::Abi)
        );
        assert!(prep.value_type(&family("Package")).is_err());
        assert!(prep.value_types.boxed.is_none());
        assert!(prep.constructors.is_empty());
    }

    #[test]
    fn construction_erases_only_type_arguments_and_only_once() {
        let engine = engine();
        let mut prep = Preparation::new(&engine.environment, IngressLimits::default());
        let mk = family("Package.mk");
        let rewritten = prep
            .specialize_constructor(&mk, &[family("Nat"), nat::literal(7)])
            .unwrap()
            .expect("the type argument is erased");
        assert_eq!(
            rewritten,
            Expr::app(
                Expr::app(mk.clone(), proofs::erased_value()),
                nat::literal(7)
            )
        );
        // An erased application is final, so expression preparation cannot loop.
        assert!(
            prep.specialize_constructor(&mk, &[proofs::erased_value(), nat::literal(7)])
                .unwrap()
                .is_none()
        );
        // A nonparametric constructor without a type field keeps its own path.
        assert!(
            prep.specialize_constructor(&family("Plain.mk"), &[nat::literal(7)])
                .unwrap()
                .is_none()
        );
    }

    #[test]
    fn a_projection_type_reduces_only_through_a_constructor() {
        let engine = engine();
        let mut prep = Preparation::new(&engine.environment, IngressLimits::default());
        let carrier = |receiver: Expr| Expr::proj(name("Package"), 0, receiver);
        assert_eq!(
            prep.type_head(&carrier(family("packed"))).unwrap(),
            family("Nat")
        );
        // A receiver stuck behind a match, or a bound variable, is returned
        // exactly as written, receiver included.
        let stuck = carrier(Expr::app(family("rebuild"), family("packed")));
        assert_eq!(prep.type_head(&stuck).unwrap(), stuck);
        let open = carrier(Expr::bvar(0).unwrap());
        assert_eq!(prep.type_head(&open).unwrap(), open);
    }
}
