//! Derive object-field layouts from admitted, closed data families.
//! These are native FIR layouts, not a claim of Reference packed-ABI parity.
//! Closed type parameters are specialized, never stored as runtime fields.
//! Direct self- and mutually recursive fields and nondependent function-valued
//! self children are supported. Proof fields keep inert scalar slots; other
//! value-dependent fields and function-valued mutual children remain refusals.
//! Nondependent function fields are owned closures with checked interfaces.
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
        let source = self.normalize_type(source)?;
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
            || (family.is_reflexive && family.all.len() != 1)
            || family.num_params as usize != parameters.len()
            || family.num_indices != 0
            || family.num_nested != 0
            || !family.all.contains(name)
            || family.ctors.is_empty()
            || family.base.level_params.len() != levels.len()
        {
            return Ok(None);
        }
        let mut family_type =
            self.universe_instance(&family.base.type_, &family.base.level_params, levels)?;
        for parameter in &parameters {
            self.tick()?;
            let normal = self.normalize_type(&family_type)?;
            let ExprNode::ForallE {
                binder_type, body, ..
            } = normal.node()
            else {
                return Ok(None);
            };
            // Erasing a static type argument is not permission to discard a
            // value parameter, even when that value happens to be closed.
            if !self.type_parameter(binder_type)? {
                return Ok(None);
            }
            family_type = self.substitution(body, parameter)?;
        }
        let family_type = self.normalize_type(&family_type)?;
        if !matches!(family_type.node(), ExprNode::Sort { level } if level.is_never_zero()) {
            return Ok(None);
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
            for parameter in &parameters {
                self.tick()?;
                let ExprNode::ForallE { body, .. } = type_.node() else {
                    return Ok(None);
                };
                type_ = self.substitution(body, parameter)?;
            }
            // Erase the checked telescope before deciding whether a field's
            // representation depends on an earlier runtime value. A proof may
            // mention that value, but its inert slot never depends on it. The
            // logical field count/order is retained for projections and minors.
            type_ = self.erase_runtime_type(&type_)?;
            while let ExprNode::ForallE {
                binder_type, body, ..
            } = type_.node()
            {
                self.tick()?;
                // A later field's representation may not depend on a runtime
                // field. Retain that boundary after substituting type params.
                if body.has_loose_bvars() {
                    return Ok(None);
                }
                let field = self.normalize_type(binder_type)?;
                let (head, _) = self.spine(&field)?;
                if !matches!(
                    head.node(),
                    ExprNode::Const { .. } | ExprNode::ForallE { .. }
                ) {
                    return Ok(None);
                }
                reserve(&mut fields, self.limits.max_context_depth)?;
                fields.push(field);
                type_ = body.clone();
            }
            if fields.len() != ctor.num_fields as usize || self.normalize_type(&type_)? != source {
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
        let source = self.normalize_type(source)?;
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
        let source = self.normalize_type(source)?;
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
                        if scalar_type(field).is_none()
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
            || rec.num_indices != 0
            || rec.base.level_params.len() != levels.len()
            || args.len() < rec.num_params as usize
        {
            return Ok(None);
        }
        let Some(ConstantInfo::Induct(family)) = self.environment.find(&rec.all[0]) else {
            return Ok(None);
        };
        if rec.num_params != family.num_params || rec.num_minors as usize != family.ctors.len() {
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
        let mut source = Expr::const_(family.base.name.clone(), family_levels);
        for parameter in &args[..rec.num_params as usize] {
            self.tick()?;
            source = Expr::app(source, parameter.clone());
        }
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
        if parameters == 0 && levels.is_empty() || args.len() < parameters {
            return Ok(None);
        }
        let mut family = Expr::const_(ctor.induct.clone(), levels.clone());
        for parameter in &args[..parameters] {
            self.tick()?;
            family = Expr::app(family, parameter.clone());
        }
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
        let mut value = Expr::const_(binding.name.clone(), vec![]);
        for field in &args[parameters..] {
            self.tick()?;
            value = Expr::app(value, field.clone());
        }
        Ok(Some(value))
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
        let ExprNode::Lam { body: motive, .. } = args[0].node() else {
            return Ok(None);
        };
        let result = self
            .value_type(motive)?
            .ok_or_else(|| unsupported("dependent record recursor result"))?;
        let major = Expr::bvar(0).map_err(|_| unsupported("record major scope"))?;
        let mut body = args[1]
            .lift_loose(0, 1)
            .map_err(|_| unsupported("record minor scope"))?;
        for index in 0..ctor.fields.len() {
            self.tick()?;
            let field = Expr::proj(shape.name.clone(), index as u64, major.clone());
            body = self.minor_apply(body, field)?;
        }
        let body = self.typed_callable_result(body, motive.clone(), result)?;
        Ok(Some(Expr::let_e(
            Name::anonymous(),
            family,
            args[2].clone(),
            body,
            false,
        )))
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
                    structure Payload where\n  carrier : Type\n  value : carrier\n\
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
        // after anchoring Bad, when its value-dependent Payload is discovered.
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
