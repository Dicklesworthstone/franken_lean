//! Derive object-field layouts from admitted, closed single-constructor types.
//! These are native FIR layouts, not a claim of Reference packed-ABI parity.
//! Dependent, polymorphic, recursive and proof-valued families remain refusals.
use super::*;
use fln_comp::ingress::ConstructorBinding;
use std::collections::BTreeSet;

struct Shape {
    name: Name,
    constructor: Name,
    fields: Vec<Expr>,
}

impl Preparation<'_> {
    fn record_shape(&mut self, name: &Name) -> Result<Option<Shape>, IngressError> {
        self.tick()?;
        let Some(ConstantInfo::Induct(family)) = self.environment.find(name) else {
            return Ok(None);
        };
        if family.is_unsafe
            || family.is_rec
            || family.is_reflexive
            || family.num_params != 0
            || family.num_indices != 0
            || family.num_nested != 0
            || family.all != [name.clone()]
            || family.ctors.len() != 1
            || !family.base.level_params.is_empty()
            || !matches!(family.base.type_.node(), ExprNode::Sort { level } if level.is_never_zero())
        {
            return Ok(None);
        }
        let Some(ConstantInfo::Ctor(ctor)) = self.environment.find(&family.ctors[0]) else {
            return Ok(None);
        };
        if ctor.is_unsafe
            || ctor.induct != *name
            || ctor.num_params != 0
            || ctor.cidx != 0
            || !ctor.base.level_params.is_empty()
        {
            return Ok(None);
        }
        let mut fields = Vec::new();
        let mut type_ = &ctor.base.type_;
        while let ExprNode::ForallE {
            binder_type, body, ..
        } = type_.node()
        {
            self.tick()?;
            // An erased type/index/proof is not an object field. Do not guess
            // its representation, even when this particular value is unused.
            if !matches!(binder_type.node(), ExprNode::Const { levels, .. } if levels.is_empty()) {
                return Ok(None);
            }
            reserve(&mut fields, self.limits.max_context_depth)?;
            fields.push(binder_type.clone());
            type_ = body;
        }
        if fields.len() != ctor.num_fields as usize
            || !matches!(type_.node(), ExprNode::Const { name: result, levels } if result == name && levels.is_empty())
        {
            return Ok(None);
        }
        Ok(Some(Shape {
            name: name.clone(),
            constructor: ctor.base.name.clone(),
            fields,
        }))
    }

    /// Discover nested record dependencies in postorder on the heap. All roots
    /// refer to the immutable, dual-checked environment, never caller layouts.
    pub(super) fn value_type(&mut self, source: &Expr) -> Result<Option<ValueType>, IngressError> {
        if let Some(value) = scalar_type(source) {
            return Ok(Some(value));
        }
        let ExprNode::Const { name, levels } = source.node() else {
            return Ok(None);
        };
        if !levels.is_empty() {
            return Ok(None);
        }
        enum Task {
            Enter(Name),
            Finish(Shape),
        }
        let mut tasks = vec![Task::Enter(name.clone())];
        let mut active = BTreeSet::new();
        while let Some(task) = tasks.pop() {
            self.tick()?;
            match task {
                Task::Enter(name) => {
                    if self.value_types.records.contains(&name) {
                        continue;
                    }
                    if !active.insert(name.clone()) {
                        return Ok(None);
                    }
                    if active.len() > self.limits.max_context_depth {
                        return Err(IngressError::ResourceLimit {
                            resource: IngressResource::ContextDepth,
                            limit: self.limits.max_context_depth,
                            observed: active.len(),
                        });
                    }
                    let Some(shape) = self.record_shape(&name)? else {
                        return Ok(None);
                    };
                    let dependencies: Vec<_> = shape
                        .fields
                        .iter()
                        .filter_map(|field| {
                            if scalar_type(field).is_some() {
                                return None;
                            }
                            match field.node() {
                                ExprNode::Const { name, .. } => Some(name.clone()),
                                _ => None,
                            }
                        })
                        .collect();
                    reserve(&mut tasks, self.limits.max_nodes)?;
                    tasks.push(Task::Finish(shape));
                    for dependency in dependencies.into_iter().rev() {
                        reserve(&mut tasks, self.limits.max_nodes)?;
                        tasks.push(Task::Enter(dependency));
                    }
                }
                Task::Finish(shape) => {
                    let mut fields = Vec::new();
                    for field in &shape.fields {
                        self.tick()?;
                        let Some((value, _)) = executable_value_type(field, &self.value_types)
                        else {
                            return Ok(None);
                        };
                        reserve(&mut fields, self.limits.max_context_depth)?;
                        fields.push(value);
                    }
                    reserve(&mut self.constructors, self.limits.fir.max_constructors)?;
                    self.constructors.push(ConstructorBinding {
                        name: shape.constructor,
                        projection_structure: Some(shape.name.clone()),
                        universe_arity: 0,
                        tag: 0,
                        fields,
                        static_scalar_bytes: Vec::new(),
                    });
                    active.remove(&shape.name);
                    self.value_types.records.insert(shape.name);
                }
            }
        }
        Ok(Some(ValueType::Constructor))
    }

    pub(crate) fn signature(
        &mut self,
        definition: &DefinitionVal,
        eta_expand: bool,
    ) -> Result<Option<ExecutableSignature>, IngressError> {
        if !definition.base.level_params.is_empty() {
            return Ok(None);
        }
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
            definition,
            &self.value_types,
            &mut self.visited,
            self.limits,
            eta_expand,
        )
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
            || rec.num_params != 0
            || rec.num_indices != 0
            || rec.num_motives != 1
            || rec.num_minors != 1
            || rec.all.len() != 1
            || rec.rules.len() != 1
            || levels.len() != rec.base.level_params.len()
            || args.len() != 3
        {
            return Ok(None);
        }
        let family = Expr::const_(rec.all[0].clone(), vec![]);
        if self.value_type(&family)? != Some(ValueType::Constructor) {
            return Ok(None);
        }
        let Some(shape) = self.record_shape(&rec.all[0])? else {
            return Ok(None);
        };
        if rec.rules[0].ctor != shape.constructor
            || rec.rules[0].nfields as usize != shape.fields.len()
        {
            return Ok(None);
        }
        let ExprNode::Lam { body: motive, .. } = args[0].node() else {
            return Ok(None);
        };
        if self.value_type(motive)?.is_none() {
            return Err(unsupported("dependent record recursor result"));
        }
        let major = Expr::bvar(0).map_err(|_| unsupported("record major scope"))?;
        let mut body = args[1]
            .lift_loose(0, 1)
            .map_err(|_| unsupported("record minor scope"))?;
        for index in 0..shape.fields.len() {
            self.tick()?;
            let field = Expr::proj(shape.name.clone(), index as u64, major.clone());
            body = self.minor_apply(body, field)?;
        }
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
