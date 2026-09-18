//! Derive object-field layouts from admitted, closed data families.
//! These are native FIR layouts, not a claim of Reference packed-ABI parity.
//! Direct self-recursive object fields are supported; dependent, polymorphic,
//! higher-order recursive and proof-valued fields remain explicit refusals.
use super::*;
use fln_comp::ingress::ConstructorBinding;
use std::collections::BTreeSet;

pub(super) struct Shape {
    pub name: Name,
    pub recursive: bool,
    pub constructors: Vec<ShapeConstructor>,
}

pub(super) struct ShapeConstructor {
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
    pub(super) fn record_shape(&mut self, name: &Name) -> Result<Option<Shape>, IngressError> {
        self.tick()?;
        let Some(ConstantInfo::Induct(family)) = self.environment.find(name) else {
            return Ok(None);
        };
        if family.is_unsafe
            || family.is_reflexive
            || family.num_params != 0
            || family.num_indices != 0
            || family.num_nested != 0
            || family.all != [name.clone()]
            || family.ctors.is_empty()
            || !family.base.level_params.is_empty()
            || !matches!(family.base.type_.node(), ExprNode::Sort { level } if level.is_never_zero())
        {
            return Ok(None);
        }
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
                || ctor.num_params != 0
                || ctor.cidx as usize != index
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
                // Types, indices and proofs are not guessed runtime fields.
                if !matches!(binder_type.node(), ExprNode::Const { levels, .. } if levels.is_empty())
                {
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
            reserve(&mut constructors, self.limits.fir.max_constructors)?;
            constructors.push(ShapeConstructor {
                name: ctor.base.name.clone(),
                tag,
                fields,
            });
        }
        Ok(Some(Shape {
            name: name.clone(),
            recursive: family.is_rec,
            constructors,
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
                        .constructors
                        .iter()
                        .flat_map(|ctor| &ctor.fields)
                        .filter_map(|field| {
                            if scalar_type(field).is_some() {
                                return None;
                            }
                            match field.node() {
                                ExprNode::Const { name, .. } if name != &shape.name => {
                                    Some(name.clone())
                                }
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
                    for ctor in &shape.constructors {
                        let mut fields = Vec::new();
                        for field in &ctor.fields {
                            self.tick()?;
                            let value = if matches!(field.node(), ExprNode::Const { name, levels }
                                if name == &shape.name && levels.is_empty())
                            {
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
                    }
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
        if shape.recursive {
            return Ok(None);
        }
        let [ctor] = shape.constructors.as_slice() else {
            return Ok(None);
        };
        if rec.rules[0].ctor != ctor.name || rec.rules[0].nfields as usize != ctor.fields.len() {
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
        for index in 0..ctor.fields.len() {
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
