//! Bind source projections to the receiver's ground runtime layout.
//!
//! Source `Expr::Proj` names a family, not a specialization. Recover its type
//! while the original lambda/let telescope is still present, before catalog
//! extraction peels binders. This is post-admission representation selection,
//! not another checker: no executable receiver is reduced, copied or discarded.
use super::*;
use fln_core::expr::Literal;
use fln_core::level::Level;

// Types here are relative to the context *before* their binder was introduced.
// Lifting by index + 1 reopens a selected domain in the current context.
enum TypeFrame {
    Apply(Expr),
    Projection(Name, u64, Expr),
    Lambda(Name, Expr, BinderInfo),
    Let(Expr),
}

enum ProjectionFrame {
    Visit(Expr),
    Apply,
    Lambda(Name, Expr, BinderInfo),
    LetValue(Name, Expr, Expr, bool),
    LetBody(Name, Expr, Expr, bool),
    Projection(Name, u64),
}

impl Preparation<'_> {
    /// Unfold an admitted record projection without creating a callable
    /// wrapper around its selected field. Type/index arguments occur only in
    /// metadata; the receiver occurs exactly once and retains its evaluation.
    pub(super) fn projection_call(
        &mut self,
        head: &Expr,
        arguments: &[Expr],
    ) -> Result<Option<Expr>, IngressError> {
        if let Some(replacement) = self.implemented_by_call(head, arguments)? {
            return Ok(Some(replacement));
        }
        let ExprNode::Const { name, levels } = head.node() else {
            return Ok(None);
        };
        let Some(ConstantInfo::Defn(definition)) = self.environment.find(name) else {
            return Ok(None);
        };
        let definition = definition.clone();
        if definition.safety != DefinitionSafety::Safe
            || definition.base.level_params.len() != levels.len()
        {
            return Ok(None);
        }
        let mut body = &definition.value;
        let mut arity = 0usize;
        while let ExprNode::Lam { body: inner, .. } = body.node() {
            self.tick()?;
            arity += 1;
            body = inner;
        }
        if arity == 0 || arguments.len() < arity {
            return Ok(None);
        }
        if !matches!(body.node(), ExprNode::Proj { expr, .. }
            if matches!(expr.node(), ExprNode::BVar { idx: 0 }))
        {
            return Ok(None);
        }
        let mut value =
            self.universe_instance(&definition.value, &definition.base.level_params, levels)?;
        let mut receiver_type = None;
        for (index, argument) in arguments[..arity].iter().enumerate() {
            self.tick()?;
            let ExprNode::Lam {
                binder_type, body, ..
            } = value.node()
            else {
                return Ok(None);
            };
            if index + 1 == arity {
                receiver_type = Some(binder_type.clone());
            }
            // Earlier value parameters may themselves be checked dictionaries,
            // as ForIn' carries its Membership dictionary before the receiver.
            // Only inert factory values may disappear with projection metadata;
            // a computed parameter keeps the ordinary strict runtime path.
            if index + 1 != arity
                && !self.type_parameter(binder_type)?
                && self.instance_factory_value(argument)?.is_none()
            {
                return Ok(None);
            }
            value = self.substitution(body, argument)?;
        }
        let ExprNode::Proj {
            struct_name,
            idx,
            expr,
        } = value.node()
        else {
            return Ok(None);
        };
        // Only expose a field when this administrative projection is fully
        // resolved. A dynamic receiver still needs the existing lexical,
        // signature-aware projection layout pass after specialization.
        if let Some(field) = self.executable_projection(struct_name, *idx, expr)? {
            return Ok(Some(
                arguments[arity..].iter().cloned().fold(field, Expr::app),
            ));
        }
        // A hidden-type field's projection function may have a dependent
        // result type. Select its checked runtime field interface from the
        // receiver's closed layout; the receiver still occurs exactly once.
        let Some(receiver_type) = receiver_type.filter(|type_| !type_.has_loose_bvars()) else {
            return Ok(None);
        };
        let Some((shape, field)) = self.projection_slot(&receiver_type, struct_name, *idx)? else {
            return Ok(None);
        };
        if self.value_type(&shape.source)? != Some(ValueType::Constructor)
            || self.value_type(&field)?.is_none()
        {
            return Ok(None);
        }
        let projected = Expr::proj(shape.projection(&shape.constructors[0]), *idx, expr.clone());
        Ok(Some(
            arguments[arity..]
                .iter()
                .cloned()
                .fold(projected, Expr::app),
        ))
    }

    /// Select only an administratively reducible field, then prepare any
    /// newly exposed logical body for execution. Static dictionary discovery
    /// still uses `static_projection` and retains its original type plane.
    pub(super) fn executable_projection(
        &mut self,
        family: &Name,
        index: u64,
        receiver: &Expr,
    ) -> Result<Option<Expr>, IngressError> {
        let Some(field) = self.static_projection(family, index, receiver)? else {
            return Ok(None);
        };
        // The selected field can come from an unfolded logical definition,
        // not from the already-erased input tree. Reapply the representation
        // barrier before scheduling it as executable code: a nested record or
        // callback may still contain original proof fields. The closed static
        // receiver supplies the complete lexical context; no runtime receiver
        // is evaluated, duplicated or discarded by this step.
        let field = self.erase_proofs(&field, None)?;
        self.lower_projections(&field).map(Some)
    }

    /// Reconstruct a source type using explicit continuations. In particular,
    /// applications and nested projections do not recurse on the host stack.
    /// Unknown or genuinely dependent representations are left unsupported.
    pub(super) fn projection_receiver_type(
        &mut self,
        source: &Expr,
        context: &[Expr],
    ) -> Result<Option<Expr>, IngressError> {
        let mut locals = Vec::new();
        for local in context {
            self.tick()?;
            reserve(&mut locals, self.limits.max_context_depth)?;
            locals.push(local.clone());
        }
        let mut frames = Vec::new();
        let mut head = source.clone();
        let mut type_ = loop {
            self.tick()?;
            let frame = match head.node() {
                ExprNode::Sort { level } => {
                    break Expr::sort(
                        Level::succ(level.clone()).map_err(|_| unsupported("proof sort depth"))?,
                    );
                }
                ExprNode::BVar { idx } => {
                    let Some(position) = locals.len().checked_sub(*idx as usize + 1) else {
                        return Ok(None);
                    };
                    let amount = idx
                        .checked_add(1)
                        .ok_or_else(|| unsupported("projection local depth"))?;
                    break self.lift(&locals[position], amount)?;
                }
                ExprNode::Const { name, levels } => {
                    let base = if let Some(info) = self.environment.find(name) {
                        info.constant_val().clone()
                    } else if let Some(definition) = self.specialized_definition(name) {
                        definition.base
                    } else {
                        return Ok(None);
                    };
                    if base.level_params.len() != levels.len() {
                        return Ok(None);
                    }
                    break self.universe_instance(&base.type_, &base.level_params, levels)?;
                }
                ExprNode::Lit {
                    literal: Literal::Nat(_),
                } => break Expr::const_(name("Nat"), vec![]),
                ExprNode::Lit {
                    literal: Literal::Str(_),
                } => break Expr::const_(name("String"), vec![]),
                ExprNode::MData { expr, .. } => {
                    head = expr.clone();
                    continue;
                }
                ExprNode::App { f, a } => {
                    let frame = TypeFrame::Apply(a.clone());
                    head = f.clone();
                    frame
                }
                ExprNode::Proj {
                    struct_name,
                    idx,
                    expr,
                } => {
                    let frame = TypeFrame::Projection(struct_name.clone(), *idx, expr.clone());
                    head = expr.clone();
                    frame
                }
                ExprNode::Lam {
                    binder_name,
                    binder_type,
                    body,
                    binder_info,
                } => {
                    reserve(&mut locals, self.limits.max_context_depth)?;
                    locals.push(binder_type.clone());
                    let frame =
                        TypeFrame::Lambda(binder_name.clone(), binder_type.clone(), *binder_info);
                    head = body.clone();
                    frame
                }
                ExprNode::LetE {
                    type_, value, body, ..
                } => {
                    reserve(&mut locals, self.limits.max_context_depth)?;
                    locals.push(type_.clone());
                    let frame = TypeFrame::Let(value.clone());
                    head = body.clone();
                    frame
                }
                _ => return Ok(None),
            };
            reserve(&mut frames, self.limits.max_nodes)?;
            frames.push(frame);
        };
        while let Some(frame) = frames.pop() {
            self.tick()?;
            type_ = match frame {
                TypeFrame::Apply(argument) => {
                    let normal = self.normalize_type(&type_)?;
                    let ExprNode::ForallE { body, .. } = normal.node() else {
                        return Ok(None);
                    };
                    self.substitution(body, &argument)?
                }
                TypeFrame::Projection(family, index, receiver) => {
                    let Some(field) =
                        self.original_projection_type(&type_, &family, index, &receiver)?
                    else {
                        return Ok(None);
                    };
                    field
                }
                TypeFrame::Lambda(name, domain, info) => {
                    locals.pop();
                    Expr::forall_e(name, domain, type_, info)
                }
                TypeFrame::Let(value) => {
                    locals.pop();
                    self.substitution(&type_, &value)?
                }
            };
        }
        Ok(Some(type_))
    }

    pub(super) fn projection_slot(
        &mut self,
        receiver_type: &Expr,
        structure: &Name,
        index: u64,
    ) -> Result<Option<(records::Shape, Expr)>, IngressError> {
        let source = self.normalize_type(receiver_type)?;
        let (head, _) = self.spine(&source)?;
        let ExprNode::Const { name, .. } = head.node() else {
            return Ok(None);
        };
        let Some(shape) = self.record_shape(&source)? else {
            return Ok(None);
        };
        // An already-specialized projection can be visited a second time by
        // expression preparation. Its private key must still select this type.
        if name != structure
            && &shape.name != structure
            && !shape
                .constructors
                .iter()
                .any(|ctor| &shape.projection(ctor) == structure)
        {
            return Err(unsupported("projection receiver family mismatch"));
        }
        if shape.recursive || shape.constructors.len() != 1 {
            return Ok(None);
        }
        let index = usize::try_from(index).map_err(|_| unsupported("projection field index"))?;
        let Some(field) = shape.constructors[0].fields.get(index) else {
            return Err(unsupported(
                "projection field outside constructor telescope",
            ));
        };
        let field = field.clone();
        Ok(Some((shape, field)))
    }

    pub(super) fn lower_projections(&mut self, input: &Expr) -> Result<Expr, IngressError> {
        // Most scalar programs have no projections. Inspect their DAG once,
        // without rebuilding every application or reopening every binder. The
        // scan key is syntax only; actual layout selection is never memoized
        // without its lexical context.
        let mut scan = vec![input.clone()];
        let mut seen = HashSet::new();
        let mut found = false;
        while let Some(expr) = scan.pop() {
            // Each charged parent inspects at most two executable children.
            // Leaf expressions cannot contain a projection and need no table
            // entry or continuation of their own.
            if !matches!(
                expr.node(),
                ExprNode::App { .. }
                    | ExprNode::Lam { .. }
                    | ExprNode::LetE { .. }
                    | ExprNode::MData { .. }
                    | ExprNode::Proj { .. }
            ) {
                continue;
            }
            if seen.contains(&expr.allocation_identity()) {
                continue;
            }
            self.tick()?;
            seen.try_reserve(1)
                .map_err(|_| IngressError::AllocationFailure {
                    resource: IngressResource::Nodes,
                    requested: seen.len().saturating_add(1),
                })?;
            seen.insert(expr.allocation_identity());
            let mut push = |child: &Expr| -> Result<(), IngressError> {
                if !matches!(
                    child.node(),
                    ExprNode::App { .. }
                        | ExprNode::Lam { .. }
                        | ExprNode::LetE { .. }
                        | ExprNode::MData { .. }
                        | ExprNode::Proj { .. }
                ) {
                    return Ok(());
                }
                reserve(&mut scan, self.limits.max_nodes)?;
                scan.push(child.clone());
                Ok(())
            };
            match expr.node() {
                ExprNode::Proj { .. } => {
                    found = true;
                    break;
                }
                ExprNode::App { f, a } => {
                    push(a)?;
                    push(f)?;
                }
                ExprNode::Lam { body, .. } => push(body)?,
                ExprNode::LetE { value, body, .. } => {
                    push(value)?;
                    push(body)?;
                }
                ExprNode::MData { expr, .. } => push(expr)?,
                _ => {}
            }
        }
        if !found {
            return Ok(input.clone());
        }
        let mut tasks = vec![ProjectionFrame::Visit(input.clone())];
        let mut values = Vec::new();
        let mut locals = Vec::new();
        while let Some(task) = tasks.pop() {
            self.tick()?;
            // The largest frame expansion adds three continuations.
            if tasks.len().saturating_add(3) > self.limits.max_nodes {
                return Err(IngressError::ResourceLimit {
                    resource: IngressResource::PendingTasks,
                    limit: self.limits.max_nodes,
                    observed: tasks.len().saturating_add(3),
                });
            }
            tasks
                .try_reserve(3)
                .map_err(|_| IngressError::AllocationFailure {
                    resource: IngressResource::PendingTasks,
                    requested: tasks.len().saturating_add(3),
                })?;
            reserve(&mut values, self.limits.max_nodes)?;
            match task {
                ProjectionFrame::Visit(expr) => match expr.node() {
                    ExprNode::App { f, a } => {
                        tasks.push(ProjectionFrame::Apply);
                        tasks.push(ProjectionFrame::Visit(a.clone()));
                        tasks.push(ProjectionFrame::Visit(f.clone()));
                    }
                    ExprNode::Lam {
                        binder_name,
                        binder_type,
                        body,
                        binder_info,
                    } => {
                        reserve(&mut locals, self.limits.max_context_depth)?;
                        locals.push(binder_type.clone());
                        tasks.push(ProjectionFrame::Lambda(
                            binder_name.clone(),
                            binder_type.clone(),
                            *binder_info,
                        ));
                        tasks.push(ProjectionFrame::Visit(body.clone()));
                    }
                    ExprNode::LetE {
                        decl_name,
                        type_,
                        value,
                        body,
                        non_dep,
                    } => {
                        tasks.push(ProjectionFrame::LetValue(
                            decl_name.clone(),
                            type_.clone(),
                            body.clone(),
                            *non_dep,
                        ));
                        tasks.push(ProjectionFrame::Visit(value.clone()));
                    }
                    ExprNode::Proj {
                        struct_name,
                        idx,
                        expr: receiver,
                    } => {
                        let mut selector = struct_name.clone();
                        if let Some(type_) = self.projection_receiver_type(receiver, &locals)?
                            && let Some((shape, _)) =
                                self.projection_slot(&type_, struct_name, *idx)?
                            && self.value_type(&shape.source)? == Some(ValueType::Constructor)
                        {
                            selector = shape.name;
                        }
                        tasks.push(ProjectionFrame::Projection(selector, *idx));
                        tasks.push(ProjectionFrame::Visit(receiver.clone()));
                    }
                    ExprNode::MData { expr, .. } => {
                        tasks.push(ProjectionFrame::Visit(expr.clone()))
                    }
                    _ => values.push(expr.clone()),
                },
                ProjectionFrame::Apply => {
                    let argument = pop(&mut values)?;
                    let function = pop(&mut values)?;
                    values.push(Expr::app(function, argument));
                }
                ProjectionFrame::Lambda(name, type_, info) => {
                    let body = pop(&mut values)?;
                    locals.pop();
                    values.push(Expr::lam(name, type_, body, info));
                }
                ProjectionFrame::LetValue(name, type_, body, nondep) => {
                    let value = pop(&mut values)?;
                    reserve(&mut locals, self.limits.max_context_depth)?;
                    locals.push(type_.clone());
                    tasks.push(ProjectionFrame::LetBody(name, type_, value, nondep));
                    tasks.push(ProjectionFrame::Visit(body));
                }
                ProjectionFrame::LetBody(name, type_, value, nondep) => {
                    let body = pop(&mut values)?;
                    locals.pop();
                    values.push(Expr::let_e(name, type_, value, body, nondep));
                }
                ProjectionFrame::Projection(name, index) => {
                    let receiver = pop(&mut values)?;
                    values.push(Expr::proj(name, index, receiver));
                }
            }
        }
        if values.len() != 1 || !locals.is_empty() {
            return Err(unsupported("projection preparation stack"));
        }
        pop(&mut values)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn record_engine() -> Engine {
        let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
        Engine::with_source_seed(limits).unwrap().into_complete().unwrap()
            .check_source_files(
                &[b"structure Box (A : Type) where\n  value : A\nstructure Other where\n  value : Nat"],
                &KVMap::new(), SourceCheckLimits::new(limits),
            ).unwrap().into_complete().unwrap().engine
    }
    #[test]
    fn equal_bound_variable_nodes_in_different_scopes_do_not_share_a_layout() {
        let engine = record_engine();
        let mut prep = Preparation::new(&engine.environment, IngressLimits::default());
        let receiver = Expr::bvar(0).unwrap();
        let projection = Expr::proj(name("Box"), 0, receiver.clone());
        let mut layouts = Vec::new();
        for field in ["Nat", "String"] {
            let type_ = Expr::app(
                Expr::const_(name("Box"), vec![]),
                Expr::const_(name(field), vec![]),
            );
            let body = Expr::lam(
                Name::anonymous(),
                type_,
                projection.clone(),
                BinderInfo::Default,
            );
            let output = prep.lower_projections(&body).unwrap();
            let ExprNode::Lam { body, .. } = output.node() else {
                panic!("lambda")
            };
            let ExprNode::Proj {
                struct_name,
                expr,
                idx,
            } = body.node()
            else {
                panic!("projection")
            };
            assert_eq!(expr, &receiver);
            assert_eq!(*idx, 0);
            layouts.push(struct_name.clone());
        }
        assert_ne!(layouts[0], layouts[1]);
        assert_eq!(prep.constructors.len(), 2);
        assert_eq!(prep.constructors[0].fields, vec![ValueType::Nat]);
        assert_eq!(prep.constructors[1].fields, vec![ValueType::String]);
    }
    #[test]
    fn incorrect_projection_family_and_field_metadata_cannot_select_a_layout() {
        let engine = record_engine();
        for (family, index) in [("Other", 0), ("Box", 1), ("Missing", 0)] {
            let mut prep = Preparation::new(&engine.environment, IngressLimits::default());
            let type_ = Expr::app(
                Expr::const_(name("Box"), vec![]),
                Expr::const_(name("Nat"), vec![]),
            );
            let body = Expr::lam(
                Name::anonymous(),
                type_,
                Expr::proj(name(family), index, Expr::bvar(0).unwrap()),
                BinderInfo::Default,
            );
            assert!(prep.lower_projections(&body).is_err());
            assert!(prep.constructors.is_empty());
        }
    }

    #[test]
    fn dictionary_metadata_is_static_only_when_all_its_fields_are_inert() {
        let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
        let engine = Engine::with_source_seed(limits)
            .unwrap()
            .into_complete()
            .unwrap()
            .check_source_files(
                &[br#"
structure Token where
  value : Nat
class Action (token : Token) where
  call : Nat -> Nat
def token : Token := { value := 7 }
instance selected : Action token := { call := fun n => n }
def count (n : Nat) : Nat := match n with | .zero => 0 | .succ k => count k + 1
def computedToken : Token := { value := count 30 }
instance computed : Action computedToken := { call := fun n => n }
"#],
                &KVMap::new(),
                SourceCheckLimits::new(limits),
            )
            .unwrap()
            .into_complete()
            .unwrap()
            .engine;
        let constant = |label| Expr::const_(name(label), vec![]);
        let mut prep = Preparation::new(&engine.environment, IngressLimits::default());
        let selected = prep
            .projection_call(
                &constant("Action.call"),
                &[constant("token"), constant("selected")],
            )
            .unwrap();
        assert!(matches!(selected, Some(value) if matches!(value.node(), ExprNode::Lam { .. })));
        // Even though this parameter lives only in the selected field's type,
        // discovering its dictionary must not drop the count computation.
        assert!(
            prep.projection_call(
                &constant("Action.call"),
                &[constant("computedToken"), constant("computed")],
            )
            .unwrap()
            .is_none()
        );
    }

    #[test]
    fn private_variant_projection_keys_must_belong_to_the_selected_family() {
        let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
        let engine = Engine::with_source_seed(limits)
            .unwrap().into_complete().unwrap()
            .check_source_files(
                &[b"mutual\ninductive T : Nat -> Type where | leaf (n : Nat) : T n | node (n : Nat) (f : F n) : T n\ninductive F : Nat -> Type where | nil (n : Nat) : F n | cons (n : Nat) (t : T n) : F n\nend"],
                &KVMap::new(), SourceCheckLimits::new(limits),
            ).unwrap().into_complete().unwrap().engine;
        let mut prep = Preparation::new(&engine.environment, IngressLimits::default());
        let t = Expr::app(Expr::const_(name("T"), vec![]), nat::literal(7));
        let f = Expr::app(Expr::const_(name("F"), vec![]), nat::literal(7));
        let t_shape = prep.record_shape(&t).unwrap().unwrap();
        let f_shape = prep.record_shape(&f).unwrap().unwrap();
        for ctor in &t_shape.constructors {
            // Valid variant projections remain for constructor-case lowering;
            // they are not incorrectly converted into single-record projections.
            assert!(
                prep.projection_slot(&t, &t_shape.projection(ctor), 0)
                    .unwrap()
                    .is_none()
            );
        }
        for ctor in &f_shape.constructors {
            assert!(
                prep.projection_slot(&t, &f_shape.projection(ctor), 0)
                    .is_err()
            );
        }
        assert!(prep.projection_slot(&t, &name("Missing"), 0).is_err());
    }

    #[test]
    fn local_telescope_and_type_synthesis_are_heap_bounded() {
        std::thread::Builder::new()
            .stack_size(128 * 1024)
            .spawn(|| {
                let environment = Environment::new();
                let mut body = Expr::proj(name("Box"), 0, Expr::bvar(0).unwrap());
                for _ in 0..2000 {
                    body = Expr::lam(
                        Name::anonymous(),
                        Expr::const_(name("Nat"), vec![]),
                        body,
                        BinderInfo::Default,
                    );
                }
                let limits = IngressLimits {
                    max_context_depth: 32,
                    ..IngressLimits::default()
                };
                let mut prep = Preparation::new(&environment, limits);
                assert!(matches!(
                    prep.lower_projections(&body),
                    Err(IngressError::ResourceLimit { .. })
                ));
                assert!(matches!(
                    prep.projection_receiver_type(&body, &[]),
                    Err(IngressError::ResourceLimit { .. })
                ));
            })
            .unwrap()
            .join()
            .unwrap();
    }
}
