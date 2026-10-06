//! Uniform representations for records that hide a type. The private boxed
//! leaf is introduced only from an admitted type field. Object storage is
//! shared only after checking every nested layout; callable signatures are
//! adapted by real closures, never by relabelling an existing closure.
use super::*;

impl Preparation<'_> {
    /// A minor's type binder denotes metadata, not its inert object slot.
    /// Reopen it at the same boxed carrier used by the checked constructor
    /// layout, so reconstructed constructors and callback annotations retain
    /// that representation. Value/proof arguments remain real projections.
    pub(in crate::runtime) fn constructor_minor_apply(
        &mut self,
        minor: Expr,
        constructor: &ShapeConstructor,
        index: usize,
        field: Expr,
    ) -> Result<Expr, IngressError> {
        let argument = match constructor.type_fields.get(index) {
            Some(true) => self.enable_boxed_type()?,
            Some(false) => field,
            None => return Err(unsupported("constructor minor field metadata")),
        };
        self.minor_apply(minor, argument)
    }

    pub(in crate::runtime) fn enable_boxed_type(&mut self) -> Result<Expr, IngressError> {
        self.tick()?;
        let boxed = boxed_slot_type();
        if self.environment.contains(&name("_fln_runtime_boxed")) {
            return Err(unsupported("runtime boxed slot name collision"));
        }
        self.value_types.boxed = Some(boxed.clone());
        Ok(boxed)
    }

    /// Remove only earlier type-field binders. An occurrence of an ordinary
    /// field becomes an unresolved marker, so even a closed-looking type
    /// computation over a runtime value remains a representation refusal.
    pub(super) fn erase_field_dependencies(
        &mut self,
        source: &Expr,
        type_fields: &[bool],
    ) -> Result<Option<Expr>, IngressError> {
        let mut result = source.clone();
        for type_field in type_fields.iter().rev() {
            self.tick()?;
            if !result.has_loose_bvars() {
                break;
            }
            let replacement = if *type_field {
                self.enable_boxed_type()?
            } else {
                indexed::pending_parameter()
            };
            result = self.substitution(&result, &replacement)?;
        }
        Ok((!result.has_loose_bvars() && !result.has_fvar()).then_some(result))
    }

    /// Normalize metadata, then replace a verified, unresolved Type-field
    /// projection by its boxed representation. Static projections keep their
    /// concrete type. Runtime receiver expressions are never evaluated here.
    pub(in crate::runtime) fn erase_hidden_types(
        &mut self,
        source: &Expr,
        context: &[Expr],
    ) -> Result<Expr, IngressError> {
        enum Work {
            Visit(Expr),
            Apply,
            Domain(Name, Expr, Expr, BinderInfo, bool),
            Body(Name, Expr, BinderInfo, bool),
        }
        // Scalar indices are representation-irrelevant. Remove them before
        // traversing their children, just as ordinary layout discovery does;
        // hidden-carrier discovery must not normalize erased computations.
        let source = self.erase_data_indices(source)?;
        let source = self.normalize_type(&source)?;
        let mut work = vec![Work::Visit(source)];
        let mut values = Vec::new();
        let mut locals = Vec::new();
        for local in context {
            self.tick()?;
            reserve(&mut locals, self.limits.max_context_depth)?;
            locals.push(local.clone());
        }
        while let Some(task) = work.pop() {
            self.tick()?;
            match task {
                Work::Visit(source) => match source.node() {
                    ExprNode::App { f, a } => {
                        for task in [Work::Apply, Work::Visit(a.clone()), Work::Visit(f.clone())] {
                            reserve(&mut work, self.limits.max_nodes)?;
                            work.push(task);
                        }
                    }
                    ExprNode::ForallE {
                        binder_name,
                        binder_type,
                        body,
                        binder_info,
                    }
                    | ExprNode::Lam {
                        binder_name,
                        binder_type,
                        body,
                        binder_info,
                    } => {
                        reserve(&mut work, self.limits.max_nodes)?;
                        work.push(Work::Domain(
                            binder_name.clone(),
                            binder_type.clone(),
                            body.clone(),
                            *binder_info,
                            matches!(source.node(), ExprNode::Lam { .. }),
                        ));
                        reserve(&mut work, self.limits.max_nodes)?;
                        work.push(Work::Visit(binder_type.clone()));
                    }
                    ExprNode::Proj {
                        struct_name,
                        idx,
                        expr,
                    } => {
                        let mut receiver_type = self.projection_receiver_type(expr, &locals)?;
                        if receiver_type.is_none()
                            && matches!(self.environment.find(struct_name),
                                Some(ConstantInfo::Induct(family))
                                if family.num_params == 0 && family.base.level_params.is_empty())
                        {
                            // A checked primitive projection already identifies
                            // this unparameterized family, even after catalog
                            // extraction removes the surrounding local context.
                            receiver_type = Some(Expr::const_(struct_name.clone(), vec![]));
                        }
                        let mut result = source.clone();
                        if let Some(receiver_type) = receiver_type
                            && let Some(original) = self.original_projection_type(
                                &receiver_type,
                                struct_name,
                                *idx,
                                expr,
                            )?
                            && matches!(self.type_head(&original)?.node(), ExprNode::Sort { .. })
                            && let Some((shape, _)) =
                                self.projection_slot(&receiver_type, struct_name, *idx)?
                            && usize::try_from(*idx).ok().is_some_and(|index| {
                                shape.constructors[0].type_fields.get(index) == Some(&true)
                            })
                        {
                            result = self.enable_boxed_type()?;
                        }
                        reserve(&mut values, self.limits.max_nodes)?;
                        values.push(result);
                    }
                    _ => {
                        reserve(&mut values, self.limits.max_nodes)?;
                        values.push(source);
                    }
                },
                Work::Apply => {
                    let argument = pop(&mut values)?;
                    let function = pop(&mut values)?;
                    values.push(Expr::app(function, argument));
                }
                Work::Domain(name, original, body, info, lambda) => {
                    let domain = pop(&mut values)?;
                    reserve(&mut locals, self.limits.max_context_depth)?;
                    locals.push(original);
                    reserve(&mut work, self.limits.max_nodes)?;
                    work.push(Work::Body(name, domain, info, lambda));
                    reserve(&mut work, self.limits.max_nodes)?;
                    work.push(Work::Visit(body));
                }
                Work::Body(name, domain, info, lambda) => {
                    locals.pop();
                    let body = pop(&mut values)?;
                    values.push(if lambda {
                        Expr::lam(name, domain, body, info)
                    } else {
                        Expr::forall_e(name, domain, body, info)
                    });
                }
            }
        }
        if values.len() != 1 || locals.len() != context.len() {
            return Err(unsupported("hidden type representation stack"));
        }
        pop(&mut values)
    }

    /// Equal callable interfaces may have different discovery-local ids.
    /// Compare their complete recursive signatures, including ownership.
    fn equal_runtime_classes(
        &mut self,
        left: ValueType,
        right: ValueType,
    ) -> Result<bool, IngressError> {
        let mut work = vec![(left, right)];
        let mut seen = HashSet::new();
        while let Some((left, right)) = work.pop() {
            self.tick()?;
            if left == right || seen.contains(&(left, right)) {
                continue;
            }
            let (ValueType::Closure(left), ValueType::Closure(right)) = (left, right) else {
                return Ok(false);
            };
            seen.try_reserve(1)
                .map_err(|_| IngressError::AllocationFailure {
                    resource: IngressResource::ProgramTables,
                    requested: seen.len().saturating_add(1),
                })?;
            seen.insert((ValueType::Closure(left), ValueType::Closure(right)));
            let Some(left) = self.interfaces.get(left.get() as usize).cloned() else {
                return Err(unsupported("hidden callback source interface"));
            };
            let Some(right) = self.interfaces.get(right.get() as usize).cloned() else {
                return Err(unsupported("hidden callback target interface"));
            };
            if left.parameters.len() != right.parameters.len()
                || left.parameter_ownership != right.parameter_ownership
                || left.result_ownership != right.result_ownership
            {
                return Ok(false);
            }
            for pair in left
                .parameters
                .into_iter()
                .zip(right.parameters)
                .chain(std::iter::once((left.result, right.result)))
            {
                self.tick()?;
                reserve(&mut work, self.limits.max_nodes)?;
                work.push(pair);
            }
        }
        Ok(true)
    }

    /// An ABI word is already the representation of every scalar or object.
    /// Container sharing additionally requires the same admitted constructors
    /// and compatible fields throughout the recursive object graph. A changed
    /// callback signature inside a container cannot be repaired by a cast.
    pub(super) fn shared_erased_storage(
        &mut self,
        actual: &Expr,
        expected: &Expr,
    ) -> Result<bool, IngressError> {
        let mut work = vec![(actual.clone(), expected.clone())];
        let mut seen = HashSet::new();
        while let Some((actual, expected)) = work.pop() {
            self.tick()?;
            if actual == expected || seen.contains(&(actual.clone(), expected.clone())) {
                continue;
            }
            seen.try_reserve(1)
                .map_err(|_| IngressError::AllocationFailure {
                    resource: IngressResource::ProgramTables,
                    requested: seen.len().saturating_add(1),
                })?;
            seen.insert((actual.clone(), expected.clone()));
            let (Some(a), Some(e)) = (self.value_type(&actual)?, self.value_type(&expected)?)
            else {
                return Ok(false);
            };
            if a == ValueType::Abi || e == ValueType::Abi {
                continue;
            }
            if a != ValueType::Constructor || e != ValueType::Constructor {
                if !self.equal_runtime_classes(a, e)? {
                    return Ok(false);
                }
                continue;
            }
            let (Some(a), Some(e)) = (self.record_shape(&actual)?, self.record_shape(&expected)?)
            else {
                return Ok(false);
            };
            if a.constructors.len() != e.constructors.len() {
                return Ok(false);
            }
            for (a, e) in a.constructors.iter().zip(&e.constructors) {
                self.tick()?;
                if a.original != e.original
                    || a.tag != e.tag
                    || a.fields.len() != e.fields.len()
                    || a.type_fields != e.type_fields
                {
                    return Ok(false);
                }
                for (a, e) in a.fields.iter().zip(&e.fields) {
                    self.tick()?;
                    reserve(&mut work, self.limits.max_nodes)?;
                    work.push((a.clone(), e.clone()));
                }
            }
        }
        Ok(true)
    }

    pub(super) fn adapt_erased_field(
        &mut self,
        value: &Expr,
        actual: &Expr,
        expected: &Expr,
    ) -> Result<Expr, IngressError> {
        let actual = self.erase_runtime_type(actual)?;
        let actual = self.erase_hidden_types(&actual, &[])?;
        let expected = self.normalize_type(expected)?;
        if self.shared_erased_storage(&actual, &expected)? {
            return Ok(value.clone());
        }
        let (Some(ValueType::Closure(_)), Some(ValueType::Closure(_))) =
            (self.value_type(&actual)?, self.value_type(&expected)?)
        else {
            return Err(unsupported("nonuniform hidden field representation"));
        };
        let mut a = actual.clone();
        let mut e = expected.clone();
        let mut domains = Vec::new();
        while let (
            ExprNode::ForallE {
                binder_type: ad,
                body: ab,
                ..
            },
            ExprNode::ForallE {
                binder_type: ed,
                body: eb,
                ..
            },
        ) = (a.node(), e.node())
        {
            self.tick()?;
            if ab.has_loose_bvars()
                || eb.has_loose_bvars()
                || !self.shared_erased_storage(ad, ed)?
            {
                return Err(unsupported("nonuniform hidden callback parameter"));
            }
            reserve(&mut domains, self.limits.max_context_depth)?;
            domains.push(ed.clone());
            a = ab.clone();
            e = eb.clone();
        }
        if domains.is_empty() || !self.shared_erased_storage(&a, &e)? {
            return Err(unsupported("nonuniform hidden callback result"));
        }
        let arity =
            u32::try_from(domains.len()).map_err(|_| unsupported("hidden callback arity"))?;
        let mut body =
            Expr::bvar(arity).map_err(|_| unsupported("hidden callback capture scope"))?;
        for index in (0..arity).rev() {
            self.tick()?;
            body = Expr::app(
                body,
                Expr::bvar(index).map_err(|_| unsupported("hidden callback argument scope"))?,
            );
        }
        for domain in domains.into_iter().rev() {
            self.tick()?;
            body = Expr::lam(Name::anonymous(), domain, body, BinderInfo::Default);
        }
        // The source value is evaluated once, before the adapter is returned.
        // Both checked signatures remain explicit, so ordinary closure ingress
        // inserts Box/Unbox at the call/result boundaries and validates captures.
        Ok(Expr::let_e(
            Name::anonymous(),
            actual,
            value.clone(),
            Expr::let_e(
                Name::anonymous(),
                expected,
                body,
                Expr::bvar(0).map_err(|_| unsupported("hidden callback result scope"))?,
                false,
            ),
            false,
        ))
    }
}
