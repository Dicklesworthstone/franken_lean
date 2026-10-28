//! Uniform representations for records that hide a type. The private boxed
//! leaf is introduced only from an admitted type field. Object storage is
//! shared only after checking every nested layout; callable signatures are
//! adapted by real closures, never by relabelling an existing closure.
use super::*;
use std::collections::HashMap;

#[derive(Clone, Copy, Eq, PartialEq)]
struct Generation {
    definitions: usize,
    shapes: usize,
    native: usize,
    boxed: bool,
}

impl Generation {
    fn current(preparation: &Preparation<'_>) -> Self {
        Self {
            definitions: preparation.canonical_definition_generation(),
            shapes: preparation.data_shapes.len(),
            native: preparation.value_types.native.len(),
            boxed: preparation.value_types.boxed.is_some(),
        }
    }
}

type Key = (Expr, usize);

struct Entry {
    generation: Generation,
    value: Expr,
}

/// One invocation's original lexical scopes and completed transformations. The borrowed
/// caller is fixed at scope zero. Interning each original domain under its parent retains
/// exact dependent contexts without copying that caller or confusing equal-depth siblings.
#[derive(Default)]
struct Memo {
    scopes: HashMap<(usize, Expr), usize>,
    entries: HashMap<Key, Entry>,
}

impl Memo {
    fn scope(&mut self, parent: usize, domain: Expr, limit: usize) -> Result<usize, IngressError> {
        let key = (parent, domain);
        if let Some(scope) = self.scopes.get(&key) {
            return Ok(*scope);
        }
        let observed = self.scopes.len().saturating_add(1);
        if observed > limit {
            return Err(IngressError::ResourceLimit {
                resource: IngressResource::Nodes,
                limit,
                observed,
            });
        }
        self.scopes
            .try_reserve(1)
            .map_err(|_| IngressError::AllocationFailure {
                resource: IngressResource::Nodes,
                requested: observed,
            })?;
        self.scopes.insert(key, observed);
        Ok(observed)
    }

    fn remember(
        &mut self,
        preparation: &Preparation<'_>,
        key: Key,
        generation: Generation,
        value: Expr,
    ) -> Result<(), IngressError> {
        // Layout discovery can register a new descriptive family during a projection.
        // Only a complete answer derived without changing that authority is reusable.
        if Generation::current(preparation) != generation {
            return Ok(());
        }
        let additional = usize::from(!self.entries.contains_key(&key));
        let observed = self.entries.len().saturating_add(additional);
        if observed > preparation.limits.max_nodes {
            return Err(IngressError::ResourceLimit {
                resource: IngressResource::Nodes,
                limit: preparation.limits.max_nodes,
                observed,
            });
        }
        self.entries
            .try_reserve(additional)
            .map_err(|_| IngressError::AllocationFailure {
                resource: IngressResource::Nodes,
                requested: observed,
            })?;
        self.entries.insert(key, Entry { generation, value });
        Ok(())
    }
}

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
            Apply(Key, Generation),
            Domain(Key, Generation),
            Body(Key, Generation, Expr),
        }
        // Scalar indices are representation-irrelevant. Remove them before
        // traversing their children, just as ordinary layout discovery does;
        // hidden-carrier discovery must not normalize erased computations.
        let source = self.erase_data_indices(source)?;
        let source = self.normalize_type(&source)?;
        let mut work = vec![Work::Visit(source)];
        let mut values = Vec::new();
        // The caller owns this immutable telescope. Retain its lexical depth
        // without cloning it on every metadata query; only binders entered by
        // this traversal need an owned suffix. Keep the original table bound
        // even when the source never inspects a caller variable.
        if context.len() > self.limits.max_context_depth {
            return Err(IngressError::ResourceLimit {
                resource: IngressResource::ProgramTables,
                limit: self.limits.max_context_depth,
                observed: self.limits.max_context_depth.saturating_add(1),
            });
        }
        let mut locals = Vec::new();
        let mut memo = Memo::default();
        let mut scope = 0;
        while let Some(task) = work.pop() {
            self.tick()?;
            match task {
                Work::Visit(source) => {
                    // A visit already meters this lookup. Leaves whose result is the input
                    // need no row; completed applications, binders and projections do.
                    let key = (source.clone(), scope);
                    let generation = Generation::current(self);
                    if let Some(entry) = memo.entries.get(&key)
                        && entry.generation == generation
                    {
                        reserve(&mut values, self.limits.max_nodes)?;
                        values.push(entry.value.clone());
                        continue;
                    }
                    match source.node() {
                        ExprNode::App { f, a } => {
                            for task in [
                                Work::Apply(key, generation),
                                Work::Visit(a.clone()),
                                Work::Visit(f.clone()),
                            ] {
                                reserve(&mut work, self.limits.max_nodes)?;
                                work.push(task);
                            }
                        }
                        ExprNode::ForallE { binder_type, .. }
                        | ExprNode::Lam { binder_type, .. } => {
                            reserve(&mut work, self.limits.max_nodes)?;
                            work.push(Work::Domain(key, generation));
                            reserve(&mut work, self.limits.max_nodes)?;
                            work.push(Work::Visit(binder_type.clone()));
                        }
                        ExprNode::Proj {
                            struct_name,
                            idx,
                            expr,
                        } => {
                            let mut receiver_type =
                                self.projection_receiver_type_in(expr, context, &locals, 0)?;
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
                                && matches!(
                                    self.type_head(&original)?.node(),
                                    ExprNode::Sort { .. }
                                )
                                && let Some((shape, _)) =
                                    self.projection_slot(&receiver_type, struct_name, *idx)?
                                && usize::try_from(*idx).ok().is_some_and(|index| {
                                    shape.constructors[0].type_fields.get(index) == Some(&true)
                                })
                            {
                                result = self.enable_boxed_type()?;
                            }
                            reserve(&mut values, self.limits.max_nodes)?;
                            memo.remember(self, key, generation, result.clone())?;
                            values.push(result);
                        }
                        _ => {
                            reserve(&mut values, self.limits.max_nodes)?;
                            values.push(source);
                        }
                    }
                }
                Work::Apply(key, generation) => {
                    let argument = pop(&mut values)?;
                    let function = pop(&mut values)?;
                    let result = Expr::app(function, argument);
                    memo.remember(self, key, generation, result.clone())?;
                    values.push(result);
                }
                Work::Domain(key, generation) => {
                    let (ExprNode::ForallE {
                        binder_type: original,
                        body,
                        ..
                    }
                    | ExprNode::Lam {
                        binder_type: original,
                        body,
                        ..
                    }) = key.0.node()
                    else {
                        return Err(unsupported("hidden type domain stack"));
                    };
                    let body = body.clone();
                    let domain = pop(&mut values)?;
                    let observed = context.len().saturating_add(locals.len()).saturating_add(1);
                    if observed > self.limits.max_context_depth {
                        return Err(IngressError::ResourceLimit {
                            resource: IngressResource::ProgramTables,
                            limit: self.limits.max_context_depth,
                            observed,
                        });
                    }
                    locals
                        .try_reserve(1)
                        .map_err(|_| IngressError::AllocationFailure {
                            resource: IngressResource::ProgramTables,
                            requested: observed,
                        })?;
                    scope = memo.scope(scope, original.clone(), self.limits.max_nodes)?;
                    locals.push(original.clone());
                    reserve(&mut work, self.limits.max_nodes)?;
                    work.push(Work::Body(key, generation, domain));
                    reserve(&mut work, self.limits.max_nodes)?;
                    work.push(Work::Visit(body));
                }
                Work::Body(key, generation, domain) => {
                    locals.pop();
                    scope = key.1;
                    let body = pop(&mut values)?;
                    let result = match key.0.node() {
                        ExprNode::Lam {
                            binder_name,
                            binder_info,
                            ..
                        } => Expr::lam(binder_name.clone(), domain, body, *binder_info),
                        ExprNode::ForallE {
                            binder_name,
                            binder_info,
                            ..
                        } => Expr::forall_e(binder_name.clone(), domain, body, *binder_info),
                        _ => return Err(unsupported("hidden type body stack")),
                    };
                    memo.remember(self, key, generation, result.clone())?;
                    values.push(result);
                }
            }
        }
        if values.len() != 1 || !locals.is_empty() || scope != 0 {
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
                if matches!(a, ValueType::Closure(_)) {
                    // A callable's FIR interface records Constructor for
                    // every container. Equal interface ids/classes therefore
                    // do not establish compatible callback slots inside a
                    // parameter or result container. Check those original
                    // types through this same structural worklist too.
                    let mut actual = self.normalize_type(&actual)?;
                    let mut expected = self.normalize_type(&expected)?;
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
                    ) = (actual.node(), expected.node())
                    {
                        self.tick()?;
                        if ab.has_loose_bvars() || eb.has_loose_bvars() {
                            return Ok(false);
                        }
                        reserve(&mut work, self.limits.max_nodes)?;
                        work.push((ad.clone(), ed.clone()));
                        actual = ab.clone();
                        expected = eb.clone();
                    }
                    if matches!(actual.node(), ExprNode::ForallE { .. })
                        || matches!(expected.node(), ExprNode::ForallE { .. })
                    {
                        return Ok(false);
                    }
                    reserve(&mut work, self.limits.max_nodes)?;
                    work.push((actual, expected));
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

    pub(in crate::runtime) fn adapt_erased_field(
        &mut self,
        value: &Expr,
        actual: &Expr,
        expected: &Expr,
    ) -> Result<Expr, IngressError> {
        let actual = self.erase_runtime_type(actual)?;
        let actual = self.erase_hidden_types(&actual, &[])?;
        let expected = self.normalize_type(expected)?;
        let adapter = self.erased_adapter(&actual, &expected)?;
        Ok(match adapter {
            None => {
                if self.value_types.boxed.as_ref() == Some(&expected)
                    && let Some(kind @ ValueType::Closure(_)) = self.value_type(&actual)?
                {
                    // A boxed field no longer exposes the callback's concrete
                    // signature to ordinary argument annotation. Register that
                    // interface before the constructor erases its carrier.
                    self.typed_callable_result(value.clone(), actual, kind)?
                } else {
                    value.clone()
                }
            }
            Some(body) => Expr::let_e(Name::anonymous(), actual, value.clone(), body, false),
        })
    }
}

#[cfg(test)]
mod context_tests;
