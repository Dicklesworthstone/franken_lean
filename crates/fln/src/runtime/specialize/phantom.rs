//! Prove that a first `Type` parameter has no represented uses.
//!
//! A recursive call can replace `A` by `A × A` forever even when every
//! executable parameter and result is Nat. Specializing each syntactically
//! different type then grows an infinite compiler graph before the VM starts.
//! We identify only a closed graph of parameters whose occurrences flow into
//! each other's erased first arguments. No provisional cycle result escapes
//! the graph walk, and the admitted logical declarations are never changed.
use super::*;

type Key = (Name, Vec<Level>);

#[derive(Default)]
pub(super) struct Store {
    // One immutable environment per Preparation. Only actual, checked
    // environment definitions participate; generated compiler bodies do not.
    completed: HashMap<Key, bool>,
}

fn first_type_parameter(type_: &Expr, value: &Expr) -> Option<Expr> {
    let ExprNode::ForallE {
        binder_type,
        body,
        binder_info: BinderInfo::Default,
        ..
    } = type_.node()
    else {
        return None;
    };
    if !matches!(binder_type.node(), ExprNode::Sort { level } if *level == Level::one())
        || body.has_loose_bvars()
    {
        return None;
    }
    let ExprNode::Lam {
        binder_type,
        body,
        binder_info: BinderInfo::Default,
        ..
    } = value.node()
    else {
        return None;
    };
    matches!(binder_type.node(), ExprNode::Sort { level } if *level == Level::one())
        .then(|| body.clone())
}

impl Preparation<'_> {
    /// Resolve the same checked recursive companion as execution, while
    /// excluding external implementations, native bodies and opaque fallbacks.
    fn phantom_definition(
        &mut self,
        requested: &Name,
    ) -> Result<Option<DefinitionVal>, IngressError> {
        self.tick()?;
        match self.environment.find(requested) {
            Some(ConstantInfo::Defn(_)) => {}
            Some(ConstantInfo::Opaque(_))
                if self
                    .environment
                    .contains(&Name::str(requested.clone(), "_unsafe_rec")) => {}
            _ => return Ok(None),
        }
        let parent = self.recursive_parent_candidate(requested);
        let owner = parent.as_ref().unwrap_or(requested);
        if self
            .runtime_initializers
            .is_some_and(|names| names.contains(owner) || names.contains(requested))
            || self.implementations()?.get(owner).is_some()
            || self.has_extern_attribute(owner)?
            || (owner != requested && self.has_extern_attribute(requested)?)
            || self.native_intrinsic_binding(owner)?.is_some()
        {
            return Ok(None);
        }
        let Some(definition) = self.recursive_definition(requested)? else {
            return Ok(None);
        };
        if !matches!(self.environment.find(&definition.base.name),
            Some(ConstantInfo::Defn(actual)) if actual == &definition)
        {
            return Ok(None);
        }
        Ok(Some(definition))
    }

    /// Collect obligations for the first argument of other constant calls.
    /// The first parameter is the outermost binder of a closed definition, so
    /// at depth `index` every other bound variable has a smaller index. The
    /// expression's cached loose-variable range therefore detects its presence
    /// exactly, without an unmetered traversal for each application argument.
    fn phantom_dependencies(&mut self, body: Expr) -> Result<Option<Vec<Key>>, IngressError> {
        let mut pending = Vec::new();
        reserve(&mut pending, self.limits.max_nodes)?;
        pending.push((body, 0_u32));
        let mut seen = HashSet::new();
        let mut dependencies = Vec::new();
        while let Some((expression, index)) = pending.pop() {
            self.tick()?;
            if expression.loose_bvar_range() <= index {
                continue;
            }
            seen.try_reserve(1)
                .map_err(|_| IngressError::AllocationFailure {
                    resource: IngressResource::ProgramTables,
                    requested: seen.len().saturating_add(1),
                })?;
            if !seen.insert((expression.clone(), index)) {
                continue;
            }
            match expression.node() {
                ExprNode::App { .. } => {
                    let (head, arguments) = self.spine(&expression)?;
                    let ExprNode::Const { name, levels } = head.node() else {
                        return Ok(None);
                    };
                    let first = arguments
                        .first()
                        .is_some_and(|argument| argument.loose_bvar_range() > index);
                    if first {
                        if levels
                            .iter()
                            .any(|level| level.has_mvar() || level.has_param())
                        {
                            return Ok(None);
                        }
                        reserve(&mut dependencies, self.limits.max_nodes)?;
                        dependencies.push((name.clone(), levels.clone()));
                    }
                    // A whole first argument may be erased only once the
                    // callee's graph obligation succeeds. All other values,
                    // including strict call operands, retain the same walk.
                    for argument in arguments.into_iter().skip(usize::from(first)) {
                        reserve(&mut pending, self.limits.max_nodes)?;
                        pending.push((argument, index));
                    }
                }
                ExprNode::Lam {
                    binder_type, body, ..
                } => {
                    // Leading runtime parameters and branch thunks are safe
                    // only when their represented domains omit the type.
                    // A closure whose argument representation depends on it
                    // is not a phantom use, even if its result is discarded.
                    if binder_type.loose_bvar_range() > index {
                        return Ok(None);
                    }
                    let next = self.producer_depth(index as usize + 1)?;
                    reserve(&mut pending, self.limits.max_nodes)?;
                    pending.push((body.clone(), next));
                }
                ExprNode::LetE {
                    type_, value, body, ..
                } => {
                    if type_.loose_bvar_range() > index {
                        return Ok(None);
                    }
                    let next = self.producer_depth(index as usize + 1)?;
                    reserve(&mut pending, self.limits.max_nodes)?;
                    pending.push((value.clone(), index));
                    reserve(&mut pending, self.limits.max_nodes)?;
                    pending.push((body.clone(), next));
                }
                ExprNode::MData { expr, .. } => {
                    reserve(&mut pending, self.limits.max_nodes)?;
                    pending.push((expr.clone(), index));
                }
                // A bare type variable, a projection, a type-valued result or
                // an unknown expression has no proved erased argument owner.
                _ => return Ok(None),
            }
        }
        Ok(Some(dependencies))
    }

    fn remember_phantom(&mut self, key: Key, phantom: bool) -> Result<(), IngressError> {
        self.tick()?;
        let entries = &mut self.specializations.phantom.completed;
        let observed = entries
            .len()
            .saturating_add(usize::from(!entries.contains_key(&key)));
        if observed > self.limits.max_nodes {
            return Err(IngressError::ResourceLimit {
                resource: IngressResource::Nodes,
                limit: self.limits.max_nodes,
                observed,
            });
        }
        entries
            .try_reserve(1)
            .map_err(|_| IngressError::AllocationFailure {
                resource: IngressResource::ProgramTables,
                requested: observed,
            })?;
        entries.insert(key, phantom);
        Ok(())
    }

    /// A completed finite graph proves every cycle at once: every occurrence
    /// is in the first erased argument of another vertex in the graph, or of
    /// a previously completed graph. Encountering an in-progress vertex only
    /// avoids revisiting it; it never returns a successful proof by itself.
    pub(super) fn phantom_first_type_parameter(
        &mut self,
        definition: &DefinitionVal,
        levels: &[Level],
        type_: &Expr,
        value: &Expr,
    ) -> Result<bool, IngressError> {
        self.tick()?;
        if !closed(type_) || !closed(value) || first_type_parameter(type_, value).is_none() {
            return Ok(false);
        }
        // Nat is only a compiler-private representative of Type. Require the
        // actual admitted carrier before introducing it into a private body.
        if !matches!(self.environment.find(&name("Nat")), Some(ConstantInfo::Induct(nat))
            if !nat.is_unsafe && nat.base.level_params.is_empty()
                && matches!(nat.base.type_.node(), ExprNode::Sort { level }
                    if *level == Level::one()))
        {
            return Ok(false);
        }
        let root = (definition.base.name.clone(), levels.to_vec());
        if let Some(found) = self.specializations.phantom.completed.get(&root) {
            return Ok(*found);
        }
        let mut pending = Vec::new();
        reserve(&mut pending, self.limits.fir.max_functions)?;
        pending.push(root.clone());
        let mut visited = HashSet::new();
        let mut proved = Vec::new();
        while let Some(key) = pending.pop() {
            self.tick()?;
            if let Some(found) = self.specializations.phantom.completed.get(&key) {
                if !found {
                    self.remember_phantom(root, false)?;
                    return Ok(false);
                }
                continue;
            }
            visited
                .try_reserve(1)
                .map_err(|_| IngressError::AllocationFailure {
                    resource: IngressResource::ProgramTables,
                    requested: visited.len().saturating_add(1),
                })?;
            if !visited.insert(key.clone()) {
                continue;
            }
            let Some(candidate) = self.phantom_definition(&key.0)? else {
                self.remember_phantom(root, false)?;
                return Ok(false);
            };
            if candidate.base.level_params.len() != key.1.len()
                || key
                    .1
                    .iter()
                    .any(|level| level.has_mvar() || level.has_param())
            {
                self.remember_phantom(root, false)?;
                return Ok(false);
            }
            let type_ = self.universe_instance(
                &candidate.base.type_,
                &candidate.base.level_params,
                &key.1,
            )?;
            let value =
                self.universe_instance(&candidate.value, &candidate.base.level_params, &key.1)?;
            let body = if closed(&type_) && closed(&value) {
                first_type_parameter(&type_, &value)
            } else {
                None
            };
            let Some(body) = body else {
                self.remember_phantom(root, false)?;
                return Ok(false);
            };
            let Some(dependencies) = self.phantom_dependencies(body)? else {
                self.remember_phantom(root, false)?;
                return Ok(false);
            };
            reserve(&mut proved, self.limits.fir.max_functions)?;
            proved.push(key);
            for dependency in dependencies {
                reserve(&mut pending, self.limits.max_nodes)?;
                pending.push(dependency);
            }
        }
        // Pay and reserve the complete publication before inserting anything.
        // A node/depth/allocation stop never leaves a partially cached cycle.
        for _ in &proved {
            self.tick()?;
        }
        let entries = &mut self.specializations.phantom.completed;
        let observed = entries.len().saturating_add(proved.len());
        if observed > self.limits.max_nodes {
            return Err(IngressError::ResourceLimit {
                resource: IngressResource::Nodes,
                limit: self.limits.max_nodes,
                observed,
            });
        }
        entries
            .try_reserve(proved.len())
            .map_err(|_| IngressError::AllocationFailure {
                resource: IngressResource::ProgramTables,
                requested: observed,
            })?;
        for key in proved {
            entries.insert(key, true);
        }
        Ok(true)
    }
}
