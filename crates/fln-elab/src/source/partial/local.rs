//! Closure conversion for local functions inside a single partial definition.
//!
//! Recursive references stay typed, opaque metavariables while the source body
//! is checked. Only after every body and delayed constraint is complete do we
//! close their lexical captures and partition the complete dependency graph.
//! No candidate constant enters an environment during this conversion.
use super::*;
use std::collections::{HashMap, HashSet};
mod copies;

#[derive(Clone, Default)]
pub(in crate::source) struct Locals {
    headers: Vec<(Name, FVarId)>,
    aliases: Vec<(FVarId, Expr)>,
    closures: Vec<Closure>,
    owner: Option<Closure>,
    definitions: Vec<DefinitionVal>,
    failed_codegen: Vec<bool>,
}

#[derive(Clone)]
struct Closure {
    name: Name,
    id: MVarId,
    term: Typed,
    captures: Vec<LocalDecl>,
}

impl Locals {
    pub(in crate::source) fn obligations(&self) -> impl Iterator<Item = &MVarId> {
        self.closures
            .iter()
            .chain(self.owner.iter())
            .map(|closed| &closed.id)
    }
}

fn refusal(expected: &'static str) -> NatDefinitionElabError {
    NatDefinitionElabError::UnexpectedSyntax { expected }
}

fn apply(
    context: &mut Context,
    mut function: Expr,
    captures: &[LocalDecl],
) -> Result<Expr, NatDefinitionElabError> {
    for local in captures {
        context.tick()?;
        function = Expr::app(function, Expr::fvar(local.id.clone()));
    }
    Ok(function)
}

fn close(
    context: &mut Context,
    mut value: Expr,
    captures: &[LocalDecl],
    lambda: bool,
) -> Result<Expr, NatDefinitionElabError> {
    for local in captures.iter().rev() {
        context.tick()?;
        let domain = context.instantiate(&local.type_)?;
        let body = value
            .abstract_fvar(&local.id, 0)
            .map_err(|_| failure(SourceInferenceError::Scope))?;
        value = if lambda {
            Expr::lam(local.user_name.clone(), domain, body, local.binder_info)
        } else {
            Expr::forall_e(local.user_name.clone(), domain, body, local.binder_info)
        };
    }
    Ok(value)
}

#[derive(Default)]
struct Substitution {
    locals: HashMap<FVarId, Expr>,
    metavars: HashMap<MVarId, Expr>,
}

impl Substitution {
    fn expression(
        &self,
        context: &mut Context,
        expr: &Expr,
    ) -> Result<Expr, NatDefinitionElabError> {
        let expr = context.instantiate(expr)?;
        group::map_beta(context, &expr, &|_, node| {
            Ok(match node.node() {
                ExprNode::FVar { id } => self.locals.get(id).cloned(),
                ExprNode::MVar { id } => self.metavars.get(id).cloned(),
                _ => None,
            })
        })
    }
}

/// Replace opaque local applications with their current closure candidates.
/// Abstracting the original telescope before substitution preserves actual
/// arguments below enclosing lambdas and pattern branches.
struct ClosureHeads<'a> {
    helpers: &'a [Expr],
    owner: Expr,
}

fn substitution(
    context: &mut Context,
    pending: &[local_functions::Deferred],
    captures: &[Vec<LocalDecl>],
    owner: &Reference,
    owner_captures: &[LocalDecl],
    heads: ClosureHeads<'_>,
    aliases: &[(FVarId, Expr)],
) -> Result<Substitution, NatDefinitionElabError> {
    let mut result = Substitution::default();
    result.locals.insert(
        owner.marker.clone(),
        apply(context, heads.owner, owner_captures)?,
    );
    for ((pending, captures), head) in pending.iter().zip(captures).zip(heads.helpers) {
        let value = apply(context, head.clone(), captures)?;
        result.locals.insert(
            pending
                .partial_marker
                .clone()
                .ok_or_else(|| failure(SourceInferenceError::Scope))?,
            value.clone(),
        );
        result.metavars.insert(
            pending.id.clone(),
            close(context, value, &pending.captures, true)?,
        );
    }
    // A sibling's source local is also opaque during elaboration. Its exact
    // checked placeholder supplies a peer reference at closure time, rather
    // than an accidental extra higher-order capture.
    for (id, value) in aliases {
        let value = result.expression(context, value)?;
        result.locals.insert(id.clone(), value);
    }
    Ok(result)
}

impl Context {
    pub(in crate::source) fn collect_partial_locals(&self) -> bool {
        self.partial.as_ref().is_some_and(|state| {
            state.kind == Kind::Partial
                && !state.ordinary
                && state.group.is_none()
                && state.reference.is_some()
        })
    }

    pub(in crate::source) fn register_partial_local(
        &mut self,
        name: &Name,
        marker: &FVarId,
    ) -> Result<(), NatDefinitionElabError> {
        self.tick()?;
        if self
            .txn
            .env
            .contains(&Name::str(name.clone(), "_unsafe_rec"))
        {
            return Err(refusal("fresh local partial names and companions"));
        }
        let state = self
            .partial
            .as_mut()
            .ok_or_else(|| failure(SourceInferenceError::Scope))?;
        // Name reservation has already distinguished one matrix row's
        // repeated source binding from a real duplicate declaration. Keep
        // every copy as an independent obligation until closed comparison.
        if state.locals.headers.len() >= local_functions::lifting::MAX_LIFTED_FUNCTIONS {
            return Err(failure(SourceInferenceError::ResourceLimit));
        }
        state.locals.headers.push((name.clone(), marker.clone()));
        Ok(())
    }

    pub(in crate::source) fn register_partial_local_alias(
        &mut self,
        id: &FVarId,
        value: &Expr,
    ) -> Result<(), NatDefinitionElabError> {
        if !self.collect_partial_locals() {
            return Ok(());
        }
        self.tick()?;
        self.partial
            .as_mut()
            .expect("partial body")
            .locals
            .aliases
            .push((id.clone(), value.clone()));
        Ok(())
    }

    pub(in crate::source) fn has_partial_local_headers(&self) -> bool {
        self.partial
            .as_ref()
            .is_some_and(|state| !state.locals.headers.is_empty())
    }

    pub(in crate::source) fn has_partial_local_closures(&self) -> bool {
        self.partial
            .as_ref()
            .is_some_and(|state| !state.locals.definitions.is_empty())
    }

    pub(in crate::source) fn partial_local_roots(&self) -> impl Iterator<Item = Expr> + '_ {
        self.partial.iter().flat_map(|state| {
            state
                .locals
                .closures
                .iter()
                .chain(state.locals.owner.iter())
                .flat_map(|closed| [closed.term.type_.clone(), closed.term.value.clone()])
        })
    }

    pub(in crate::source) fn complete_partial_local_functions(
        &mut self,
        term: &mut Typed,
        parameters: &[LocalDecl],
    ) -> Result<(), NatDefinitionElabError> {
        if !self.has_partial_local_headers() {
            return Ok(());
        }
        let state = self
            .partial
            .as_ref()
            .ok_or_else(|| failure(SourceInferenceError::Scope))?
            .clone();
        let owner = state
            .reference
            .as_ref()
            .ok_or_else(|| failure(SourceInferenceError::Scope))?;
        let mut pending = std::mem::take(&mut self.deferred_local_functions);
        if pending.iter().any(|local| local.partial_marker.is_none())
            || pending.len() != state.locals.headers.len()
        {
            return Err(failure(SourceInferenceError::Scope));
        }
        pending.sort_by_key(|local| {
            state
                .locals
                .headers
                .iter()
                .position(|(_, marker)| Some(marker) == local.partial_marker.as_ref())
        });
        let mut excluded: HashSet<_> = state
            .locals
            .headers
            .iter()
            .map(|(_, marker)| marker.clone())
            .collect();
        excluded.insert(owner.marker.clone());
        excluded.extend(state.locals.aliases.iter().map(|(id, _)| id.clone()));
        let heads: Vec<_> = pending
            .iter()
            .map(|local| Expr::fvar(local.partial_marker.clone().expect("partial local")))
            .collect();
        let mut captures = vec![Vec::new(); pending.len()];
        let mut owner_captures = Vec::new();
        loop {
            self.tick()?;
            let substitution = substitution(
                self,
                &pending,
                &captures,
                owner,
                &owner_captures,
                ClosureHeads {
                    helpers: &heads,
                    owner: Expr::fvar(owner.marker.clone()),
                },
                &state.locals.aliases,
            )?;
            let mut next = Vec::new();
            for local in &pending {
                let value = substitution.expression(self, &local.value.value)?;
                let type_ = substitution.expression(self, &local.value.type_)?;
                let mut reads = self.elimination_reads(&type_)?;
                if reads.iter().any(|id| excluded.contains(id)) {
                    return Err(refusal(
                        "a local partial signature independent of recursive functions",
                    ));
                }
                reads.extend(self.elimination_reads(&value)?);
                let mut selected = Vec::new();
                for declaration in local.lift_context.decls().iter().rev() {
                    self.tick()?;
                    if !reads.contains(&declaration.id) || excluded.contains(&declaration.id) {
                        continue;
                    }
                    let mut declaration = declaration.clone();
                    if let Some(name) = local.capture_names.get(&declaration.id) {
                        declaration.user_name = name.clone();
                    }
                    declaration.type_ = substitution.expression(self, &declaration.type_)?;
                    let dependencies = self.elimination_reads(&declaration.type_)?;
                    if dependencies.iter().any(|id| excluded.contains(id)) {
                        return Err(refusal(
                            "lexical capture types independent of recursive functions",
                        ));
                    }
                    reads.extend(dependencies);
                    selected.push(declaration);
                }
                if reads.iter().any(|id| {
                    !excluded.contains(id) && !selected.iter().any(|local| &local.id == id)
                }) {
                    return Err(refusal("a partial local closed over its lexical context"));
                }
                selected.reverse();
                next.push(selected);
            }
            let mut roots: Vec<_> = parameters.iter().map(|local| local.type_.clone()).collect();
            roots.push(substitution.expression(self, &term.type_)?);
            roots.push(substitution.expression(self, &term.value)?);
            let next_owner = self.section_parameters(&roots, false)?;
            let stable = next
                .iter()
                .zip(&captures)
                .all(|(new, old)| same_captures(new, old))
                && same_captures(&next_owner, &owner_captures);
            captures = next;
            owner_captures = next_owner;
            if stable {
                break;
            }
        }

        let mut closures = Vec::new();
        for (local, captures) in pending.iter().zip(&captures) {
            let type_ = self.instantiate(&local.value.type_)?;
            let type_ = close(self, type_, captures, false)?;
            if type_.has_fvar() || type_.has_loose_bvars() {
                return Err(refusal("a closed local partial signature"));
            }
            let id = self.partial_closure_metavar(type_.clone())?;
            closures.push(Closure {
                name: local
                    .lift_name
                    .clone()
                    .ok_or_else(|| failure(SourceInferenceError::Scope))?,
                id,
                term: Typed {
                    type_,
                    value: local.value.value.clone(),
                },
                captures: captures.clone(),
            });
        }
        let owner_type = self.instantiate(&owner.term.type_)?;
        let owner_type = close(self, owner_type, &owner_captures, false)?;
        if owner_type.has_fvar() || owner_type.has_loose_bvars() {
            return Err(refusal("a closed owner partial signature"));
        }
        let owner_id = self.partial_closure_metavar(owner_type.clone())?;
        let heads: Vec<_> = closures
            .iter()
            .map(|closed| Expr::mvar(closed.id.clone()))
            .collect();
        let substitution = substitution(
            self,
            &pending,
            &captures,
            owner,
            &owner_captures,
            ClosureHeads {
                helpers: &heads,
                owner: Expr::mvar(owner_id.clone()),
            },
            &state.locals.aliases,
        )?;
        for (closed, pending) in closures.iter_mut().zip(&pending) {
            let value = substitution.expression(self, &pending.value.value)?;
            closed.term.value = close(self, value, &closed.captures, true)?;
        }
        term.value = substitution.expression(self, &term.value)?;
        term.type_ = substitution.expression(self, &term.type_)?;
        for pending in &pending {
            let value = substitution
                .metavars
                .get(&pending.id)
                .ok_or_else(|| failure(SourceInferenceError::Scope))?
                .clone();
            self.txn
                .mvars
                .assign(
                    pending.id.clone(),
                    value,
                    AssignmentJustification::UserGiven,
                )
                .map_err(|_| failure(SourceInferenceError::Scope))?;
        }
        let locals = &mut self.partial.as_mut().expect("partial body").locals;
        locals.closures = closures;
        locals.owner = Some(Closure {
            name: owner.name.clone(),
            id: owner_id,
            term: Typed {
                type_: owner_type,
                value: term.value.clone(),
            },
            captures: owner_captures,
        });
        Ok(())
    }

    fn partial_closure_metavar(&mut self, type_: Expr) -> Result<MVarId, NatDefinitionElabError> {
        let name = self.fresh_name()?;
        let id = MVarId(name.clone());
        self.txn.mvars.declare(
            id.clone(),
            name,
            type_,
            LocalContext::new(),
            MetavarKind::SyntheticOpaque,
            0,
            None,
        );
        Ok(id)
    }

    pub(in crate::source) fn close_partial_local_references(
        &mut self,
        term: &mut Typed,
        parameters: &[LocalDecl],
        captures: &[LocalDecl],
    ) -> Result<(), NatDefinitionElabError> {
        let Some(mut locals) = self.partial.as_ref().map(|state| state.locals.clone()) else {
            return Ok(());
        };
        let Some(owner) = &mut locals.owner else {
            return Ok(());
        };
        if !same_captures(captures, &owner.captures) {
            return Err(failure(SourceInferenceError::Scope));
        }
        owner.term.value = close(self, term.value.clone(), parameters, true)?;
        let mut all: Vec<_> = locals
            .closures
            .iter()
            .chain(locals.owner.iter())
            .cloned()
            .collect();
        let explicit = self.explicit_levels;
        self.explicit_levels = 0;
        let result =
            (|| {
                let mut levels = Vec::new();
                let mut dependencies = Vec::new();
                for closed in &mut all {
                    closed.term.value = self.instantiate(&closed.term.value)?;
                    closed.term.type_ = self.instantiate(&closed.term.type_)?;
                    levels.push(self.declaration_levels(&[
                        closed.term.type_.clone(),
                        closed.term.value.clone(),
                    ])?);
                    dependencies.push(self.txn.mvars.collect_mvars(&closed.term.value));
                }
                loop {
                    let mut next = levels.clone();
                    for (index, dependencies) in dependencies.iter().enumerate() {
                        for (peer, target) in all.iter().enumerate() {
                            self.tick()?;
                            if dependencies.contains(&target.id) {
                                for level in &levels[peer] {
                                    if !next[index].contains(level) {
                                        next[index].push(level.clone());
                                    }
                                }
                            }
                        }
                    }
                    if next == levels {
                        break;
                    }
                    levels = next;
                }
                for (index, closed) in all.iter().enumerate() {
                    let roots: Vec<_> = levels[index]
                        .iter()
                        .map(|name| Expr::sort(Level::param(name.clone())))
                        .collect();
                    // Explicit owner universes must be used, including by a helper
                    // its surviving body calls. Helpers have no written universe list.
                    self.explicit_levels = if index + 1 == all.len() { explicit } else { 0 };
                    levels[index] = self.declaration_levels(&roots)?;
                    let value = Expr::const_(
                        Name::str(closed.name.clone(), "_unsafe_rec"),
                        levels[index].iter().cloned().map(Level::param).collect(),
                    );
                    self.txn
                        .mvars
                        .assign(closed.id.clone(), value, AssignmentJustification::UserGiven)
                        .map_err(|_| failure(SourceInferenceError::Scope))?;
                }
                Ok::<_, NatDefinitionElabError>(levels)
            })();
        self.explicit_levels = explicit;
        let levels = result?;
        let mut definitions = Vec::new();
        let mut failed_codegen = Vec::new();
        for (closed, levels) in all[..all.len() - 1].iter().zip(&levels) {
            let term = self.finish(closed.term.clone())?;
            if term.value.has_fvar()
                || term.type_.has_fvar()
                || term.value.has_loose_bvars()
                || term.type_.has_loose_bvars()
            {
                return Err(failure(SourceInferenceError::Scope));
            }
            failed_codegen.push(self.check_definition_codegen(&term)?);
            let name = Name::str(closed.name.clone(), "_unsafe_rec");
            definitions.push(DefinitionVal {
                base: ConstantVal {
                    name: name.clone(),
                    level_params: levels.clone(),
                    type_: term.type_,
                },
                value: term.value,
                hints: ReducibilityHints::Opaque,
                safety: DefinitionSafety::Partial,
                all: vec![name],
            });
        }
        term.value = self.instantiate(&term.value)?;
        term.type_ = self.instantiate(&term.type_)?;
        let locals = &mut self.partial.as_mut().expect("partial body").locals;
        locals.definitions = definitions;
        locals.failed_codegen = failed_codegen;
        Ok(())
    }
}

fn same_captures(left: &[LocalDecl], right: &[LocalDecl]) -> bool {
    left.len() == right.len()
        && left
            .iter()
            .zip(right)
            .all(|(left, right)| left.id == right.id)
}

pub(super) fn finish(
    mut context: Context,
    candidate: Declaration,
    environment: &Environment,
    kernel: Budget,
    scope: &SourceScope,
) -> Result<ElaboratedPartial, NatDefinitionElabError> {
    let state = context
        .partial
        .as_ref()
        .ok_or_else(|| failure(SourceInferenceError::Scope))?;
    let owner = state
        .reference
        .as_ref()
        .ok_or_else(|| failure(SourceInferenceError::Scope))?
        .name
        .clone();
    let Declaration::Mutual(owner_body) = candidate else {
        return Err(failure(SourceInferenceError::Scope));
    };
    let [owner_body] = owner_body.as_slice() else {
        return Err(failure(SourceInferenceError::Scope));
    };
    let local_names: Vec<_> = state
        .locals
        .closures
        .iter()
        .map(|closed| closed.name.clone())
        .collect();
    let local_bodies = state.locals.definitions.clone();
    let local_failed = state.locals.failed_codegen.clone();
    if local_names.len() != local_bodies.len() || local_names.len() != local_failed.len() {
        return Err(failure(SourceInferenceError::Scope));
    }
    let mut names = Vec::new();
    let mut bodies: Vec<DefinitionVal> = Vec::new();
    let mut failed = Vec::new();
    for ((name, body), failure) in local_names.into_iter().zip(local_bodies).zip(local_failed) {
        context.tick()?;
        if let Some(index) = names.iter().position(|existing| existing == &name) {
            let previous = &bodies[index];
            if previous.base.level_params != body.base.level_params
                || !copies::equivalent(&mut context, &previous.base.type_, &body.base.type_)?
                || !copies::equivalent(&mut context, &previous.value, &body.value)?
            {
                return Err(refusal(
                    "identical closed partial helpers for repeated matrix source bindings",
                ));
            }
            failed[index] |= failure;
        } else {
            names.push(name);
            bodies.push(body);
            failed.push(failure);
        }
    }
    names.push(owner.clone());
    let mut reserved = HashSet::new();
    for name in &names {
        for name in [name.clone(), Name::str(name.clone(), "_unsafe_rec")] {
            if environment.contains(&name) || !reserved.insert(name) {
                return Err(refusal("fresh distinct partial closures and companions"));
            }
        }
    }
    bodies.push(owner_body.clone());
    failed.push(context.noncomputable_definition);
    let scopes = vec![scope.clone(); names.len()];
    let mut result = group::finish_components(
        context,
        group::Components {
            names,
            bodies,
            failed_codegen: failed,
            kind: Kind::Partial,
            scopes,
        },
        environment,
        kernel,
        scope,
    )?;
    result.owner = Some(owner);
    Ok(result)
}
