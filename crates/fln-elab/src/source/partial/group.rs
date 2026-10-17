//! Mutual partial and unsafe predefinitions. Headers are candidates, never installed as
//! axioms; every recursive occurrence is a typed private local until closure.
//! The pin partitions dependencies into SCCs before choosing partial/nonrec.
use super::*;
use std::collections::{BTreeSet, HashMap, HashSet};

#[derive(Clone, Default)]
pub(in crate::source) struct Group {
    pub names: Vec<Name>,
    pub header_only: bool,
    headers: Vec<ConstantVal>,
    calls: Vec<(FVarId, Expr)>,
    /// The exact identities closed by the current declaration, never guessed
    /// from binder names (which may be shadowed by ordinary parameters).
    pub captures: Vec<LocalDecl>,
}

fn refusal(expected: &'static str) -> NatDefinitionElabError {
    NatDefinitionElabError::UnexpectedSyntax { expected }
}

fn validate_group_member(syntax: &Syntax, kind: Kind) -> Result<(), NatDefinitionElabError> {
    if kind == Kind::Partial {
        return validate(syntax);
    }
    let declaration = expect_node(
        syntax,
        &parser_kind(&["Command", "declaration"]),
        2,
        "mutual unsafe declaration",
    )?;
    expect_node(
        &declaration[1],
        &parser_kind(&["Command", "definition"]),
        5,
        "mutual unsafe def",
    )?;
    let modifiers = expect_node(
        &declaration[0],
        &parser_kind(&["Command", "declModifiers"]),
        7,
        "declaration modifiers",
    )?;
    validate_unsafe_modifier(&modifiers[5])?;
    // The whole group must have the same safety. Unsupported attributes and
    // compute modifiers cannot be dropped by taking the group admission door.
    for index in [1, PROTECTED_SLOT, NONCOMPUTABLE_SLOT, 6] {
        expect_empty_null(&modifiers[index], "unattributed unsafe def without partial")?;
    }
    Ok(())
}

/// Return a complete, untrusted group in dependency/admission order. No prefix
/// is observable unless the caller's ordinary two-checker batch succeeds.
pub fn elaborate_group(
    members: &[Syntax],
    environment: &Environment,
    kernel: Budget,
    scope: &SourceScope,
) -> Result<ElaboratedPartial, NatDefinitionElabError> {
    if members.is_empty() || members.len() > 8 {
        return Err(refusal("one to eight mutual partial or unsafe definitions"));
    }
    let kind = if is_unsafe_definition(&members[0]) {
        Kind::Unsafe
    } else {
        Kind::Partial
    };
    let mut meter = Context::scoped(environment, kernel, scope);
    // Section locals have one meaning throughout the group. Their universes
    // cannot be independently instantiated at a peer occurrence. Declaration-
    // local polymorphism remains fresh at each occurrence as before.
    let section_types: Vec<_> = scope
        .variables
        .locals()
        .decls()
        .iter()
        .map(|local| local.type_.clone())
        .collect();
    let fixed_levels: BTreeSet<_> = meter
        .declaration_levels(&section_types)?
        .into_iter()
        .collect();
    let mut names = Vec::new();
    let mut scopes = Vec::new();
    let mut reserved = HashSet::new();
    for member in members {
        meter.tick()?;
        validate_group_member(member, kind)?;
        let effective = scope.for_declaration(member)?;
        let declaration = expect_node(
            member,
            &parser_kind(&["Command", "declaration"]),
            2,
            "declaration",
        )?;
        let definition = expect_node(
            &declaration[1],
            &parser_kind(&["Command", "definition"]),
            5,
            "partial def",
        )?;
        let id = expect_node(
            &definition[1],
            &parser_kind(&["Command", "declId"]),
            2,
            "declaration id",
        )?;
        let Syntax::Ident { val, .. } = &id[0] else {
            return Err(refusal("a named mutual partial definition"));
        };
        let name = effective
            .declaration_name(val)
            .map_err(|_| failure(SourceInferenceError::Scope))?;
        let mut candidates = vec![name.clone()];
        if kind == Kind::Partial {
            candidates.push(Name::str(name.clone(), "_unsafe_rec"));
        }
        for reserved_name in candidates {
            if environment.contains(&reserved_name) || !reserved.insert(reserved_name) {
                return Err(refusal("fresh distinct mutual names and companions"));
            }
        }
        names.push(name);
        scopes.push(effective);
    }
    let prototype = Group {
        names: names.clone(),
        header_only: true,
        ..Group::default()
    };
    let mut headers = Vec::new();
    for (member, scope) in members.iter().zip(&scopes) {
        let mut context = Context::scoped(environment, kernel, scope);
        context.txn.budget = meter.txn.budget.clone();
        context.partial = Some(State {
            kind,
            group: Some(prototype.clone()),
            ..State::default()
        });
        // This header-only return is just data. It NEVER enters an Environment.
        let Declaration::Axiom(mut header) = definition_in_context(member, &mut context)? else {
            return Err(refusal("a complete mutual partial header"));
        };
        // Reopen precisely the section prefix. Peer references see the written
        // parameters, not the later implicit closure-conversion arguments.
        reopen_captures(&mut context, &mut header.base.type_, None)?;
        header
            .base
            .level_params
            .retain(|level| !fixed_levels.contains(level));
        meter.txn.budget = context.txn.budget;
        headers.push(header.base);
    }
    let group = Group {
        names: names.clone(),
        headers: headers.clone(),
        ..Group::default()
    };
    let mut bodies = Vec::new();
    let mut universes = Vec::new();
    let mut failed_codegen = Vec::new();
    for (member, scope) in members.iter().zip(&scopes) {
        let mut context = Context::scoped(environment, kernel, scope);
        context.txn.budget = meter.txn.budget.clone();
        context.partial = Some(State {
            kind,
            group: Some(group.clone()),
            ..State::default()
        });
        let Declaration::Mutual(mut body) = definition_in_context(member, &mut context)? else {
            return Err(refusal("a closed mutual partial body"));
        };
        if body.len() != 1 {
            return Err(refusal("one body per mutual partial definition"));
        }
        let mut body = body.pop().expect("one body");
        reopen_captures(&mut context, &mut body.base.type_, Some(&mut body.value))?;
        universes.push((context.level_params.clone(), context.explicit_levels));
        meter.txn.budget = context.txn.budget;
        failed_codegen.push(context.noncomputable_definition);
        bodies.push(body);
    }

    if !scope.variables.is_empty() {
        close_shared_captures(&mut meter, &headers, &mut bodies, &universes, &fixed_levels)?;
    }

    let executable: Vec<_> = names
        .iter()
        .map(|name| {
            if kind == Kind::Unsafe {
                name.clone()
            } else {
                Name::str(name.clone(), "_unsafe_rec")
            }
        })
        .collect();
    let mut edges = vec![vec![false; names.len()]; names.len()];
    for (index, body) in bodies.iter().enumerate() {
        let mut seen = HashSet::new();
        let mut todo = vec![&body.value];
        while let Some(expr) = todo.pop() {
            meter.tick()?;
            if !seen.insert(expr.allocation_identity()) {
                continue;
            }
            if let ExprNode::Const { name, .. } = expr.node()
                && let Some(peer) = executable.iter().position(|candidate| candidate == name)
            {
                edges[index][peer] = true;
            }
            todo.extend(children(expr));
        }
    }
    let mut reachable = edges.clone();
    for via in 0..names.len() {
        for from in 0..names.len() {
            for to in 0..names.len() {
                meter.tick()?;
                reachable[from][to] |= reachable[from][via] && reachable[via][to];
            }
        }
    }
    let mut remaining = vec![true; names.len()];
    let mut declarations = Vec::new();
    let mut noncomputable = BTreeSet::new();
    while remaining.iter().any(|pending| *pending) {
        // A sink SCC has no unadmitted dependency outside itself. Source order
        // breaks ties, so hash iteration never decides admission order.
        let mut selected = None;
        for root in 0..names.len() {
            meter.tick()?;
            if !remaining[root] {
                continue;
            }
            let component: Vec<_> = (0..names.len())
                .filter(|&other| {
                    remaining[other]
                        && (other == root || reachable[root][other] && reachable[other][root])
                })
                .collect();
            if component.iter().all(|&from| {
                (0..names.len())
                    .all(|to| !remaining[to] || !edges[from][to] || component.contains(&to))
            }) {
                selected = Some(component);
                break;
            }
        }
        let component = selected.ok_or_else(|| refusal("a finite partial dependency graph"))?;
        let recursive = component.len() > 1 || edges[component[0]][component[0]];
        let logical_group: Vec<_> = component.iter().map(|&i| names[i].clone()).collect();
        let implementation_group: Vec<_> =
            component.iter().map(|&i| executable[i].clone()).collect();
        let mut implementations = Vec::new();
        for &index in &component {
            meter.tick()?;
            let mut definition = bodies[index].clone();
            definition.value = map(&mut meter, &definition.value, &|_, expr| {
                let ExprNode::Const { name, levels } = expr.node() else {
                    return Ok(None);
                };
                let Some(target) = executable.iter().position(|candidate| candidate == name) else {
                    return Ok(None);
                };
                Ok((!recursive || !component.contains(&target))
                    .then(|| Expr::const_(names[target].clone(), levels.clone())))
            })?;
            if recursive && kind == Kind::Unsafe {
                // Unsafe SCCs keep their real names and checked executable
                // bodies. There is no safe logical witness to manufacture.
                definition.safety = DefinitionSafety::Unsafe;
                definition.hints = ReducibilityHints::Opaque;
                definition.all = implementation_group.clone();
                if failed_codegen[index] {
                    noncomputable.insert(definition.base.name.clone());
                }
                implementations.push(definition);
            } else if recursive {
                if !matches!(
                    meter.whnf(&definition.base.type_)?.node(),
                    ExprNode::ForallE { .. }
                ) {
                    return Err(refusal("a function type for recursive partial def"));
                }
                let mut inhabitant = Context::scoped(environment, kernel, &scopes[index]);
                inhabitant.txn.budget = meter.txn.budget.clone();
                inhabitant.level_params = definition.base.level_params.clone();
                let value = inhabitant.partial_inhabitant(&definition.base.type_)?;
                meter.txn.budget = inhabitant.txn.budget;
                declarations.push(Declaration::Opaque(fln_env::constants::OpaqueVal {
                    base: ConstantVal {
                        name: names[index].clone(),
                        ..definition.base.clone()
                    },
                    value,
                    is_unsafe: false,
                    all: logical_group.clone(),
                }));
                definition.all = implementation_group.clone();
                if failed_codegen[index] {
                    noncomputable.insert(definition.base.name.clone());
                }
                implementations.push(definition);
            } else {
                definition.base.name = names[index].clone();
                definition.all = logical_group.clone();
                definition.safety = if kind == Kind::Unsafe {
                    DefinitionSafety::Unsafe
                } else {
                    DefinitionSafety::Safe
                };
                definition.hints = ReducibilityHints::Regular(1);
                if failed_codegen[index] {
                    noncomputable.insert(definition.base.name.clone());
                }
                declarations.push(Declaration::Defn(definition));
            }
            remaining[index] = false;
        }
        if recursive {
            declarations.push(Declaration::Mutual(implementations));
        }
    }
    Ok(ElaboratedPartial {
        declarations,
        noncomputable,
        scope: scope.clone(),
        budget: meter.txn.budget,
        kernel,
    })
}

impl Context {
    pub(in crate::source) fn partial_group_reference(
        &mut self,
        name: &Name,
    ) -> Result<Option<Typed>, NatDefinitionElabError> {
        let Some(header) = self
            .partial
            .as_ref()
            .and_then(|state| state.group.as_ref())
            .and_then(|group| group.headers.iter().find(|header| &header.name == name))
            .cloned()
        else {
            return Ok(None);
        };
        let mut levels = Vec::new();
        for _ in &header.level_params {
            levels.push(self.level()?);
        }
        let type_ = self.instantiate_params(&header.type_, &header.level_params, &levels)?;
        let marker = FVarId(self.fresh_name()?);
        self.txn.lctx.add_param(
            marker.clone(),
            marker.0.clone(),
            type_.clone(),
            BinderInfo::Default,
        );
        let executable = if self
            .partial
            .as_ref()
            .is_some_and(|state| state.kind == Kind::Unsafe)
        {
            name.clone()
        } else {
            Name::str(name.clone(), "_unsafe_rec")
        };
        self.partial
            .as_mut()
            .and_then(|state| state.group.as_mut())
            .expect("group exists")
            .calls
            .push((marker.clone(), Expr::const_(executable, levels)));
        Ok(Some(Typed {
            value: Expr::fvar(marker),
            type_,
        }))
    }

    pub(in crate::source) fn close_partial_group_references(
        &mut self,
        term: &mut Typed,
    ) -> Result<(), NatDefinitionElabError> {
        let Some(group) = self.partial.as_ref().and_then(|state| state.group.as_ref()) else {
            return Ok(());
        };
        let calls: HashMap<_, _> = group.calls.iter().cloned().collect();
        // The signature must not depend on a recursive function. Closing only
        // values lets the existing free-variable guard reject such a signature.
        term.value = map(self, &term.value, &|_, expr| {
            Ok(match expr.node() {
                ExprNode::FVar { id } => calls.get(id).cloned(),
                _ => None,
            })
        })?;
        Ok(())
    }
}

/// Individual declaration elaboration already checks and closes its selected
/// section variables. Reopen that exact prefix as private candidate data so
/// the group can compute a common, dependency-closed telescope afterwards.
fn reopen_captures(
    context: &mut Context,
    type_: &mut Expr,
    mut value: Option<&mut Expr>,
) -> Result<(), NatDefinitionElabError> {
    let captures = context
        .partial
        .as_ref()
        .and_then(|state| state.group.as_ref())
        .ok_or_else(|| failure(SourceInferenceError::Scope))?
        .captures
        .clone();
    for local in captures {
        context.tick()?;
        let ExprNode::ForallE {
            binder_type,
            body,
            binder_info,
            ..
        } = type_.node()
        else {
            return Err(failure(SourceInferenceError::Scope));
        };
        if binder_type != &local.type_ || binder_info != &local.binder_info {
            return Err(failure(SourceInferenceError::Scope));
        }
        *type_ = context.substitute(body, &Expr::fvar(local.id.clone()))?;
        if let Some(value) = &mut value {
            let ExprNode::Lam {
                binder_type,
                body,
                binder_info,
                ..
            } = value.node()
            else {
                return Err(failure(SourceInferenceError::Scope));
            };
            if binder_type != &local.type_ || binder_info != &local.binder_info {
                return Err(failure(SourceInferenceError::Scope));
            }
            **value = context.substitute(body, &Expr::fvar(local.id.clone()))?;
        }
    }
    Ok(())
}

/// The pin's MutualClosure closes every main definition over the same used
/// section variables *before* dependency partitioning. A peer-only dependency
/// is therefore captured by its callers without exposing extra source args.
fn close_shared_captures(
    context: &mut Context,
    headers: &[ConstantVal],
    bodies: &mut [DefinitionVal],
    universes: &[(Vec<Name>, usize)],
    fixed_levels: &BTreeSet<Name>,
) -> Result<(), NatDefinitionElabError> {
    let mut roots = Vec::new();
    for body in bodies.iter() {
        context.tick()?;
        roots.extend([body.base.type_.clone(), body.value.clone()]);
    }
    let captures = context.section_parameters(&roots, false)?;
    let capture_types: Vec<_> = captures.iter().map(|local| local.type_.clone()).collect();
    for (body, (levels, explicit)) in bodies.iter_mut().zip(universes) {
        context.tick()?;
        context.level_params = levels.clone();
        context.explicit_levels = *explicit;
        let mut roots = capture_types.clone();
        roots.extend([body.base.type_.clone(), body.value.clone()]);
        body.base.level_params = context.declaration_levels(&roots)?;
    }
    let signatures: Vec<_> = bodies.iter().map(|body| body.base.clone()).collect();
    for body in bodies {
        body.value = map(context, &body.value, &|context, expr| {
            let ExprNode::Const { name, levels } = expr.node() else {
                return Ok(None);
            };
            let Some(target) = signatures.iter().position(|base| &base.name == name) else {
                return Ok(None);
            };
            let header = &headers[target];
            if levels.len() != header.level_params.len() {
                return Err(failure(SourceInferenceError::Scope));
            }
            let mut actual = Vec::new();
            for parameter in &signatures[target].level_params {
                context.tick()?;
                let level = if fixed_levels.contains(parameter) {
                    Level::param(parameter.clone())
                } else {
                    let index = header
                        .level_params
                        .iter()
                        .position(|name| name == parameter)
                        .ok_or_else(|| refusal("peer universes determined by the mutual header"))?;
                    levels[index].clone()
                };
                actual.push(level);
            }
            let mut replacement = Expr::const_(name.clone(), actual);
            for local in &captures {
                context.tick()?;
                replacement = Expr::app(replacement, Expr::fvar(local.id.clone()));
            }
            Ok(Some(replacement))
        })?;
        for local in captures.iter().rev() {
            context.tick()?;
            let abstract_ = |expr: &Expr| {
                expr.abstract_fvar(&local.id, 0)
                    .map_err(|_| failure(SourceInferenceError::Scope))
            };
            body.base.type_ = Expr::forall_e(
                local.user_name.clone(),
                local.type_.clone(),
                abstract_(&body.base.type_)?,
                local.binder_info,
            );
            body.value = Expr::lam(
                local.user_name.clone(),
                local.type_.clone(),
                abstract_(&body.value)?,
                local.binder_info,
            );
        }
        if body.base.type_.has_fvar()
            || body.value.has_fvar()
            || body.base.type_.has_loose_bvars()
            || body.value.has_loose_bvars()
        {
            return Err(failure(SourceInferenceError::Scope));
        }
    }
    Ok(())
}

fn children(expr: &Expr) -> Vec<&Expr> {
    match expr.node() {
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
        _ => Vec::new(),
    }
}

/// Iterative, DAG-preserving leaf replacement. The original root pins every
/// address key throughout the walk; all visits, including memo hits, cost work.
fn map(
    context: &mut Context,
    root: &Expr,
    replace: &impl Fn(&mut Context, &Expr) -> Result<Option<Expr>, NatDefinitionElabError>,
) -> Result<Expr, NatDefinitionElabError> {
    let mut pending = vec![(root, false)];
    let mut done = HashMap::new();
    while let Some((expr, build)) = pending.pop() {
        context.tick()?;
        let key = expr.allocation_identity();
        if done.contains_key(&key) {
            continue;
        }
        if let Some(value) = replace(context, expr)? {
            done.insert(key, value);
            continue;
        }
        if !build {
            pending.push((expr, true));
            pending.extend(children(expr).into_iter().map(|child| (child, false)));
            continue;
        }
        let child = |expr: &Expr| {
            done.get(&expr.allocation_identity())
                .expect("child precedes parent")
                .clone()
        };
        let value = match expr.node() {
            ExprNode::App { f, a } => Expr::app(child(f), child(a)),
            ExprNode::Lam {
                binder_name,
                binder_type,
                body,
                binder_info,
            } => Expr::lam(
                binder_name.clone(),
                child(binder_type),
                child(body),
                *binder_info,
            ),
            ExprNode::ForallE {
                binder_name,
                binder_type,
                body,
                binder_info,
            } => Expr::forall_e(
                binder_name.clone(),
                child(binder_type),
                child(body),
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
                child(type_),
                child(value),
                child(body),
                *non_dep,
            ),
            ExprNode::MData { data, expr } => Expr::mdata(data.clone(), child(expr)),
            ExprNode::Proj {
                struct_name,
                idx,
                expr,
            } => Expr::proj(struct_name.clone(), *idx, child(expr)),
            _ => expr.clone(),
        };
        done.insert(key, value);
    }
    Ok(done
        .remove(&root.allocation_identity())
        .expect("root visited"))
}
