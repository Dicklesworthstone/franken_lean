//! Ordinary mutual predefinitions, following MutualDef's header/body boundary
//! and dependency partition. Headers are private candidate data, never
//! temporary environment axioms. Same-family structural components share one
//! course-of-values recursor; explicit measures and inferred SizeOf measures
//! share one well-founded fixpoint. Unsupported components are never downgraded
//! to partial logical definitions.
use super::*;
use recursion::MemberHint;
use std::collections::BTreeMap;

/// One column of GuessLex's mutual call matrix. Only completed classifications
/// are cached; candidate contexts and their proof assignments are discarded.
struct MutualMeasureCandidate {
    measures: Vec<Expr>,
    after_complex: bool,
    plan: Option<std::sync::Arc<recursion::WellFoundedPlan>>,
    measure_sum: Option<Expr>,
    calls: Vec<BTreeMap<usize, recursion::MutualMeasureRelation>>,
}

impl MutualMeasureCandidate {
    fn new(measures: Vec<Expr>, after_complex: bool) -> Self {
        let calls = vec![BTreeMap::new(); measures.len()];
        Self {
            measures,
            after_complex,
            plan: None,
            measure_sum: None,
            calls,
        }
    }
}

/// Create a fresh scoped context on the same immutable `environment`/`scope`,
/// inheriting only immutable environment-keyed read caches, the shared
/// heartbeat budget, and `nat_sub_model_cache` (never locals, metavariables,
/// or proof assignments). Avoids rebuilding `InstanceIndex` per child pass.
fn fork_scoped_with_caches(
    meter: &Context,
    environment: &Environment,
    kernel: Budget,
    scope: &SourceScope,
) -> Result<Context, NatDefinitionElabError> {
    let mut child = Context::scoped(environment, kernel, scope)?;
    child.txn.budget = meter.txn.budget.clone();
    child.txn.nat_sub_model_cache = meter.txn.nat_sub_model_cache.clone();
    child.registry_cache = meter.registry_cache.clone();
    child.txn.registry_cache = meter.registry_cache.clone();
    child.alias_cache = meter.alias_cache.clone();
    child.protected_cache = meter.protected_cache.clone();
    child.auxiliary_cache = meter.auxiliary_cache.clone();
    child.deprecation_cache = meter.deprecation_cache.clone();
    child.simp_key_cache = meter.simp_key_cache.clone();
    Ok(child)
}

fn absorb_child_caches(meter: &mut Context, child: &Context) {
    meter.txn.budget = child.txn.budget.clone();
    meter.txn.nat_sub_model_cache = child.txn.nat_sub_model_cache.clone();
    meter.registry_cache = child.registry_cache.clone();
    meter.txn.registry_cache = child.registry_cache.clone();
    meter.alias_cache = child.alias_cache.clone();
    meter.protected_cache = child.protected_cache.clone();
    meter.auxiliary_cache = child.auxiliary_cache.clone();
    meter.deprecation_cache = child.deprecation_cache.clone();
    meter.simp_key_cache = child.simp_key_cache.clone();
}

pub fn is_ordinary_group_member(syntax: &Syntax) -> bool {
    let Some(declaration) = syntax_args(syntax, &parser_kind(&["Command", "declaration"])) else {
        return false;
    };
    declaration
        .get(1)
        .and_then(Syntax::kind)
        .is_some_and(|kind| {
            ["definition", "abbrev", "theorem"]
                .iter()
                .any(|label| kind == &parser_kind(&["Command", label]))
        })
        && !is_partial(syntax)
        && !is_unsafe_definition(syntax)
}

fn member(syntax: &Syntax, computed: bool) -> Result<(&Syntax, bool), NatDefinitionElabError> {
    let declaration = expect_node(
        syntax,
        &parser_kind(&["Command", "declaration"]),
        2,
        "ordinary mutual declaration",
    )?;
    let modifiers = expect_node(
        &declaration[0],
        &parser_kind(&["Command", "declModifiers"]),
        7,
        "mutual declaration modifiers",
    )?;
    doc_comment_slot(&modifiers[0])?;
    if computed {
        // Only the computed-field source adapter enters here. It retains every
        // attribute for transactional registration and supplies one effective
        // visibility scope for the whole group.
        expect_empty_null(
            &modifiers[1],
            "externally retained computed-field attributes",
        )?;
        scope::visibility::modifier(&modifiers[2])?;
        protected_slot(&modifiers[PROTECTED_SLOT])?;
        if !noncomputable_slot(&modifiers[NONCOMPUTABLE_SLOT])? {
            return Err(refusal("explicitly noncomputable computed-field getter"));
        }
        for modifier in &modifiers[5..] {
            expect_empty_null(modifier, "safe computed-field getter without partial")?;
        }
    } else {
        // Visibility and attribute publication are effects, not permission to drop
        // syntax. Keep unsupported effects outside this atomic aperture.
        for modifier in &modifiers[1..] {
            expect_empty_null(
                modifier,
                "ordinary mutual declaration without attributes or modifiers",
            )?;
        }
    }
    let theorem = declaration[1].kind() == Some(&parser_kind(&["Command", "theorem"]));
    let abbrev = declaration[1].kind() == Some(&parser_kind(&["Command", "abbrev"]));
    let (label, arity) = if theorem {
        ("theorem", 4)
    } else if abbrev {
        ("abbrev", 4)
    } else {
        ("definition", 5)
    };
    let parts = expect_node(
        &declaration[1],
        &parser_kind(&["Command", label]),
        arity,
        "mutual def, abbrev, or theorem",
    )?;
    Ok((&parts[1], theorem))
}

/// Collect all signatures before any body. The existing group's direct-name
/// mode is used only to close typed locals into UNTRUSTED candidate terms.
/// Its temporary safety labels are never admitted: after rejecting cycles,
/// each candidate is submitted as Safe or Thm to the normal two-checker batch.
pub fn elaborate_ordinary_group(
    members: &[Syntax],
    environment: &Environment,
    kernel: Budget,
    scope: &SourceScope,
) -> Result<ElaboratedPartial, NatDefinitionElabError> {
    elaborate_with_meter(
        members,
        environment,
        kernel,
        scope,
        Context::scoped(environment, kernel, scope)?,
        false,
    )
}

/// Internal entry for a fully read computed-field block. Logical bodies use
/// the ordinary SCC/termination pipeline, but explicitly noncomputable fields
/// must not acquire executable `_unsafe_rec` companions before caching exists.
pub(in crate::source) fn elaborate_computed_group(
    members: &[Syntax],
    environment: &Environment,
    kernel: Budget,
    scope: &SourceScope,
) -> Result<ElaboratedPartial, NatDefinitionElabError> {
    elaborate_with_meter(
        members,
        environment,
        kernel,
        scope,
        Context::scoped(environment, kernel, scope)?,
        true,
    )
}

/// Public computed-field signatures are elaborated in their exported
/// predecessor before the private body group. A private definition cannot
/// supply an otherwise unavailable public type through body inference.
pub(in crate::source) fn elaborate_computed_headers(
    members: &[Syntax],
    environment: &Environment,
    kernel: Budget,
    scope: &SourceScope,
) -> Result<Vec<Declaration>, NatDefinitionElabError> {
    if members.is_empty() || members.len() > 8 {
        return Err(refusal("one to eight computed fields"));
    }
    let mut meter = Context::scoped(environment, kernel, scope)?;
    let mut names = Vec::new();
    for syntax in members {
        meter.tick()?;
        let (id, theorem) = member(syntax, true)?;
        if theorem {
            return Err(refusal("a computed-field definition"));
        }
        let id = expect_node(
            id,
            &parser_kind(&["Command", "declId"]),
            2,
            "computed-field name",
        )?;
        let Syntax::Ident { val, .. } = &id[0] else {
            return Err(refusal("a named computed field"));
        };
        let name = scope
            .declaration_name(val)
            .map_err(|error| failure(SourceInferenceError::NameScope(error)))?;
        if environment.contains(&name) || names.contains(&name) {
            return Err(refusal("fresh distinct computed-field names"));
        }
        names.push(name);
    }
    let group = Group {
        names,
        header_only: true,
        ..Group::default()
    };
    let mut headers = Vec::new();
    for syntax in members {
        let mut context = fork_scoped_with_caches(&meter, environment, kernel, scope)?;
        context.partial = Some(State {
            kind: Kind::Unsafe,
            group: Some(group.clone()),
            ..State::default()
        });
        let header = definition_in_context(syntax, &mut context)?;
        if !matches!(&header, Declaration::Axiom(header) if !header.is_unsafe) {
            return Err(refusal("a safe computed-field signature"));
        }
        absorb_child_caches(&mut meter, &context);
        headers.push(header);
    }
    Ok(headers)
}

fn elaborate_with_meter(
    members: &[Syntax],
    environment: &Environment,
    kernel: Budget,
    scope: &SourceScope,
    mut meter: Context,
    computed: bool,
) -> Result<ElaboratedPartial, NatDefinitionElabError> {
    if members.is_empty() || members.len() > 8 {
        return Err(refusal("one to eight ordinary mutual declarations"));
    }
    if scope.private_module.is_some() && !computed {
        return Err(refusal(
            "ordinary mutual group outside module visibility projection",
        ));
    }
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
    let mut reserved = HashSet::new();
    let mut proof_group = None;
    let mut level_names: Option<Vec<Name>> = None;
    for syntax in members {
        meter.tick()?;
        let (id, theorem) = member(syntax, computed)?;
        if proof_group.is_some_and(|previous| previous != theorem) {
            return Err(refusal("mutual group cannot mix theorems and definitions"));
        }
        proof_group = Some(theorem);
        let parts = expect_node(
            id,
            &parser_kind(&["Command", "declId"]),
            2,
            "mutual member name",
        )?;
        // MutualDef.check compares written universe lists, including names
        // and order, before independently elaborating any member's header.
        meter.declare_levels(&parts[1])?;
        let current = meter.level_params[..meter.explicit_levels].to_vec();
        if level_names
            .as_ref()
            .is_some_and(|previous| previous != &current)
        {
            return Err(refusal("ordinary mutual universe parameters mismatch"));
        }
        level_names = Some(current);
        let Syntax::Ident { val, .. } = &parts[0] else {
            return Err(refusal("named ordinary mutual declaration"));
        };
        let name = scope
            .declaration_name(val)
            .map_err(|_| failure(SourceInferenceError::Scope))?;
        if environment.contains(&name) || !reserved.insert(name.clone()) {
            return Err(refusal("fresh distinct ordinary mutual names"));
        }
        names.push(name);
    }
    let prototype = Group {
        names: names.clone(),
        header_only: true,
        ..Group::default()
    };
    let mut headers = Vec::new();
    for syntax in members {
        let mut context = fork_scoped_with_caches(&meter, environment, kernel, scope)?;
        context.partial = Some(State {
            kind: Kind::Unsafe,
            group: Some(prototype.clone()),
            ..State::default()
        });
        let Declaration::Axiom(mut header) = definition_in_context(syntax, &mut context)? else {
            return Err(refusal("explicit ordinary mutual header"));
        };
        reopen_captures(&mut context, &mut header.base.type_, None)?;
        header
            .base
            .level_params
            .retain(|level| !fixed_levels.contains(level));
        absorb_child_caches(&mut meter, &context);
        headers.push(header.base);
    }
    let mut group = Group {
        names: names.clone(),
        headers: headers.clone(),
        ..Group::default()
    };
    let mut bodies = Vec::new();
    let mut universes = Vec::new();
    let mut hints = Vec::new();
    let theorem = proof_group == Some(true);
    for syntax in members {
        let mut context = fork_scoped_with_caches(&meter, environment, kernel, scope)?;
        context.partial = Some(State {
            kind: Kind::Unsafe,
            group: Some(group.clone()),
            ordinary: true,
            ..State::default()
        });
        let mut definition = match definition_in_context(syntax, &mut context)? {
            Declaration::Mutual(mut definitions) if !theorem && definitions.len() == 1 => {
                definitions.pop().expect("one candidate")
            }
            Declaration::Thm(proof) if theorem => DefinitionVal {
                base: proof.base,
                value: proof.value,
                all: proof.all,
                hints: ReducibilityHints::Opaque,
                safety: DefinitionSafety::Safe,
            },
            _ => return Err(refusal("one ordinary body per mutual header")),
        };
        if context.noncomputable_definition {
            // Do not publish an untagged compile failure or use the partial
            // batch's propagation law for a safe theorem/definition group.
            return Err(refusal("computable ordinary mutual definition"));
        }
        reopen_captures(
            &mut context,
            &mut definition.base.type_,
            Some(&mut definition.value),
        )?;
        universes.push((context.level_params.clone(), context.explicit_levels));
        hints.push(context.finish_mutual_member_hint()?);
        absorb_child_caches(&mut meter, &context);
        bodies.push(definition);
    }
    if !scope.variables.is_empty() {
        group.shared = Some(close_shared_captures(
            &mut meter,
            &headers,
            &mut bodies,
            &universes,
            &fixed_levels,
        )?);
    }
    let mut edges = vec![vec![false; names.len()]; names.len()];
    for (from, body) in bodies.iter().enumerate() {
        let mut seen = HashSet::new();
        let mut pending = vec![&body.base.type_, &body.value];
        while let Some(expr) = pending.pop() {
            meter.tick()?;
            if !seen.insert(expr.allocation_identity()) {
                continue;
            }
            if let ExprNode::Const { name, .. } = expr.node()
                && let Some(to) = names.iter().position(|candidate| candidate == name)
            {
                edges[from][to] = true;
            }
            pending.extend(children(expr));
        }
    }
    // `partitionPreDefs` (Lean/Elab/PreDefinition/Main.lean): components of the
    // value-only call graph, members in the pin's Tarjan order. Admission keeps
    // this module's source-ordered dependency sort over the components.
    let mut successors = Vec::new();
    for body in &bodies {
        successors.push(meter.mutual_call_order(&body.value, &names)?);
    }
    let components = recursion::strongly_connected(&successors);
    let mut component_of = vec![0; names.len()];
    for (index, component) in components.iter().enumerate() {
        for &member in component {
            component_of[member] = index;
        }
    }
    let mut remaining = vec![true; names.len()];
    let mut declarations = Vec::new();
    let mut irreducible = BTreeSet::new();
    while remaining.iter().any(|pending| *pending) {
        let mut next = None;
        for (index, pending) in remaining.iter().enumerate() {
            meter.tick()?;
            let component = &components[component_of[index]];
            if *pending
                && component.iter().all(|&from| {
                    edges[from]
                        .iter()
                        .zip(&remaining)
                        .enumerate()
                        .all(|(to, (edge, live))| !edge || !live || component.contains(&to))
                })
            {
                next = Some(component_of[index]);
                break;
            }
        }
        let component = components[next.ok_or_else(|| {
            refusal("recursive ordinary mutual component requires termination elaboration")
        })?]
        .clone();
        if component.len() > 1 || edges[component[0]][component[0]] {
            if theorem {
                return Err(refusal(
                    "recursive ordinary mutual component requires termination elaboration",
                ));
            }
            let parts = Parts {
                group: &group,
                members,
                names: &names,
                bodies: &bodies,
                hints: &hints,
                headers: &headers,
            };
            let structural = component
                .iter()
                .all(|&index| matches!(hints[index], MemberHint::None | MemberHint::Structural));
            let compiled = if structural {
                match mutual_structural(
                    &mut meter,
                    (environment, kernel, scope),
                    &parts,
                    &component,
                ) {
                    Ok(compiled) => Some(compiled),
                    // An automatic attempt that cannot establish structural descent retains
                    // the existing well-founded boundary. Resource/type failures never select
                    // another interpretation, and an explicit structural hint never falls back.
                    Err(NatDefinitionElabError::Inference(SourceInferenceError::Recursion(
                        recursion::RecursionError::MutualStructuralUnsupported(_)
                        | recursion::RecursionError::NotDecreasing
                        | recursion::RecursionError::ChangedParameter
                        | recursion::RecursionError::PartialApplication,
                    ))) if component
                        .iter()
                        .all(|&index| matches!(hints[index], MemberHint::None)) =>
                    {
                        None
                    }
                    Err(problem) => return Err(problem),
                }
            } else {
                None
            };
            let is_structural = compiled.is_some();
            let (mutual, members_published, executable) = match compiled {
                Some(compiled) => compiled,
                None => mutual_well_founded(
                    &mut meter,
                    (environment, kernel, scope),
                    &parts,
                    &component,
                )?,
            };
            declarations.push(Declaration::Defn(mutual));
            let component_names: Vec<Name> = component
                .iter()
                .map(|&index| names[index].clone())
                .collect();
            let mut max_wrapper_height = 0u32;
            for definition in members_published {
                if !is_structural {
                    irreducible.insert(definition.base.name.clone());
                } else if let ReducibilityHints::Regular(h) = definition.hints {
                    max_wrapper_height = max_wrapper_height.max(h);
                }
                declarations.push(Declaration::Defn(definition));
            }
            if is_structural {
                for &index in &component {
                    let is_prop_type = meter
                        .known_type(&bodies[index].base.type_)
                        .ok()
                        .flatten()
                        .and_then(|sort| meter.whnf(&sort).ok())
                        .is_some_and(|sort| {
                            matches!(sort.node(), ExprNode::Sort { level } if level.is_always_zero())
                        });
                    if !is_prop_type
                        && let Some(sunfold) = recursion::mutual_smart_unfolding(
                            environment,
                            &bodies[index],
                            &component_names,
                            max_wrapper_height,
                        )
                    {
                        declarations.push(Declaration::Defn(sunfold));
                    }
                }
            }
            if !computed {
                declarations.push(Declaration::Mutual(executable));
            }
            for &index in &component {
                remaining[index] = false;
            }
            continue;
        }
        let index = component[0];
        let mut definition = bodies[index].clone();
        definition.safety = DefinitionSafety::Safe;
        definition.all = vec![names[index].clone()];
        declarations.push(if theorem {
            Declaration::Thm(fln_env::constants::TheoremVal {
                base: definition.base,
                value: definition.value,
                all: definition.all,
            })
        } else {
            Declaration::Defn(definition)
        });
        remaining[index] = false;
    }
    Ok(ElaboratedPartial {
        owner: None,
        declarations,
        noncomputable: BTreeSet::new(),
        irreducible,
        scope: scope.clone(),
        budget: meter.txn.budget,
        kernel,
    })
}

/// The whole group's elaborated data, indexed by source position.
struct Parts<'a> {
    group: &'a Group,
    members: &'a [Syntax],
    names: &'a [Name],
    bodies: &'a [DefinitionVal],
    hints: &'a [MemberHint],
    headers: &'a [ConstantVal],
}

/// Build every component against one below dictionary, then publish the fully checked
/// product recursor and reducible projections. Runtime companions retain the source bodies.
fn mutual_structural(
    meter: &mut Context,
    (environment, kernel, scope): (&Environment, Budget, &SourceScope),
    parts: &Parts<'_>,
    component: &[usize],
) -> Result<(DefinitionVal, Vec<DefinitionVal>, Vec<DefinitionVal>), NatDefinitionElabError> {
    let unsupported = |shape| {
        failure(SourceInferenceError::Recursion(
            recursion::RecursionError::MutualStructuralUnsupported(shape),
        ))
    };
    let captures = parts
        .group
        .shared
        .as_ref()
        .map_or_else(Vec::new, |shared| shared.locals.clone());
    let names: Vec<_> = component
        .iter()
        .map(|&index| parts.names[index].clone())
        .collect();
    let levels = parts.bodies[component[0]].base.level_params.clone();
    let header_levels: Vec<_> = levels
        .iter()
        .filter(|level| {
            !parts
                .group
                .shared
                .as_ref()
                .is_some_and(|shared| shared.fixed_levels.contains(*level))
        })
        .cloned()
        .collect();
    if component.iter().any(|&index| {
        parts.headers[index].level_params != header_levels
            || parts.bodies[index].base.level_params != levels
    }) {
        return Err(unsupported("one universe telescope for all members"));
    }
    let mut arities = Vec::new();
    let mut values = Vec::new();
    let mut types = Vec::new();
    for &index in component {
        let value = &parts.bodies[index].value;
        let mut cursor = value;
        let mut arity = 0;
        while let ExprNode::Lam { body, .. } = cursor.node() {
            meter.tick()?;
            arity += 1;
            cursor = body;
        }
        arities.push(arity);
        values.push(value.clone());
        types.push(parts.bodies[index].base.type_.clone());
    }
    let fixed = meter.mutual_structural_fixed_prefix(&values, &arities, &names)?;
    if fixed < captures.len() {
        return Err(unsupported("section captures in the common fixed prefix"));
    }
    let auxiliary = Name::str(names[0].clone(), "_mutual");
    if std::iter::once(auxiliary)
        .chain(
            names
                .iter()
                .map(|name| Name::str(name.clone(), "_unsafe_rec")),
        )
        .chain(names.iter().map(|name| Name::str(name.clone(), "_sunfold")))
        .any(|name| environment.contains(&name) || parts.names.contains(&name))
    {
        return Err(refusal("fresh distinct ordinary mutual names"));
    }
    // An indexed family's major follows its varying index binders. Try each source
    // position in order; preceding varying binders are either independent family
    // indices or arguments generalized within each component. Each attempt has fresh
    // contexts, and failed attempts still charge the shared budget.
    let candidates = arities.iter().copied().min().unwrap_or(0);
    let mut last = None;
    for decreasing in fixed..candidates {
        let attempt = (|| {
            let mut planner = fork_scoped_with_caches(meter, environment, kernel, scope)?;
            let planned = planner.mutual_structural_plan(
                names.clone(),
                types.clone(),
                arities.clone(),
                fixed,
                decreasing,
                levels.clone(),
            );
            absorb_child_caches(meter, &planner);
            let plan = std::sync::Arc::new(planned?);
            let mut wrappers = Vec::new();
            let mut pieces = Vec::new();
            for (position, &index) in component.iter().enumerate() {
                let mut context = fork_scoped_with_caches(meter, environment, kernel, scope)?;
                context.partial = Some(State {
                    kind: Kind::Unsafe,
                    group: Some(parts.group.clone()),
                    ordinary: true,
                    ..State::default()
                });
                context.mutual_structural_member = Some(recursion::StructuralMember::new(
                    plan.clone(),
                    position,
                    captures.clone(),
                ));
                let elaborated = definition_in_context(&parts.members[index], &mut context);
                absorb_child_caches(meter, &context);
                let Declaration::Mutual(mut definitions) = elaborated? else {
                    return Err(refusal("one ordinary body per mutual header"));
                };
                let (Some(mut wrapper), true) = (definitions.pop(), definitions.is_empty()) else {
                    return Err(refusal("one ordinary body per mutual header"));
                };
                if context.noncomputable_definition {
                    return Err(refusal("computable ordinary mutual definition"));
                }
                let piece = context
                    .mutual_structural_member
                    .as_ref()
                    .and_then(recursion::StructuralMember::piece)
                    .cloned()
                    .ok_or_else(|| failure(SourceInferenceError::Scope))?;
                wrapper.safety = DefinitionSafety::Safe;
                if !matches!(wrapper.hints, ReducibilityHints::Abbrev) {
                    wrapper.hints = ReducibilityHints::Regular(1);
                }
                wrapper.all = names.clone();
                if wrapper.base.name != names[position] {
                    return Err(failure(SourceInferenceError::Scope));
                }
                wrappers.push(wrapper);
                pieces.push(piece);
            }
            let mut obligations = Vec::new();
            for &index in component {
                obligations.push(mutual_typing_obligation(
                    meter,
                    &plan,
                    &parts.bodies[index],
                )?);
            }
            let mut assembler = fork_scoped_with_caches(meter, environment, kernel, scope)?;
            let assembled = assembler.assemble_mutual_structural(&plan, &pieces, &obligations);
            absorb_child_caches(meter, &assembler);
            let mutual = assembled?;
            let implementations = mutual_implementations(meter, parts.bodies, component, &names)?;
            Ok((mutual, wrappers, implementations))
        })();
        match attempt {
            Ok(compiled) => return Ok(compiled),
            Err(
                problem @ NatDefinitionElabError::Inference(SourceInferenceError::Recursion(
                    recursion::RecursionError::MutualStructuralUnsupported(_)
                    | recursion::RecursionError::NotDecreasing
                    | recursion::RecursionError::ChangedParameter
                    | recursion::RecursionError::PartialApplication,
                )),
            ) => last = Some(problem),
            Err(problem) => return Err(problem),
        }
    }
    Err(last.unwrap_or_else(|| unsupported("a structural major in every member")))
}

/// Retain the original source body as a checked initializer under abstract peer functions.
/// This prevents structural compilation from erasing a malformed source annotation.
fn mutual_typing_obligation(
    meter: &mut Context,
    plan: &recursion::StructuralPlan,
    definition: &DefinitionVal,
) -> Result<Typed, NatDefinitionElabError> {
    let mut markers = Vec::new();
    for _ in &plan.names {
        markers.push(FVarId(meter.fresh_name()?));
    }
    let levels: Vec<_> = plan
        .level_params
        .iter()
        .cloned()
        .map(Level::param)
        .collect();
    let original = map(meter, &definition.value, &|_, expr| {
        let ExprNode::Const {
            name,
            levels: actual,
        } = expr.node()
        else {
            return Ok(None);
        };
        let Some(index) = plan.names.iter().position(|candidate| candidate == name) else {
            return Ok(None);
        };
        if actual != &levels {
            return Err(failure(SourceInferenceError::Recursion(
                recursion::RecursionError::MutualStructuralUnsupported(
                    "polymorphic recursive calls",
                ),
            )));
        }
        Ok(Some(Expr::fvar(markers[index].clone())))
    })?;
    let bound = |index| Expr::bvar(index).map_err(|_| failure(SourceInferenceError::Scope));
    let proposition = Expr::forall_e(
        Name::anonymous(),
        Expr::sort(Level::zero()),
        Expr::forall_e(Name::anonymous(), bound(0)?, bound(1)?, BinderInfo::Default),
        BinderInfo::Default,
    );
    let proof = Expr::lam(
        Name::anonymous(),
        Expr::sort(Level::zero()),
        Expr::lam(Name::anonymous(), bound(0)?, bound(0)?, BinderInfo::Default),
        BinderInfo::Default,
    );
    let mut value = Expr::let_e(
        Name::anonymous(),
        definition.base.type_.clone(),
        original,
        proof,
        false,
    );
    let mut type_ = proposition;
    for (marker, domain) in markers.iter().zip(&plan.types).rev() {
        meter.tick()?;
        value = Expr::lam(
            Name::anonymous(),
            domain.clone(),
            value
                .abstract_fvar(marker, 0)
                .map_err(|_| failure(SourceInferenceError::Scope))?,
            BinderInfo::Default,
        );
        type_ = Expr::forall_e(
            Name::anonymous(),
            domain.clone(),
            type_
                .abstract_fvar(marker, 0)
                .map_err(|_| failure(SourceInferenceError::Scope))?,
            BinderInfo::Default,
        );
    }
    Ok(Typed { value, type_ })
}

fn mutual_implementations(
    meter: &mut Context,
    bodies: &[DefinitionVal],
    component: &[usize],
    names: &[Name],
) -> Result<Vec<DefinitionVal>, NatDefinitionElabError> {
    let executable: Vec<_> = names
        .iter()
        .map(|name| Name::str(name.clone(), "_unsafe_rec"))
        .collect();
    let mut implementations = Vec::new();
    for &index in component {
        let mut definition = bodies[index].clone();
        definition.value = map(meter, &definition.value, &|_, expr| {
            let ExprNode::Const { name, levels } = expr.node() else {
                return Ok(None);
            };
            Ok(names
                .iter()
                .position(|member| member == name)
                .map(|target| Expr::const_(executable[target].clone(), levels.clone())))
        })?;
        let position = names
            .iter()
            .position(|member| member == &definition.base.name)
            .ok_or_else(|| failure(SourceInferenceError::Scope))?;
        definition.base.name = executable[position].clone();
        definition.safety = DefinitionSafety::Partial;
        definition.hints = ReducibilityHints::Opaque;
        definition.all = executable.clone();
        implementations.push(definition);
    }
    Ok(implementations)
}

/// A recursive component of two or more definitions with explicit or inferred measures:
/// the pin's `wfRecursion` over the component (see
/// `recursion::well_founded::mutual`). Returns `<first>._mutual`, the members'
/// wrappers in SCC order, and their `_unsafe_rec` executable companions.
/// Every other recursive component is refused.
fn mutual_well_founded(
    meter: &mut Context,
    (environment, kernel, scope): (&Environment, Budget, &SourceScope),
    parts: &Parts<'_>,
    component: &[usize],
) -> Result<(DefinitionVal, Vec<DefinitionVal>, Vec<DefinitionVal>), NatDefinitionElabError> {
    let Parts {
        group,
        members: _,
        names,
        bodies,
        hints,
        headers,
    } = *parts;
    let unsupported = |shape| {
        failure(SourceInferenceError::Recursion(
            recursion::RecursionError::MutualWellFoundedUnsupported(shape),
        ))
    };
    if component.len() < 2 {
        return Err(refusal(
            "recursive ordinary mutual component requires termination elaboration",
        ));
    }
    let component_hints: Vec<_> = component.iter().map(|&index| &hints[index]).collect();
    let inferred = component_hints
        .iter()
        .all(|hint| matches!(hint, MemberHint::None | MemberHint::DecreasingOnly));
    if component_hints
        .iter()
        .any(|hint| matches!(hint, MemberHint::Structural))
    {
        return Err(unsupported("structural mutual recursion"));
    }
    let mut measured = Vec::new();
    for hint in component_hints {
        match hint {
            MemberHint::Measured(Ok(member)) => measured.push(member.clone()),
            MemberHint::Measured(Err(problem)) => return Err(problem.clone()),
            MemberHint::None | MemberHint::DecreasingOnly if inferred => {}
            // A mixture of explicit and missing hints is an error at the pin.
            // Do not infer a measure and silently turn that error into acceptance.
            MemberHint::None | MemberHint::DecreasingOnly => {
                return Err(unsupported("an incomplete set of termination_by measures"));
            }
            MemberHint::Structural => return Err(unsupported("structural mutual recursion")),
            MemberHint::Pending(_) => return Err(failure(SourceInferenceError::Scope)),
        }
    }
    // Codomains and the selected relation are checked by the shared planner,
    // after the group's fixed parameters have been identified and opened.
    // This admits lexicographic and user-selected well-founded measures without
    // treating their executable companions as logical termination evidence.
    let captures = group
        .shared
        .as_ref()
        .map_or_else(Vec::new, |shared| shared.locals.clone());
    // MutualClosure selects variables from the bodies, before elaborating
    // termination hints. A hint cannot add a parameter the source body omitted,
    // even if an unused let would erase its occurrence during reduction.
    let mut captured = HashSet::new();
    for capture in &captures {
        meter.tick()?;
        captured.insert(capture.id.clone());
    }
    for member in &measured {
        for id in &member.section_captures {
            meter.tick()?;
            if !captured.contains(id) {
                return Err(unsupported(
                    "termination measures over captured section variables",
                ));
            }
        }
    }
    let levels = bodies[component[0]].base.level_params.clone();
    let header_levels: Vec<_> = levels
        .iter()
        .filter(|level| {
            !group
                .shared
                .as_ref()
                .is_some_and(|shared| shared.fixed_levels.contains(*level))
        })
        .cloned()
        .collect();
    for &index in component {
        if headers[index].level_params != header_levels || bodies[index].base.level_params != levels
        {
            return Err(unsupported("one universe telescope for all members"));
        }
    }
    // Headers and bodies were elaborated independently. Equal parameter names
    // alone do not establish a common universe telescope: each recursive call
    // must instantiate its peer at those same levels. In particular, never
    // silently replace a polymorphic call's instantiation when packing it into
    // the single shared fixpoint. Both checked executable companions retain
    // the complete original terms and their universe applications.
    let recursive_levels: Vec<_> = levels.iter().cloned().map(Level::param).collect();
    for &index in component {
        for root in [&bodies[index].base.type_, &bodies[index].value] {
            map(meter, root, &|_, expr| {
                if let ExprNode::Const { name, levels } = expr.node()
                    && component.iter().any(|&target| names[target] == *name)
                    && levels != &recursive_levels
                {
                    return Err(unsupported("polymorphic recursive calls"));
                }
                Ok(None)
            })?;
        }
    }
    let component_names: Vec<_> = component
        .iter()
        .map(|&index| names[index].clone())
        .collect();
    let values: Vec<_> = component
        .iter()
        .map(|&index| bodies[index].value.clone())
        .collect();
    let arities: Vec<_> = if inferred {
        let mut arities = Vec::new();
        for value in &values {
            let mut cursor = value;
            let mut arity = 0;
            while let ExprNode::Lam { body, .. } = cursor.node() {
                meter.tick()?;
                arity += 1;
                cursor = body;
            }
            arities.push(arity);
        }
        arities
    } else {
        measured
            .iter()
            .map(|member| {
                member
                    .arity
                    .checked_add(captures.len())
                    .ok_or_else(|| failure(SourceInferenceError::Scope))
            })
            .collect::<Result<_, _>>()?
    };
    let fixed = meter
        .mutual_fixed_prefix(&values, &arities, &component_names)?
        .ok_or_else(|| {
            unsupported("fixed parameters that are not one common unreordered prefix")
        })?;
    if fixed < captures.len() {
        return Err(unsupported("section captures in the common fixed prefix"));
    }
    let auxiliary = Name::str(component_names[0].clone(), "_mutual");
    let executable: Vec<_> = component_names
        .iter()
        .map(|name| Name::str(name.clone(), "_unsafe_rec"))
        .collect();
    if std::iter::once(&auxiliary)
        .chain(&executable)
        .any(|name| environment.contains(name) || names.contains(name))
    {
        return Err(refusal("fresh distinct ordinary mutual names"));
    }
    let types: Vec<_> = component
        .iter()
        .map(|&index| bodies[index].base.type_.clone())
        .collect();
    let mut choices = Vec::new();
    if inferred {
        let mut planner = fork_scoped_with_caches(meter, environment, kernel, scope)?;
        planner.level_params = levels.clone();
        planner.explicit_levels = levels.len();
        for (type_, &arity) in types.iter().zip(&arities) {
            let result = planner.mutual_simple_measures(type_, arity, fixed);
            absorb_child_caches(meter, &planner);
            choices.push(result?);
        }
    } else {
        for member in &measured {
            choices.push(vec![meter.close_mutual_fixed(
                &member.measure,
                &captures,
                true,
            )?]);
        }
    }
    let combinations =
        mutual_measure_combinations(&choices.iter().map(Vec::len).collect::<Vec<_>>())
            .ok_or_else(|| unsupported("too many inferred measure combinations"))?;
    let mut candidates = Vec::new();
    for combination in combinations {
        meter.tick()?;
        let mut measures = Vec::new();
        for (choices, &index) in choices.iter().zip(&combination) {
            meter.tick()?;
            measures.push(choices[index].clone());
        }
        candidates.push(MutualMeasureCandidate::new(
            measures,
            combination.iter().any(|index| index != &combination[0]),
        ));
    }
    let make_plan = |meter: &mut Context, measures: &[Expr]| {
        let mut planner = fork_scoped_with_caches(meter, environment, kernel, scope)?;
        let planned = planner.mutual_well_founded_plan(
            component_names.clone(),
            types.clone(),
            arities.clone(),
            measures,
            fixed,
            levels.clone(),
        );
        absorb_child_caches(meter, &planner);
        planned.map(std::sync::Arc::new)
    };
    let make_measure = |meter: &mut Context, measures: &[Expr]| {
        let mut planner = fork_scoped_with_caches(meter, environment, kernel, scope)?;
        let built = planner.mutual_candidate_measure(
            &component_names,
            &types,
            &arities,
            measures,
            fixed,
            levels.clone(),
        );
        absorb_child_caches(meter, &planner);
        built
    };
    let mut base_plan: Option<std::sync::Arc<recursion::WellFoundedPlan>> = None;
    let mut captured: Vec<Option<(Context, recursion::MemberProbeSnapshot)>> =
        vec![None; component.len()];
    let mut counts = vec![None; component.len()];
    let mut remaining: Vec<Option<Vec<usize>>> = vec![None; component.len()];
    let mut order = Vec::new();
    let mut complex = false;
    let plan = loop {
        let mut chosen = None;
        for (slot, candidate) in candidates.iter_mut().enumerate() {
            meter.tick()?;
            if order.contains(&slot) {
                continue;
            }
            // Complex measures can precede nonuniform argument combinations.
            // Keep that existing boundary at every lexicographic step,
            // including after an earlier prefix.
            if complex && candidate.after_complex {
                return Err(unsupported("earlier complex inferred measures"));
            }
            if !inferred {
                if candidate.plan.is_none() {
                    candidate.plan = Some(make_plan(meter, &candidate.measures)?);
                }
                chosen = Some(slot);
                break;
            }
            if candidate.measure_sum.is_none() {
                candidate.measure_sum = Some(make_measure(meter, &candidate.measures)?);
            }
            let measure_sum = candidate
                .measure_sum
                .as_ref()
                .expect("prepared candidate measure")
                .clone();
            let mut disqualified = false;
            for (position, &index) in component.iter().enumerate() {
                let needed_calls = if disqualified {
                    // GuessLex stops querying a column at its first Unknown.
                    // Still discover unseen members' calls and complex-measure
                    // boundary, without running any decreasing proof tactics.
                    remaining[position].is_none().then(Vec::new)
                } else {
                    match &remaining[position] {
                        None => None, // captured below, then all calls requested
                        Some(calls) => {
                            let mut missing = Vec::new();
                            for &call in calls {
                                meter.tick()?;
                                match candidate.calls[position].get(&call) {
                                    Some(recursion::MutualMeasureRelation::Unknown) => {
                                        disqualified = true;
                                        break;
                                    }
                                    Some(_) => {}
                                    None => missing.push(call),
                                }
                            }
                            Some(missing)
                        }
                    }
                };
                if remaining[position].is_none() {
                    if base_plan.is_none() {
                        base_plan = Some(make_plan(meter, &candidate.measures)?);
                        if slot == 0 {
                            candidate.plan = base_plan.clone();
                        }
                    }
                    let (ctx, snapshot) = capture_mutual_member(
                        meter,
                        (environment, kernel, scope),
                        parts,
                        base_plan.as_ref().expect("base plan").clone(),
                        (position, index),
                        &captures,
                    )?;
                    let total = snapshot.goals.len();
                    if counts[position].is_some_and(|previous| previous != total) {
                        return Err(failure(SourceInferenceError::Scope));
                    }
                    counts[position] = Some(total);
                    let mut calls = Vec::with_capacity(total);
                    for call in 0..total {
                        meter.tick()?;
                        calls.push(call);
                    }
                    remaining[position] = Some(calls);
                    complex |= snapshot.complex;
                    captured[position] = Some((ctx, snapshot));
                    if complex && candidate.after_complex {
                        return Err(unsupported("earlier complex inferred measures"));
                    }
                }
                let missing = if disqualified {
                    continue;
                } else if let Some(missing) = needed_calls {
                    missing
                } else {
                    remaining[position]
                        .as_ref()
                        .expect("captured remaining calls")
                        .clone()
                };
                if missing.is_empty() {
                    continue;
                }
                let (ctx, snapshot) = captured[position].as_mut().expect("captured member probe");
                ctx.txn.budget = meter.txn.budget.clone();
                ctx.txn.nat_sub_model_cache = meter.txn.nat_sub_model_cache.clone();
                ctx.registry_cache = meter.registry_cache.clone();
                ctx.txn.registry_cache = meter.registry_cache.clone();
                ctx.alias_cache = meter.alias_cache.clone();
                ctx.protected_cache = meter.protected_cache.clone();
                ctx.auxiliary_cache = meter.auxiliary_cache.clone();
                ctx.deprecation_cache = meter.deprecation_cache.clone();
                ctx.simp_key_cache = meter.simp_key_cache.clone();
                let probed = ctx.probe_mutual_calls(snapshot, &measure_sum, &missing);
                absorb_child_caches(meter, ctx);
                let total = counts[position].expect("captured total");
                for (call, relation) in probed? {
                    meter.tick()?;
                    disqualified |= relation == recursion::MutualMeasureRelation::Unknown;
                    if call >= total
                        || candidate.calls[position]
                            .insert(call, relation)
                            .is_some_and(|previous| previous != relation)
                    {
                        return Err(failure(SourceInferenceError::Scope));
                    }
                }
            }
            if disqualified {
                continue;
            }
            let mut strict = false;
            let mut nonincreasing = true;
            'calls: for (position, calls) in remaining.iter().enumerate() {
                for call in calls
                    .as_ref()
                    .ok_or_else(|| failure(SourceInferenceError::Scope))?
                {
                    meter.tick()?;
                    match candidate.calls[position].get(call) {
                        Some(recursion::MutualMeasureRelation::Lt) => strict = true,
                        Some(
                            recursion::MutualMeasureRelation::Eq
                            | recursion::MutualMeasureRelation::Le,
                        ) => {}
                        Some(recursion::MutualMeasureRelation::Unknown) | None => {
                            nonincreasing = false;
                            break 'calls;
                        }
                    }
                }
            }
            if strict && nonincreasing {
                chosen = Some(slot);
                break;
            }
        }
        let slot = chosen.ok_or_else(|| {
            failure(SourceInferenceError::Recursion(
                recursion::RecursionError::WellFoundedMeasureSearchFailed,
            ))
        })?;
        if !inferred {
            break candidates[slot]
                .plan
                .as_ref()
                .expect("selected plan")
                .clone();
        }
        order.push(slot);
        for (position, calls) in remaining.iter_mut().enumerate() {
            let calls = calls
                .as_mut()
                .ok_or_else(|| failure(SourceInferenceError::Scope))?;
            let mut kept = 0;
            for current in 0..calls.len() {
                meter.tick()?;
                if candidates[slot].calls[position].get(&calls[current])
                    != Some(&recursion::MutualMeasureRelation::Lt)
                {
                    calls[kept] = calls[current];
                    kept += 1;
                }
            }
            calls.truncate(kept);
        }
        if remaining
            .iter()
            .all(|calls| calls.as_ref().is_some_and(Vec::is_empty))
        {
            if order.len() == 1 {
                if let Some(plan) = candidates[slot].plan.clone() {
                    break plan;
                }
                break make_plan(meter, &candidates[slot].measures)?;
            }
            let mut planner = fork_scoped_with_caches(meter, environment, kernel, scope)?;
            planner.level_params = levels.clone();
            planner.explicit_levels = levels.len();
            let mut measures = Vec::new();
            for (member, (type_, &arity)) in types.iter().zip(&arities).enumerate() {
                let coordinates: Vec<_> = order
                    .iter()
                    .map(|&slot| candidates[slot].measures[member].clone())
                    .collect();
                let measure = planner.mutual_lexicographic_measure(type_, arity, &coordinates);
                absorb_child_caches(meter, &planner);
                measures.push(measure?);
            }
            break make_plan(meter, &measures)?;
        }
    };
    let mut wrappers = Vec::new();
    let mut pieces = Vec::new();
    for (position, &index) in component.iter().enumerate() {
        let (wrapper, piece) = mutual_well_founded_member(
            meter,
            (environment, kernel, scope),
            parts,
            plan.clone(),
            (position, index),
            &captures,
            None,
        )?;
        wrappers.push(wrapper);
        pieces.push(piece);
    }
    let mut assembler = fork_scoped_with_caches(meter, environment, kernel, scope)?;
    let mutual = assembler.assemble_mutual_well_founded(&plan, &pieces)?;
    absorb_child_caches(meter, &assembler);
    // `addAndCompileUnsafe` (Lean/Elab/PreDefinition/Basic.lean): the pin also
    // admits each member's original recursive body as `partial def
    // <member>._unsafe_rec`, calling its peers' companions, and compiles those.
    // The runtime selects such a companion only for a complete linked group.
    let implementations = mutual_implementations(meter, bodies, component, &component_names)?;
    Ok((mutual, wrappers, implementations))
}

/// The pin's `generateCombinations?`: uniform measure positions first, then
/// the remaining product in telescope order, with its 32-combination bound.
fn mutual_measure_combinations(counts: &[usize]) -> Option<Vec<Vec<usize>>> {
    if counts.is_empty() || counts.contains(&0) {
        return Some(Vec::new());
    }
    let total = counts
        .iter()
        .try_fold(1usize, |total, count| total.checked_mul(*count))?;
    if total > 32 {
        return None;
    }
    let mut combinations = Vec::with_capacity(total);
    for index in 0..*counts.iter().min()? {
        combinations.push(vec![index; counts.len()]);
    }
    let mut current = vec![0; counts.len()];
    loop {
        if current.iter().any(|index| index != &current[0]) {
            combinations.push(current.clone());
        }
        let mut position = counts.len();
        loop {
            if position == 0 {
                return Some(combinations);
            }
            position -= 1;
            current[position] += 1;
            if current[position] < counts[position] {
                break;
            }
            current[position] = 0;
        }
    }
}

/// Elaborate one mutual member body once against the shared `PSum` domain and
/// return its captured probe context and packed call obligations for reuse
/// across GuessLex candidates.
fn capture_mutual_member(
    meter: &mut Context,
    (environment, kernel, scope): (&Environment, Budget, &SourceScope),
    parts: &Parts<'_>,
    plan: std::sync::Arc<recursion::WellFoundedPlan>,
    (position, index): (usize, usize),
    captures: &[LocalDecl],
) -> Result<(Context, recursion::MemberProbeSnapshot), NatDefinitionElabError> {
    let mut context = fork_scoped_with_caches(meter, environment, kernel, scope)?;
    let result = (|| {
        context.txn.lctx = LocalContext::new();
        for capture in captures {
            context.tick()?;
            tactics::eliminate::add_local(&mut context.txn.lctx, capture);
        }
        context.partial = Some(State {
            kind: Kind::Unsafe,
            group: Some(parts.group.clone()),
            ordinary: true,
            ..State::default()
        });
        context.mutual_member = Some(recursion::MutualMember::new(
            plan,
            position,
            captures.to_vec(),
            Some(recursion::MutualMeasureRequest::Capture),
        ));
        match definition_in_context(&parts.members[index], &mut context) {
            Err(NatDefinitionElabError::Inference(SourceInferenceError::Recursion(
                recursion::RecursionError::MutualMeasureProbe { .. },
            ))) => context
                .mutual_member
                .as_mut()
                .and_then(recursion::MutualMember::take_probe_snapshot)
                .ok_or_else(|| failure(SourceInferenceError::Scope)),
            Err(problem) => Err(problem),
            Ok(_) => Err(failure(SourceInferenceError::Scope)),
        }
    })();
    absorb_child_caches(meter, &context);
    let snapshot = result?;
    Ok((context, snapshot))
}

/// Every candidate uses a fresh context over the same admitted predecessor.
/// A failed probe retains spent work, but no assignments or unfinished proof
/// can reach the selected component's declaration assembly.
fn mutual_well_founded_member(
    meter: &mut Context,
    (environment, kernel, scope): (&Environment, Budget, &SourceScope),
    parts: &Parts<'_>,
    plan: std::sync::Arc<recursion::WellFoundedPlan>,
    (position, index): (usize, usize),
    captures: &[LocalDecl],
    probe: Option<recursion::MutualMeasureRequest>,
) -> Result<(DefinitionVal, Expr), NatDefinitionElabError> {
    let mut context = fork_scoped_with_caches(meter, environment, kernel, scope)?;
    let result = (|| {
        // Termination proofs run after MutualClosure. Unused section locals
        // are no longer in scope, even when their names could solve a goal.
        context.txn.lctx = LocalContext::new();
        for capture in captures {
            context.tick()?;
            tactics::eliminate::add_local(&mut context.txn.lctx, capture);
        }
        context.partial = Some(State {
            kind: Kind::Unsafe,
            group: Some(parts.group.clone()),
            ordinary: true,
            ..State::default()
        });
        context.mutual_member = Some(recursion::MutualMember::new(
            plan.clone(),
            position,
            captures.to_vec(),
            probe,
        ));
        let Declaration::Mutual(mut definitions) =
            definition_in_context(&parts.members[index], &mut context)?
        else {
            return Err(refusal("one ordinary body per mutual header"));
        };
        let (Some(mut wrapper), true) = (definitions.pop(), definitions.is_empty()) else {
            return Err(refusal("one ordinary body per mutual header"));
        };
        if context.noncomputable_definition {
            return Err(refusal("computable ordinary mutual definition"));
        }
        let piece = context
            .mutual_member
            .as_ref()
            .and_then(|member| member.piece())
            .cloned()
            .ok_or_else(|| failure(SourceInferenceError::Scope))?;
        wrapper.safety = DefinitionSafety::Safe;
        wrapper.hints = ReducibilityHints::Regular(1);
        wrapper.all = plan.names.clone();
        if wrapper.base.name != plan.names[position] {
            return Err(failure(SourceInferenceError::Scope));
        }
        Ok((wrapper, piece))
    })();
    absorb_child_caches(meter, &context);
    result
}

#[cfg(test)]
mod tests {
    use super::*;
    const SOURCE: &[u8] = b"mutual\n def first (n : Nat) : Nat := last n\n def middle (n : Nat) : Nat := n\n def last (n : Nat) : Nat := n\nend";
    #[test]
    fn mutual_measure_order_matches_guesslex_uniform_then_product_order() {
        assert_eq!(
            mutual_measure_combinations(&[2, 3]),
            Some(vec![
                vec![0, 0],
                vec![1, 1],
                vec![0, 1],
                vec![0, 2],
                vec![1, 0],
                vec![1, 2],
            ]),
        );
        assert_eq!(
            mutual_measure_combinations(&[1, 1, 1]),
            Some(vec![vec![0, 0, 0]]),
        );
        assert_eq!(mutual_measure_combinations(&[4, 8]).unwrap().len(), 32);
        assert!(mutual_measure_combinations(&[4, 9]).is_none());
        assert!(mutual_measure_combinations(&[usize::MAX, 2]).is_none());
    }

    #[test]
    fn acyclic_order_is_deterministic_and_every_candidate_is_safe() {
        let kernel = Budget::for_stack_bytes(2 * 1024 * 1024);
        let env = crate::seed::bootstrap_nat_environment(kernel).unwrap();
        let scope = SourceScope::default();
        let members = fln_parse::command_scope::mutual::parse(SOURCE)
            .unwrap()
            .unwrap();
        let result = elaborate_ordinary_group(&members, &env, kernel, &scope).unwrap();
        let expected = ["middle", "last", "first"];
        for (declaration, label) in result.declarations().iter().zip(expected) {
            let Declaration::Defn(value) = declaration else {
                panic!("safe definition");
            };
            assert_eq!(value.base.name, Name::from_components([label]));
            assert_eq!(value.safety, DefinitionSafety::Safe);
            assert!(!value.value.has_fvar());
            assert!(!value.value.has_loose_bvars());
            assert!(!env.contains(&value.base.name));
        }
        assert_eq!(result.declarations().len(), expected.len());
        let retry = elaborate_ordinary_group(&members, &env, kernel, &scope).unwrap();
        assert_eq!(result.declarations(), retry.declarations());
        assert_eq!(
            result.budget.heartbeats_consumed,
            retry.budget.heartbeats_consumed
        );
    }
    #[test]
    fn resource_stops_preserve_the_original_environment_and_retry() {
        let kernel = Budget::for_stack_bytes(2 * 1024 * 1024);
        let env = crate::seed::bootstrap_nat_environment(kernel).unwrap();
        let before = env.clone();
        let scope = SourceScope::default();
        let members = fln_parse::command_scope::mutual::parse(SOURCE)
            .unwrap()
            .unwrap();
        let control = elaborate_ordinary_group(&members, &env, kernel, &scope).unwrap();
        let used = control.budget.heartbeats_consumed;
        assert!(used > 3);
        for allowed in [1, used / 4, used / 2, used - 1] {
            let mut meter = Context::scoped(&env, kernel, &scope).unwrap();
            meter.txn.budget.max_heartbeats = allowed;
            let stopped = elaborate_with_meter(&members, &env, kernel, &scope, meter, false);
            let exhausted = match stopped.as_ref().err() {
                Some(NatDefinitionElabError::Inference(SourceInferenceError::ResourceLimit)) => {
                    true
                }
                Some(NatDefinitionElabError::Inference(SourceInferenceError::Unification(
                    error,
                ))) => {
                    matches!(error.as_ref(), UnificationError::HeartbeatLimit)
                }
                _ => false,
            };
            assert!(
                exhausted,
                "budget {allowed}/{used}: {:?}",
                stopped.as_ref().err()
            );
            assert_eq!(env, before);
        }
        let retry = elaborate_ordinary_group(&members, &env, kernel, &scope).unwrap();
        assert_eq!(retry.declarations(), control.declarations());
        assert_eq!(retry.budget.heartbeats_consumed, used);
    }
}
