//! Ordinary mutual predefinitions, following MutualDef's header/body boundary
//! and dependency partition. Headers are private candidate data, never
//! temporary environment axioms. A recursive component of definitions with Nat
//! `termination_by` measures is elaborated by well-founded recursion over one
//! shared fixpoint; any other recursive component is refused here, never
//! downgraded to a partial definition.
use super::*;
use recursion::MemberHint;

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

fn member(syntax: &Syntax) -> Result<(&Syntax, bool), NatDefinitionElabError> {
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
    // Visibility and attribute publication are effects, not permission to drop
    // syntax. Keep unsupported effects outside this atomic aperture.
    for modifier in &modifiers[1..] {
        expect_empty_null(
            modifier,
            "ordinary mutual declaration without attributes or modifiers",
        )?;
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
        Context::scoped(environment, kernel, scope),
    )
}

fn elaborate_with_meter(
    members: &[Syntax],
    environment: &Environment,
    kernel: Budget,
    scope: &SourceScope,
    mut meter: Context,
) -> Result<ElaboratedPartial, NatDefinitionElabError> {
    if members.is_empty() || members.len() > 8 {
        return Err(refusal("one to eight ordinary mutual declarations"));
    }
    if scope.private_module.is_some() {
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
        let (id, theorem) = member(syntax)?;
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
        let mut context = Context::scoped(environment, kernel, scope);
        context.txn.budget = meter.txn.budget.clone();
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
    let mut hints = Vec::new();
    let theorem = proof_group == Some(true);
    for syntax in members {
        let mut context = Context::scoped(environment, kernel, scope);
        context.txn.budget = meter.txn.budget.clone();
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
        hints.push(
            context
                .partial
                .as_ref()
                .and_then(|state| state.member_hint.clone())
                .unwrap_or(MemberHint::None),
        );
        meter.txn.budget = context.txn.budget;
        bodies.push(definition);
    }
    if !scope.variables.is_empty() {
        close_shared_captures(&mut meter, &headers, &mut bodies, &universes, &fixed_levels)?;
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
            let (mutual, members_published, executable) = mutual_well_founded(
                &mut meter,
                (environment, kernel, scope),
                &Parts {
                    group: &group,
                    members,
                    names: &names,
                    bodies: &bodies,
                    hints: &hints,
                    headers: &headers,
                    level_names: level_names.as_deref().unwrap_or_default(),
                },
                &component,
            )?;
            declarations.push(Declaration::Defn(mutual));
            for definition in members_published {
                irreducible.insert(definition.base.name.clone());
                declarations.push(Declaration::Defn(definition));
            }
            declarations.push(Declaration::Mutual(executable));
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
    level_names: &'a [Name],
}

/// A recursive component of two or more definitions, all with Nat measures:
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
        members,
        names,
        bodies,
        hints,
        headers,
        level_names,
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
    if component_hints
        .iter()
        .all(|hint| matches!(hint, MemberHint::None))
    {
        return Err(refusal(
            "recursive ordinary mutual component requires termination elaboration",
        ));
    }
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
            // The pin reports an incomplete set of termination hints and
            // guesses every measure (GuessLex), which this group does not.
            MemberHint::None | MemberHint::DecreasingOnly => {
                return Err(unsupported(
                    "a member without a termination_by measure (the pin's GuessLex)",
                ));
            }
            MemberHint::Structural => return Err(unsupported("structural mutual recursion")),
        }
    }
    // `checkCodomains` (WF/Rel.lean): one measure type for the whole group.
    if let Some(position) = measured.iter().position(|member| !member.nat) {
        if measured.iter().any(|member| member.nat) {
            let first = measured.iter().position(|member| member.nat).unwrap_or(0);
            let (first, other) = if first < position {
                (first, position)
            } else {
                (position, first)
            };
            return Err(failure(SourceInferenceError::Recursion(
                recursion::RecursionError::MutualMeasureTypeMismatch {
                    first: names[component[first]].clone(),
                    other: names[component[other]].clone(),
                },
            )));
        }
        return Err(unsupported("measures of a type other than Nat"));
    }
    if measured.iter().any(|member| !member.natural) {
        return Err(unsupported(
            "a Nat measure under a WellFoundedRelation other than Nat.lt_wfRel",
        ));
    }
    if !scope.variables.is_empty() {
        return Err(unsupported("section variables"));
    }
    for &index in component {
        if headers[index].level_params != level_names {
            return Err(unsupported(
                "universe parameters written identically on every member",
            ));
        }
    }
    let component_names: Vec<_> = component
        .iter()
        .map(|&index| names[index].clone())
        .collect();
    let arities: Vec<_> = measured.iter().map(|member| member.arity).collect();
    let values: Vec<_> = component
        .iter()
        .map(|&index| bodies[index].value.clone())
        .collect();
    let fixed = meter
        .mutual_fixed_prefix(&values, &arities, &component_names)?
        .ok_or_else(|| {
            unsupported("fixed parameters that are not one common unreordered prefix")
        })?;
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
        .map(|&index| headers[index].type_.clone())
        .collect();
    let measures: Vec<_> = measured
        .iter()
        .map(|member| member.measure.clone())
        .collect();
    let mut planner = Context::scoped(environment, kernel, scope);
    planner.txn.budget = meter.txn.budget.clone();
    let plan = std::sync::Arc::new(planner.mutual_well_founded_plan(
        component_names.clone(),
        types,
        arities,
        &measures,
        fixed,
        level_names.to_vec(),
    )?);
    meter.txn.budget = planner.txn.budget;
    let mut wrappers = Vec::new();
    let mut pieces = Vec::new();
    for (position, &index) in component.iter().enumerate() {
        let member = &members[index];
        let mut context = Context::scoped(environment, kernel, scope);
        context.txn.budget = meter.txn.budget.clone();
        context.partial = Some(State {
            kind: Kind::Unsafe,
            group: Some(group.clone()),
            ordinary: true,
            ..State::default()
        });
        context.mutual_member = Some(recursion::MutualMember::new(plan.clone(), position));
        let Declaration::Mutual(mut definitions) = definition_in_context(member, &mut context)?
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
        meter.txn.budget = context.txn.budget;
        wrapper.safety = DefinitionSafety::Safe;
        wrapper.hints = ReducibilityHints::Regular(1);
        wrapper.all = component_names.clone();
        if wrapper.base.name != component_names[position] {
            return Err(failure(SourceInferenceError::Scope));
        }
        wrappers.push(wrapper);
        pieces.push(piece);
    }
    let mut assembler = Context::scoped(environment, kernel, scope);
    assembler.txn.budget = meter.txn.budget.clone();
    let mutual = assembler.assemble_mutual_well_founded(&plan, &pieces)?;
    meter.txn.budget = assembler.txn.budget;
    // `addAndCompileUnsafe` (Lean/Elab/PreDefinition/Basic.lean): the pin also
    // admits each member's original recursive body as `partial def
    // <member>._unsafe_rec`, calling its peers' companions, and compiles those.
    // The runtime selects such a companion only for a complete linked group.
    let mut implementations = Vec::new();
    for &index in component {
        let mut definition = bodies[index].clone();
        definition.value = map(meter, &definition.value, &|_, expr| {
            let ExprNode::Const { name, levels } = expr.node() else {
                return Ok(None);
            };
            Ok(component_names
                .iter()
                .position(|member| member == name)
                .map(|target| Expr::const_(executable[target].clone(), levels.clone())))
        })?;
        let position = component_names
            .iter()
            .position(|member| member == &definition.base.name)
            .ok_or_else(|| failure(SourceInferenceError::Scope))?;
        definition.base.name = executable[position].clone();
        definition.safety = DefinitionSafety::Partial;
        definition.hints = ReducibilityHints::Opaque;
        definition.all = executable.clone();
        implementations.push(definition);
    }
    Ok((mutual, wrappers, implementations))
}

#[cfg(test)]
mod tests {
    use super::*;
    const SOURCE: &[u8] = b"mutual\n def first (n : Nat) : Nat := last n\n def middle (n : Nat) : Nat := n\n def last (n : Nat) : Nat := n\nend";
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
            let mut meter = Context::scoped(&env, kernel, &scope);
            meter.txn.budget.max_heartbeats = allowed;
            let stopped = elaborate_with_meter(&members, &env, kernel, &scope, meter);
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
