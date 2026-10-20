//! Acyclic ordinary mutual predefinitions, following MutualDef's header/body
//! boundary and dependency partition. Headers are private candidate data, never
//! temporary environment axioms. A recursive component needs a termination
//! elaborator and is refused here, never downgraded to a partial definition.
use super::*;

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
    let theorem = proof_group == Some(true);
    for syntax in members {
        let mut context = Context::scoped(environment, kernel, scope);
        context.txn.budget = meter.txn.budget.clone();
        context.partial = Some(State {
            kind: Kind::Unsafe,
            group: Some(group.clone()),
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
    let mut remaining = vec![true; names.len()];
    let mut declarations = Vec::new();
    while declarations.len() < names.len() {
        let mut next = None;
        for (index, pending) in remaining.iter().enumerate() {
            meter.tick()?;
            if *pending
                && edges[index]
                    .iter()
                    .zip(&remaining)
                    .all(|(edge, live)| !edge || !live)
            {
                next = Some(index);
                break;
            }
        }
        let index = next.ok_or_else(|| {
            refusal("recursive ordinary mutual component requires termination elaboration")
        })?;
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
        scope: scope.clone(),
        budget: meter.txn.budget,
        kernel,
    })
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
