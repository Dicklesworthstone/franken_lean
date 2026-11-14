//! A quoted declaration owns its name and parameter telescope. Its parameters
//! scope over the result and body; its recursive name scopes only over the body.
use super::*;

fn command_args<'a>(syntax: &'a Syntax, leaf: &str) -> Option<&'a [Syntax]> {
    match syntax {
        Syntax::Node { kind, args, .. }
            if *kind == Name::from_components(["Lean", "Parser", "Command", leaf]) =>
        {
            Some(args)
        }
        _ => None,
    }
}

fn unsupported() -> EngineExecutionError {
    EngineExecutionError::NotImplemented {
        feature: "a quoted command declaration with an unsupported binding shape",
    }
}

pub(super) fn schedule<'a>(
    syntax: &'a Syntax,
    rule: &NotationRule,
    tasks: &mut Vec<Task<'a>>,
    scope_depth: usize,
) -> Result<bool, EngineExecutionError> {
    let Some(declarations) = command_args(syntax, "declaration") else {
        return Ok(false);
    };
    let [modifiers, declaration] = declarations else {
        return Err(unsupported());
    };
    if rule.prechecked {
        return Err(unsupported());
    }
    let Some(modifiers_args) = command_args(modifiers, "declModifiers") else {
        return Err(unsupported());
    };
    if modifiers_args.len() != 7 || !null_args(&modifiers_args[1])?.is_empty() {
        // Attribute arguments can have their own binding/name-resolution rules.
        return Err(unsupported());
    }
    let (parts, theorem) = if let Some(parts) = command_args(declaration, "definition") {
        if parts.len() != 5 || !null_args(&parts[4])?.is_empty() {
            return Err(unsupported());
        }
        (parts, false)
    } else if let Some(parts) = command_args(declaration, "abbrev") {
        if parts.len() != 4 {
            return Err(unsupported());
        }
        (parts, false)
    } else if let Some(parts) = command_args(declaration, "theorem") {
        if parts.len() != 4 {
            return Err(unsupported());
        }
        (parts, true)
    } else {
        return Err(unsupported());
    };
    let [keyword, id, signature, value, ..] = parts else {
        return Err(unsupported());
    };
    let expected_keyword = if theorem {
        "theorem"
    } else if parts.len() == 5 {
        "def"
    } else {
        "abbrev"
    };
    if !atom(keyword, &[expected_keyword]) {
        return Err(unsupported());
    }
    let Some([name, universes]) = command_args(id, "declId") else {
        return Err(unsupported());
    };
    if !null_args(universes)?.is_empty() {
        return Err(unsupported());
    }
    let mut names = Vec::new();
    binder_name(name, rule, &mut names)?;
    let Some([parameters, result]) =
        command_args(signature, if theorem { "declSig" } else { "optDeclSig" })
    else {
        return Err(unsupported());
    };
    null_args(parameters)?;
    if theorem {
        if !matches!(term_args(result, "typeSpec")?, [colon, _] if atom(colon, &[":"])) {
            return Err(unsupported());
        }
    } else {
        shared_type(result)?;
    }
    let Some([assignment, body, termination, helpers]) = command_args(value, "declValSimple") else {
        return Err(unsupported());
    };
    if !atom(assignment, &[":="]) || !null_args(helpers)?.is_empty() {
        return Err(unsupported());
    }
    let Syntax::Node { kind, args, .. } = termination else {
        return Err(unsupported());
    };
    if *kind != Name::from_components(["Lean", "Parser", "Termination", "suffix"])
        || args.len() != 2
        || args
            .iter()
            .any(|part| !null_args(part).is_ok_and(<[Syntax]>::is_empty))
    {
        return Err(unsupported());
    }

    tasks.push(Task::Restore(scope_depth));
    tasks.push(build(syntax)?);
    tasks.push(build(declaration)?);
    if let Some(deriving) = parts.get(4) {
        tasks.push(Task::Copy(deriving));
    }
    tasks.push(build(value)?);
    tasks.push(Task::Copy(helpers));
    tasks.push(Task::Copy(termination));
    tasks.push(Task::Visit(body));
    tasks.push(Task::Copy(assignment));
    tasks.push(Task::Bind(names));
    tasks.push(build(signature)?);
    tasks.push(Task::Visit(result));
    tasks.push(Task::Binders(parameters));
    tasks.push(Task::Copy(id));
    tasks.push(Task::Copy(keyword));
    tasks.push(Task::Copy(modifiers));
    Ok(true)
}
