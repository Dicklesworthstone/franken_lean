//! Quoted declarations retain their own telescopes and recursive-name scopes.
//! Mutual peers scope over member bodies, not their headers. Inductive fields
//! have separate telescopes; constructor labels retain quotation hygiene.
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
    if let Some(parts) = command_args(syntax, "mutual") {
        if rule.prechecked {
            return Err(unsupported());
        }
        let members =
            fln_parse::command_scope::mutual::syntax_members(syntax).ok_or_else(unsupported)?;
        let mut names = Vec::new();
        for member in members {
            let Some([_, declaration]) = command_args(member, "declaration") else {
                return Err(unsupported());
            };
            let Syntax::Node { args, .. } = declaration else {
                return Err(unsupported());
            };
            names.extend(declaration_names(
                args.get(1).ok_or_else(unsupported)?,
                rule,
            )?);
        }
        tasks.push(build(syntax)?);
        tasks.push(Task::Copy(&parts[2]));
        tasks.push(build(&parts[1])?);
        tasks.extend(
            members
                .iter()
                .rev()
                .map(|member| Task::CommandDeclaration(member, names.clone())),
        );
        tasks.push(Task::Copy(&parts[0]));
        return Ok(true);
    }
    if command_args(syntax, "declaration").is_none() {
        return Ok(false);
    }
    declaration(syntax, rule, tasks, scope_depth, &[])?;
    Ok(true)
}

fn modifiers(syntax: &Syntax) -> Result<(), EngineExecutionError> {
    let Some(args) = command_args(syntax, "declModifiers") else {
        return Err(unsupported());
    };
    if args.len() != 7 || !null_args(&args[1])?.is_empty() {
        // Attribute arguments can have their own binding/name-resolution rules.
        return Err(unsupported());
    }
    Ok(())
}

fn declaration_names(id: &Syntax, rule: &NotationRule) -> Result<Vec<Name>, EngineExecutionError> {
    let Some([name, universes]) = command_args(id, "declId") else {
        return Err(unsupported());
    };
    if !null_args(universes)?.is_empty() {
        return Err(unsupported());
    }
    let mut names = Vec::new();
    binder_name(name, rule, &mut names)?;
    Ok(names)
}

fn signature(syntax: &Syntax, required: bool) -> Result<(&Syntax, &Syntax), EngineExecutionError> {
    let Some([parameters, result]) =
        command_args(syntax, if required { "declSig" } else { "optDeclSig" })
    else {
        return Err(unsupported());
    };
    null_args(parameters)?;
    if required {
        if !matches!(term_args(result, "typeSpec")?, [colon, _] if atom(colon, &[":"])) {
            return Err(unsupported());
        }
    } else {
        shared_type(result)?;
    }
    Ok((parameters, result))
}

pub(super) fn declaration<'a>(
    syntax: &'a Syntax,
    rule: &NotationRule,
    tasks: &mut Vec<Task<'a>>,
    scope_depth: usize,
    peers: &[Name],
) -> Result<(), EngineExecutionError> {
    let Some(declarations) = command_args(syntax, "declaration") else {
        return Err(unsupported());
    };
    let [modifiers, declaration] = declarations else {
        return Err(unsupported());
    };
    if rule.prechecked {
        return Err(unsupported());
    }
    self::modifiers(modifiers)?;
    if command_args(declaration, "inductive").is_some()
        || command_args(declaration, "classInductive").is_some()
    {
        return inductive(
            syntax,
            declaration,
            modifiers,
            rule,
            tasks,
            scope_depth,
            peers,
        );
    }
    let (parts, keyword, theorem, example) =
        if let Some(parts) = command_args(declaration, "definition") {
            if parts.len() != 5 || !null_args(&parts[4])?.is_empty() {
                return Err(unsupported());
            }
            (parts, "def", false, false)
        } else if let Some(parts) = command_args(declaration, "abbrev") {
            if parts.len() != 4 {
                return Err(unsupported());
            }
            (parts, "abbrev", false, false)
        } else if let Some(parts) = command_args(declaration, "theorem") {
            if parts.len() != 4 {
                return Err(unsupported());
            }
            (parts, "theorem", true, false)
        } else if let Some(parts) = command_args(declaration, "example") {
            if parts.len() != 3 {
                return Err(unsupported());
            }
            (parts, "example", false, true)
        } else {
            return Err(unsupported());
        };
    let (id, signature, value) = if example {
        (None, &parts[1], &parts[2])
    } else {
        (Some(&parts[1]), &parts[2], &parts[3])
    };
    if !atom(&parts[0], &[keyword]) {
        return Err(unsupported());
    }
    let mut names = match id {
        Some(id) => declaration_names(id, rule)?,
        None => Vec::new(),
    };
    names.extend(peers.iter().cloned());
    let (parameters, result) = self::signature(signature, theorem)?;

    tasks.push(Task::Restore(scope_depth));
    tasks.push(build(syntax)?);
    tasks.push(build(declaration)?);
    if let Some(deriving) = parts.get(4) {
        tasks.push(Task::Copy(deriving));
    }
    tasks.push(Task::DeclarationValue(value));
    tasks.push(Task::Bind(names));
    tasks.push(build(signature)?);
    tasks.push(Task::Visit(result));
    tasks.push(Task::Binders(parameters));
    if let Some(id) = id {
        tasks.push(Task::Copy(id));
    }
    tasks.push(Task::Copy(&parts[0]));
    tasks.push(Task::Copy(modifiers));
    Ok(())
}

fn empty_termination(syntax: &Syntax) -> Result<(), EngineExecutionError> {
    let Syntax::Node { kind, args, .. } = syntax else {
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
    Ok(())
}

/// Scheduled after the telescope and recursive names have entered scope.
/// Equation patterns share the ordinary match-quotation scope analysis.
pub(super) fn value<'a>(
    syntax: &'a Syntax,
    rule: &NotationRule,
    resolve: &impl Fn(&Name) -> Resolution,
    tasks: &mut Vec<Task<'a>>,
    outer: &[Name],
) -> Result<(), EngineExecutionError> {
    if let Some([assignment, body, termination, helpers]) = command_args(syntax, "declValSimple") {
        if !atom(assignment, &[":="]) || !null_args(helpers)?.is_empty() {
            return Err(unsupported());
        }
        empty_termination(termination)?;
        tasks.push(build(syntax)?);
        tasks.push(Task::Copy(helpers));
        tasks.push(Task::Copy(termination));
        tasks.push(Task::Visit(body));
        tasks.push(Task::Copy(assignment));
        return Ok(());
    }
    let Some([equations]) = command_args(syntax, "declValEqns") else {
        return Err(unsupported());
    };
    let [alternatives, termination, helpers] = term_args(equations, "matchAltsWhereDecls")? else {
        return Err(unsupported());
    };
    if !null_args(helpers)?.is_empty() {
        return Err(unsupported());
    }
    empty_termination(termination)?;
    tasks.push(build(syntax)?);
    tasks.push(build(equations)?);
    tasks.push(Task::Copy(helpers));
    tasks.push(Task::Copy(termination));
    matches::schedule_alternatives(
        alternatives,
        rule,
        resolve,
        tasks,
        outer,
        matches::equation_columns(alternatives)?,
    )
}

#[allow(clippy::too_many_arguments)]
fn inductive<'a>(
    syntax: &'a Syntax,
    declaration: &'a Syntax,
    modifiers: &'a Syntax,
    rule: &NotationRule,
    tasks: &mut Vec<Task<'a>>,
    scope_depth: usize,
    peers: &[Name],
) -> Result<(), EngineExecutionError> {
    let class = command_args(declaration, "classInductive");
    let parts = class
        .or_else(|| command_args(declaration, "inductive"))
        .ok_or_else(unsupported)?;
    if parts.len() != if class.is_some() { 6 } else { 7 } {
        return Err(unsupported());
    }
    if class.is_some() {
        let Syntax::Node { kind, args, .. } = &parts[0] else {
            return Err(unsupported());
        };
        if *kind != Name::from_components(["group"])
            || !matches!(args.as_slice(), [first, second]
                if atom(first, &["class"]) && atom(second, &["inductive"]))
        {
            return Err(unsupported());
        }
    } else if !atom(&parts[0], &["inductive"]) || !null_args(&parts[5])?.is_empty() {
        return Err(unsupported());
    }
    match null_args(&parts[3])? {
        [] => {}
        [keyword] if atom(keyword, &["where", ":="]) => {}
        _ => return Err(unsupported()),
    }
    let Some([deriving]) = command_args(&parts[parts.len() - 1], "optDeriving") else {
        return Err(unsupported());
    };
    if !null_args(deriving)?.is_empty() {
        return Err(unsupported());
    }
    let mut names = declaration_names(&parts[1], rule)?;
    names.extend(peers.iter().cloned());
    let (parameters, result) = signature(&parts[2], false)?;
    null_args(&parts[4])?;
    tasks.push(Task::Restore(scope_depth));
    tasks.push(build(syntax)?);
    tasks.push(build(declaration)?);
    tasks.push(Task::Copy(&parts[parts.len() - 1]));
    if class.is_none() {
        tasks.push(Task::Copy(&parts[5]));
    }
    tasks.push(Task::Constructors(&parts[4]));
    tasks.push(Task::Copy(&parts[3]));
    tasks.push(Task::Bind(names));
    tasks.push(build(&parts[2])?);
    tasks.push(Task::Visit(result));
    tasks.push(Task::Binders(parameters));
    tasks.push(Task::Copy(&parts[1]));
    tasks.push(Task::Copy(&parts[0]));
    tasks.push(Task::Copy(modifiers));
    Ok(())
}

pub(super) fn constructors<'a>(
    syntax: &'a Syntax,
    tasks: &mut Vec<Task<'a>>,
    scope_depth: usize,
) -> Result<(), EngineExecutionError> {
    tasks.push(build(syntax)?);
    for constructor in null_args(syntax)?.iter().rev() {
        let Some([documentation, pipe, modifiers, name, signature]) =
            command_args(constructor, "ctor")
        else {
            return Err(unsupported());
        };
        if !atom(pipe, &["|"])
            || !matches!(name, Syntax::Ident { val, .. } if !val.is_anonymous())
            || null_args(documentation)?.len() > 1
        {
            return Err(unsupported());
        }
        self::modifiers(modifiers)?;
        let (parameters, result) = self::signature(signature, false)?;
        // Copy the label, including captured caller syntax. Only its field
        // telescope binds locals, and those locals end before the next ctor.
        tasks.push(Task::Restore(scope_depth));
        tasks.push(build(constructor)?);
        tasks.push(build(signature)?);
        tasks.push(Task::Visit(result));
        tasks.push(Task::Binders(parameters));
        tasks.push(Task::Copy(name));
        tasks.push(Task::Copy(modifiers));
        tasks.push(Task::Copy(pipe));
        tasks.push(Task::Copy(documentation));
    }
    Ok(())
}
