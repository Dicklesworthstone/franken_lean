//! Lexical scopes in native user-macro do quotations. Declarations extend the
//! remainder of a sequence only after their initializer. Local-function
//! parameters never escape that declaration. A bare nested do is flattened by
//! the pin's `elabDoNested` (`Lean/Elab/BuiltinDo/Misc.lean`); a do in term position
//! owns its scope instead. Nothing here executes the upstream elaborator.
use super::*;

pub(super) fn sequence<'a>(
    syntax: &'a Syntax,
    tasks: &mut Vec<Task<'a>>,
    restore: Option<usize>,
) -> Result<(), EngineExecutionError> {
    let Syntax::Node { kind, args, .. } = syntax else {
        return Err(unsupported_binder());
    };
    let (items, delimiters) = if term_kind(kind, "doSeqIndent") {
        let [items] = args.as_slice() else {
            return Err(unsupported_binder());
        };
        (items, None)
    } else if term_kind(kind, "doSeqBracketed") {
        let [open, items, close] = args.as_slice() else {
            return Err(unsupported_binder());
        };
        if !atom(open, &["{"]) || !atom(close, &["}"]) {
            return Err(unsupported_binder());
        }
        (items, Some((open, close)))
    } else {
        return Err(unsupported_binder());
    };
    let entries = null_args(items)?;
    if entries.is_empty() {
        return Err(unsupported_binder());
    }
    for item in entries {
        let [_element, separators] = term_args(item, "doSeqItem")? else {
            return Err(unsupported_binder());
        };
        match null_args(separators)? {
            [] => {}
            [separator] if atom(separator, &[";"]) => {}
            _ => return Err(unsupported_binder()),
        }
    }
    if let Some(depth) = restore {
        tasks.push(Task::Restore(depth));
    }
    tasks.push(build(syntax)?);
    if let Some((_, close)) = delimiters {
        tasks.push(Task::Copy(close));
    }
    tasks.push(build(items)?);
    for item in entries.iter().rev() {
        tasks.push(Task::Visit(item));
    }
    if let Some((open, _)) = delimiters {
        tasks.push(Task::Copy(open));
    }
    Ok(())
}

/// Named pure and monadic bindings have different parser trees but the same
/// scope boundary. Function parameters belong only to a pure declaration.
fn binding<'a>(
    syntax: &'a Syntax,
    rule: &NotationRule,
    tasks: &mut Vec<Task<'a>>,
    scope_depth: usize,
) -> Result<(), EngineExecutionError> {
    let Syntax::Node { kind, args, .. } = syntax else {
        return Err(unsupported_binder());
    };
    let have = term_kind(kind, "doHave");
    let arrow = term_kind(kind, "doLetArrow");
    let (keyword, mutable, config, wrapper) = match args.as_slice() {
        [keyword, config, declaration] if have => (keyword, None, config, declaration),
        [keyword, mutable, config, declaration] if !have => {
            (keyword, Some(mutable), config, declaration)
        }
        _ => return Err(unsupported_binder()),
    };
    if !atom(keyword, &[if have { "have" } else { "let" }])
        || mutable.is_some_and(|m| !null_args(m).is_ok_and(<[Syntax]>::is_empty))
    {
        return Err(unsupported_binder());
    }
    let [settings] = term_args(config, "letConfig")? else {
        return Err(unsupported_binder());
    };
    if !null_args(settings)?.is_empty() {
        return Err(unsupported_binder());
    }
    let mut names = Vec::new();
    if arrow {
        let [name, annotation, assignment, value] = term_args(wrapper, "doIdDecl")? else {
            return Err(unsupported_binder());
        };
        binder_name(name, rule, &mut names)?;
        shared_type(annotation)?;
        if !atom(assignment, &["←", "<-"]) {
            return Err(unsupported_binder());
        }
        tasks.push(Task::Bind(names));
        tasks.push(Task::Restore(scope_depth));
        tasks.push(build(syntax)?);
        tasks.push(build(wrapper)?);
        tasks.push(Task::Visit(value));
        tasks.push(Task::Copy(assignment));
        tasks.push(Task::Visit(annotation));
        tasks.push(Task::Copy(name));
    } else {
        let [declaration] = term_args(wrapper, "letDecl")? else {
            return Err(unsupported_binder());
        };
        let [id, parameters, annotation, assignment, value] = term_args(declaration, "letIdDecl")?
        else {
            return Err(unsupported_binder());
        };
        let [name] = term_args(id, "letId")? else {
            return Err(unsupported_binder());
        };
        binder_name(name, rule, &mut names)?;
        null_args(parameters)?;
        shared_type(annotation)?;
        if !atom(assignment, &[":="]) {
            return Err(unsupported_binder());
        }
        tasks.push(Task::Bind(names));
        tasks.push(Task::Restore(scope_depth));
        tasks.push(build(syntax)?);
        tasks.push(build(wrapper)?);
        tasks.push(build(declaration)?);
        tasks.push(Task::Visit(value));
        tasks.push(Task::Copy(assignment));
        tasks.push(Task::Visit(annotation));
        tasks.push(Task::Binders(parameters));
        tasks.push(Task::Copy(id));
    }
    tasks.push(Task::Copy(config));
    if let Some(mutable) = mutable {
        tasks.push(Task::Copy(mutable));
    }
    tasks.push(Task::Copy(keyword));
    Ok(())
}

pub(super) fn visit<'a>(
    syntax: &'a Syntax,
    rule: &NotationRule,
    tasks: &mut Vec<Task<'a>>,
    scope_depth: usize,
) -> Result<bool, EngineExecutionError> {
    let Syntax::Node { kind, args, .. } = syntax else {
        return Ok(false);
    };
    if ["do", "doNested"].iter().any(|k| term_kind(kind, k)) {
        // The pin has no quotation-precheck hook for do notation. Analysing
        // unchecked macros must not silently admit checked notation templates.
        if rule.prechecked {
            return Err(unsupported_binder());
        }
        let [keyword, sequence] = args.as_slice() else {
            return Err(unsupported_binder());
        };
        if !atom(keyword, &["do"]) {
            return Err(unsupported_binder());
        }
        tasks.push(build(syntax)?);
        tasks.push(Task::DoSequence(sequence, term_kind(kind, "do")));
        tasks.push(Task::Copy(keyword));
        return Ok(true);
    }
    if ["doSeqIndent", "doSeqBracketed"]
        .iter()
        .any(|k| term_kind(kind, k))
    {
        if rule.prechecked {
            return Err(unsupported_binder());
        }
        sequence(syntax, tasks, Some(scope_depth))?;
        return Ok(true);
    }
    if ["doLet", "doHave", "doLetArrow"]
        .iter()
        .any(|k| term_kind(kind, k))
    {
        if rule.prechecked {
            return Err(unsupported_binder());
        }
        binding(syntax, rule, tasks, scope_depth)?;
        return Ok(true);
    }
    // These shapes also bind identifiers. Until their scope is analysed, do
    // not send them through the generic walk and pre-resolve binders as globals.
    if [
        "doLetRec",
        "doFor",
        "termFor",
        "doMatch",
        "doIfLet",
        "doReassign",
        "doReassignArrow",
        "doTry",
    ]
    .iter()
    .any(|k| term_kind(kind, k))
    {
        return Err(unsupported_binder());
    }
    if term_kind(kind, "doIfProp") {
        let [binding, _condition] = args.as_slice() else {
            return Err(unsupported_binder());
        };
        if !null_args(binding)?.is_empty() {
            return Err(unsupported_binder());
        }
    }
    Ok(false)
}
