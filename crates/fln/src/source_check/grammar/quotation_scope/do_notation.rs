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

/// An iterator's annotation and collection belong to the enclosing context.
/// Only the body sees the element and optional membership proof. A bare name
/// here is a binder even when it also names a constructor at the declaration
/// site (the pin's `expandDoFor` tests `isIdent` before expanding patterns).
fn for_loop<'a>(
    syntax: &'a Syntax,
    rule: &NotationRule,
    tasks: &mut Vec<Task<'a>>,
    scope_depth: usize,
) -> Result<(), EngineExecutionError> {
    let Syntax::Node { args, .. } = syntax else {
        return Err(unsupported_binder());
    };
    let [keyword, declarations, do_, body] = args.as_slice() else {
        return Err(unsupported_binder());
    };
    let [declaration] = null_args(declarations)? else {
        // Multiple collections use streams, not independent nested loops.
        return Err(unsupported_binder());
    };
    let [witness, iterator, in_, collection] = term_args(declaration, "doForDecl")? else {
        return Err(unsupported_binder());
    };
    if !atom(keyword, &["for"]) || !atom(do_, &["do"]) || !atom(in_, &["in"]) {
        return Err(unsupported_binder());
    }
    let name = if bare_binder(iterator) {
        iterator
    } else {
        let [_open, name @ Syntax::Ident { .. }, colon, annotation, close] =
            term_args(iterator, "typeAscription")?
        else {
            return Err(unsupported_binder());
        };
        if !atom(colon, &[":"]) || !atom(close, &[")"]) || null_args(annotation)?.len() != 1 {
            return Err(unsupported_binder());
        }
        name
    };
    let mut names = Vec::new();
    binder_name(name, rule, &mut names)?;
    match null_args(witness)? {
        [] => {}
        [name @ Syntax::Ident { .. }, colon] if atom(colon, &[":"]) => {
            binder_name(name, rule, &mut names)?;
        }
        _ => return Err(unsupported_binder()),
    }
    if names.iter().any(|name| {
        let plain = name.erase_macro_scopes();
        plain.is_anonymous() || !plain.parent().is_anonymous()
    }) {
        return Err(unsupported_binder());
    }
    tasks.push(Task::Restore(scope_depth));
    tasks.push(build(syntax)?);
    tasks.push(Task::DoSequence(body, true));
    tasks.push(Task::Copy(do_));
    tasks.push(Task::Bind(names));
    tasks.push(build(declarations)?);
    tasks.push(build(declaration)?);
    tasks.push(Task::Visit(collection));
    tasks.push(Task::Copy(in_));
    // Binder resolves the annotation first. Discard its temporary binding
    // before visiting the collection, then introduce all names for the body.
    tasks.push(Task::Restore(scope_depth));
    tasks.push(Task::Binder(iterator, None));
    tasks.push(Task::Copy(witness));
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
    if term_kind(kind, "doFor") || term_kind(kind, "termFor") {
        if rule.prechecked {
            return Err(unsupported_binder());
        }
        for_loop(syntax, rule, tasks, scope_depth)?;
        return Ok(true);
    }
    // These shapes also bind identifiers. Until their scope is analysed, do
    // not send them through the generic walk and pre-resolve binders as globals.
    if [
        "doLetRec",
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

/// The syntax of a condition and the names available on its two exits.
/// Evidence binders name a proof on both exits (with different types, checked
/// by elaboration); a pattern's fields are in scope on the success exit only.
struct Condition<'a> {
    tasks: Vec<Task<'a>>,
    yes: Vec<Name>,
    no: Vec<Name>,
    depth: usize,
}

fn condition<'a>(
    syntax: &'a Syntax,
    rule: &NotationRule,
    resolve: &impl Fn(&Name) -> Resolution,
    outer: &[Name],
) -> Result<Condition<'a>, EngineExecutionError> {
    let mut tasks = vec![build(syntax)?];
    let mut names = Vec::new();
    let negative;
    if let Ok(parts) = term_args(syntax, "doIfProp") {
        let [binding, predicate] = parts else {
            return Err(unsupported_binder());
        };
        match null_args(binding)? {
            [] => {}
            [name, colon] if atom(colon, &[":"]) => {
                if !atom(name, &["_"]) {
                    binder_name(name, rule, &mut names)?;
                    if names
                        .iter()
                        .any(|name| !name.erase_macro_scopes().parent().is_anonymous())
                    {
                        return Err(unsupported_binder());
                    }
                }
            }
            _ => return Err(unsupported_binder()),
        }
        tasks.push(Task::Visit(predicate));
        tasks.push(Task::Copy(binding));
        negative = names.clone();
    } else {
        let [keyword, pattern, assignment] = term_args(syntax, "doIfLet")? else {
            return Err(unsupported_binder());
        };
        if !atom(keyword, &["let"]) {
            return Err(unsupported_binder());
        }
        let monadic = term_args(assignment, "doIfLetBind").is_ok();
        let [operator, value] = term_args(
            assignment,
            if monadic {
                "doIfLetBind"
            } else {
                "doIfLetPure"
            },
        )?
        else {
            return Err(unsupported_binder());
        };
        if !(if monadic {
            atom(operator, &["←", "<-"])
        } else {
            atom(operator, &[":="])
        }) {
            return Err(unsupported_binder());
        }
        let (pattern, bound) = matches::single_pattern(pattern, rule, resolve, outer)?;
        names = bound;
        negative = Vec::new();
        tasks.push(build(assignment)?);
        tasks.push(Task::Visit(value));
        tasks.push(Task::Copy(operator));
        tasks.push(Task::Emit(pattern));
        tasks.push(Task::Copy(keyword));
    }
    Ok(Condition {
        tasks,
        yes: names,
        no: negative,
        depth: outer.len(),
    })
}

/// Keep the original six-slot doIf and its else-if group nodes. Work is queued
/// in source order: predicate, success-only locals, success sequence, restore,
/// failure evidence, next predicate. Each sequence restores its own local lets;
/// the whole conditional restores all evidence before its enclosing suffix.
/// No branch body is visited with another branch's pattern variables.
pub(super) fn conditional<'a>(
    syntax: &'a Syntax,
    rule: &NotationRule,
    resolve: &impl Fn(&Name) -> Resolution,
    tasks: &mut Vec<Task<'a>>,
    outer: &[Name],
) -> Result<(), EngineExecutionError> {
    if rule.prechecked {
        return Err(unsupported_binder());
    }
    let [keyword, predicate, then, yes, clauses, otherwise] = term_args(syntax, "doIf")? else {
        return Err(unsupported_binder());
    };
    if !atom(keyword, &["if"]) || !atom(then, &["then"]) {
        return Err(unsupported_binder());
    }
    let first = condition(predicate, rule, resolve, outer)?;
    let mut failures = outer.to_vec();
    failures.extend(first.no.iter().cloned());
    let mut following = Vec::new();
    for clause in null_args(clauses)? {
        let Syntax::Node { kind, args, .. } = clause else {
            return Err(unsupported_binder());
        };
        let [prefix, predicate, then, body] = args.as_slice() else {
            return Err(unsupported_binder());
        };
        let Syntax::Node {
            kind: prefix_kind,
            args: words,
            ..
        } = prefix
        else {
            return Err(unsupported_binder());
        };
        if *kind != Name::from_components(["group"])
            || *prefix_kind != *kind
            || words.len() != 2
            || !atom(&words[0], &["else"])
            || !atom(&words[1], &["if"])
            || !atom(then, &["then"])
        {
            return Err(unsupported_binder());
        }
        let header = condition(predicate, rule, resolve, &failures)?;
        failures.extend(header.no.iter().cloned());
        following.push((clause, prefix, then, body, header));
    }
    let other = null_args(otherwise)?;
    if !(other.is_empty() || (other.len() == 2 && atom(&other[0], &["else"]))) {
        return Err(unsupported_binder());
    }
    tasks.push(Task::Restore(outer.len()));
    tasks.push(build(syntax)?);
    tasks.push(build(otherwise)?);
    if let [keyword, body] = other {
        tasks.push(Task::Visit(body));
        tasks.push(Task::Copy(keyword));
    }
    tasks.push(build(clauses)?);
    for (clause, prefix, then, body, header) in following.into_iter().rev() {
        tasks.push(Task::Bind(header.no));
        tasks.push(Task::Restore(header.depth));
        tasks.push(build(clause)?);
        tasks.push(Task::Visit(body));
        tasks.push(Task::Copy(then));
        tasks.push(Task::Bind(header.yes));
        tasks.extend(header.tasks);
        tasks.push(Task::Copy(prefix));
    }
    tasks.push(Task::Bind(first.no));
    tasks.push(Task::Restore(first.depth));
    tasks.push(Task::Visit(yes));
    tasks.push(Task::Copy(then));
    tasks.push(Task::Bind(first.yes));
    tasks.extend(first.tasks);
    tasks.push(Task::Copy(keyword));
    Ok(())
}


/// A protected sequence, each catch handler, and the finalizer have separate
/// lexical scopes. The ordinary exception elaborator owns their dynamic
/// extent and control effects; this walk only resolves template identifiers.
pub(super) fn exception_region<'a>(
    syntax: &'a Syntax,
    rule: &NotationRule,
    resolve: &impl Fn(&Name) -> Resolution,
    tasks: &mut Vec<Task<'a>>,
    outer: &[Name],
) -> Result<(), EngineExecutionError> {
    if rule.prechecked {
        return Err(unsupported_binder());
    }
    let [keyword, body, catches, finally] = term_args(syntax, "doTry")? else {
        return Err(unsupported_binder());
    };
    let handlers = null_args(catches)?;
    let finalizers = null_args(finally)?;
    if !atom(keyword, &["try"])
        || finalizers.len() > 1
        || handlers.is_empty() && finalizers.is_empty()
    {
        return Err(unsupported_binder());
    }
    tasks.push(Task::Restore(outer.len()));
    tasks.push(build(syntax)?);
    tasks.push(build(finally)?);
    if let [finalizer] = finalizers {
        let [keyword, body] = term_args(finalizer, "doFinally")? else {
            return Err(unsupported_binder());
        };
        if !atom(keyword, &["finally"]) {
            return Err(unsupported_binder());
        }
        tasks.push(build(finalizer)?);
        tasks.push(Task::Visit(body));
        tasks.push(Task::Copy(keyword));
    }
    tasks.push(build(catches)?);
    for handler in handlers.iter().rev() {
        if let Ok(parts) = term_args(handler, "doCatchMatch") {
            let [keyword, alternatives] = parts else {
                return Err(unsupported_binder());
            };
            if !atom(keyword, &["catch"]) {
                return Err(unsupported_binder());
            }
            tasks.push(build(handler)?);
            matches::schedule_alternatives(alternatives, rule, resolve, tasks, outer, 1)?;
            tasks.push(Task::Copy(keyword));
            continue;
        }
        let [keyword, name, annotation, arrow, body] = term_args(handler, "doCatch")? else {
            return Err(unsupported_binder());
        };
        if !atom(keyword, &["catch"]) || !atom(arrow, &["=>", "↦"]) {
            return Err(unsupported_binder());
        }
        optional_type(annotation)?;
        let mut names = Vec::new();
        binder_name(name, rule, &mut names)?;
        if names
            .iter()
            .any(|name| !name.erase_macro_scopes().parent().is_anonymous())
        {
            return Err(unsupported_binder());
        }
        tasks.push(Task::Restore(outer.len()));
        tasks.push(build(handler)?);
        tasks.push(Task::Visit(body));
        tasks.push(Task::Copy(arrow));
        tasks.push(Task::Bind(names));
        tasks.push(Task::Visit(annotation));
        tasks.push(Task::Copy(name));
        tasks.push(Task::Copy(keyword));
    }
    tasks.push(Task::Visit(body));
    tasks.push(Task::Copy(keyword));
    Ok(())
}
