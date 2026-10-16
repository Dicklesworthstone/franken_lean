//! Quoted match branches have independent pattern-variable scopes. Constructor
//! heads are resolved at the declaration site; pattern variables shadow ordinary
//! constants. The term elaborator still owns typing and exhaustive coverage.
use super::*;

fn rebuild(syntax: &Syntax, args: Vec<Syntax>) -> Result<Syntax, EngineExecutionError> {
    let Syntax::Node { info, kind, .. } = syntax else {
        return Err(unsupported_binder());
    };
    Ok(Syntax::Node {
        info: *info,
        kind: kind.clone(),
        args,
    })
}

fn global_ident(syntax: &Syntax, global: Name) -> Result<Syntax, EngineExecutionError> {
    let Syntax::Ident { info, raw_val, .. } = syntax else {
        return Err(unsupported_binder());
    };
    Ok(Syntax::Ident {
        info: *info,
        raw_val: *raw_val,
        val: Name::from_components(["_root_"]).append_core(&global),
        preresolved: vec![Preresolved::Decl {
            name: global,
            fields: Vec::new(),
        }],
    })
}

fn bind_pattern(
    syntax: &Syntax,
    rule: &NotationRule,
    names: &mut Vec<Name>,
) -> Result<(), EngineExecutionError> {
    let mut bound = Vec::new();
    binder_name(syntax, rule, &mut bound)?;
    for name in bound {
        if !name.erase_macro_scopes().parent().is_anonymous() || names.contains(&name) {
            return Err(unsupported_binder());
        }
        names.push(name);
    }
    Ok(())
}

fn separated<'a>(
    syntax: &'a Syntax,
    separator: &str,
) -> Result<&'a [Syntax], EngineExecutionError> {
    let entries = null_args(syntax)?;
    if entries.is_empty()
        || entries.len().is_multiple_of(2)
        || entries
            .iter()
            .enumerate()
            .any(|(i, e)| i % 2 == 1 && !atom(e, &[separator]))
    {
        return Err(unsupported_binder());
    }
    Ok(entries)
}

/// The accessible, explicit pattern subset. Antiquoted patterns, explicit
/// constructor parameters, inaccessible patterns and annotations need their own
/// scope analysis; refusing them is preferable to guessing which names bind.
fn patterns(
    row: &Syntax,
    rule: &NotationRule,
    resolve: &impl Fn(&Name) -> Resolution,
    outer: &[Name],
) -> Result<(Syntax, Vec<Name>), EngineExecutionError> {
    enum Walk<'a> {
        Pattern(&'a Syntax),
        Head(&'a Syntax),
        Copy(&'a Syntax),
        Build(&'a Syntax, usize),
    }
    let entries = separated(row, ",")?;
    let mut tasks = vec![Walk::Build(row, entries.len())];
    tasks.extend(entries.iter().enumerate().rev().map(|(i, e)| {
        if i % 2 == 0 {
            Walk::Pattern(e)
        } else {
            Walk::Copy(e)
        }
    }));
    let mut built = Vec::new();
    let mut names = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            Walk::Pattern(ident @ Syntax::Ident { val, .. }) => {
                if rule.variables.iter().any(|(_, variable)| variable == val) {
                    return Err(unsupported_binder());
                }
                match resolve(val) {
                    Resolution::Constructor(global) if !outer.contains(val) => {
                        built.push(global_ident(ident, global)?);
                    }
                    Resolution::Undetermined => return Err(unsupported_binder()),
                    _ => {
                        bind_pattern(ident, rule, &mut names)?;
                        built.push(ident.clone());
                    }
                }
            }
            Walk::Head(ident @ Syntax::Ident { val, .. }) => {
                if outer.contains(val) || rule.variables.iter().any(|(_, variable)| variable == val)
                {
                    return Err(unsupported_binder());
                }
                match resolve(val) {
                    Resolution::Constructor(global) => built.push(global_ident(ident, global)?),
                    Resolution::Unchecked => built.push(ident.clone()),
                    Resolution::Nothing if !rule.prechecked => built.push(ident.clone()),
                    // Match-pattern definitions require their attribute and
                    // parameter accessibility, not just a resolvable name.
                    _ => return Err(unsupported_binder()),
                }
            }
            Walk::Pattern(node @ Syntax::Node { kind, args, .. }) if term_kind(kind, "app") => {
                let [head, arguments] = args.as_slice() else {
                    return Err(unsupported_binder());
                };
                let fields = null_args(arguments)?;
                if fields.is_empty() {
                    return Err(unsupported_binder());
                }
                tasks.push(Walk::Build(node, 2));
                tasks.push(Walk::Build(arguments, fields.len()));
                tasks.extend(fields.iter().rev().map(Walk::Pattern));
                tasks.push(Walk::Head(head));
            }
            Walk::Pattern(node @ Syntax::Node { kind, args, .. }) if term_kind(kind, "paren") => {
                let [open, inner, close] = args.as_slice() else {
                    return Err(unsupported_binder());
                };
                if !atom(close, &[")"]) {
                    return Err(unsupported_binder());
                }
                tasks.push(Walk::Build(node, 3));
                tasks.push(Walk::Copy(close));
                tasks.push(Walk::Pattern(inner));
                tasks.push(Walk::Copy(open));
            }
            Walk::Pattern(node @ Syntax::Node { kind, args, .. })
                if term_kind(kind, "anonymousCtor") =>
            {
                let [open, fields, close] = args.as_slice() else {
                    return Err(unsupported_binder());
                };
                if !atom(open, &["⟨"]) || !atom(close, &["⟩"]) {
                    return Err(unsupported_binder());
                }
                let fields_args = separated(fields, ",")?;
                tasks.push(Walk::Build(node, 3));
                tasks.push(Walk::Copy(close));
                tasks.push(Walk::Build(fields, fields_args.len()));
                tasks.extend(fields_args.iter().enumerate().rev().map(|(i, e)| {
                    if i % 2 == 0 {
                        Walk::Pattern(e)
                    } else {
                        Walk::Copy(e)
                    }
                }));
                tasks.push(Walk::Copy(open));
            }
            Walk::Pattern(node @ Syntax::Node { kind, args, .. })
                if term_kind(kind, "hole") && args.len() == 1 && atom(&args[0], &["_"]) =>
            {
                built.push(node.clone());
            }
            Walk::Pattern(node @ Syntax::Node { kind, args, .. })
                if ["num", "str", "char"]
                    .iter()
                    .any(|leaf| *kind == Name::from_components([*leaf]))
                    && args.len() == 1
                    && matches!(args[0], Syntax::Atom { .. }) =>
            {
                built.push(node.clone());
            }
            Walk::Pattern(node @ Syntax::Node { kind, args, .. })
            | Walk::Head(node @ Syntax::Node { kind, args, .. })
                if term_kind(kind, "dotIdent")
                    && args.len() == 2
                    && atom(&args[0], &["."])
                    && matches!(args[1], Syntax::Ident { .. }) =>
            {
                // Dot-constructor labels have raw-identifier semantics. The
                // checked match compiler resolves them from the subject type.
                built.push(node.clone());
            }
            Walk::Copy(node) => built.push(node.clone()),
            Walk::Build(node, count) => {
                let start = built
                    .len()
                    .checked_sub(count)
                    .ok_or_else(unsupported_binder)?;
                let args = built.split_off(start);
                built.push(rebuild(node, args)?);
            }
            _ => return Err(unsupported_binder()),
        }
    }
    if built.len() != 1 {
        return Err(unsupported_binder());
    }
    Ok((built.pop().ok_or_else(unsupported_binder)?, names))
}

pub(super) fn schedule<'a>(
    syntax: &'a Syntax,
    rule: &NotationRule,
    resolve: &impl Fn(&Name) -> Resolution,
    tasks: &mut Vec<Task<'a>>,
    outer: &[Name],
) -> Result<(), EngineExecutionError> {
    let (keyword, dependent, generalizing, motive, discriminants, with, alternatives) =
        if let Ok(parts) = term_args(syntax, "doMatch") {
            let [
                keyword,
                dependent,
                generalizing,
                motive,
                discriminants,
                with,
                alternatives,
            ] = parts
            else {
                return Err(unsupported_binder());
            };
            if rule.prechecked || !null_args(dependent)?.is_empty() {
                return Err(unsupported_binder());
            }
            (
                keyword,
                Some(dependent),
                generalizing,
                motive,
                discriminants,
                with,
                alternatives,
            )
        } else {
            let [
                keyword,
                generalizing,
                motive,
                discriminants,
                with,
                alternatives,
            ] = term_args(syntax, "match")?
            else {
                return Err(unsupported_binder());
            };
            (
                keyword,
                None,
                generalizing,
                motive,
                discriminants,
                with,
                alternatives,
            )
        };
    if !atom(keyword, &["match"])
        || !atom(with, &["with"])
        || !null_args(generalizing)?.is_empty()
        || !null_args(motive)?.is_empty()
    {
        return Err(unsupported_binder());
    }
    let discrs = separated(discriminants, ",")?;
    for discr in discrs.iter().step_by(2) {
        let [binding, _term] = term_args(discr, "matchDiscr")? else {
            return Err(unsupported_binder());
        };
        if !null_args(binding)?.is_empty() {
            return Err(unsupported_binder());
        }
    }
    let [alt_list] = term_args(alternatives, "matchAlts")? else {
        return Err(unsupported_binder());
    };
    let alts = null_args(alt_list)?;
    if alts.is_empty() {
        return Err(unsupported_binder());
    }
    tasks.push(build(syntax)?);
    tasks.push(build(alternatives)?);
    tasks.push(build(alt_list)?);
    for alternative in alts.iter().rev() {
        let [pipe, rows, arrow, body] = term_args(alternative, "matchAlt")? else {
            return Err(unsupported_binder());
        };
        if !atom(pipe, &["|"]) || !atom(arrow, &["=>", "↦"]) {
            return Err(unsupported_binder());
        }
        let rows_args = separated(rows, "|")?;
        let mut transformed = Vec::with_capacity(rows_args.len());
        let mut variables = None;
        for (index, row) in rows_args.iter().enumerate() {
            if index % 2 == 1 {
                transformed.push(row.clone());
                continue;
            }
            if separated(row, ",")?.len() != discrs.len() {
                return Err(unsupported_binder());
            }
            let (pattern, mut names) = patterns(row, rule, resolve, outer)?;
            names.sort();
            if variables.as_ref().is_some_and(|first| first != &names) {
                return Err(unsupported_binder());
            }
            variables = Some(names);
            transformed.push(pattern);
        }
        // Every alternative restores the enclosing context before its sibling
        // starts. Its pattern names enter only after the patterns are rebuilt.
        tasks.push(Task::Restore(outer.len()));
        tasks.push(build(alternative)?);
        tasks.push(Task::Visit(body));
        tasks.push(Task::Copy(arrow));
        tasks.push(Task::Bind(variables.ok_or_else(unsupported_binder)?));
        tasks.push(Task::Emit(rebuild(rows, transformed)?));
        tasks.push(Task::Copy(pipe));
    }
    tasks.push(Task::Copy(with));
    tasks.push(Task::Visit(discriminants));
    tasks.push(Task::Copy(motive));
    tasks.push(Task::Copy(generalizing));
    if let Some(dependent) = dependent {
        tasks.push(Task::Copy(dependent));
    }
    tasks.push(Task::Copy(keyword));
    Ok(())
}

/// A conditional has one pattern rather than a comma-separated matrix row.
/// Use the same constructor/binder analysis as match alternatives, not a
/// second recognizer with different hygiene or name-resolution rules.
pub(super) fn single_pattern(
    syntax: &Syntax,
    rule: &NotationRule,
    resolve: &impl Fn(&Name) -> Resolution,
    outer: &[Name],
) -> Result<(Syntax, Vec<Name>), EngineExecutionError> {
    let row = Syntax::node(Name::from_components(["null"]), vec![syntax.clone()]);
    let (mut row, names) = patterns(&row, rule, resolve, outer)?;
    let Syntax::Node { args, .. } = &mut row else {
        return Err(unsupported_binder());
    };
    Ok((args.pop().ok_or_else(unsupported_binder)?, names))
}
