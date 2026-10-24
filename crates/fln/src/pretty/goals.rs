//! Goal display shares the normal bounded term printer and its name resolution.
use super::*;
use fln_elab::{
    lctx::LocalDecl,
    source::trace::{SourceTrace, TraceContent},
};

fn close(expr: &Expr, locals: &[LocalDecl]) -> Result<Expr, Unsupported> {
    let mut closed = expr.clone();
    for (index, local) in locals.iter().rev().enumerate() {
        closed = closed
            .abstract_fvar(
                &local.id,
                u32::try_from(index).map_err(|_| Unsupported("too many goal locals"))?,
            )
            .map_err(|_| Unsupported("goal local scope"))?;
    }
    if closed.has_fvar() {
        return Err(Unsupported("unknown free variable in goal"));
    }
    Ok(closed)
}

/// The names a goal display shows for `locals`, outermost first: a hygienic or
/// shadowed name gains `✝` and a superscript index, as the pin's `ppGoal` shows it.
fn shown_names(locals: &[LocalDecl]) -> Result<Vec<String>, Unsupported> {
    let mut names = Vec::new();
    let mut used = std::collections::HashSet::new();
    let mut stems = std::collections::HashMap::<String, usize>::new();
    for local in locals.iter().rev() {
        let hygienic = local.user_name.has_macro_scopes();
        let base = if hygienic {
            escaped_name(&local.user_name.erase_macro_scopes())
        } else if accessible(&local.user_name) {
            escaped_name(&local.user_name)
        } else {
            return Err(Unsupported(
                "the original inaccessible goal name is unavailable",
            ));
        };
        let mut shown = base.clone();
        if hygienic || used.contains(&local.user_name) {
            let index = stems.entry(base.clone()).or_default();
            let number = if *index == 0 {
                String::new()
            } else {
                index
                    .to_string()
                    .chars()
                    .map(|c| {
                        SUPERSCRIPTS
                            .chars()
                            .nth(c.to_digit(10).unwrap() as usize)
                            .unwrap()
                    })
                    .collect()
            };
            shown = format!("{base}✝{number}");
            *index += 1;
        }
        // Hygiene does not shadow an independently accessible outer name.
        used.insert(local.user_name.clone());
        names.push(shown);
    }
    names.reverse();
    Ok(names)
}

impl Printer<'_> {
    /// Enter the leading binders of a `#check` candidate closed over section variables
    /// (`fln_elab::source::scope::elaborate_check`): one per entry of `positions`, which index
    /// `variables`, the scope's whole `variable` list. Each is shown as the pin's message shows
    /// that variable, free in its local context: a variable a later one shadows shows as `x✝`
    /// (`LocalContext.sanitizeNames`), whether or not the later one is used. Returns the value
    /// and type under the binders.
    pub fn open_section_variables(
        &mut self,
        variables: &[LocalDecl],
        positions: &[usize],
        value: &Expr,
        type_: &Expr,
    ) -> Result<(Expr, Expr), Unsupported> {
        let mut value = value.clone();
        let mut type_ = type_.clone();
        if positions.is_empty() {
            return Ok((value, type_));
        }
        let names = shown_names(variables)?;
        for &position in positions {
            self.tick()?;
            let shown = names
                .get(position)
                .ok_or(Unsupported("a section variable outside its scope"))?;
            let (
                ExprNode::Lam {
                    binder_type,
                    body: value_body,
                    ..
                },
                ExprNode::ForallE {
                    body: type_body, ..
                },
            ) = (value.node(), type_.node())
            else {
                return Err(Unsupported(
                    "a #check candidate without its section binders",
                ));
            };
            self.bind(shown.clone(), binder_type);
            (value, type_) = (value_body.clone(), type_body.clone());
        }
        // The term printed next is the top of the line, as at the pin, where these variables are
        // free rather than bound.
        self.top_names = self.names.len();
        Ok((value, type_))
    }
}

/// `term`, elaborated in `locals`, as a message prints it inline (`MessageData.ofExpr`).
pub fn term_in_locals(
    env: &Environment,
    scope: &fln_elab::source::scope::SourceScope,
    locals: &[LocalDecl],
    term: &Expr,
) -> Result<String, Unsupported> {
    let names = shown_names(locals)?;
    let mut printer = Printer::in_scope(env, scope);
    for (index, local) in locals.iter().enumerate() {
        printer.tick()?;
        let type_ = close(&local.type_, &locals[..index])?;
        printer.bind(names[index].clone(), &type_);
    }
    let term = close(term, locals)?;
    printer
        .doc(&term, 0)?
        .try_pretty(
            WIDTH,
            format::FormatRenderLimits {
                max_work: 10_000_000,
                max_output_bytes: 1024 * 1024,
            },
        )
        .map_err(|_| Unsupported("message term rendering resource limit"))
}

/// Render a raw trace without changing goals, definitions or metavariables.
/// An unrenderable expression remains a refusal, even when a guard drops traces.
pub fn render(env: &Environment, event: &SourceTrace) -> Result<String, Unsupported> {
    let goals = match &event.content {
        TraceContent::Goals(goals) => goals,
        TraceContent::Message(message) | TraceContent::Info(message) => {
            return Ok(message.clone());
        }
    };
    let mut displayed = Vec::new();
    let mut total = 0usize;
    for goal in goals {
        let locals = goal.locals.decls();
        let mut printer = Printer::in_scope(env, &event.scope);
        let names = shown_names(locals)?;
        let mut lines = Vec::new();
        if !goal.tag.is_anonymous() {
            lines.push(Format::text(format!("case {}", escaped_name(&goal.tag))));
        }
        let mut group: Vec<String> = Vec::new();
        let mut group_type: Option<Expr> = None;
        let mut type_doc = Format::text("");
        for (index, local) in locals.iter().enumerate() {
            printer.tick()?;
            let type_ = close(&local.type_, &locals[..index])?;
            let shown = &names[index];
            if local.value.is_some() || group_type.as_ref() != Some(&local.type_) {
                if !group.is_empty() {
                    lines.push(
                        Format::text(format!("{} :", group.join(" ")))
                            .then(Format::Line.then(type_doc.clone()).nest(2))
                            .group(),
                    );
                    group.clear();
                }
                type_doc = printer.doc(&type_, 0)?;
                group_type = Some(local.type_.clone());
            }
            if let Some(value) = &local.value {
                let value = close(value, &locals[..index])?;
                lines.push(
                    Format::text(format!("{shown} : "))
                        .then(type_doc.clone())
                        .then(Format::text(" :="))
                        .then(
                            Format::Line
                                .then(if atomic(&value) || value.approx_depth() <= 254 {
                                    printer.doc(&value, 0)?
                                } else {
                                    Format::text("⋯")
                                })
                                .nest(2),
                        )
                        .group(),
                );
                group_type = None;
            } else {
                group.push(shown.clone());
            }
            printer.bind(shown.clone(), &type_);
        }
        if !group.is_empty() {
            lines.push(
                Format::text(format!("{} :", group.join(" ")))
                    .then(Format::Line.then(type_doc).nest(2))
                    .group(),
            );
        }
        let target = close(&goal.target, locals)?;
        lines.push(Format::text("⊢ ").then(printer.doc(&target, 0)?.nest(2)));
        let document = lines
            .into_iter()
            .reduce(|all, line| all.then(Format::text("\n")).then(line))
            .unwrap_or(Format::Nil);
        let text = document
            .try_pretty(
                WIDTH,
                format::FormatRenderLimits {
                    max_work: 10_000_000,
                    max_output_bytes: (16 * 1024 * 1024usize).saturating_sub(total),
                },
            )
            .map_err(|_| Unsupported("goal trace rendering resource limit"))?;
        total = total
            .checked_add(text.len())
            .filter(|n| *n <= 16 * 1024 * 1024)
            .ok_or(Unsupported("goal trace output limit"))?;
        displayed.push(text);
    }
    Ok(displayed.join("\n\n"))
}
