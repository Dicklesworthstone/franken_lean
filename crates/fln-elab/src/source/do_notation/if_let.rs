//! Pure and monadic pattern conditions lower through the existing match backend.
//! The tested expression occurs once; branch bindings never enclose the else
//! arm or the shared continuation. There is no new kernel or VM operation.
use super::*;

pub(super) fn parts(syntax: Syntax) -> Result<(Syntax, Syntax, bool), NatDefinitionElabError> {
    let mut parts = node(syntax, "doIfLet", 3)?;
    let assignment = parts.pop().expect("pattern condition value");
    let monadic = assignment.kind() == Some(&parser_kind(&["Term", "doIfLetBind"]));
    let mut value = node(
        assignment,
        if monadic {
            "doIfLetBind"
        } else {
            "doIfLetPure"
        },
        2,
    )?;
    if monadic {
        if !matches!(&value[0], Syntax::Atom { val, .. } if val == "←" || val == "<-") {
            return Err(invalid());
        }
    } else {
        expect_atom(&value[0], ":=", "pure pattern condition")?;
    }
    let pattern = parts.pop().expect("condition pattern");
    expect_atom(&parts[0], "let", "pattern condition keyword")?;
    Ok((pattern, value.pop().expect("condition expression"), monadic))
}

fn alternative(pattern: Syntax, body: Syntax) -> Syntax {
    Syntax::node(
        parser_kind(&["Term", "matchAlt"]),
        vec![atom("|"), null(vec![null(vec![pattern])]), atom("=>"), body],
    )
}

impl Context {
    pub(super) fn expand_do_pattern_condition(
        &mut self,
        pattern: Syntax,
        value: Syntax,
        monadic: bool,
        yes: Syntax,
        no: Syntax,
    ) -> Result<Syntax, NatDefinitionElabError> {
        self.tick()?;
        let (subject, action) = if monadic {
            let name = self.do_control_name()?;
            (name.clone(), Some((name, value)))
        } else {
            (value, None)
        };
        let candidate = Syntax::node(
            parser_kind(&["Term", "match"]),
            vec![
                atom("match"),
                null(vec![]),
                null(vec![]),
                null(vec![Syntax::node(
                    parser_kind(&["Term", "matchDiscr"]),
                    vec![null(vec![]), subject],
                )]),
                atom("with"),
                Syntax::node(
                    parser_kind(&["Term", "matchAlts"]),
                    vec![null(vec![
                        alternative(pattern, yes),
                        alternative(
                            Syntax::node(parser_kind(&["Term", "hole"]), vec![atom("_")]),
                            no,
                        ),
                    ])],
                ),
            ],
        );
        let body = self.lower_do_pattern_match(candidate)?;
        match action {
            Some((name, value)) => Ok(call(true, vec![value, lambda(name, null(vec![]), body)?])),
            None => Ok(body),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn term(kind: &str, args: Vec<Syntax>) -> Syntax {
        Syntax::node(parser_kind(&["Term", kind]), args)
    }
    fn named(name: &str) -> Syntax {
        ident(Name::from_components([name]))
    }
    fn condition(kind: &str, assignment: &str) -> Syntax {
        term(
            "doIfLet",
            vec![
                atom("let"),
                named("pattern"),
                term(kind, vec![atom(assignment), named("value")]),
            ],
        )
    }

    #[test]
    fn pure_and_monadic_headers_retain_their_distinct_meaning() {
        for (kind, symbol, monadic) in [
            ("doIfLetPure", ":=", false),
            ("doIfLetBind", "←", true),
            ("doIfLetBind", "<-", true),
        ] {
            assert_eq!(
                parts(condition(kind, symbol)).unwrap(),
                (named("pattern"), named("value"), monadic)
            );
        }
    }

    #[test]
    fn malformed_headers_never_drop_or_reinterpret_fields() {
        for (kind, assignment) in [
            ("doIfLetPure", "←"),
            ("doIfLetBind", ":="),
            ("doIfLetBind", "="),
            ("other", ":="),
        ] {
            assert!(parts(condition(kind, assignment)).is_err());
        }
        for index in [0, 2] {
            let mut input = condition("doIfLetPure", ":=");
            let Syntax::Node { args, .. } = &mut input else {
                unreachable!()
            };
            args[index] = Syntax::Missing;
            assert!(parts(input).is_err());
        }
        let mut input = condition("doIfLetPure", ":=");
        let Syntax::Node { args, .. } = &mut input else {
            unreachable!()
        };
        args.push(named("extra"));
        assert!(parts(input).is_err());
    }

    #[test]
    fn pattern_lowering_stops_at_the_existing_request_budget() {
        let mut context = Context::new(
            &Environment::new(),
            Budget::for_stack_bytes(2 * 1024 * 1024),
        );
        context.txn.budget.max_heartbeats = 1;
        assert!(matches!(
            context.expand_do_pattern_condition(
                named("pattern"),
                named("action"),
                true,
                named("yes"),
                named("no")
            ),
            Err(NatDefinitionElabError::Inference(
                SourceInferenceError::ResourceLimit
            ))
        ));
    }
}
