//! Multi-arm do branches use the ordinary matrix compiler and its coverage
//! witnesses. Only branch sequencing is special: arm-local binders must never
//! enclose the shared suffix, and a match does not create a return/loop scope.
use super::*;

pub(super) struct MatchHeader {
    prefix: Vec<Syntax>,
    alternatives: Vec<Vec<Syntax>>,
    action: Option<(Syntax, Syntax)>,
}

pub(super) fn split(
    context: &mut Context,
    syntax: Syntax,
) -> Result<conditional::Branches, NatDefinitionElabError> {
    context.tick()?;
    let mut parts = node(syntax, "doMatch", 7)?;
    expect_atom(&parts[0], "match", "do match keyword")?;
    // The bounded source profile has no explicit dependent/generalizing/motive
    // switches. Refuse unsupported metadata instead of silently dropping it.
    for option in &parts[1..4] {
        expect_empty_null(option, "plain do match option")?;
    }
    expect_atom(&parts[5], "with", "do match alternatives keyword")?;
    let mut alternatives = node(parts.pop().expect("match alternatives"), "matchAlts", 1)?;
    let alternatives = children(alternatives.pop().expect("match rows"))?;
    if alternatives.is_empty() {
        return Err(invalid());
    }
    // Same arm ceiling as the existing checked match/matrix backend, before
    // allocating the parallel branch worklist or processing any arm.
    if alternatives.len() > 256 {
        return Err(failure(SourceInferenceError::ResourceLimit));
    }
    // Remove only the do-only dependent switch. Remaining fields have exactly
    // the ordinary match shape, including original discriminant proof binders.
    parts.remove(1);
    let mut action = None;
    let mut discriminants = children(std::mem::replace(&mut parts[3], Syntax::Missing))?;
    let arity = discriminants.len();
    for discriminant in discriminants.iter_mut().step_by(2) {
        context.tick()?;
        let mut fields = node(
            std::mem::replace(discriminant, Syntax::Missing),
            "matchDiscr",
            2,
        )?;
        if fields[1].kind() == Some(&parser_kind(&["Term", "nestedAction"])) {
            if arity != 1 {
                return Err(invalid());
            }
            let mut nested = node(fields.pop().expect("nested action"), "nestedAction", 2)?;
            let mut value = node(nested.pop().expect("monadic discriminant"), "doExpr", 1)?;
            if !matches!(&nested[0], Syntax::Atom { val, .. } if val == "←" || val == "<-") {
                return Err(invalid());
            }
            let name = context.do_control_name()?;
            fields.push(name.clone());
            action = Some((name, value.pop().expect("discriminant action")));
        }
        *discriminant = Syntax::node(parser_kind(&["Term", "matchDiscr"]), fields);
    }
    parts[3] = null(discriminants);
    let mut headers = Vec::with_capacity(alternatives.len());
    let mut arms = Vec::with_capacity(alternatives.len());
    for alternative in alternatives {
        context.tick()?;
        let mut row = node(alternative, "matchAlt", 4)?;
        expect_atom(&row[0], "|", "match alternative pipe")?;
        if !matches!(&row[2], Syntax::Atom { val, .. } if val == "=>" || val == "↦") {
            return Err(invalid());
        }
        arms.push(Some(row.pop().expect("branch sequence")));
        headers.push(row);
    }
    Ok(conditional::Branches {
        header: conditional::Header::Match(Box::new(MatchHeader {
            prefix: parts,
            alternatives: headers,
            action,
        })),
        arms,
    })
}

impl Context {
    pub(super) fn finish_do_match(
        &mut self,
        mut header: MatchHeader,
        bodies: Vec<Syntax>,
    ) -> Result<Syntax, NatDefinitionElabError> {
        if bodies.len() != header.alternatives.len() {
            return Err(invalid());
        }
        let mut alternatives = Vec::with_capacity(bodies.len());
        for (mut row, body) in header.alternatives.into_iter().zip(bodies) {
            self.tick()?;
            row.push(body);
            alternatives.push(Syntax::node(parser_kind(&["Term", "matchAlt"]), row));
        }
        header.prefix.push(Syntax::node(
            parser_kind(&["Term", "matchAlts"]),
            vec![null(alternatives)],
        ));
        let body = self
            .lower_do_pattern_match(Syntax::node(parser_kind(&["Term", "match"]), header.prefix))?;
        match header.action {
            Some((name, action)) => Ok(call(true, vec![action, lambda(name, null(vec![]), body)?])),
            None => Ok(body),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn term(label: &str, args: Vec<Syntax>) -> Syntax {
        Syntax::node(parser_kind(&["Term", label]), args)
    }
    fn named(label: &str) -> Syntax {
        ident(Name::from_components([label]))
    }
    fn action(label: &str) -> Syntax {
        term("doExpr", vec![named(label)])
    }
    fn returning(label: &str) -> Syntax {
        term("doReturn", vec![atom("return"), null(vec![named(label)])])
    }
    fn sequence(elements: Vec<Syntax>) -> Syntax {
        term(
            "doSeqIndent",
            vec![null(
                elements
                    .into_iter()
                    .map(|element| term("doSeqItem", vec![element, null(vec![])]))
                    .collect(),
            )],
        )
    }
    fn input(yes: Syntax, no: Syntax) -> Syntax {
        let alternative = |name: &str, body| {
            term(
                "matchAlt",
                vec![
                    atom("|"),
                    null(vec![null(vec![named(name)])]),
                    atom("=>"),
                    body,
                ],
            )
        };
        term(
            "doMatch",
            vec![
                atom("match"),
                null(vec![]),
                null(vec![]),
                null(vec![]),
                null(vec![term(
                    "matchDiscr",
                    vec![null(vec![]), named("subject")],
                )]),
                atom("with"),
                term(
                    "matchAlts",
                    vec![null(vec![
                        alternative("true", yes),
                        alternative("false", no),
                    ])],
                ),
            ],
        )
    }
    fn context() -> Context {
        Context::new(
            &Environment::new(),
            Budget::for_stack_bytes(2 * 1024 * 1024),
        )
    }
    fn count(syntax: &Syntax, name: &Name) -> usize {
        let mut pending = vec![syntax];
        let mut result = 0;
        while let Some(syntax) = pending.pop() {
            match syntax {
                Syntax::Ident { val, .. } if val == name => result += 1,
                Syntax::Node { args, .. } => pending.extend(args),
                _ => {}
            }
        }
        result
    }
    #[test]
    fn shared_suffix_and_original_branch_expressions_are_retained_once() {
        let input = sequence(vec![
            input(
                sequence(vec![action("first"), returning("early")]),
                sequence(vec![action("second"), action("third")]),
            ),
            action("suffix"),
        ]);
        let result = context().expand_do_sequence(input, None).unwrap();
        let parts = expect_node(
            &result,
            &parser_kind(&["Term", "nativeDoJoin"]),
            3,
            "match join",
        )
        .unwrap();
        assert_eq!(count(&parts[1], &Name::from_components(["suffix"])), 1);
        assert_eq!(count(&parts[2], &Name::from_components(["suffix"])), 0);
        for label in ["subject", "first", "early", "second", "third", "suffix"] {
            assert_eq!(count(&result, &Name::from_components([label])), 1);
        }
    }
    #[test]
    fn terminal_matches_keep_the_standard_match_arity_and_original_arm_order() {
        let mut context = context();
        let branches = split(
            &mut context,
            input(
                sequence(vec![returning("yes")]),
                sequence(vec![returning("no")]),
            ),
        )
        .unwrap();
        let result = context
            .finish_do_condition(branches.header, vec![named("yes"), named("no")])
            .unwrap();
        let parts = expect_node(
            &result,
            &parser_kind(&["Term", "match"]),
            6,
            "ordinary match",
        )
        .unwrap();
        let rows = expect_node(&parts[5], &parser_kind(&["Term", "matchAlts"]), 1, "rows").unwrap();
        let rows = expect_null_args(&rows[0], "rows").unwrap();
        for (row, body) in rows.iter().zip(["yes", "no"]) {
            let row = expect_node(row, &parser_kind(&["Term", "matchAlt"]), 4, "row").unwrap();
            assert_eq!(row[3], named(body));
        }
    }
    #[test]
    fn malformed_options_empty_arms_and_changed_arity_fail_closed() {
        let good = input(sequence(vec![action("yes")]), sequence(vec![action("no")]));
        for slot in 0..7 {
            let mut bad = good.clone();
            let Syntax::Node { args, .. } = &mut bad else {
                unreachable!()
            };
            args[slot] = Syntax::Missing;
            assert!(
                context()
                    .expand_do_sequence(sequence(vec![bad]), None)
                    .is_err(),
                "slot {slot}"
            );
        }
        let branches = split(&mut context(), good).unwrap();
        assert!(
            context()
                .finish_do_condition(branches.header, vec![named("only_one")])
                .is_err()
        );
        assert!(
            context()
                .expand_do_sequence(
                    sequence(vec![input(sequence(vec![]), sequence(vec![action("no")]))]),
                    None
                )
                .is_err()
        );
    }
    #[test]
    fn malformed_and_mixed_monadic_discriminants_are_not_discarded() {
        for arrow in ["=", ":=", "return"] {
            let mut bad = input(sequence(vec![action("yes")]), sequence(vec![action("no")]));
            let Syntax::Node { args, .. } = &mut bad else {
                unreachable!()
            };
            args[4] = null(vec![term(
                "matchDiscr",
                vec![
                    null(vec![]),
                    term("nestedAction", vec![atom(arrow), action("fetch")]),
                ],
            )]);
            assert!(split(&mut context(), bad).is_err());
        }
        let mut bad = input(sequence(vec![action("yes")]), sequence(vec![action("no")]));
        let Syntax::Node { args, .. } = &mut bad else {
            unreachable!()
        };
        args[4] = null(vec![
            term(
                "matchDiscr",
                vec![
                    null(vec![]),
                    term("nestedAction", vec![atom("←"), action("fetch")]),
                ],
            ),
            atom(","),
            term("matchDiscr", vec![null(vec![]), named("other")]),
        ]);
        assert!(split(&mut context(), bad).is_err());
    }
    #[test]
    fn request_budget_and_existing_arm_limit_apply_before_expansion() {
        let good = input(sequence(vec![action("yes")]), sequence(vec![action("no")]));
        let mut stopped = context();
        stopped.txn.budget.max_heartbeats = 1;
        assert!(matches!(
            split(&mut stopped, good.clone()),
            Err(NatDefinitionElabError::Inference(
                SourceInferenceError::ResourceLimit
            ))
        ));
        let mut wide = good.clone();
        let Syntax::Node { args, .. } = &mut wide else {
            unreachable!()
        };
        args[6] = term("matchAlts", vec![null(vec![Syntax::Missing; 257])]);
        assert!(matches!(
            split(&mut context(), wide),
            Err(NatDefinitionElabError::Inference(
                SourceInferenceError::ResourceLimit
            ))
        ));
        assert!(
            context()
                .expand_do_sequence(sequence(vec![good]), None)
                .is_ok()
        );
    }
    #[test]
    fn deeply_nested_matches_keep_linear_syntax_and_do_not_recurse_in_rust() {
        let mut nested = input(
            sequence(vec![returning("early")]),
            sequence(vec![action("leaf")]),
        );
        for _ in 0..800 {
            nested = input(
                sequence(vec![nested, action("inner_suffix")]),
                sequence(vec![action("other")]),
            );
        }
        let result = context()
            .expand_do_sequence(sequence(vec![nested, action("outer_suffix")]), None)
            .unwrap();
        assert_eq!(
            count(&result, &Name::from_components(["inner_suffix"])),
            800
        );
        assert_eq!(count(&result, &Name::from_components(["outer_suffix"])), 1);
        let mut pending = vec![&result];
        let mut n = 0;
        while let Some(syntax) = pending.pop() {
            n += 1;
            if let Syntax::Node { args, .. } = syntax {
                pending.extend(args);
            }
        }
        assert!(n < 801 * 150, "nonlinear output: {n}");
    }
}
