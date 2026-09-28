//! Immutable monadic pattern bindings reuse the ordinary checked matcher.
//!
//! The action occurs once, outside the pattern match. A fresh, unspellable
//! lambda parameter owns its result; neither a failed monadic action nor an
//! unselected constructor can evaluate the source continuation. This module
//! generates syntax only. Coverage, annotations and both admission checkers
//! retain their ordinary authority.
use super::*;

impl Context {
    /// A generated do-binding match is created after the inside-out source
    /// walk has visited its children. Compile it here exactly once, rather than
    /// recursively replaying that walk or bypassing matrix coverage witnesses.
    fn lower_do_binding_pattern(
        &mut self,
        pattern: Syntax,
        subject: Syntax,
        body: Syntax,
    ) -> Result<Syntax, NatDefinitionElabError> {
        self.tick()?;
        let alternative = Syntax::node(
            parser_kind(&["Term", "matchAlt"]),
            vec![atom("|"), null(vec![null(vec![pattern])]), atom("=>"), body],
        );
        let syntax = Syntax::node(
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
                    vec![null(vec![alternative])],
                ),
            ],
        );
        self.lower_do_pattern_match(syntax)
    }

    pub(super) fn expand_do_pattern_binding(
        &mut self,
        declaration: Syntax,
        body: Syntax,
    ) -> Result<Syntax, NatDefinitionElabError> {
        self.tick()?;
        let mut parts = node(declaration, "doPatDecl", 5)?;
        let fallback = parts.pop().expect("validated pattern fallback");
        // Refutable patterns with an explicit failure branch require control
        // flow handling. Never discard that branch or manufacture a default.
        expect_empty_null(&fallback, "unsupported pattern-bind failure branch")?;
        let mut action = node(parts.pop().expect("validated pattern action"), "doExpr", 1)?;
        let arrow = parts.pop().expect("validated pattern arrow");
        if !matches!(&arrow, Syntax::Atom { val, .. } if val == "←" || val == "<-") {
            return Err(invalid());
        }
        let annotation = parts.pop().expect("validated pattern annotation");
        let pattern = parts.pop().expect("validated pattern");
        let subject = self.do_control_name()?;
        let body = self.lower_do_binding_pattern(pattern, subject.clone(), body)?;
        Ok(call(
            true,
            vec![
                action.pop().expect("validated action expression"),
                lambda(subject, annotation, body)?,
            ],
        ))
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

    fn context() -> Context {
        Context::new(
            &Environment::new(),
            Budget::for_stack_bytes(2 * 1024 * 1024),
        )
    }

    fn declaration(pattern: Syntax) -> Syntax {
        term(
            "doPatDecl",
            vec![
                pattern,
                null(vec![]),
                atom("←"),
                term("doExpr", vec![named("action")]),
                null(vec![]),
            ],
        )
    }

    fn count_name(syntax: &Syntax, name: &Name) -> usize {
        let mut pending = vec![syntax];
        let mut count = 0;
        while let Some(syntax) = pending.pop() {
            match syntax {
                Syntax::Ident { val, .. } if val == name => count += 1,
                Syntax::Node { args, .. } => pending.extend(args),
                _ => {}
            }
        }
        count
    }

    #[test]
    fn wildcard_binding_retains_one_action_and_one_continuation() {
        let actual = context()
            .expand_do_pattern_binding(
                declaration(term("hole", vec![atom("_")])),
                named("continuation"),
            )
            .unwrap();
        assert_eq!(actual.kind(), Some(&parser_kind(&["Term", "nativeDoBind"])));
        for name in ["action", "continuation"] {
            assert_eq!(count_name(&actual, &Name::from_components([name])), 1);
        }
    }

    #[test]
    fn generated_subject_cannot_capture_a_source_identifier() {
        let actual = context()
            .expand_do_pattern_binding(declaration(named("x")), named("x"))
            .unwrap();
        let parts = expect_node(
            &actual,
            &parser_kind(&["Term", "nativeDoBind"]),
            2,
            "test bind",
        )
        .unwrap();
        let fun = expect_node(&parts[1], &parser_kind(&["Term", "fun"]), 2, "test lambda").unwrap();
        let fun = expect_node(
            &fun[1],
            &parser_kind(&["Term", "basicFun"]),
            4,
            "test lambda body",
        )
        .unwrap();
        let binders = expect_null_args(&fun[0], "test binders").unwrap();
        assert!(matches!(&binders[0], Syntax::Ident { val, .. }
            if val == &Name::num(Name::anonymous(), 0)));
    }

    #[test]
    fn malformed_nodes_and_unhandled_fallbacks_are_not_erased() {
        let original = declaration(term("hole", vec![atom("_")]));
        for (index, replacement) in [
            (1, named("notAnAnnotation")),
            (2, atom(":=")),
            (3, named("notADoElement")),
            (4, null(vec![atom("|"), named("uncheckedFallback")])),
        ] {
            let mut syntax = original.clone();
            let Syntax::Node { args, .. } = &mut syntax else {
                unreachable!()
            };
            args[index] = replacement;
            assert!(
                context()
                    .expand_do_pattern_binding(syntax, named("continuation"))
                    .is_err()
            );
        }
        let missing_field = term("doPatDecl", vec![]);
        assert!(
            context()
                .expand_do_pattern_binding(missing_field, named("continuation"))
                .is_err()
        );
    }
}
