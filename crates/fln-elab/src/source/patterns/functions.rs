//! Lambda patterns preserve the complete source telescope before destructuring.
use super::*;

/// Whether `syntax` is a lambda with an anonymous-constructor binder, which
/// [`Context::expand_fun_patterns`] rewrites.
pub(super) fn needs_expansion(syntax: &Syntax) -> bool {
    matches!(syntax, Syntax::Node { kind, args, .. }
        if kind == &parser_kind(&["Term", "fun"])
            && matches!(args.get(1), Some(Syntax::Node { kind, args: basic, .. })
                if kind == &parser_kind(&["Term", "basicFun"])
                    && matches!(basic.first(), Some(Syntax::Node { args: binders, .. })
                        if binders.iter().any(pattern_binder))))
}

/// An anonymous-constructor (`⟨a, b⟩`) or tuple (`(a, b)`) lambda binder. A binder is lowered as
/// a term before its lambda is rebuilt, so a tuple arrives here as its macro's
/// `_root_.Prod.mk a b` (`expandTuple`), itself the pattern the tuple stands for.
fn pattern_binder(binder: &Syntax) -> bool {
    binder.kind() == Some(&parser_kind(&["Term", "anonymousCtor"]))
        || binder.kind() == Some(&parser_kind(&["Term", "tuple"]))
        || matches!(binder, Syntax::Node { kind, args, .. }
            if kind == &parser_kind(&["Term", "app"])
                && matches!(args.first(), Some(Syntax::Ident { val, .. })
                    if *val == Name::from_components(["_root_", "Prod", "mk"])))
}

impl Context {
    /// `expandFunBinders` in the pin's `Lean/Elab/Binders.lean` retains ordinary
    /// binders and replaces each pattern by a fresh explicit parameter. Its
    /// matches surround the body, after *all* lambda parameters are in scope.
    /// In particular a pattern variable must not scope over a later parameter
    /// annotation, and implicit/instance parameters must not become explicit
    /// columns in a pattern function. Source annotations are never discarded.
    pub(super) fn expand_fun_patterns(
        &mut self,
        mut syntax: Syntax,
        pattern: bool,
    ) -> Result<Syntax, NatDefinitionElabError> {
        if pattern || !fun_patterns(&syntax) {
            return Ok(syntax);
        }
        let Syntax::Node { args, .. } = &mut syntax else {
            unreachable!("checked lambda");
        };
        if args.len() != 2 {
            return Err(invalid());
        }
        let basic = match &mut args[1] {
            Syntax::Node { args, .. } if args.len() == 4 => args,
            _ => return Err(invalid()),
        };
        // `fun x y : T => body` annotates every simple binder, not the
        // result. The pin does not apply that rule to pattern/group binders.
        // Leave it to the ordinary telescope's existing refusal, never erase T.
        if !expect_null_args(&basic[1], "lambda binder annotation")?.is_empty() {
            return Ok(syntax);
        }
        let Syntax::Node { args: binders, .. } = &mut basic[0] else {
            return Err(invalid());
        };
        let mut cases = Vec::new();
        for binder in binders {
            self.tick()?;
            if pattern_binder(binder) {
                let major = self.matrix_name()?;
                let case = std::mem::replace(binder, identifier(major.clone()));
                cases.push((major, case));
            }
        }
        let mut body = std::mem::replace(&mut basic[3], null(vec![]));
        // Nested matches follow binder order. Separate patterns therefore have
        // separate scopes, just as at the pin; a later pattern may shadow a
        // variable from an earlier one, but duplicates inside one still refuse.
        for (major, case) in cases.into_iter().rev() {
            self.tick()?;
            let matched = Syntax::node(
                parser_kind(&["Term", "match"]),
                vec![
                    atom("match"),
                    null(vec![]),
                    null(vec![]),
                    null(vec![Syntax::node(
                        parser_kind(&["Term", "matchDiscr"]),
                        vec![null(vec![]), identifier(major)],
                    )]),
                    atom("with"),
                    Syntax::node(
                        parser_kind(&["Term", "matchAlts"]),
                        vec![null(vec![Syntax::node(
                            parser_kind(&["Term", "matchAlt"]),
                            vec![atom("|"), null(vec![null(vec![case])]), atom("=>"), body],
                        )])],
                    ),
                ],
            );
            // The inside-out walk has already visited the lambda's children.
            // Lower just this generated match, retaining its coverage scope,
            // rather than recursively walking the growing body again.
            body = self.lower_do_pattern_match(matched)?;
        }
        basic[3] = body;
        Ok(syntax)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn context() -> Context {
        Context::new(
            &Environment::new(),
            Budget::for_stack_bytes(2 * 1024 * 1024),
        )
    }

    fn input() -> Syntax {
        let case = Syntax::node(
            parser_kind(&["Term", "anonymousCtor"]),
            vec![
                atom("⟨"),
                null(vec![identifier(Name::from_components(["x"]))]),
                atom("⟩"),
            ],
        );
        Syntax::node(
            parser_kind(&["Term", "fun"]),
            vec![
                atom("fun"),
                Syntax::node(
                    parser_kind(&["Term", "basicFun"]),
                    vec![
                        null(vec![case]),
                        null(vec![]),
                        atom("=>"),
                        identifier(Name::from_components(["x"])),
                    ],
                ),
            ],
        )
    }

    #[test]
    fn expansion_work_stops_are_typed_and_fresh_requests_recover() {
        for heartbeats in [1, 2, 3, 8] {
            let mut cx = context();
            cx.txn.budget.max_heartbeats = heartbeats;
            assert!(matches!(
                cx.expand_fun_patterns(input(), false),
                Err(NatDefinitionElabError::Inference(
                    SourceInferenceError::ResourceLimit
                ))
            ));
        }
        let mut unlimited = context();
        unlimited.txn.budget.max_heartbeats = 0;
        assert!(unlimited.expand_fun_patterns(input(), false).is_ok());
        assert_eq!(
            context().expand_fun_patterns(input(), false).unwrap(),
            context().expand_fun_patterns(input(), false).unwrap()
        );
    }

    #[test]
    fn shared_type_annotations_and_pattern_context_are_not_erased() {
        let mut annotated = input();
        let Syntax::Node { args, .. } = &mut annotated else {
            unreachable!()
        };
        let Syntax::Node { args: basic, .. } = &mut args[1] else {
            unreachable!()
        };
        basic[1] = null(vec![Syntax::node(
            parser_kind(&["Term", "typeSpec"]),
            vec![atom(":"), identifier(Name::from_components(["Nat"]))],
        )]);
        assert_eq!(
            context()
                .expand_fun_patterns(annotated.clone(), false)
                .unwrap(),
            annotated
        );
        assert_eq!(
            context().expand_fun_patterns(input(), true).unwrap(),
            input()
        );
    }
}
