//! Native collection notation expands to ordinary source applications.
//!
//! No declaration, type, recursor, or proof is created here. Existing implicit
//! inference, constructor typing, pattern coverage and both admission seats
//! remain authoritative. Traversal and list construction use explicit stacks.
use super::*;
use fln_syntax::source::{ByteSpan, SourceInfo};

fn null(args: Vec<Syntax>) -> Syntax {
    Syntax::node(Name::from_components(["null"]), args)
}
fn atom(text: &str) -> Syntax {
    Syntax::atom(SourceInfo::None, text)
}
fn constructor(label: &str) -> Syntax {
    Syntax::Ident {
        info: SourceInfo::None,
        raw_val: ByteSpan::default(),
        // Notation refers to the root constructor, even inside a namespace
        // defining its own List or an opened namespace containing cons/nil.
        val: Name::from_components(["_root_", "List", label]),
        preresolved: Vec::new(),
    }
}
fn application(head: Syntax, arguments: Vec<Syntax>) -> Syntax {
    Syntax::node(parser_kind(&["Term", "app"]), vec![head, null(arguments)])
}
fn nil(pattern: bool) -> Syntax {
    let head = constructor("nil");
    if pattern {
        return head;
    }
    // Force a type argument even when no expected type is available. Leaving
    // bare List.nil here could silently turn [] into an unapplied polymorphic
    // function under the bounded source frontend's implicit insertion policy.
    application(
        Syntax::node(parser_kind(&["Term", "explicit"]), vec![atom("@"), head]),
        vec![Syntax::node(
            parser_kind(&["Term", "hole"]),
            vec![atom("_")],
        )],
    )
}
fn cons(head: Syntax, tail: Syntax) -> Syntax {
    application(constructor("cons"), vec![head, tail])
}

pub(super) fn is_notation(syntax: &Syntax) -> bool {
    syntax.kind().is_some_and(|kind| {
        kind == &Name::from_components(["term[_]"])
            || kind == &Name::from_components(["term#[_,]"])
            || kind == &Name::from_components(["term{_:_//_}"])
            || kind == &Name::from_components(["term_::_"])
            || kind == &parser_kind(&["Term", "tuple"])
    })
}

/// `{x // p}` is `Subtype (fun (x : _) => p)` and `{x : T // p}` is `Subtype (fun (x : T) =>
/// p)`, the macro's quoted `Subtype` resolved where it is defined (`Init/Core.lean`). Not a
/// pattern here.
fn expand_subtype(args: Vec<Syntax>, pattern: bool) -> Result<Syntax, NatDefinitionElabError> {
    if pattern {
        return Err(failure(SourceInferenceError::Scope));
    }
    let Ok([open, name, type_, separator, predicate, close]) = <[Syntax; 6]>::try_from(args) else {
        return Err(failure(SourceInferenceError::Scope));
    };
    expect_atom(&open, "{", "subtype opener")?;
    expect_atom(&separator, "//", "subtype separator")?;
    expect_atom(&close, "}", "subtype closer")?;
    if !matches!(name, Syntax::Ident { .. }) {
        return Err(failure(SourceInferenceError::Scope));
    }
    let annotation = match expect_null_args(&type_, "subtype binder type")? {
        [] => null(Vec::new()),
        [colon, domain] => {
            expect_atom(colon, ":", "subtype binder colon")?;
            null(vec![Syntax::node(
                parser_kind(&["Term", "typeSpec"]),
                vec![atom(":"), domain.clone()],
            )])
        }
        _ => return Err(failure(SourceInferenceError::Scope)),
    };
    let lambda = Syntax::node(
        parser_kind(&["Term", "fun"]),
        vec![
            atom("fun"),
            Syntax::node(
                parser_kind(&["Term", "basicFun"]),
                vec![null(vec![name]), annotation, atom("=>"), predicate],
            ),
        ],
    );
    let head = Syntax::Ident {
        info: SourceInfo::None,
        raw_val: ByteSpan::default(),
        val: Name::from_components(["_root_", "Subtype"]),
        preresolved: Vec::new(),
    };
    Ok(application(head, vec![lambda]))
}

fn pair(first: Syntax, second: Syntax) -> Syntax {
    let head = Syntax::Ident {
        info: SourceInfo::None,
        raw_val: ByteSpan::default(),
        // The macro's quoted `Prod.mk` is resolved where the macro is defined.
        val: Name::from_components(["_root_", "Prod", "mk"]),
        preresolved: Vec::new(),
    };
    application(head, vec![first, second])
}

impl Context {
    /// A tuple's body `[e "," [es,*]]` as `mkPairs` builds it (`expandTuple`,
    /// `Lean/Elab/BuiltinNotation.lean:414`): `Prod.mk e₀ (Prod.mk e₁ … eₙ)`, nested right.
    fn expand_pairs(&mut self, mut body: Syntax) -> Result<Syntax, NatDefinitionElabError> {
        let parts = expect_null_args(&body, "tuple body")?;
        let [_, separator, rest] = parts else {
            return Err(failure(SourceInferenceError::Scope));
        };
        expect_atom(separator, ",", "tuple separator")?;
        // `sepBy1 term ", " (allowTrailingSep := true)`: terms at even positions, at least one.
        let rest = expect_null_args(rest, "tuple elements")?;
        if rest.is_empty() {
            return Err(failure(SourceInferenceError::Scope));
        }
        for (index, element) in rest.iter().enumerate() {
            self.tick()?;
            if index % 2 == 1 {
                expect_atom(element, ",", "tuple separator")?;
            }
        }
        let Syntax::Node { args: parts, .. } = &mut body else {
            return Err(failure(SourceInferenceError::Scope));
        };
        let mut rest = parts.pop().expect("validated tuple elements");
        let first = parts.swap_remove(0);
        let Syntax::Node { args: rest, .. } = &mut rest else {
            return Err(failure(SourceInferenceError::Scope));
        };
        let mut elements: Vec<Syntax> = std::mem::take(rest).into_iter().step_by(2).collect();
        elements.insert(0, first);
        let mut tuple = elements.pop().expect("a tuple has two elements");
        while let Some(element) = elements.pop() {
            self.tick()?;
            tuple = pair(element, tuple);
        }
        Ok(tuple)
    }

    /// Called by the existing inside-out pattern-planning traversal. Children
    /// are already lowered; the pattern flag comes from matchAlt's pattern slot.
    /// This leaves that traversal's recursion-root and source-row witnesses intact.
    pub(super) fn expand_collection_node(
        &mut self,
        mut syntax: Syntax,
        pattern: bool,
    ) -> Result<Syntax, NatDefinitionElabError> {
        if !is_notation(&syntax) {
            return Ok(syntax);
        }
        let Syntax::Node { kind, args, .. } = &mut syntax else {
            return Err(failure(SourceInferenceError::Scope));
        };
        if kind == &Name::from_components(["term{_:_//_}"]) {
            return expand_subtype(std::mem::take(args), pattern);
        }
        if args.len() != 3 {
            return Err(failure(SourceInferenceError::Scope));
        }
        if kind == &parser_kind(&["Term", "tuple"]) {
            let opener = expect_node(
                &args[0],
                &parser_kind(&["Term", "hygienicLParen"]),
                2,
                "empty tuple hygienic opener",
            )?;
            expect_atom(&opener[0], "(", "empty tuple opener")?;
            let hygiene = expect_node(
                &opener[1],
                &Name::from_components(["hygieneInfo"]),
                1,
                "empty tuple hygiene information",
            )?;
            if !matches!(hygiene, [Syntax::Ident { val, .. }] if val.is_anonymous()) {
                return Err(failure(SourceInferenceError::Scope));
            }
            expect_atom(&args[2], ")", "empty tuple closer")?;
            if !expect_null_args(&args[1], "tuple optional body")?.is_empty() {
                return self.expand_pairs(std::mem::replace(&mut args[1], null(Vec::new())));
            }
            // The pinned expandTuple macro chooses Unit.unit, whose universe
            // is fixed. A generic PUnit.unit would accept additional types.
            // Root qualification preserves that macro reference under local
            // binders and namespaces; ordinary constant checking still applies.
            return Ok(Syntax::Ident {
                info: SourceInfo::None,
                raw_val: ByteSpan::default(),
                val: Name::from_components(["_root_", "Unit", "unit"]),
                preresolved: Vec::new(),
            });
        }
        // `#[a, b]` is `List.toArray [a, b]` (`Init/Data/Array/Basic.lean`); not a pattern here.
        let array = kind == &Name::from_components(["term#[_,]"]);
        if array && pattern {
            return Err(failure(SourceInferenceError::Scope));
        }
        let literal = array || kind == &Name::from_components(["term[_]"]);
        let mut args = std::mem::take(args);
        if literal {
            expect_atom(
                &args[0],
                if array { "#[" } else { "[" },
                "list literal opener",
            )?;
            expect_atom(&args[2], "]", "list literal closer")?;
            // Validate separators before taking ownership. A hand-constructed
            // malformed tree must not hide a term in a separator slot.
            let elements = expect_null_args(&args[1], "list elements")?;
            for (index, element) in elements.iter().enumerate() {
                self.tick()?;
                if index % 2 == 1 {
                    expect_atom(element, ",", "list element separator")?;
                }
            }
            let mut sequence = args.swap_remove(1);
            let Syntax::Node { args: elements, .. } = &mut sequence else {
                return Err(failure(SourceInferenceError::Scope));
            };
            let mut tail = nil(pattern);
            // Element positions stay even, also with a trailing comma. Reverse
            // folding preserves source order without host-language recursion.
            for (index, element) in std::mem::take(elements).into_iter().enumerate().rev() {
                self.tick()?;
                if index % 2 == 0 {
                    tail = cons(element, tail);
                }
            }
            if array {
                let to_array = Syntax::Ident {
                    info: SourceInfo::None,
                    raw_val: ByteSpan::default(),
                    // The macro's quoted `List.toArray` is resolved where it is defined.
                    val: Name::from_components(["_root_", "List", "toArray"]),
                    preresolved: Vec::new(),
                };
                return Ok(application(to_array, vec![tail]));
            }
            Ok(tail)
        } else {
            expect_atom(&args[1], "::", "list cons operator")?;
            let tail = args.pop().expect("validated cons tail");
            let _separator = args.pop().expect("validated cons separator");
            let head = args.pop().expect("validated cons head");
            Ok(cons(head, tail))
        }
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
    fn literal(elements: Vec<Syntax>) -> Syntax {
        Syntax::node(
            Name::from_components(["term[_]"]),
            vec![atom("["), null(elements), atom("]")],
        )
    }
    fn number(n: &str) -> Syntax {
        Syntax::node(Name::from_components(["num"]), vec![atom(n)])
    }

    fn empty_tuple() -> Syntax {
        let hygiene = Syntax::node(
            Name::from_components(["hygieneInfo"]),
            vec![Syntax::Ident {
                info: SourceInfo::None,
                raw_val: ByteSpan::default(),
                val: Name::anonymous(),
                preresolved: Vec::new(),
            }],
        );
        Syntax::node(
            parser_kind(&["Term", "tuple"]),
            vec![
                Syntax::node(
                    parser_kind(&["Term", "hygienicLParen"]),
                    vec![atom("("), hygiene],
                ),
                null(vec![]),
                atom(")"),
            ],
        )
    }

    #[test]
    fn empty_tuple_expands_to_the_fixed_global_unit_constant() {
        let expanded = context()
            .expand_collection_node(empty_tuple(), false)
            .unwrap();
        assert!(matches!(&expanded, Syntax::Ident { val, .. }
            if val == &Name::from_components(["_root_", "Unit", "unit"])));
    }

    #[test]
    fn empty_tuple_expansion_cannot_discard_a_body_or_malformed_delimiters() {
        for replacement in [number("42"), null(vec![number("42")])] {
            let mut tuple = empty_tuple();
            let Syntax::Node { args, .. } = &mut tuple else {
                unreachable!();
            };
            args[1] = replacement;
            assert!(context().expand_collection_node(tuple, false).is_err());
        }
        for index in [0, 2] {
            let mut tuple = empty_tuple();
            let Syntax::Node { args, .. } = &mut tuple else {
                unreachable!();
            };
            args[index] = atom("not a delimiter");
            assert!(context().expand_collection_node(tuple, false).is_err());
        }
        let mut tuple = empty_tuple();
        let Syntax::Node { args, .. } = &mut tuple else {
            unreachable!();
        };
        let Syntax::Node { args, .. } = &mut args[0] else {
            unreachable!();
        };
        args[1] = null(vec![]);
        assert!(context().expand_collection_node(tuple, false).is_err());
    }

    fn tuple(body: Vec<Syntax>) -> Syntax {
        let mut tuple = empty_tuple();
        let Syntax::Node { args, .. } = &mut tuple else {
            unreachable!();
        };
        args[1] = null(body);
        tuple
    }

    /// `Prod.mk head tail`, or `None` for anything else.
    fn pair_parts(syntax: &Syntax) -> Option<(&Syntax, &Syntax)> {
        let Syntax::Node { kind, args, .. } = syntax else {
            return None;
        };
        if kind != &parser_kind(&["Term", "app"]) {
            return None;
        }
        let Syntax::Ident { val, .. } = &args[0] else {
            return None;
        };
        if val != &Name::from_components(["_root_", "Prod", "mk"]) {
            return None;
        }
        match expect_null_args(&args[1], "pair arguments").ok()? {
            [head, tail] => Some((head, tail)),
            _ => None,
        }
    }

    #[test]
    fn a_tuple_expands_to_right_nested_root_pairs() {
        let body = || {
            vec![
                number("1"),
                atom(","),
                null(vec![number("2"), atom(","), number("3")]),
            ]
        };
        let expanded = context()
            .expand_collection_node(tuple(body()), false)
            .unwrap();
        let (first, rest) = pair_parts(&expanded).expect("an outer pair");
        assert_eq!(first, &number("1"));
        let (second, third) = pair_parts(rest).expect("an inner pair");
        assert_eq!((second, third), (&number("2"), &number("3")));
        // A trailing comma adds no element.
        let trailing = vec![number("1"), atom(","), null(vec![number("2"), atom(",")])];
        let expanded = context()
            .expand_collection_node(tuple(trailing), false)
            .unwrap();
        assert_eq!(pair_parts(&expanded), Some((&number("1"), &number("2"))));
    }

    #[test]
    fn a_malformed_tuple_body_is_refused_not_reinterpreted() {
        for body in [
            vec![number("1")],
            vec![number("1"), atom(",")],
            vec![number("1"), atom(","), null(vec![])],
            vec![number("1"), atom(";"), null(vec![number("2")])],
            vec![number("1"), atom(","), null(vec![number("2"), number("3")])],
            vec![number("1"), atom(","), number("2")],
        ] {
            assert!(
                context()
                    .expand_collection_node(tuple(body), false)
                    .is_err()
            );
        }
    }

    #[test]
    fn term_nil_has_a_type_hole_but_pattern_nil_has_no_hidden_field() {
        let mut context = context();
        let term = context
            .expand_collection_node(literal(vec![]), false)
            .unwrap();
        let pattern = context
            .expand_collection_node(literal(vec![]), true)
            .unwrap();
        assert_eq!(term.kind(), Some(&parser_kind(&["Term", "app"])));
        assert_eq!(pattern, constructor("nil"));
        assert_ne!(term, pattern);
    }

    #[test]
    fn list_expansion_keeps_order_with_or_without_a_trailing_comma() {
        let mut context = context();
        for trailing in [false, true] {
            let mut elements = vec![number("1"), atom(","), number("2")];
            if trailing {
                elements.push(atom(","));
            }
            for pattern in [false, true] {
                let actual = context
                    .expand_collection_node(literal(elements.clone()), pattern)
                    .unwrap();
                assert_eq!(actual, cons(number("1"), cons(number("2"), nil(pattern))));
            }
        }
    }

    #[test]
    fn malformed_external_syntax_cannot_hide_an_element_as_a_separator() {
        let mut context = context();
        for elements in [
            vec![number("1"), number("2")],
            vec![number("1"), atom(";"), number("2")],
            vec![number("1"), number("2"), number("3"), atom(",")],
        ] {
            assert!(
                context
                    .expand_collection_node(literal(elements), false)
                    .is_err()
            );
        }
        let cons = |args| Syntax::node(Name::from_components(["term_::_"]), args);
        for syntax in [
            cons(vec![]),
            cons(vec![number("1"), atom("++"), literal(vec![])]),
            Syntax::node(
                Name::from_components(["term[_]"]),
                vec![atom("["), null(vec![])],
            ),
        ] {
            assert!(context.expand_collection_node(syntax, false).is_err());
        }
    }
}
