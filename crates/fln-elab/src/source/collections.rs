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
            || kind == &Name::from_components(["term_::_"])
            || kind == &parser_kind(&["Term", "tuple"])
    })
}

impl Context {
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
            if !expect_null_args(&args[1], "empty tuple optional body")?.is_empty() {
                return Err(failure(SourceInferenceError::Scope));
            }
            expect_atom(&args[2], ")", "empty tuple closer")?;
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
        let literal = kind == &Name::from_components(["term[_]"]);
        let mut args = std::mem::take(args);
        if literal {
            expect_atom(&args[0], "[", "list literal opener")?;
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
