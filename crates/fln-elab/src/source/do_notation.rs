//! Native expansion of immutable sequential do notation.
//!
//! No monad implementation lives here. The resulting Bind.bind / Pure.pure
//! calls use ordinary universe inference, typed implicit arguments and instance
//! search. Continuations are real lambdas, so actions are never duplicated or
//! eagerly evaluated by the frontend. Final declarations still face both judges.
use super::*;
mod conditional;
mod control;
mod for_loop;
mod returns;
pub(super) use returns::join_parts;
mod unless;

fn null(args: Vec<Syntax>) -> Syntax {
    Syntax::node(Name::from_components(["null"]), args)
}
fn atom(s: &str) -> Syntax {
    Syntax::Atom {
        info: fln_syntax::source::SourceInfo::None,
        val: s.to_owned(),
    }
}
fn ident(name: Name) -> Syntax {
    Syntax::Ident {
        info: fln_syntax::source::SourceInfo::None,
        raw_val: fln_syntax::source::ByteSpan::empty_at(fln_syntax::source::BytePos(0)),
        val: name,
        preresolved: Vec::new(),
    }
}
fn invalid() -> NatDefinitionElabError {
    failure(SourceInferenceError::Scope)
}
fn take(
    mut syntax: Syntax,
    kind: Name,
    count: Option<usize>,
) -> Result<Vec<Syntax>, NatDefinitionElabError> {
    let Syntax::Node {
        kind: actual, args, ..
    } = &mut syntax
    else {
        return Err(invalid());
    };
    if *actual != kind || count.is_some_and(|n| n != args.len()) {
        return Err(invalid());
    }
    Ok(std::mem::take(args))
}
fn node(syntax: Syntax, kind: &str, count: usize) -> Result<Vec<Syntax>, NatDefinitionElabError> {
    take(syntax, parser_kind(&["Term", kind]), Some(count))
}
fn children(syntax: Syntax) -> Result<Vec<Syntax>, NatDefinitionElabError> {
    take(syntax, Name::from_components(["null"]), None)
}
fn sequence_items(sequence: Syntax) -> Result<Vec<Syntax>, NatDefinitionElabError> {
    if sequence.kind() == Some(&parser_kind(&["Term", "doSeqBracketed"])) {
        let mut parts = node(sequence, "doSeqBracketed", 3)?;
        expect_atom(&parts[0], "{", "do opening brace")?;
        expect_atom(&parts[2], "}", "do closing brace")?;
        children(parts.remove(1))
    } else {
        let mut parts = node(sequence, "doSeqIndent", 1)?;
        children(parts.pop().expect("sequence items"))
    }
}
fn call(bind: bool, arguments: Vec<Syntax>) -> Syntax {
    // These internal nodes preserve the expected monad before type conversion
    // unfolds aliases such as Id. They do not name user-overridable globals.
    Syntax::node(
        parser_kind(&["Term", if bind { "nativeDoBind" } else { "nativeDoPure" }]),
        arguments,
    )
}

fn unit_annotation() -> Syntax {
    null(vec![Syntax::node(
        parser_kind(&["Term", "typeSpec"]),
        vec![atom(":"), ident(Name::from_components(["_root_", "PUnit"]))],
    )])
}

fn lambda(
    name: Syntax,
    annotation: Syntax,
    body: Syntax,
) -> Result<Syntax, NatDefinitionElabError> {
    let annotation = children(annotation)?;
    let binder = if annotation.is_empty() {
        name
    } else {
        let mut annotation = annotation;
        if annotation.len() != 1 {
            return Err(invalid());
        }
        let mut specification = node(annotation.pop().expect("single type"), "typeSpec", 2)?;
        let type_ = specification.pop().expect("annotation type");
        expect_atom(&specification[0], ":", "do binding type")?;
        Syntax::node(
            parser_kind(&["Term", "typeAscription"]),
            vec![
                Syntax::node(
                    parser_kind(&["Term", "hygienicLParen"]),
                    vec![
                        atom("("),
                        Syntax::node(
                            Name::from_components(["hygieneInfo"]),
                            vec![ident(Name::anonymous())],
                        ),
                    ],
                ),
                name,
                atom(":"),
                null(vec![type_]),
                atom(")"),
            ],
        )
    };
    Ok(Syntax::node(
        parser_kind(&["Term", "fun"]),
        vec![
            atom("fun"),
            Syntax::node(
                parser_kind(&["Term", "basicFun"]),
                vec![null(vec![binder]), null(vec![]), atom("=>"), body],
            ),
        ],
    ))
}

// A conditional inside a loop forwards a tagged exit until the loop-level
// join unwraps it. `allow_return` is independent: an ordinary nested do owns
// its return scope, but a conditional branch does not introduce a new one.
#[derive(Clone, Copy)]
struct SequenceScope<'a> {
    targets: Option<&'a control::LoopTargets>,
    signal: bool,
    require_unit: bool,
    allow_return: bool,
}

fn sequence_element(statement: Syntax) -> Result<Syntax, NatDefinitionElabError> {
    let mut item = node(statement, "doSeqItem", 2)?;
    let separators = children(item.pop().expect("optional semicolon"))?;
    match separators.as_slice() {
        [] => {}
        [separator] => {
            expect_atom(separator, ";", "do separator")?;
        }
        _ => return Err(invalid()),
    }
    item.pop().ok_or_else(invalid)
}

impl Context {
    fn do_control_name(&mut self) -> Result<Syntax, NatDefinitionElabError> {
        let serial = self.next;
        self.fresh_name()?;
        Ok(ident(Name::num(Name::anonymous(), serial)))
    }

    pub(super) fn do_monad(
        &mut self,
        type_: &Expr,
    ) -> Result<Option<Expr>, NatDefinitionElabError> {
        let mut type_ = self.instantiate(type_)?;
        loop {
            self.tick()?;
            match type_.node() {
                ExprNode::App { f, .. } => return Ok(Some(f.clone())),
                ExprNode::MData { expr, .. } => type_ = expr.clone(),
                ExprNode::LetE { body, value, .. } => type_ = self.substitute(body, value)?,
                _ => return Ok(None),
            }
        }
    }

    /// Specialize the ordinary operation's monad argument before inserting
    /// its dictionary and element-type holes. This is a typed application, not
    /// an injectivity assumption about an unknown higher-kinded function.
    pub(super) fn do_operation(
        &mut self,
        bind: bool,
        monad: Option<Expr>,
    ) -> Result<Typed, NatDefinitionElabError> {
        let name = if bind {
            Name::from_components(["Bind", "bind"])
        } else {
            Name::from_components(["Pure", "pure"])
        };
        let mut function = self.constant(&name)?;
        if let Some(monad) = monad {
            function.type_ = self.whnf(&function.type_)?;
            let ExprNode::ForallE {
                binder_type, body, ..
            } = function.type_.node()
            else {
                return Err(failure(SourceInferenceError::ExpectedFunction));
            };
            let actual = self
                .known_type(&monad)?
                .ok_or_else(|| failure(SourceInferenceError::ExpectedType))?;
            self.constrain_type(&actual, binder_type)?;
            let type_ = self.substitute(body, &monad)?;
            function = Typed {
                value: Expr::app(function.value, monad),
                type_,
            };
        }
        Ok(function)
    }

    /// Preserve the written result parameter of a monadic expected type before
    /// conversion can erase it. A monad need not be injective in its argument;
    /// this is a checked choice of Pure's value domain, not an equality theorem.
    pub(super) fn do_pure_result(
        &mut self,
        function: Typed,
        expected: Option<&Expr>,
    ) -> Result<Typed, NatDefinitionElabError> {
        let Some(expected) = expected else {
            return Ok(function);
        };
        let expected = self.instantiate(expected)?;
        let ExprNode::App { a: result, .. } = expected.node() else {
            return Ok(function);
        };
        let function = self.insert_implicits(function, ImplicitInsertion::ExplicitArgument)?;
        let function = self.coerce_function(function)?;
        let ExprNode::ForallE { binder_type, .. } = function.type_.node() else {
            return Err(failure(SourceInferenceError::ExpectedFunction));
        };
        self.constrain_type(binder_type, result)?;
        Ok(function)
    }

    pub(super) fn do_action(&mut self, action: Typed) -> Result<Typed, NatDefinitionElabError> {
        let monad = self.do_monad(&action.type_)?;
        let function = self.do_operation(true, monad)?;
        let function = self.insert_implicits(function, ImplicitInsertion::ExplicitArgument)?;
        let function = self.coerce_function(function)?;
        let ExprNode::ForallE {
            binder_type, body, ..
        } = function.type_.node()
        else {
            return Err(failure(SourceInferenceError::ExpectedFunction));
        };
        let action = self.finish_term(action, Some(binder_type))?;
        let type_ = self.substitute(body, &action.value)?;
        Ok(Typed {
            value: Expr::app(function.value, action.value),
            type_,
        })
    }

    pub(super) fn expand_do_node(
        &mut self,
        syntax: Syntax,
        pattern: bool,
    ) -> Result<Syntax, NatDefinitionElabError> {
        if syntax.kind() == Some(&parser_kind(&["Term", "doUnless"])) {
            if pattern {
                return Err(invalid());
            }
            self.tick()?;
            return unless::expand(syntax);
        }
        if syntax.kind() == Some(&parser_kind(&["Term", "doFor"])) {
            if pattern {
                return Err(invalid());
            }
            return self.expand_for_loop(syntax);
        }
        if syntax.kind() != Some(&parser_kind(&["Term", "do"])) {
            return Ok(syntax);
        }
        if pattern {
            return Err(invalid());
        }
        let mut parts = node(syntax, "do", 2)?;
        let sequence = parts.pop().expect("do sequence");
        expect_atom(&parts[0], "do", "do keyword")?;
        self.expand_do_sequence(sequence, None)
    }

    // The top-level sequence and conditional branches share the same statement
    // rules. Only the control-result shape differs inside a branch.
    fn expand_do_sequence(
        &mut self,
        sequence: Syntax,
        mut result: Option<Syntax>,
    ) -> Result<Syntax, NatDefinitionElabError> {
        if result.is_none() && self.has_branch_return(&sequence)? {
            return self.expand_returning_sequence(sequence);
        }
        let targets = result.as_ref().map(control::LoopTargets::new).transpose()?;
        let scope = SequenceScope {
            targets: targets.as_ref(),
            signal: false,
            require_unit: result.is_some(),
            allow_return: targets.is_none(),
        };
        let statements = sequence_items(sequence)?;
        if statements.is_empty() {
            return Err(invalid());
        }
        for (offset, statement) in statements.into_iter().rev().enumerate() {
            self.tick()?;
            let element = sequence_element(statement)?;
            result = Some(if element.kind() == Some(&parser_kind(&["Term", "doIf"])) {
                self.expand_do_conditional(element, result, targets.as_ref())?
            } else {
                self.prepend_do_element(element, result, scope, offset == 0)?
            });
        }
        result.ok_or_else(invalid)
    }

    /// Prepend one non-compound statement. This is shared with the conditional
    /// worklist so branch-local lets and binds cannot acquire weaker checking.
    fn prepend_do_element(
        &mut self,
        element: Syntax,
        result: Option<Syntax>,
        scope: SequenceScope<'_>,
        terminal: bool,
    ) -> Result<Syntax, NatDefinitionElabError> {
        if control::is_jump(&element) {
            // Never erase unchecked source following an unconditional exit.
            if !terminal {
                return Err(invalid());
            }
            return if scope.signal {
                let stop = control::jump_kind(element)?;
                Ok(scope.targets.ok_or_else(invalid)?.signal(Some(stop)))
            } else {
                control::jump(element, scope.targets)
            };
        }
        if element.kind() == Some(&parser_kind(&["Term", "doReturn"])) {
            // A branch may return only when there is no enclosing source
            // continuation. Loop returns are nonlocal and remain unsupported.
            if !scope.allow_return || result.is_some() {
                return Err(invalid());
            }
            let mut parts = node(element, "doReturn", 2)?;
            let value = children(parts.pop().expect("return value"))?;
            expect_atom(&parts[0], "return", "return keyword")?;
            if value.len() != 1 {
                return Err(invalid());
            }
            return Ok(call(false, value));
        }
        if element.kind() == Some(&parser_kind(&["Term", "doExpr"])) {
            let mut parts = node(element, "doExpr", 1)?;
            let action = parts.pop().expect("action");
            return Ok(if let Some(body) = result {
                let name = self.do_control_name()?;
                let annotation = if scope.require_unit {
                    unit_annotation()
                } else {
                    null(vec![])
                };
                call(true, vec![action, lambda(name, annotation, body)?])
            } else {
                action
            });
        }
        let body = result.ok_or_else(invalid)?;
        if element.kind() == Some(&parser_kind(&["Term", "doLet"])) {
            let mut parts = node(element, "doLet", 4)?;
            let declaration = parts.pop().expect("let declaration");
            let config = parts.pop().expect("let config");
            expect_empty_null(&parts[1], "immutable do let")?;
            expect_atom(&parts[0], "let", "let keyword")?;
            return Ok(Syntax::node(
                parser_kind(&["Term", "let"]),
                vec![parts.remove(0), config, declaration, atom(";"), body],
            ));
        }
        let mut parts = node(element, "doLetArrow", 4)?;
        let mut declaration = node(parts.pop().expect("bind declaration"), "doIdDecl", 4)?;
        expect_atom(&parts[0], "let", "bind keyword")?;
        expect_empty_null(&parts[1], "immutable do bind")?;
        let config = expect_node(
            &parts[2],
            &parser_kind(&["Term", "letConfig"]),
            1,
            "bind config",
        )?;
        expect_empty_null(&config[0], "plain bind config")?;
        let mut value = node(declaration.pop().expect("bind action"), "doExpr", 1)?;
        let arrow = declaration.pop().expect("bind arrow");
        if !matches!(&arrow, Syntax::Atom {val,..} if val == "←" || val == "<-") {
            return Err(invalid());
        }
        let annotation = declaration.pop().expect("bind annotation");
        let name = declaration.pop().expect("bind name");
        if !matches!(name, Syntax::Ident { .. }) {
            return Err(invalid());
        }
        Ok(call(
            true,
            vec![
                value.pop().expect("action"),
                lambda(name, annotation, body)?,
            ],
        ))
    }
}
