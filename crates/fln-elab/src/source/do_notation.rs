//! Native expansion of immutable sequential do notation.
//!
//! No monad implementation lives here. The resulting Bind.bind / Pure.pure
//! calls use ordinary universe inference, typed implicit arguments and instance
//! search. Continuations are real lambdas, so actions are never duplicated or
//! eagerly evaluated by the frontend. Final declarations still face both judges.
use super::*;

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
fn call(bind: bool, arguments: Vec<Syntax>) -> Syntax {
    // These internal nodes preserve the expected monad before type conversion
    // unfolds aliases such as Id. They do not name user-overridable globals.
    Syntax::node(
        parser_kind(&["Term", if bind { "nativeDoBind" } else { "nativeDoPure" }]),
        arguments,
    )
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

impl Context {
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
        if syntax.kind() != Some(&parser_kind(&["Term", "do"])) {
            return Ok(syntax);
        }
        if pattern {
            return Err(invalid());
        }
        let mut parts = node(syntax, "do", 2)?;
        let sequence = parts.pop().expect("do sequence");
        expect_atom(&parts[0], "do", "do keyword")?;
        let mut sequence = node(sequence, "doSeqIndent", 1)?;
        let statements = children(sequence.pop().expect("sequence items"))?;
        let mut result = None;
        for statement in statements.into_iter().rev() {
            self.tick()?;
            let mut item = node(statement, "doSeqItem", 2)?;
            let separators = children(item.pop().expect("optional semicolon"))?;
            if separators.len() > 1 {
                return Err(invalid());
            }
            if let Some(separator) = separators.first() {
                expect_atom(separator, ";", "do separator")?;
            }
            let element = item.pop().expect("do element");
            if element.kind() == Some(&parser_kind(&["Term", "doReturn"])) {
                // This slice has terminal return only. Rejecting a continuation
                // is essential: treating early return as pure would run it.
                if result.is_some() {
                    return Err(invalid());
                }
                let mut parts = node(element, "doReturn", 2)?;
                let value = children(parts.pop().expect("return value"))?;
                expect_atom(&parts[0], "return", "return keyword")?;
                if value.len() != 1 {
                    return Err(invalid());
                }
                result = Some(call(false, value));
            } else if element.kind() == Some(&parser_kind(&["Term", "doExpr"])) {
                let mut parts = node(element, "doExpr", 1)?;
                let action = parts.pop().expect("action");
                result = Some(if let Some(body) = result {
                    let serial = self.next;
                    let _ = self.fresh_name()?;
                    // Numeric names below anonymous cannot be spelled in source.
                    let name = ident(Name::num(Name::anonymous(), serial));
                    call(true, vec![action, lambda(name, null(vec![]), body)?])
                } else {
                    action
                });
            } else if element.kind() == Some(&parser_kind(&["Term", "doLet"])) {
                let body = result.take().ok_or_else(invalid)?;
                let mut parts = node(element, "doLet", 4)?;
                let declaration = parts.pop().expect("let declaration");
                let config = parts.pop().expect("let config");
                expect_empty_null(&parts[1], "immutable do let")?;
                expect_atom(&parts[0], "let", "let keyword")?;
                let keyword = parts.remove(0);
                result = Some(Syntax::node(
                    parser_kind(&["Term", "let"]),
                    vec![keyword, config, declaration, atom(";"), body],
                ));
            } else {
                let body = result.take().ok_or_else(invalid)?;
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
                result = Some(call(
                    true,
                    vec![
                        value.pop().expect("action"),
                        lambda(name, annotation, body)?,
                    ],
                ));
            }
        }
        result.ok_or_else(invalid)
    }
}
