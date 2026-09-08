#!/usr/bin/env python3
"""Apply the native source-lambda increment, refusing unexpected source drift."""
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

def once(source, before, after):
    if source.count(before) != 1:
        raise SystemExit(f"expected exactly one source anchor: {before[:90]!r}")
    return source.replace(before, after, 1)

def main():
    parser_path = ROOT / 'crates/fln-parse/src/lib.rs'
    source_path = ROOT / 'crates/fln-elab/src/source.rs'
    tests_path = ROOT / 'crates/fln-elab/tests/source_inference.rs'
    parser = parser_path.read_text()
    source = source_path.read_text()
    tests = tests_path.read_text()
    if 'struct LambdaTokens {' in parser:
        raise SystemExit('lambda increment already exists; do not replay it')
    parser = once(parser, 'struct BoundedTermFrame {\n    open: Option<usize>,', '''struct LambdaTokens {
    keyword: usize,
    names: std::ops::Range<usize>,
    arrow: usize,
}

struct BoundedTermFrame {
    open: Option<usize>,
    lambda: Option<LambdaTokens>,''')
    parser = once(parser, '"⦃", "⦄", "->", "→",', '"⦃", "⦄", "->", "→", "fun", "λ", "=>", "↦",')
    parser = once(parser, '    ParameterTypeAscription,', '    ParameterTypeAscription,\n    LambdaArrow,')
    start = parser.index('fn bounded_term(\n')
    end = parser.index('\n/// Parse the first production', start)
    term = parser[start:end]
    term = once(term, 'open: None,', 'open: None,\n        lambda: None,')
    term = once(term, 'open: Some(index),', 'open: Some(index),\n                    lambda: None,')
    term = once(term, 'for index in range.clone() {', 'let mut cursor = range.start;\n    while cursor < range.end {\n        let index = cursor;\n        cursor += 1;')
    anchor = '            Some(TokenKind::Symbol(symbol)) if symbol == "(" => {'
    term = once(term, anchor, '''            Some(TokenKind::Symbol(symbol))
                if grammar == DefinitionGrammar::Scalar && (symbol == "fun" || symbol == "λ") =>
            {
                let names_start = cursor;
                while cursor < range.end && matches!(tokens[cursor].kind, TokenKind::Ident(_)) {
                    cursor += 1;
                }
                if cursor == names_start {
                    return Err(NatDefinitionParseError::OutsideSeedGrammar {
                        at: original_position(view, tokens, cursor),
                        expected: NatDefinitionExpectation::ParameterIdentifier,
                    });
                }
                if cursor >= range.end || !matches!(&tokens[cursor].kind,
                    TokenKind::Symbol(arrow) if arrow == "=>" || arrow == "↦") {
                    return Err(NatDefinitionParseError::OutsideSeedGrammar {
                        at: original_position(view, tokens, cursor),
                        expected: NatDefinitionExpectation::LambdaArrow,
                    });
                }
                frames.push(BoundedTermFrame {
                    open: None,
                    lambda: Some(LambdaTokens { keyword: index, names: names_start..cursor, arrow: cursor }),
                    application: Vec::new(), operands: Vec::new(), operators: Vec::new(),
                });
                cursor += 1;
            }
''' + anchor)
    anchor = '            Some(TokenKind::Symbol(symbol)) if symbol == ")" => {\n'
    term = once(term, anchor, anchor + '                finish_lambda_frames(leaves, view, tokens, &mut frames, grammar, index)?;\n')
    term = once(term, '    if frames.len() != 1 {', '    finish_lambda_frames(leaves, view, tokens, &mut frames, grammar, range.end)?;\n    if frames.len() != 1 {')
    parser = parser[:start] + term + parser[end:]
    parser = once(parser, 'fn bounded_term(\n', '''/// Lambda bodies extend through their enclosing term frame. Nested lambda
/// frames are folded on the heap before closing their containing parenthesis.
/// The nodes follow Parser.Term.fun/basicFun at the pinned Reference.
fn finish_lambda_frames(
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    frames: &mut Vec<BoundedTermFrame>,
    grammar: DefinitionGrammar,
    at: usize,
) -> Result<(), NatDefinitionParseError> {
    while frames.last().is_some_and(|frame| frame.lambda.is_some()) {
        let mut frame = frames.pop().expect("the guarded lambda frame exists");
        let prefix = frame.lambda.take().expect("the guarded lambda has a prefix");
        let body = finish_bounded_frame(view, tokens, frame, grammar, at)?;
        let names = prefix.names.map(|index| leaves.leaf(index)).collect::<Result<Vec<_>, _>>()?;
        let basic = Syntax::node(parser_kind(&["Term", "basicFun"]), vec![
            null_node(names), null_node(Vec::new()), leaves.leaf(prefix.arrow)?, body,
        ]);
        let lambda = Syntax::node(parser_kind(&["Term", "fun"]), vec![leaves.leaf(prefix.keyword)?, basic]);
        frames.last_mut().expect("a lambda frame always has a parent").application.push((lambda, prefix.keyword));
    }
    Ok(())
}

fn bounded_term(
''')
    source = once(source, '            LetBody(LocalContext, FVarId, Name, Typed),', '            LetBody(LocalContext, FVarId, Name, Typed),\n            Lambda(LocalContext, Vec<LocalDecl>),')
    anchor = '                        if kind == &parser_kind(&["Term", "let"]) {'
    source = once(source, anchor, '''                        if kind == &parser_kind(&["Term", "fun"]) {
                            let parts = expect_node(syntax, kind, 2, "Lean.Parser.Term.fun")?;
                            match &parts[0] {
                                Syntax::Atom { val, .. } if val == "fun" || val == "λ" => {}
                                _ => return Err(failure(SourceInferenceError::Scope)),
                            }
                            let basic = expect_node(&parts[1], &parser_kind(&["Term", "basicFun"]), 4, "Lean.Parser.Term.basicFun")?;
                            let names = expect_null_args(&basic[0], "lambda binders")?;
                            if names.is_empty() { return Err(failure(SourceInferenceError::Scope)); }
                            expect_empty_null(&basic[1], "absent lambda result ascription")?;
                            match &basic[2] {
                                Syntax::Atom { val, .. } if val == "=>" || val == "↦" => {}
                                _ => return Err(failure(SourceInferenceError::Scope)),
                            }
                            let saved = self.txn.lctx.clone();
                            let mut binders = Vec::new();
                            let mut expected_body = expected;
                            for name in names {
                                self.tick()?;
                                let Syntax::Ident { val: name, .. } = name else { return Err(failure(SourceInferenceError::Scope)); };
                                if name.is_anonymous() { return Err(NatDefinitionElabError::AnonymousReferenceName); }
                                let (domain, codomain) = if let Some(expected) = &expected_body {
                                    let expected = self.whnf(expected)?;
                                    let ExprNode::ForallE { binder_type, body, binder_info: BinderInfo::Default, .. } = expected.node() else {
                                        return Err(failure(SourceInferenceError::ExpectedFunction));
                                    };
                                    (binder_type.clone(), Some(body.clone()))
                                } else {
                                    let universe = self.level()?;
                                    (self.hole(Expr::sort(universe))?, None)
                                };
                                let id = FVarId(self.fresh_name()?);
                                expected_body = codomain.map(|body| self.substitute(&body, &Expr::fvar(id.clone()))).transpose()?;
                                self.txn.lctx.add_param(id.clone(), name.clone(), domain, BinderInfo::Default);
                                binders.push(self.txn.lctx.find(&id).expect("the new lambda binder is present").clone());
                            }
                            tasks.push(Task::Lambda(saved, binders));
                            tasks.push(Task::Visit(&basic[3], expected_body, true));
                            continue;
                        }
''' + anchor)
    anchor = '                Task::Function(arguments, expected) => {'
    source = once(source, anchor, '''                Task::Lambda(saved, binders) => {
                    let mut body = values.pop().expect("lambda body visit");
                    self.flush(false)?;
                    body.value = self.instantiate(&body.value)?;
                    body.type_ = self.instantiate(&body.type_)?;
                    for local in binders.into_iter().rev() {
                        self.tick()?;
                        let domain = self.instantiate(&local.type_)?;
                        body.value = body.value.abstract_fvar(&local.id, 0).map_err(|_| failure(SourceInferenceError::Scope))?;
                        body.type_ = body.type_.abstract_fvar(&local.id, 0).map_err(|_| failure(SourceInferenceError::Scope))?;
                        body.value = Expr::lam(local.user_name.clone(), domain.clone(), body.value, local.binder_info);
                        body.type_ = Expr::forall_e(local.user_name, domain, body.type_, local.binder_info);
                    }
                    self.txn.lctx = saved;
                    values.push(body);
                }
''' + anchor)
    tests += '''

#[test]
fn lambda_binders_receive_expected_domains() {
    let result = accepted("def identity : Nat -> Nat := fun x => x", &env());
    let ExprNode::Lam { binder_type, body, .. } = result.value.node() else { panic!("lambda expected"); };
    assert_eq!(binder_type, &nat());
    assert_eq!(body, &b(0));
}

#[test]
fn lambda_application_infers_an_unannotated_domain() {
    let result = accepted("def answer := (fun x => x) 37", &env());
    assert_eq!(result.base.type_, nat());
}

#[test]
fn nested_lambda_binders_are_closed_capture_avoidantly() {
    let result = accepted("def first : Nat -> Nat -> Nat := fun x y => x", &env());
    let ExprNode::Lam { body, .. } = result.value.node() else { panic!("outer lambda"); };
    let ExprNode::Lam { body, .. } = body.node() else { panic!("inner lambda"); };
    assert_eq!(body, &b(1));
    accepted("def inner : Nat -> Nat := fun x => (fun y => x) 0", &env());
}

#[test]
fn unicode_lambdas_and_nested_calls_preserve_expected_types() {
    accepted("def identity : Nat → Nat := λ x ↦ polyId x", &env());
}

#[test]
fn higher_order_arguments_can_be_source_lambdas() {
    let env = env();
    let apply = accepted("def apply (f : Nat -> Nat) (x : Nat) : Nat := f x", &env);
    let env = publish(&env, Declaration::Defn(apply));
    accepted("def answer := apply (fun x => polyId x) 37", &env);
}

#[test]
fn a_bare_unconstrained_lambda_does_not_get_a_guessed_domain() {
    assert!(matches!(check_definition_source(b"def unknown := fun x => x", &env(), budget()),
        Err(DefinitionFrontendError::Elaborate(NatDefinitionElabError::Inference(_)))));
}

#[test]
fn lambda_scope_restoration_preserves_outer_bindings() {
    accepted("def shadow (x : Nat) : Nat -> Nat := fun x => x", &env());
    accepted("def shadow : Nat -> Nat := let x := 7; fun x => x", &env());
}
'''
    for path, text in ((parser_path, parser), (source_path, source), (tests_path, tests)):
        path.write_text(text)

if __name__ == '__main__':
    main()
