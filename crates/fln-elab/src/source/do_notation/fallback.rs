//! Refutable do bindings are checked two-arm branches, not unchecked lets.
//!
//! The pin captures the success continuation inside the binding. Keeping that
//! sequence separate from the failure sequence preserves both lexical scope
//! and nonlocal control flow through the existing branch worklists.
use super::*;

pub(super) fn is_binding(syntax: &Syntax) -> bool {
    if syntax.kind() == Some(&parser_kind(&["Term", "doLetElse"])) {
        return true;
    }
    let Syntax::Node { kind, args, .. } = syntax else {
        return false;
    };
    if kind != &parser_kind(&["Term", "doLetArrow"]) {
        return false;
    }
    matches!(args.last(), Some(Syntax::Node { kind, args, .. })
        if kind == &parser_kind(&["Term", "doPatDecl"])
            && args.get(4).is_some_and(|fallback|
                !matches!(fallback, Syntax::Node {kind, args, ..}
                    if kind == &Name::from_components(["null"]) && args.is_empty())))
}

pub(super) struct Header {
    pattern: Syntax,
    value: Syntax,
    annotation: Syntax,
    monadic: bool,
}

fn continuation(syntax: Syntax) -> Result<Option<Syntax>, NatDefinitionElabError> {
    let mut parts = children(syntax)?;
    match parts.len() {
        0 => Ok(None),
        1 => Ok(parts.pop()),
        _ => Err(invalid()),
    }
}

pub(super) fn split(syntax: Syntax) -> Result<conditional::Branches, NatDefinitionElabError> {
    let monadic = syntax.kind() == Some(&parser_kind(&["Term", "doLetArrow"]));
    let mut parts = node(
        syntax,
        if monadic { "doLetArrow" } else { "doLetElse" },
        if monadic { 4 } else { 9 },
    )?;
    expect_atom(&parts[0], "let", "refutable binding keyword")?;
    expect_empty_null(&parts[1], "immutable refutable binding")?;
    let config = expect_node(
        &parts[2],
        &parser_kind(&["Term", "letConfig"]),
        1,
        "refutable binding config",
    )?;
    expect_empty_null(&config[0], "plain refutable binding config")?;
    let (header, no, yes) = if monadic {
        let mut declaration = node(parts.pop().expect("bind declaration"), "doPatDecl", 5)?;
        let mut otherwise = children(declaration.pop().expect("failure branch"))?;
        if otherwise.len() != 3 {
            return Err(invalid());
        }
        let yes = continuation(otherwise.pop().expect("success continuation"))?;
        let no = otherwise.pop().expect("failure sequence");
        expect_atom(&otherwise[0], "|", "failure branch separator")?;
        let mut action = node(declaration.pop().expect("binding action"), "doExpr", 1)?;
        let arrow = declaration.pop().expect("binding arrow");
        if !matches!(&arrow, Syntax::Atom {val, ..} if val == "←" || val == "<-") {
            return Err(invalid());
        }
        let annotation = declaration.pop().expect("binding annotation");
        let pattern = declaration.pop().expect("binding pattern");
        (
            Header {
                pattern,
                value: action.pop().expect("action expression"),
                annotation,
                monadic,
            },
            no,
            yes,
        )
    } else {
        let yes = continuation(parts.pop().expect("success continuation"))?;
        let no = parts.pop().expect("failure sequence");
        expect_atom(
            &parts.pop().expect("failure separator"),
            "|",
            "failure branch separator",
        )?;
        let value = parts.pop().expect("binding value");
        expect_atom(
            &parts.pop().expect("assignment"),
            ":=",
            "pure refutable binding",
        )?;
        let pattern = parts.pop().expect("binding pattern");
        (
            Header {
                pattern,
                value,
                annotation: null(vec![]),
                monadic,
            },
            no,
            yes,
        )
    };
    Ok(conditional::Branches {
        header: conditional::Header::Binding(Box::new(header)),
        arms: vec![yes, Some(no)],
    })
}

impl Context {
    pub(super) fn finish_do_fallback(
        &mut self,
        header: Header,
        yes: Syntax,
        no: Syntax,
    ) -> Result<Syntax, NatDefinitionElabError> {
        let Header {
            pattern,
            value,
            annotation,
            monadic,
        } = header;
        if !monadic {
            return self.expand_do_pattern_condition(pattern, value, false, yes, no);
        }
        // Check a written element annotation on the actual bind parameter,
        // including on failing paths. Do not ascribe the monadic action to the
        // element type or infer injectivity of the user's higher-kinded monad.
        let subject = self.do_control_name()?;
        let body = self.expand_do_pattern_condition(pattern, subject.clone(), false, yes, no)?;
        Ok(call(true, vec![value, lambda(subject, annotation, body)?]))
    }
}
