//! Checked exception combinators. Handlers are real lambdas; the instance's
//! admitted implementation decides which action runs. No host exception or
//! privileged execution path is introduced by this syntax expansion.
use super::*;

fn apply(name: &[&str], arguments: Vec<Syntax>) -> Syntax {
    Syntax::node(
        parser_kind(&["Term", "app"]),
        vec![
            ident(Name::from_components(
                std::iter::once("_root_").chain(name.iter().copied()),
            )),
            null(arguments),
        ],
    )
}
impl Context {
    fn exception_control(&mut self, syntax: &Syntax) -> Result<bool, NatDefinitionElabError> {
        let mut work = vec![syntax];
        while let Some(s) = work.pop() {
            self.tick()?;
            if control::is_jump(s) || s.kind() == Some(&parser_kind(&["Term", "doReturn"])) {
                return Ok(true);
            }
            if s.kind() == Some(&parser_kind(&["Term", "nativeDoTry"])) {
                let parts = expect_node(
                    s,
                    &parser_kind(&["Term", "nativeDoTry"]),
                    2,
                    "exception action",
                )?;
                if matches!(&parts[1],Syntax::Atom {val,..} if val=="returning") {
                    return Ok(true);
                }
                continue;
            }
            if let Syntax::Node { args, .. } = s {
                work.extend(args);
            }
        }
        Ok(false)
    }

    pub(super) fn expand_do_try(
        &mut self,
        syntax: Syntax,
    ) -> Result<Syntax, NatDefinitionElabError> {
        let mut parts = node(syntax, "doTry", 4)?;
        expect_atom(&parts[0], "try", "exception keyword")?;
        let finally = parts.pop().expect("optional finalizer");
        // Finalizer semantics are not emulated by ordinary sequencing.
        expect_empty_null(&finally, "exception without finalizer")?;
        let catches = children(parts.pop().expect("handlers"))?;
        let body = parts.pop().expect("protected sequence");
        let mut returning = self.exception_control(&body)?;
        let mut action = self.expand_do_sequence(body, None)?;
        for handler in catches {
            let mut parts = node(handler, "doCatch", 5)?;
            expect_atom(&parts[0], "catch", "handler keyword")?;
            if !matches!(&parts[3],Syntax::Atom{val,..} if val=="=>" || val=="↦") {
                return Err(invalid());
            }
            let body = parts.pop().expect("handler sequence");
            returning |= self.exception_control(&body)?;
            let body = self.expand_do_sequence(body, None)?;
            let annotation = children(parts.remove(2))?;
            let name = parts.remove(1);
            let handler = lambda(name, null(vec![]), body)?;
            action = match annotation.as_slice() {
                [] => apply(&["MonadExcept", "tryCatch"], vec![action, handler]),
                [colon, type_] => {
                    expect_atom(colon, ":", "handler type")?;
                    apply(&["tryCatchThe"], vec![type_.clone(), action, handler])
                }
                _ => return Err(invalid()),
            };
        }
        Ok(if returning {
            Syntax::node(
                parser_kind(&["Term", "nativeDoTry"]),
                vec![action, atom("returning")],
            )
        } else {
            // Normal completion must remain a doExpr: the enclosing nested-do
            // worklist attaches its value continuation to that category.
            Syntax::node(parser_kind(&["Term", "doExpr"]), vec![action])
        })
    }

    pub(super) fn prepend_do_try(
        &mut self,
        syntax: Syntax,
        suffix: Option<Syntax>,
        scope: SequenceScope<'_>,
        terminal: bool,
    ) -> Result<Syntax, NatDefinitionElabError> {
        let mut parts = node(syntax, "nativeDoTry", 2)?;
        let flag = parts.pop().expect("exception control flag");
        let returning = match &flag {
            Syntax::Atom { val, .. } if val == "returning" => true,
            Syntax::Atom { val, .. } if val == "action" => false,
            _ => return Err(invalid()),
        };
        // Until tagged exits are threaded through the combinator, refuse a
        // nonlocal exit rather than treating return/break as ordinary fallthrough.
        if returning && (!terminal || suffix.is_some() || !scope.allow_return) {
            return Err(invalid());
        }
        self.prepend_do_element(
            Syntax::node(parser_kind(&["Term", "doExpr"]), parts),
            suffix,
            scope,
            terminal,
        )
    }
}
