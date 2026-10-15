//! A bare nested `do` extends the surrounding lexical and control scope.
//!
//! The pin's `BuiltinDo/Misc.lean::elabDoNested` passes the existing continuation
//! straight to `elabDoSeq`. Flatten direct sequence elements before the final
//! continuation-producing expansion. A binding's action and a parenthesized
//! term retain their own wrappers, so their locals never escape.
use super::*;

fn entries(sequence: &mut Syntax) -> Result<&mut Vec<Syntax>, NatDefinitionElabError> {
    let Syntax::Node { kind, args, .. } = sequence else {
        return Err(invalid());
    };
    let index = if kind == &parser_kind(&["Term", "doSeqIndent"]) {
        if args.len() != 1 {
            return Err(invalid());
        }
        0
    } else if kind == &parser_kind(&["Term", "doSeqBracketed"]) {
        if args.len() != 3 {
            return Err(invalid());
        }
        expect_atom(&args[0], "{", "do opening brace")?;
        expect_atom(&args[2], "}", "do closing brace")?;
        1
    } else {
        return Err(invalid());
    };
    let Syntax::Node {
        kind, args: items, ..
    } = &mut args[index]
    else {
        return Err(invalid());
    };
    if kind != &Name::from_components(["null"]) {
        return Err(invalid());
    }
    Ok(items)
}

pub(super) fn flatten_bare_nested(
    context: &mut Context,
    mut syntax: Syntax,
) -> Result<Syntax, NatDefinitionElabError> {
    if syntax.kind() != Some(&parser_kind(&["Term", "doSeqIndent"]))
        && syntax.kind() != Some(&parser_kind(&["Term", "doSeqBracketed"]))
    {
        return Ok(syntax);
    }
    let items = entries(&mut syntax)?;
    // Owned iterators avoid cloning subtrees and host recursion. Charge every
    // additional presentation here, including the wrappers we remove.
    let mut pending = vec![std::mem::take(items).into_iter()];
    while let Some(iter) = pending.last_mut() {
        context.tick()?;
        let Some(mut item) = iter.next() else {
            pending.pop();
            continue;
        };
        let parts = expect_node(&item, &parser_kind(&["Term", "doSeqItem"]), 2, "do item")?;
        if parts[0].kind() != Some(&parser_kind(&["Term", "doNested"])) {
            items.push(item);
            continue;
        }
        match expect_null_args(&parts[1], "do separator")? {
            [] => {}
            [separator] => {
                expect_atom(separator, ";", "do separator")?;
            }
            _ => return Err(invalid()),
        }
        let Syntax::Node { args, .. } = &mut item else {
            unreachable!("checked item")
        };
        let Syntax::Node { args, .. } = &mut args[0] else {
            unreachable!("checked nested do")
        };
        if args.len() != 2 {
            return Err(invalid());
        }
        expect_atom(&args[0], "do", "nested do keyword")?;
        let inner = entries(&mut args[1])?;
        let last = inner.last().ok_or_else(invalid)?;
        let last = &expect_node(last, &parser_kind(&["Term", "doSeqItem"]), 2, "do item")?[0];
        let exits = ["doReturn", "doBreak", "doContinue"]
            .iter()
            .any(|kind| last.kind() == Some(&parser_kind(&["Term", kind])));
        if exits && inner.len() == 1 {
            // Keep the original exit boundary so the shared-control worklist
            // checks, but does not execute, a syntactically following suffix.
            // Moving the declarations before it is what preserves their scope.
            items.push(item);
            continue;
        }
        let mut prefix = std::mem::take(inner);
        if exits {
            inner.push(prefix.pop().expect("nonempty nested do"));
            prefix.push(item);
        }
        pending.push(prefix.into_iter());
    }
    Ok(syntax)
}
