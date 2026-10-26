//! `while c do s` and `repeat s`, as the pin (`Lean/Elab/BuiltinDo/Repeat.lean`). The macro
//! `expandDoWhile` makes `while c do s` into `repeat if c then s else break`, and `elabDoRepeat`
//! makes `repeat s` into `for _ in Loop.mk do s`, a loop over `Lean.Loop` (`Init/While.lean`) whose
//! `ForIn` instance runs until a `break`. The rewrite runs before nested actions are lifted and
//! before `mut` variables are threaded, as a macro expands before its element elaborates: an action
//! in the condition runs on every iteration, and the loop's reassignments are an ordinary loop's.
use super::*;
mod until;

fn is(syntax: &Syntax, kind: &str) -> bool {
    syntax.kind() == Some(&parser_kind(&["Term", kind]))
}

pub(in crate::source) fn is_while_loop(syntax: &Syntax) -> bool {
    is(syntax, "doWhile") || is(syntax, "doRepeat") || is(syntax, "doRepeatUntil")
}

fn sequence(element: Syntax) -> Syntax {
    Syntax::node(
        parser_kind(&["Term", "doSeqIndent"]),
        vec![null(vec![Syntax::node(
            parser_kind(&["Term", "doSeqItem"]),
            vec![element, null(vec![])],
        )])],
    )
}

/// Retain the pin's result-dependent `unreachable!` until the enclosing monad's result is known.
/// The collection marker survives mutation and return lowering without duplicating the loop.
fn repeat_loop(context: &mut Context, syntax: Syntax) -> Result<Syntax, NatDefinitionElabError> {
    let mut parts = node(syntax, "doRepeat", 2)?;
    let body = parts.pop().expect("loop body");
    expect_atom(&parts[0], "repeat", "loop keyword")?;
    let fallback = if context.repeat_has_break(&body)? {
        None
    } else {
        Some(Syntax::node(
            parser_kind(&["Term", "unreachable"]),
            vec![Syntax::Atom {
                info: parts[0].info(),
                val: "unreachable!".to_owned(),
            }],
        ))
    };
    Ok(loop_over_collection(body, fallback))
}

/// `for _ in Loop.mk do body`.
fn loop_over(body: Syntax) -> Syntax {
    loop_over_collection(body, None)
}

fn loop_over_collection(body: Syntax, fallback: Option<Syntax>) -> Syntax {
    let collection = ident(Name::from_components(["_root_", "Lean", "Loop", "mk"]));
    let collection = match fallback {
        Some(fallback) => Syntax::node(
            parser_kind(&["Term", "nativeDoRepeatCollection"]),
            vec![collection, fallback],
        ),
        None => collection,
    };
    let declaration = Syntax::node(
        parser_kind(&["Term", "doForDecl"]),
        vec![
            null(vec![]),
            Syntax::node(parser_kind(&["Term", "hole"]), vec![atom("_")]),
            atom("in"),
            collection,
        ],
    );
    Syntax::node(
        parser_kind(&["Term", "doFor"]),
        vec![atom("for"), null(vec![declaration]), atom("do"), body],
    )
}

/// The collection itself is elaborated normally; only this private marker carries the fallback.
pub(super) fn split_collection(
    collection: Syntax,
) -> Result<(Syntax, Option<Syntax>), NatDefinitionElabError> {
    if !is(&collection, "nativeDoRepeatCollection") {
        return Ok((collection, None));
    }
    let mut parts = node(collection, "nativeDoRepeatCollection", 2)?;
    let fallback = parts.pop().expect("repeat fallback");
    Ok((parts.pop().expect("repeat collection"), Some(fallback)))
}

/// A state-carrying terminal loop ends in a separate action after rebinding its variables.
/// Preserve the same fallback at that action, rather than changing the accumulator's type.
pub(super) fn state_fallback(
    declarations: &Syntax,
) -> Result<Option<Syntax>, NatDefinitionElabError> {
    let declarations = expect_null_args(declarations, "loop declarations")?;
    let [declaration] = declarations else {
        return Ok(None);
    };
    let parts = expect_node(
        declaration,
        &parser_kind(&["Term", "doForDecl"]),
        4,
        "loop declaration",
    )?;
    if !is(&parts[3], "nativeDoRepeatCollection") {
        return Ok(None);
    }
    let parts = expect_node(
        &parts[3],
        &parser_kind(&["Term", "nativeDoRepeatCollection"]),
        2,
        "repeat collection",
    )?;
    Ok(Some(parts[1].clone()))
}

pub(super) fn default_result(normal: Syntax, fallback: Option<Syntax>) -> Syntax {
    match fallback {
        Some(fallback) => Syntax::node(
            parser_kind(&["Term", "nativeDoRepeatDefault"]),
            vec![normal, fallback],
        ),
        None => normal,
    }
}

/// `while cond do body` as `for _ in Loop.mk do (if cond then body else break)`.
fn while_loop(syntax: Syntax) -> Result<Syntax, NatDefinitionElabError> {
    let mut parts = node(syntax, "doWhile", 4)?;
    let body = parts.pop().expect("loop body");
    expect_atom(&parts[2], "do", "loop body keyword")?;
    let condition = parts.remove(1);
    expect_atom(&parts[0], "while", "loop keyword")?;
    let conditional = Syntax::node(
        parser_kind(&["Term", "doIf"]),
        vec![
            atom("if"),
            condition,
            atom("then"),
            body,
            null(vec![]),
            null(vec![
                atom("else"),
                sequence(Syntax::node(
                    parser_kind(&["Term", "doBreak"]),
                    vec![atom("break")],
                )),
            ]),
        ],
    );
    Ok(loop_over(sequence(conditional)))
}

impl Context {
    /// `inferControlInfoSeq` observes statements, not terms containing their own `do` blocks.
    /// An inner loop owns its `break`; bare nested blocks, branches and handlers share ours.
    fn repeat_has_break(&mut self, body: &Syntax) -> Result<bool, NatDefinitionElabError> {
        let mut work = vec![body];
        while let Some(syntax) = work.pop() {
            self.tick()?;
            let Syntax::Node { kind, args, .. } = syntax else {
                continue;
            };
            if is(syntax, "doBreak") {
                return Ok(true);
            }
            for (index, child) in args.iter().enumerate() {
                let shared = kind == &Name::from_components(["null"])
                    || kind == &Name::from_components(["group"])
                    || is(syntax, "doSeqIndent")
                    || is(syntax, "doSeqBracketed")
                    || is(syntax, "matchAlts")
                    || (is(syntax, "doSeqItem") && index == 0)
                    || ((is(syntax, "doNested")
                        || is(syntax, "doCatchMatch")
                        || is(syntax, "doFinally"))
                        && index == 1)
                    || (is(syntax, "doIf") && index >= 3)
                    || (is(syntax, "doUnless") && index == 3)
                    || (is(syntax, "doMatch") && index == 6)
                    || (is(syntax, "matchAlt") && index == 3)
                    || (is(syntax, "doLetElse") && index >= 7)
                    || (is(syntax, "doLetArrow") && index == 3)
                    || (is(syntax, "doReassignArrow") && index == 0)
                    || (is(syntax, "doIdDecl") && index == 3)
                    || (is(syntax, "doPatDecl") && index >= 3)
                    || (is(syntax, "doTry") && index >= 1)
                    || (is(syntax, "doCatch") && index == 4);
                if shared {
                    work.push(child);
                }
            }
        }
        Ok(false)
    }

    /// Like `isDefEqGuarded dec.resultType mkPUnit`, a successful comparison keeps its inferred
    /// universes/metavariables; a failed comparison cannot constrain the surrounding result.
    pub(in crate::source) fn do_repeat_needs_fallback(
        &mut self,
        expected: Option<&Expr>,
    ) -> Result<bool, NatDefinitionElabError> {
        let Some(result) = self.do_pure_result_type(expected)? else {
            return Ok(false);
        };
        let unit = self.constant(&Name::from_components(["PUnit"]))?.value;
        Ok(!self.defeq_guarded(&result, &unit)?)
    }

    /// `syntax` with every `while` and `repeat` loop rewritten, inner loops first.
    pub(in crate::source) fn expand_while_loops(
        &mut self,
        syntax: &Syntax,
    ) -> Result<Syntax, NatDefinitionElabError> {
        enum Task<'a> {
            Visit(&'a Syntax),
            Build(&'a Syntax, usize),
        }
        let mut tasks = vec![Task::Visit(syntax)];
        let mut built: Vec<Syntax> = Vec::new();
        while let Some(task) = tasks.pop() {
            self.tick()?;
            match task {
                Task::Visit(node @ Syntax::Node { args, .. }) => {
                    tasks.push(Task::Build(node, built.len()));
                    tasks.extend(args.iter().rev().map(Task::Visit));
                }
                Task::Visit(leaf) => built.push(leaf.clone()),
                Task::Build(Syntax::Node { info, kind, .. }, start) => {
                    let node = Syntax::Node {
                        info: *info,
                        kind: kind.clone(),
                        args: built.split_off(start),
                    };
                    built.push(if is(&node, "doWhile") {
                        while_loop(node)?
                    } else if is(&node, "doRepeat") {
                        repeat_loop(self, node)?
                    } else if is(&node, "doRepeatUntil") {
                        until::expand(node)?
                    } else {
                        node
                    });
                }
                Task::Build(..) => unreachable!("only nodes are built"),
            }
        }
        let result = built.pop().ok_or_else(invalid)?;
        if !built.is_empty() {
            return Err(invalid());
        }
        Ok(result)
    }
}
