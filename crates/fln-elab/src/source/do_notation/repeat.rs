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

/// `repeat body` as `for _ in Loop.mk do body` (`elabDoRepeat`). The pin appends `unreachable!` when
/// the body cannot `break` and the block's value is not `PUnit`; without it such a block is refused
/// here (a gap, never a different value).
fn repeat_loop(syntax: Syntax) -> Result<Syntax, NatDefinitionElabError> {
    let mut parts = node(syntax, "doRepeat", 2)?;
    let body = parts.pop().expect("loop body");
    expect_atom(&parts[0], "repeat", "loop keyword")?;
    Ok(loop_over(body))
}

/// `for _ in Loop.mk do body`.
fn loop_over(body: Syntax) -> Syntax {
    let declaration = Syntax::node(
        parser_kind(&["Term", "doForDecl"]),
        vec![
            null(vec![]),
            Syntax::node(parser_kind(&["Term", "hole"]), vec![atom("_")]),
            atom("in"),
            ident(Name::from_components(["_root_", "Lean", "Loop", "mk"])),
        ],
    );
    Syntax::node(
        parser_kind(&["Term", "doFor"]),
        vec![atom("for"), null(vec![declaration]), atom("do"), body],
    )
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
                        repeat_loop(node)?
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
