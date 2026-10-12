//! Nested actions: `(← e)` in a do element runs `e` before the element, as `let x ← e`, and the
//! element reads `x`. This is the pin's `expandNestedActions` (`Lean/Elab/Do/Basic.lean`), run on
//! each element before it elaborates:
//! - inner actions first, then left to right;
//! - never out of another do block (`do`, a sequence, a term-position `return`/`unless`/`for`);
//! - out of a pure `if` only from its condition;
//! - never past a binder (`fun`, match alternatives, `let rec`, a `let` with parameters).
//!
//! The pin refuses an action it cannot lift ("must be nested inside a `do` expression", "cannot
//! lift … over a binder"), and so does this pass. An `else if` condition runs only when its branch
//! is reached (`if c then … else if (← e) then …` never runs `e` when `c` holds), so an action
//! there is refused rather than lifted early.
use super::*;

fn is(syntax: &Syntax, kind: &str) -> bool {
    syntax.kind() == Some(&parser_kind(&["Term", kind]))
}

/// `liftNestedActionDelimiter`: the inside belongs to another do block.
fn delimiter(syntax: &Syntax) -> bool {
    [
        "do",
        "doSeqIndent",
        "doSeqBracketed",
        "termReturn",
        "termUnless",
        "termTry",
        "termFor",
    ]
    .iter()
    .any(|kind| is(syntax, kind))
}

/// `nestedActionForbiddenBinder`.
fn binder(syntax: &Syntax) -> bool {
    if ["fun", "matchAlts", "doLetRec", "letrec"]
        .iter()
        .any(|kind| is(syntax, kind))
    {
        return true;
    }
    // `letDeclHasBinders`: equations, or a named `let` with parameters.
    let Syntax::Node { args, .. } = syntax else {
        return false;
    };
    is(syntax, "letDecl")
        && args.first().is_some_and(|declaration| {
            is(declaration, "letEqnsDecl")
                || (is(declaration, "letIdDecl")
                    && matches!(declaration, Syntax::Node { args, .. }
                        if matches!(args.get(1), Some(Syntax::Node { args: binders, .. })
                            if !binders.is_empty())))
        })
}

/// The pure `if`, whose branches keep their actions (`termIfThenElse`, `termDepIfThenElse`).
fn pure_conditional(syntax: &Syntax) -> bool {
    syntax.kind() == Some(&Name::from_components(["termIfThenElse"]))
        || syntax.kind() == Some(&Name::from_components(["termDepIfThenElse"]))
}

fn sequence(elements: Vec<Syntax>) -> Syntax {
    Syntax::node(
        parser_kind(&["Term", "doSeqIndent"]),
        vec![null(
            elements
                .into_iter()
                .map(|element| {
                    Syntax::node(
                        parser_kind(&["Term", "doSeqItem"]),
                        vec![element, null(vec![])],
                    )
                })
                .collect(),
        )],
    )
}

impl Context {
    /// `syntax` with the nested actions of every do element lifted, or `None` when there is none
    /// to lift. One outside every do element stays, and is refused where it is elaborated.
    pub(in crate::source) fn lift_nested_actions(
        &mut self,
        syntax: &Syntax,
    ) -> Result<Option<Syntax>, NatDefinitionElabError> {
        enum Task<'a> {
            Visit(&'a Syntax),
            Build(&'a Syntax, usize),
        }
        let mut lifted = 0usize;
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
                    // A term-position `unless`/`for`/`return` is its own do block (`toDoElem`):
                    // its element's actions are that block's.
                    let node = match term_element(&node) {
                        Some(element) => Syntax::node(
                            parser_kind(&["Term", "do"]),
                            vec![
                                atom("do"),
                                self.lift_sequence(sequence(vec![element]), &mut lifted)?,
                            ],
                        ),
                        None if is(&node, "doSeqIndent") || is(&node, "doSeqBracketed") => {
                            self.lift_sequence(node, &mut lifted)?
                        }
                        None => node,
                    };
                    built.push(node);
                }
                Task::Build(..) => unreachable!("only nodes are built"),
            }
        }
        if lifted == 0 {
            return Ok(None);
        }
        built.pop().map(Some).ok_or_else(invalid)
    }

    /// One sequence, each element preceded by its lifted actions.
    #[inline(never)]
    fn lift_sequence(
        &mut self,
        sequence: Syntax,
        lifted: &mut usize,
    ) -> Result<Syntax, NatDefinitionElabError> {
        let kind = sequence.kind().cloned().ok_or_else(invalid)?;
        let bracketed = kind == parser_kind(&["Term", "doSeqBracketed"]);
        let mut parts = node(
            sequence,
            if bracketed {
                "doSeqBracketed"
            } else {
                "doSeqIndent"
            },
            if bracketed { 3 } else { 1 },
        )?;
        let index = usize::from(bracketed);
        let items = children(std::mem::replace(&mut parts[index], Syntax::Missing))?;
        let mut rewritten = Vec::with_capacity(items.len());
        for item in items {
            self.tick()?;
            let mut item = node(item, "doSeqItem", 2)?;
            let separator = item.pop().expect("item separator");
            let element = item.pop().expect("item element");
            let (lifts, element) = self.lift_element(element)?;
            *lifted += lifts.len();
            for lift in lifts {
                rewritten.push(Syntax::node(
                    parser_kind(&["Term", "doSeqItem"]),
                    vec![lift, null(vec![])],
                ));
            }
            rewritten.push(Syntax::node(
                parser_kind(&["Term", "doSeqItem"]),
                vec![element, separator],
            ));
        }
        parts[index] = null(rewritten);
        Ok(Syntax::node(kind, parts))
    }

    /// The lifted actions of one element, in the order they run, and the element reading them.
    #[inline(never)]
    fn lift_element(
        &mut self,
        element: Syntax,
    ) -> Result<(Vec<Syntax>, Syntax), NatDefinitionElabError> {
        enum Task<'a> {
            /// A subtree, and whether it lies under a binder.
            Visit(&'a Syntax, bool),
            Build(&'a Syntax, usize),
            /// The action whose element was just built: bind it, and read its name.
            Lift,
        }
        let mut lifts = Vec::new();
        let mut tasks = vec![Task::Visit(&element, false)];
        let mut built: Vec<Syntax> = Vec::new();
        while let Some(task) = tasks.pop() {
            self.tick()?;
            match task {
                Task::Visit(node, _) if delimiter(node) => built.push(node.clone()),
                Task::Visit(node @ Syntax::Node { args, .. }, under_binder)
                    if is(node, "nestedAction") =>
                {
                    let [arrow, action] = args.as_slice() else {
                        return Err(invalid());
                    };
                    if under_binder
                        || !matches!(arrow, Syntax::Atom { val, .. } if val == "←" || val == "<-")
                    {
                        return Err(invalid());
                    }
                    tasks.push(Task::Lift);
                    tasks.push(Task::Visit(action, false));
                }
                Task::Visit(node @ Syntax::Node { args, .. }, under_binder) => {
                    let under = under_binder || binder(node);
                    tasks.push(Task::Build(node, built.len()));
                    for (index, argument) in args.iter().enumerate().rev() {
                        // A pure `if`'s branches, and a `doIf`'s `else if` conditions, which run
                        // only when reached: an action there is not lifted, and the pin refuses
                        // it ("must be nested inside a `do` expression").
                        let refused = (pure_conditional(node) && index != 1)
                            || (is(node, "doIf") && index == 4);
                        tasks.push(Task::Visit(argument, under || refused));
                    }
                }
                Task::Visit(leaf, _) => built.push(leaf.clone()),
                Task::Build(Syntax::Node { info, kind, .. }, start) => {
                    let node = Syntax::Node {
                        info: *info,
                        kind: kind.clone(),
                        args: built.split_off(start),
                    };
                    built.push(node);
                }
                Task::Build(..) => unreachable!("only nodes are built"),
                Task::Lift => {
                    let action = built.pop().ok_or_else(invalid)?;
                    let name = self.do_control_name()?;
                    lifts.push(mutation::bind_element(name.clone(), null(vec![]), action));
                    built.push(name);
                }
            }
        }
        let element = built.pop().ok_or_else(invalid)?;
        if !built.is_empty() {
            return Err(invalid());
        }
        Ok((lifts, element))
    }
}
