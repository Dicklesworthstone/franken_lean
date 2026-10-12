//! `let mut` and reassignment (`x := e`, `x ← e`), as the pin's `do` elaborator
//! (`Lean/Elab/BuiltinDo/Let.lean`, `For.lean`, `Lean/Elab/Do/Basic.lean`), rewritten into the
//! immutable `do` the rest of this module expands. One pass per `do` block, before expansion:
//! - `let mut x := e` is `let x := e`. A reassignment `x := e` is `let x : T := e` and `x ← e` is
//!   `let x : T ← e`, where `T` is the type of the `x` it replaces (`pushTypeIntoReassignment`).
//! - A branch statement (`if`, `match`, `unless`, a nested `do`) that reassigns variables declared
//!   before it, and is followed by statements that read them, binds them again from its result.
//!   Each branch ends with `pure (x, y, …)`, the right-nested `Prod` of `mkProdMkN`, which stands
//!   for the pin's join-point parameters.
//! - A `for` loop that reassigns them carries them as its `ForIn` state (`elabDoFor`). The
//!   callback starts from the tuple. Every exit (`continue`, `break`, the end of the body) yields
//!   the variables' values at that point. The loop's result binds them again.
//!   A returning loop also carries Option R; its checked state continuation receives the final
//!   values before either resuming the suffix or forwarding a nonlocal return.
//!
//! - A branch statement whose every reassigning branch ends in `break` or `continue` needs no join:
//!   the jump yields the values it reads, so it stays a plain `do` element.
//! - In a loop body, a reassigning branch statement whose other branches jump is closed over the
//!   statements after it: they, and then `continue`, end each branch that falls through, which is
//!   what falling off the body's end means (`close_over_rest`). Every reassigning branch then jumps.
//!
//! Refused where the pin accepts, a refusal and never a different meaning:
//! - a reassigning branch statement that also contains `return`, or that is a `try`;
//! - outside a loop body, one that also contains `break` or `continue` with a reassigning branch
//!   that falls through (its join would also have to forward the exit). Inside one, the same when
//!   a branch binds a name the statements after it read (`| some n => …` before `s := s + n` with
//!   an outer `n`): their copy in that branch would capture it;
//! - a pattern reassignment (`(a, b) := e`).
//!
//! Refused as the pin refuses them:
//! - reassigning a name not declared `mut` in this `do` block ("cannot be mutated");
//! - declaring a name that shadows a `mut` variable (`checkMutVarsForShadowing`).
use super::*;

fn is(syntax: &Syntax, kind: &str) -> bool {
    syntax.kind() == Some(&parser_kind(&["Term", kind]))
}

/// A term-level `do` (and the pin's term forms that expand into one) is its own block: its
/// variables, and those it may mutate, are its own (`elabDo` starts a fresh context).
fn is_block(syntax: &Syntax) -> bool {
    ["do", "termFor", "termTry", "termUnless", "termReturn"]
        .iter()
        .any(|kind| is(syntax, kind))
}

/// Inner blocks are rewritten first, so any mutation below a block is its own.
fn contains_mutation(block: &Syntax) -> bool {
    let mut pending = vec![block];
    while let Some(syntax) = pending.pop() {
        if is_mutation(syntax) {
            return true;
        }
        if let Syntax::Node { args, .. } = syntax {
            pending.extend(args);
        }
    }
    false
}

fn non_empty(syntax: &Syntax) -> bool {
    matches!(syntax, Syntax::Node { args, .. } if !args.is_empty())
}

/// `let mut …` or a reassignment: the elements this pass rewrites.
pub(in crate::source) fn is_mutation(syntax: &Syntax) -> bool {
    ((is(syntax, "doLet") || is(syntax, "doLetArrow"))
        && matches!(syntax, Syntax::Node { args, .. } if args.get(1).is_some_and(non_empty)))
        || is(syntax, "doReassign")
        || is(syntax, "doReassignArrow")
}

/// The variable a reassignment names; `None` for a pattern reassignment.
fn reassigned_name(element: &Syntax) -> Option<Name> {
    let Syntax::Node { args, .. } = element else {
        return None;
    };
    let declaration = args.first()?;
    let Syntax::Node { args, .. } = declaration else {
        return None;
    };
    let name = if is(declaration, "letIdDeclNoBinders") {
        let Syntax::Node { args, .. } = args.first()? else {
            return None;
        };
        args.first()?
    } else if is(declaration, "doIdDecl") {
        args.first()?
    } else {
        return None;
    };
    match name {
        Syntax::Ident { val, .. } => Some(val.clone()),
        _ => None,
    }
}

/// What the do elements of one element do, not counting nested `do` blocks: the names it
/// reassigns, whether it returns, and whether it leaves an enclosing loop (`break`/`continue`
/// outside its own loops). `try` is reported too: its handlers are not rewritten here.
#[derive(Default)]
struct Facts {
    reassigned: Vec<Name>,
    returns: bool,
    jumps: bool,
    handles: bool,
}

fn facts(element: &Syntax) -> Facts {
    let mut facts = Facts::default();
    let mut pending = vec![(element, false)];
    while let Some((syntax, looped)) = pending.pop() {
        if is_block(syntax) {
            continue;
        }
        if (is(syntax, "doReassign") || is(syntax, "doReassignArrow"))
            && let Some(name) = reassigned_name(syntax)
            && !facts.reassigned.contains(&name)
        {
            facts.reassigned.push(name);
        }
        facts.returns |= is(syntax, "doReturn");
        facts.jumps |= !looped && (is(syntax, "doBreak") || is(syntax, "doContinue"));
        facts.handles |= is(syntax, "doTry") || is(syntax, "nativeDoTry");
        if let Syntax::Node { args, .. } = syntax {
            let looped = looped || is(syntax, "doFor") || is(syntax, "nativeDoMutFor");
            pending.extend(args.iter().map(|argument| (argument, looped)));
        }
    }
    facts
}

/// The last element of a `doSeqIndent` or `doSeqBracketed`.
fn last_element(sequence: &Syntax) -> Option<&Syntax> {
    let Syntax::Node { args, .. } = sequence else {
        return None;
    };
    let items = if is(sequence, "doSeqBracketed") {
        args.get(1)
    } else {
        args.first()
    };
    let Some(Syntax::Node { args: items, .. }) = items else {
        return None;
    };
    match items.last() {
        Some(Syntax::Node { args, .. }) => args.first(),
        _ => None,
    }
}

/// The branch sequences of a branch statement: an `if`'s then, else-if and else sequences, a
/// `match`'s alternatives, and the sequence of a nested `do` or of an `unless` body.
fn branch_sequences(element: &Syntax) -> Vec<&Syntax> {
    fn last(syntax: &Syntax) -> Option<&Syntax> {
        match syntax {
            Syntax::Node { args, .. } => args.last(),
            _ => None,
        }
    }
    let Syntax::Node { args, .. } = element else {
        return Vec::new();
    };
    let mut sequences = Vec::new();
    if is(element, "doIf") {
        sequences.extend(args.get(3));
        if let Some(Syntax::Node { args: clauses, .. }) = args.get(4) {
            sequences.extend(clauses.iter().filter_map(last));
        }
        sequences.extend(args.get(5).and_then(last));
    } else if is(element, "doMatch") {
        if let Some(Syntax::Node {
            args: alternatives, ..
        }) = args.last()
            && let Some(Syntax::Node { args: rows, .. }) = alternatives.first()
        {
            sequences.extend(rows.iter().filter_map(last));
        }
    } else {
        sequences.extend(args.last());
    }
    sequences
}

/// Whether every branch of `element` that reassigns one of `state` ends in `break` or `continue`,
/// so that control never leaves the statement with one of them reassigned.
fn jumps_out_with(element: &Syntax, state: &[Name]) -> bool {
    branch_sequences(element).into_iter().all(|sequence| {
        !facts(sequence)
            .reassigned
            .iter()
            .any(|name| state.contains(name))
            || last_element(sequence)
                .is_some_and(|last| is(last, "doBreak") || is(last, "doContinue"))
    })
}

/// A loop body's branch statement that reassigns, jumps in one branch and falls through in
/// another (`if c then s := s + 1 else break`, then statements that read `s`), with `rest`, the
/// statements after it, and then `continue` appended to each branch that falls through. Falling
/// off the end of the body is `continue`, so this is the same loop body, and now every branch that
/// reassigns ends in a jump, which needs no join (`jumps_out_with`). `None` when the statement is
/// not of that kind, or when a branch binds a name that `rest` reads: the copy in that branch would
/// capture it.
fn close_over_rest(
    element: &Syntax,
    muts: &[Name],
    rest: &[Syntax],
) -> Result<Option<Syntax>, NatDefinitionElabError> {
    if !["doIf", "doMatch", "doUnless", "doNested"]
        .iter()
        .any(|kind| is(element, kind))
    {
        return Ok(None);
    }
    let facts = facts(element);
    let state: Vec<Name> = muts
        .iter()
        .filter(|name| facts.reassigned.contains(name))
        .cloned()
        .collect();
    if state.is_empty() || !facts.jumps || facts.returns || facts.handles {
        return Ok(None);
    }
    if jumps_out_with(element, &state) {
        return Ok(None);
    }
    let mut read = Vec::new();
    for statement in rest {
        identifier_roots(statement, &mut read);
    }
    let element = if is(element, "doUnless") {
        unless::expand(element.clone())?
    } else {
        element.clone()
    };
    let close = |sequence: Syntax,
                 bound: Vec<Name>|
     -> Result<Option<Syntax>, NatDefinitionElabError> {
        if last_element(&sequence).is_some_and(|last| is(last, "doBreak") || is(last, "doContinue"))
        {
            return Ok(Some(sequence));
        }
        let Some(mut bound) = sequence_binders(&sequence, bound) else {
            return Ok(None);
        };
        bound.retain(|name| !muts.contains(name));
        if bound.iter().any(|name| read.contains(name)) {
            return Ok(None);
        }
        let bracketed = is(&sequence, "doSeqBracketed");
        let mut items = sequence_items(sequence)?;
        items.extend(rest.iter().cloned());
        items.push(term("doSeqItem", vec![continue_element(), null(vec![])]));
        Ok(Some(items_sequence(items, bracketed)))
    };
    if is(&element, "doNested") {
        let mut parts = node(element, "doNested", 2)?;
        let sequence = parts.pop().expect("nested sequence");
        let Some(sequence) = close(sequence, Vec::new())? else {
            return Ok(None);
        };
        parts.push(sequence);
        return Ok(Some(term("doNested", parts)));
    }
    if is(&element, "doMatch") {
        let mut parts = node(element, "doMatch", 7)?;
        let mut alternatives = node(parts.pop().expect("match alternatives"), "matchAlts", 1)?;
        let rows = children(alternatives.pop().expect("match rows"))?;
        let mut rebuilt = Vec::with_capacity(rows.len());
        for row in rows {
            let mut row = node(row, "matchAlt", 4)?;
            let sequence = row.pop().expect("match alternative sequence");
            let mut bound = Vec::new();
            binder_names(&row[1], &mut bound);
            let Some(sequence) = close(sequence, bound)? else {
                return Ok(None);
            };
            row.push(sequence);
            rebuilt.push(term("matchAlt", row));
        }
        parts.push(term("matchAlts", vec![null(rebuilt)]));
        return Ok(Some(term("doMatch", parts)));
    }
    let mut parts = node(element, "doIf", 6)?;
    let otherwise = parts.pop().expect("else clause");
    let clauses = children(parts.pop().expect("else-if clauses"))?;
    let sequence = parts.pop().expect("then sequence");
    let mut bound = Vec::new();
    if let Some(binder) = condition_binder(&parts[1]) {
        binder_names(binder, &mut bound);
    }
    let Some(sequence) = close(sequence, bound)? else {
        return Ok(None);
    };
    parts.push(sequence);
    let mut rebuilt = Vec::with_capacity(clauses.len());
    for clause in clauses {
        let mut clause = take(clause, Name::from_components(["group"]), Some(4))?;
        let sequence = clause.pop().expect("else-if sequence");
        let mut bound = Vec::new();
        if let Some(binder) = condition_binder(&clause[1]) {
            binder_names(binder, &mut bound);
        }
        let Some(sequence) = close(sequence, bound)? else {
            return Ok(None);
        };
        clause.push(sequence);
        rebuilt.push(Syntax::node(Name::from_components(["group"]), clause));
    }
    parts.push(null(rebuilt));
    let mut otherwise = children(otherwise)?;
    let otherwise = match otherwise.pop() {
        Some(sequence) => {
            let keyword = otherwise.pop().ok_or_else(invalid)?;
            let Some(sequence) = close(sequence, Vec::new())? else {
                return Ok(None);
            };
            vec![keyword, sequence]
        }
        // An absent `else` falls through to `rest`.
        None => {
            let mut items = rest.to_vec();
            items.push(term("doSeqItem", vec![continue_element(), null(vec![])]));
            vec![atom("else"), items_sequence(items, false)]
        }
    };
    parts.push(null(otherwise));
    Ok(Some(term("doIf", parts)))
}

/// The names a branch sequence binds for the statements after its end: `bound` (its condition's
/// or pattern's names) and its top-level `let`, `have` and `←` binders. `None` for a binding form
/// this does not read (`let … | else`, `let rec`, a pattern bind with a fallback).
fn sequence_binders(sequence: &Syntax, mut bound: Vec<Name>) -> Option<Vec<Name>> {
    let items = match sequence {
        Syntax::Node { args, .. } if is(sequence, "doSeqBracketed") => args.get(1),
        Syntax::Node { args, .. } => args.first(),
        _ => None,
    };
    let Some(Syntax::Node { args: items, .. }) = items else {
        return Some(bound);
    };
    for item in items {
        let Syntax::Node { args, .. } = item else {
            continue;
        };
        let Some(element) = args.first() else {
            continue;
        };
        if is(element, "doLetElse") || is(element, "doLetRec") || fallback::is_binding(element) {
            return None;
        }
        let Syntax::Node { args, .. } = element else {
            continue;
        };
        if is(element, "doLet") || is(element, "doHave") {
            // `letDecl`'s binder: `letIdDecl`'s `letId`, or `letPatDecl`'s pattern.
            if let Some(Syntax::Node { args, .. }) = args.last()
                && let Some(Syntax::Node { args, .. }) = args.first()
                && let Some(binder) = args.first()
            {
                binder_names(binder, &mut bound);
            }
        } else if is(element, "doLetArrow")
            && let Some(Syntax::Node { args, .. }) = args.last()
            && let Some(binder) = args.first()
        {
            binder_names(binder, &mut bound);
        }
    }
    Some(bound)
}

/// Every name a binder or pattern mentions, constructor names included (a superset is safe).
fn binder_names(binder: &Syntax, out: &mut Vec<Name>) {
    let mut pending = vec![binder];
    while let Some(syntax) = pending.pop() {
        match syntax {
            Syntax::Ident { val, .. } => out.push(root_name(val)),
            Syntax::Node { args, .. } => pending.extend(args),
            _ => {}
        }
    }
}

/// The first component of every identifier in `syntax`: what `x.succ` reads is `x`.
fn identifier_roots(syntax: &Syntax, out: &mut Vec<Name>) {
    let mut pending = vec![syntax];
    while let Some(syntax) = pending.pop() {
        match syntax {
            Syntax::Ident { val, .. } => out.push(root_name(val)),
            Syntax::Node { args, .. } => pending.extend(args),
            _ => {}
        }
    }
}

fn root_name(name: &Name) -> Name {
    let mut name = name.clone();
    while !name.parent().is_anonymous() {
        name = name.parent();
    }
    name
}

fn continue_element() -> Syntax {
    term("doContinue", vec![atom("continue")])
}

/// A `doSeqIndent` or `doSeqBracketed` of these `doSeqItem`s.
fn items_sequence(items: Vec<Syntax>, bracketed: bool) -> Syntax {
    if bracketed {
        term("doSeqBracketed", vec![atom("{"), null(items), atom("}")])
    } else {
        term("doSeqIndent", vec![null(items)])
    }
}

/// Whether a binder (a name or a pattern) mentions a `mut` variable.
fn shadows(binder: &Syntax, muts: &[Name]) -> bool {
    let mut pending = vec![binder];
    while let Some(syntax) = pending.pop() {
        match syntax {
            Syntax::Ident { val, .. } if muts.contains(val) => return true,
            Syntax::Node { args, .. } => pending.extend(args),
            _ => {}
        }
    }
    false
}

fn term(kind: &str, args: Vec<Syntax>) -> Syntax {
    Syntax::node(parser_kind(&["Term", kind]), args)
}

fn named(name: &Name) -> Syntax {
    ident(name.clone())
}

fn root(components: &[&str]) -> Syntax {
    ident(Name::from_components(
        std::iter::once("_root_").chain(components.iter().copied()),
    ))
}

fn application(function: Syntax, arguments: Vec<Syntax>) -> Syntax {
    term("app", vec![function, null(arguments)])
}

/// `(x, y, z)` as `mkProdMkN` builds it: `Prod.mk x (Prod.mk y z)`; one variable is itself.
pub(super) fn state_tuple(state: &[Syntax]) -> Syntax {
    let mut components = state.iter().rev();
    let mut tuple = components.next().cloned().expect("a nonempty state");
    for component in components {
        tuple = application(root(&["Prod", "mk"]), vec![component.clone(), tuple]);
    }
    tuple
}

/// Whether `syntax` is a `state_tuple` of plain names.
pub(super) fn is_state_tuple(syntax: &Syntax) -> bool {
    let mut syntax = syntax;
    loop {
        if matches!(syntax, Syntax::Ident { val, .. } if !val.is_anonymous() && val.parent().is_anonymous())
        {
            return true;
        }
        let Syntax::Node { args, .. } = syntax else {
            return false;
        };
        if !is(syntax, "app")
            || !matches!(&args[..], [Syntax::Ident { val, .. }, _]
                if val == &Name::from_components(["_root_", "Prod", "mk"]))
        {
            return false;
        }
        let Syntax::Node { args: pair, .. } = &args[1] else {
            return false;
        };
        let [first, rest] = &pair[..] else {
            return false;
        };
        if !matches!(first, Syntax::Ident { val, .. } if !val.is_anonymous() && val.parent().is_anonymous())
        {
            return false;
        }
        syntax = rest;
    }
}

/// The `index`-th of `count` components of a `state_tuple` value.
pub(super) fn component(tuple: &Syntax, index: usize, count: usize) -> Syntax {
    let mut value = tuple.clone();
    for _ in 0..index {
        value = application(root(&["Prod", "snd"]), vec![value]);
    }
    if index + 1 < count {
        value = application(root(&["Prod", "fst"]), vec![value]);
    }
    value
}

/// The type of the local `name` in scope where this node is elaborated.
fn type_of(name: &Name) -> Syntax {
    null(vec![term(
        "typeSpec",
        vec![atom(":"), term("nativeDoTypeOf", vec![named(name)])],
    )])
}

fn let_config() -> Syntax {
    term("letConfig", vec![null(vec![])])
}

/// `let name annotation := value`.
fn let_element(name: &Name, annotation: Syntax, value: Syntax) -> Syntax {
    term(
        "doLet",
        vec![
            atom("let"),
            null(vec![]),
            let_config(),
            term(
                "letDecl",
                vec![term(
                    "letIdDecl",
                    vec![
                        term("letId", vec![named(name)]),
                        null(vec![]),
                        annotation,
                        atom(":="),
                        value,
                    ],
                )],
            ),
        ],
    )
}

/// `let name annotation ← value`, `value` a do element.
fn bind_element(name: Syntax, annotation: Syntax, value: Syntax) -> Syntax {
    term(
        "doLetArrow",
        vec![
            atom("let"),
            null(vec![]),
            let_config(),
            term("doIdDecl", vec![name, annotation, atom("←"), value]),
        ],
    )
}

fn sequence_of(elements: Vec<Syntax>, bracketed: bool) -> Syntax {
    let items = null(
        elements
            .into_iter()
            .map(|element| term("doSeqItem", vec![element, null(vec![])]))
            .collect(),
    );
    if bracketed {
        term("doSeqBracketed", vec![atom("{"), items, atom("}")])
    } else {
        term("doSeqIndent", vec![items])
    }
}

/// The pin's error for this pass's own refusals: the names in scope do not admit the program.
fn refused() -> NatDefinitionElabError {
    invalid()
}

impl Context {
    /// Rewrite every `do` block of `syntax` that declares or reassigns a `mut` variable, inner
    /// blocks first. The result contains no mutation: an element this pass does not rewrite is
    /// refused when it contains one.
    pub(in crate::source) fn eliminate_do_mutation(
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
                    built.push(if is(&node, "do") && contains_mutation(&node) {
                        self.mutable_block(node)?
                    } else {
                        node
                    });
                }
                Task::Build(..) => unreachable!("only nodes are built"),
            }
        }
        let result = built.pop().ok_or_else(invalid)?;
        // Mutation outside any `do` block (or in an element kept as written) is refused.
        let mut pending = vec![&result];
        while let Some(syntax) = pending.pop() {
            self.tick()?;
            if is_mutation(syntax) {
                return Err(refused());
            }
            if let Syntax::Node { args, .. } = syntax {
                pending.extend(args);
            }
        }
        Ok(result)
    }

    fn mutable_block(&mut self, block: Syntax) -> Result<Syntax, NatDefinitionElabError> {
        let mut parts = node(block, "do", 2)?;
        let sequence = parts.pop().expect("do sequence");
        parts.push(self.mutable_sequence(sequence, &[], None, false, false)?);
        Ok(term("do", parts))
    }

    /// One sequence with the `mut` variables `muts` in scope. `tail`: the variables its end yields
    /// as the result of a rewritten branch. `continues`: whether statements after this sequence
    /// read the variables it reassigns (a loop body's next iteration does). `looped`: the sequence
    /// is (inside) the body of a loop that carries state, where a bound branch statement becomes
    /// a term (`stateful_term`).
    fn mutable_sequence(
        &mut self,
        sequence: Syntax,
        muts: &[Name],
        tail: Option<&[Name]>,
        continues: bool,
        looped: bool,
    ) -> Result<Syntax, NatDefinitionElabError> {
        let bracketed = is(&sequence, "doSeqBracketed");
        let statements = sequence_items(sequence)?;
        let count = statements.len();
        let mut muts = muts.to_vec();
        let mut elements = Vec::with_capacity(count);
        // The body of a loop that carries state: falling off its end is `continue`.
        let loop_body = looped && continues && tail.is_none();
        let mut statements = statements.into_iter();
        let mut index = 0;
        while let Some(statement) = statements.next() {
            self.tick()?;
            let element = sequence_element(statement)?;
            let continues = index + 1 < count || tail.is_some() || continues;
            if loop_body
                && let Some(closed) = close_over_rest(&element, &muts, statements.as_slice())?
            {
                // The statements after it now end each branch that falls through.
                self.mutable_element(closed, &mut muts, continues, looped, &mut elements)?;
                break;
            }
            self.mutable_element(element, &mut muts, continues, looped, &mut elements)?;
            index += 1;
        }
        if let Some(state) = tail {
            let state: Vec<Syntax> = state.iter().map(named).collect();
            elements.push(term("doExpr", vec![call(false, vec![state_tuple(&state)])]));
        }
        Ok(sequence_of(elements, bracketed))
    }

    fn mutable_element(
        &mut self,
        element: Syntax,
        muts: &mut Vec<Name>,
        continues: bool,
        looped: bool,
        out: &mut Vec<Syntax>,
    ) -> Result<(), NatDefinitionElabError> {
        if is(&element, "doLet") || is(&element, "doHave") {
            let have = is(&element, "doHave");
            let mut parts = node(
                element,
                if have { "doHave" } else { "doLet" },
                if have { 3 } else { 4 },
            )?;
            let declaration = parts.last().expect("let declaration");
            // `letDecl`'s binder: `letIdDecl`'s `letId`, or `letPatDecl`'s pattern.
            let binder = match declaration {
                Syntax::Node { args, .. } => match args.first() {
                    Some(Syntax::Node { args, .. }) => args.first(),
                    _ => None,
                },
                _ => None,
            }
            .ok_or_else(invalid)?;
            if shadows(binder, muts) {
                return Err(refused());
            }
            let declared = if !have && non_empty(&parts[1]) {
                // `let mut` binds one name (the parser reads no mutable pattern).
                let declared = match binder {
                    Syntax::Node { args, .. } if is(binder, "letId") => match args.first() {
                        Some(Syntax::Ident { val, .. }) => val.clone(),
                        _ => return Err(refused()),
                    },
                    _ => return Err(refused()),
                };
                parts[1] = null(vec![]);
                Some(declared)
            } else {
                None
            };
            out.push(term(if have { "doHave" } else { "doLet" }, parts));
            muts.extend(declared);
            return Ok(());
        }
        if is(&element, "doLetArrow") {
            let mut parts = node(element, "doLetArrow", 4)?;
            let mutable = non_empty(&parts[1]);
            let declaration = parts.pop().expect("bind declaration");
            let mut declaration_parts = match &declaration {
                Syntax::Node { args, .. } => args.clone(),
                _ => return Err(invalid()),
            };
            let kind = declaration.kind().cloned().ok_or_else(invalid)?;
            let binder = declaration_parts.first().ok_or_else(invalid)?;
            if shadows(binder, muts) {
                return Err(refused());
            }
            let declared = if mutable {
                match binder {
                    Syntax::Ident { val, .. } if kind == parser_kind(&["Term", "doIdDecl"]) => {
                        Some(val.clone())
                    }
                    _ => return Err(refused()),
                }
            } else {
                None
            };
            // The bound action (index 3 of `doIdDecl` and `doPatDecl`) may be a branch statement.
            let value = std::mem::replace(
                declaration_parts.get_mut(3).ok_or_else(invalid)?,
                Syntax::Missing,
            );
            declaration_parts[3] = self.mutable_action(value, muts, looped)?;
            parts[1] = null(vec![]);
            parts.push(Syntax::node(kind, declaration_parts));
            out.push(term("doLetArrow", parts));
            muts.extend(declared);
            return Ok(());
        }
        if is(&element, "doReassign") {
            let name = reassigned_name(&element).ok_or_else(refused)?;
            if !muts.contains(&name) {
                return Err(refused());
            }
            let mut parts = node(element, "doReassign", 1)?;
            let mut declaration =
                node(parts.pop().expect("reassignment"), "letIdDeclNoBinders", 5)?;
            expect_empty_null(&declaration[1], "reassignment parameters")?;
            expect_empty_null(&declaration[2], "reassignment type")?;
            expect_atom(&declaration[3], ":=", "reassignment")?;
            let value = declaration.pop().expect("reassigned value");
            out.push(let_element(&name, type_of(&name), value));
            return Ok(());
        }
        if is(&element, "doReassignArrow") {
            let name = reassigned_name(&element).ok_or_else(refused)?;
            if !muts.contains(&name) {
                return Err(refused());
            }
            let mut parts = node(element, "doReassignArrow", 1)?;
            let mut declaration = node(parts.pop().expect("reassignment"), "doIdDecl", 4)?;
            expect_empty_null(&declaration[1], "reassignment type")?;
            let value = declaration.pop().expect("reassigned action");
            let value = self.mutable_action(value, muts, looped)?;
            let arrow = declaration.pop().expect("reassignment arrow");
            out.push(term(
                "doLetArrow",
                vec![
                    atom("let"),
                    null(vec![]),
                    let_config(),
                    term("doIdDecl", vec![named(&name), type_of(&name), arrow, value]),
                ],
            ));
            return Ok(());
        }
        if is(&element, "doFor") {
            return self.mutable_loop(element, muts, looped, !continues, out);
        }
        if is(&element, "doIf")
            || is(&element, "doMatch")
            || is(&element, "doUnless")
            || is(&element, "doNested")
        {
            let facts = facts(&element);
            let state: Vec<Name> = muts
                .iter()
                .filter(|name| facts.reassigned.contains(name))
                .cloned()
                .collect();
            if state.is_empty() || !continues {
                // Reassignments nothing reads afterwards stay inside their branches.
                out.push(self.mutable_branches(element, muts, None, looped)?);
                return Ok(());
            }
            if facts.returns || facts.handles {
                return Err(refused());
            }
            if facts.jumps {
                // Every branch that reassigns ends in `break` or `continue`, which yields the
                // values it reads: no reassignment falls through, so the statement needs no join.
                if !jumps_out_with(&element, &state) {
                    return Err(refused());
                }
                out.push(self.mutable_branches(element, muts, None, looped)?);
                return Ok(());
            }
            let branches = if looped {
                term(
                    "doExpr",
                    vec![self.stateful_term(element, muts, Some(&state))?],
                )
            } else {
                self.mutable_branches(element, muts, Some(&state), false)?
            };
            self.bind_state(&state, branches, out)?;
            return Ok(());
        }
        // Everything else is kept as written. It may not reassign this block's variables, nor bind
        // a name that shadows one (the pin's check covers every do binder).
        let facts = facts(&element);
        if muts.iter().any(|name| facts.reassigned.contains(name)) {
            return Err(refused());
        }
        if !muts.is_empty()
            && (facts.handles
                || is(&element, "doLetElse")
                || is(&element, "doLetRec")
                || fallback::is_binding(&element))
            && shadows(&element, muts)
        {
            return Err(refused());
        }
        out.push(element);
        Ok(())
    }

    /// A bound action (`let x ← a`, `x ← a`): a branch statement in it may declare its own `mut`
    /// variables, but may not reassign the enclosing ones.
    fn mutable_action(
        &mut self,
        value: Syntax,
        muts: &[Name],
        looped: bool,
    ) -> Result<Syntax, NatDefinitionElabError> {
        if !(is(&value, "doIf")
            || is(&value, "doMatch")
            || is(&value, "doUnless")
            || is(&value, "doNested"))
        {
            return Ok(value);
        }
        let facts = facts(&value);
        if muts.iter().any(|name| facts.reassigned.contains(name)) {
            return Err(refused());
        }
        if looped {
            if facts.returns || facts.jumps || facts.handles {
                return Err(refused());
            }
            return Ok(term("doExpr", vec![self.stateful_term(value, muts, None)?]));
        }
        self.mutable_branches(value, muts, None, false)
    }

    /// `let x : T ← branches` for one variable; `let s ← branches; let x := s.1; …` for several.
    fn bind_state(
        &mut self,
        state: &[Name],
        action: Syntax,
        out: &mut Vec<Syntax>,
    ) -> Result<(), NatDefinitionElabError> {
        if let [name] = state {
            out.push(bind_element(named(name), type_of(name), action));
            return Ok(());
        }
        let result = self.do_control_name()?;
        out.push(bind_element(result.clone(), null(vec![]), action));
        for (index, name) in state.iter().enumerate() {
            self.tick()?;
            out.push(let_element(
                name,
                null(vec![]),
                component(&result, index, state.len()),
            ));
        }
        Ok(())
    }

    /// Each branch sequence of a branch statement, ending in `pure tail` when given.
    fn mutable_branches(
        &mut self,
        element: Syntax,
        muts: &[Name],
        tail: Option<&[Name]>,
        looped: bool,
    ) -> Result<Syntax, NatDefinitionElabError> {
        if is(&element, "doUnless") {
            // `unless c do s` is `if c then pure () else s` (`unless::expand`).
            return self.mutable_branches(unless::expand(element)?, muts, tail, looped);
        }
        if is(&element, "doNested") {
            let mut parts = node(element, "doNested", 2)?;
            let sequence = parts.pop().expect("nested sequence");
            parts.push(self.mutable_sequence(sequence, muts, tail, false, looped)?);
            return Ok(term("doNested", parts));
        }
        if is(&element, "doMatch") {
            let mut parts = node(element, "doMatch", 7)?;
            let mut alternatives = node(parts.pop().expect("match alternatives"), "matchAlts", 1)?;
            let rows = children(alternatives.pop().expect("match rows"))?;
            let mut rebuilt = Vec::with_capacity(rows.len());
            for row in rows {
                self.tick()?;
                let mut row = node(row, "matchAlt", 4)?;
                if shadows(&row[1], muts) {
                    return Err(refused());
                }
                let sequence = row.pop().expect("match alternative sequence");
                row.push(self.mutable_sequence(sequence, muts, tail, false, looped)?);
                rebuilt.push(term("matchAlt", row));
            }
            parts.push(term("matchAlts", vec![null(rebuilt)]));
            return Ok(term("doMatch", parts));
        }
        let mut parts = node(element, "doIf", 6)?;
        if condition_binder(&parts[1]).is_some_and(|binder| shadows(binder, muts)) {
            return Err(refused());
        }
        let otherwise = parts.pop().expect("else clause");
        let clauses = children(parts.pop().expect("else-if clauses"))?;
        let sequence = parts.pop().expect("then sequence");
        parts.push(self.mutable_sequence(sequence, muts, tail, false, looped)?);
        let mut rebuilt = Vec::with_capacity(clauses.len());
        for clause in clauses {
            self.tick()?;
            let mut clause = take(clause, Name::from_components(["group"]), Some(4))?;
            if condition_binder(&clause[1]).is_some_and(|binder| shadows(binder, muts)) {
                return Err(refused());
            }
            let sequence = clause.pop().expect("else-if sequence");
            clause.push(self.mutable_sequence(sequence, muts, tail, false, looped)?);
            rebuilt.push(Syntax::node(Name::from_components(["group"]), clause));
        }
        parts.push(null(rebuilt));
        let mut otherwise = children(otherwise)?;
        let otherwise = match (otherwise.pop(), tail) {
            (Some(sequence), _) => {
                let keyword = otherwise.pop().ok_or_else(invalid)?;
                vec![
                    keyword,
                    self.mutable_sequence(sequence, muts, tail, false, looped)?,
                ]
            }
            // An absent `else` yields the variables unchanged.
            (None, Some(state)) => {
                let state: Vec<Syntax> = state.iter().map(named).collect();
                vec![
                    atom("else"),
                    sequence_of(
                        vec![term("doExpr", vec![call(false, vec![state_tuple(&state)])])],
                        false,
                    ),
                ]
            }
            (None, None) => vec![],
        };
        parts.push(null(otherwise));
        Ok(term("doIf", parts))
    }

    /// A jump-free branch statement as a term whose branches are `do` blocks: `if c then do s else
    /// do t`, `match d with | p => do s`, or `do s`. A loop that carries state expands its body
    /// without the nested-sequence joins that a bound `do` element needs; a term needs none.
    fn stateful_term(
        &mut self,
        element: Syntax,
        muts: &[Name],
        tail: Option<&[Name]>,
    ) -> Result<Syntax, NatDefinitionElabError> {
        let block = |sequence: Syntax| term("do", vec![atom("do"), sequence]);
        let element = if is(&element, "doIf") {
            nest_else_ifs(element)?
        } else {
            element
        };
        let element = self.mutable_branches(element, muts, tail, false)?;
        if is(&element, "doNested") {
            let mut parts = node(element, "doNested", 2)?;
            return Ok(block(parts.pop().expect("nested sequence")));
        }
        if is(&element, "doMatch") {
            let mut parts = node(element, "doMatch", 7)?;
            // The do-only dependent switch; the rest is the term `match`'s shape.
            expect_empty_null(&parts[1], "plain do match option")?;
            parts.remove(1);
            for discriminant in children(parts[3].clone())?.iter().step_by(2) {
                let Syntax::Node { args, .. } = discriminant else {
                    return Err(invalid());
                };
                if args.iter().any(|field| is(field, "nestedAction")) {
                    return Err(refused());
                }
            }
            let mut alternatives = node(parts.pop().expect("match alternatives"), "matchAlts", 1)?;
            let rows = children(alternatives.pop().expect("match rows"))?;
            let mut rebuilt = Vec::with_capacity(rows.len());
            for row in rows {
                self.tick()?;
                let mut row = node(row, "matchAlt", 4)?;
                let sequence = row.pop().expect("match alternative sequence");
                row.push(block(sequence));
                rebuilt.push(term("matchAlt", row));
            }
            parts.push(term("matchAlts", vec![null(rebuilt)]));
            return Ok(term("match", parts));
        }
        // `doIf`, its else-if clauses already nested into its `else`.
        let mut parts = node(element, "doIf", 6)?;
        let mut otherwise = children(parts.pop().expect("else clause"))?;
        expect_empty_null(
            &parts.pop().expect("else-if clauses"),
            "nested else-if clauses",
        )?;
        let yes = block(parts.pop().expect("then sequence"));
        let then = parts.pop().expect("then keyword");
        let mut condition =
            node(parts.pop().expect("condition"), "doIfProp", 2).map_err(|_| refused())?;
        let proposition = condition.pop().expect("condition proposition");
        let binder = condition.pop().expect("condition binder");
        let keyword = parts.pop().expect("if keyword");
        let no = match otherwise.pop() {
            Some(sequence) => block(sequence),
            None => block(sequence_of(
                vec![term(
                    "doExpr",
                    vec![call(false, vec![root(&["PUnit", "unit"])])],
                )],
                false,
            )),
        };
        Ok(term(
            "ifThenElse",
            vec![keyword, binder, proposition, then, yes, atom("else"), no],
        ))
    }

    /// A `for` loop. One that reassigns variables declared before it carries them as its state
    /// (`nativeDoMutFor`, expanded by `expand_state_for_loop`), then binds them again.
    /// `last`: nothing follows the loop. Its result is then the block's, the pin's `PUnit`
    /// (`elabDoFor`), so a loop that carries state ends with `pure PUnit.unit` after binding its
    /// state; a block may not end in a binding.
    fn mutable_loop(
        &mut self,
        element: Syntax,
        muts: &[Name],
        looped: bool,
        last: bool,
        out: &mut Vec<Syntax>,
    ) -> Result<(), NatDefinitionElabError> {
        let mut parts = node(element, "doFor", 4)?;
        if loop_binders(&parts[1])
            .into_iter()
            .any(|binder| shadows(binder, muts))
        {
            return Err(refused());
        }
        let body = parts.pop().expect("loop body");
        let facts = facts(&body);
        let state: Vec<Name> = muts
            .iter()
            .filter(|name| facts.reassigned.contains(name))
            .cloned()
            .collect();
        if state.is_empty() {
            parts.push(self.mutable_sequence(body, muts, None, false, looped)?);
            out.push(term("doFor", parts));
            return Ok(());
        }
        if facts.returns {
            parts.push(self.mutable_sequence(body, muts, None, true, true)?);
            parts.push(null(state.iter().map(named).collect()));
            // Retain this sequence for the enclosing return worklist. Its
            // state must parameterize the suffix, not a thunk over old values.
            out.push(term("nativeDoReturningMutFor", parts));
            return Ok(());
        }
        parts.push(self.mutable_sequence(body, muts, None, true, true)?);
        let result = match state.as_slice() {
            [name] => named(name),
            _ => self.do_control_name()?,
        };
        parts.push(null(state.iter().map(named).collect()));
        parts.push(result.clone());
        out.push(term("nativeDoMutFor", parts));
        if state.len() > 1 {
            for (index, name) in state.iter().enumerate() {
                self.tick()?;
                out.push(let_element(
                    name,
                    null(vec![]),
                    component(&result, index, state.len()),
                ));
            }
        }
        if last {
            out.push(term(
                "doExpr",
                vec![call(false, vec![root(&["PUnit", "unit"])])],
            ));
        }
        Ok(())
    }

    /// `nativeDoMutFor`: the loop with its state, as `let s ← forIn xs s (fun x s => body)`.
    pub(super) fn expand_state_for_loop(
        &mut self,
        syntax: Syntax,
    ) -> Result<Syntax, NatDefinitionElabError> {
        let mut parts = node(syntax, "nativeDoMutFor", 6)?;
        let result = parts.pop().expect("loop result");
        let state = children(parts.pop().expect("loop state"))?;
        if state.is_empty() {
            return Err(invalid());
        }
        let (header, sequence) = self.split_for_loop(term("doFor", parts))?;
        let tuple = state_tuple(&state);
        let parameter = match state.as_slice() {
            [name] => name.clone(),
            _ => self.do_control_name()?,
        };
        let yield_step = application(root(&["ForInStep", "yield"]), vec![tuple.clone()]);
        let mut body = self.expand_do_sequence(sequence, Some(call(false, vec![yield_step])))?;
        if state.len() > 1 {
            for (index, name) in state.iter().enumerate().rev() {
                self.tick()?;
                body = Syntax::node(
                    parser_kind(&["Term", "let"]),
                    vec![
                        atom("let"),
                        let_config(),
                        term(
                            "letDecl",
                            vec![term(
                                "letIdDecl",
                                vec![
                                    term("letId", vec![name.clone()]),
                                    null(vec![]),
                                    null(vec![]),
                                    atom(":="),
                                    component(&parameter, index, state.len()),
                                ],
                            )],
                        ),
                        atom(";"),
                        body,
                    ],
                );
            }
        }
        let action = self.finish_for_loop(header, parameter, tuple, body)?;
        Ok(bind_element(
            result,
            null(vec![]),
            term("doExpr", vec![action]),
        ))
    }
}

/// The binder of a `doIf` condition: `h` of `if h : c`, `p` of `if let p := e`.
fn condition_binder(condition: &Syntax) -> Option<&Syntax> {
    let Syntax::Node { args, .. } = condition else {
        return None;
    };
    if is(condition, "doIfProp") {
        args.first()
    } else if is(condition, "doIfLet") {
        args.get(1)
    } else {
        None
    }
}

/// The binders of a `for`'s declarations: the membership witness and the element.
fn loop_binders(declarations: &Syntax) -> Vec<&Syntax> {
    let Syntax::Node { args, .. } = declarations else {
        return Vec::new();
    };
    args.iter()
        .filter_map(|declaration| match declaration {
            Syntax::Node { args, .. } => Some(args.iter().take(2)),
            _ => None,
        })
        .flatten()
        .collect()
}
