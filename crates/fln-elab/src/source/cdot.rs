//! `·`: the pin's cdot functions (`Term.cdot`; `expandCDot?`, `Lean/Elab/BuiltinNotation.lean:323`,
//! applied by `expandParen`, `expandTuple` and `expandTypeAscription`), bead
//! `franken_lean-z8j.1.10`.
//!
//! Parentheses, tuples and type ascriptions bind only the `·` in their own
//! scope whose complete hygiene identity matches the opening delimiter:
//! - `(e)` with `·` in `e` is `fun x₁ … xₙ => e'`, one binder per `·` in source order;
//! - `(e, f)` is `fun x₁ … xₙ => (e', f')`;
//! - `(e : T)` is `((fun x₁ … xₙ => e') : T)`; `T` is not searched.
//!
//! The search never enters a nested parentheses, tuple or ascription, which scopes its own `·`.
//! Each binder gets a fresh name no source identifier can spell, so it never captures a source
//! name (`fun x => (· - x) 10` is `10 - x`, as at the pin). A `·` that no such node scopes is
//! the pin's "invalid occurrence of `·` notation" error, raised where the term is elaborated.
//!
//! The expansion runs inside `lower_pattern_matrices`' single bottom-up rebuild, before
//! collection notation (which would turn a tuple into `Prod.mk` and lose its scope). By the
//! time a node is rebuilt, every nested scope has already been processed. An
//! unmatched quoted or antiquoted `·` is refused before lowering can erase
//! its delimiter and expose it to an enclosing scope.
use super::*;
use fln_syntax::source::{ByteSpan, SourceInfo};

fn null(args: Vec<Syntax>) -> Syntax {
    Syntax::node(Name::from_components(["null"]), args)
}

fn atom(text: &str) -> Syntax {
    Syntax::atom(SourceInfo::None, text)
}

fn identifier(name: Name) -> Syntax {
    Syntax::Ident {
        info: SourceInfo::None,
        raw_val: ByteSpan::default().into(),
        val: name,
        preresolved: Vec::new(),
    }
}

/// A node's parts, taken out of it: `Syntax` drops iteratively, so it cannot be destructured by
/// move. Anything else is handed back unchanged.
fn parts(mut syntax: Syntax) -> Result<(SourceInfo, Name, Vec<Syntax>), Syntax> {
    if let Syntax::Node { info, kind, args } = &mut syntax {
        return Ok((*info, kind.clone(), std::mem::take(args)));
    }
    Err(syntax)
}

fn binds_cdots(kind: &Name) -> bool {
    kind == &parser_kind(&["Term", "paren"])
        || kind == &parser_kind(&["Term", "tuple"])
        || kind == &parser_kind(&["Term", "typeAscription"])
}

pub(super) fn is_cdot(syntax: &Syntax) -> bool {
    syntax.kind() == Some(&parser_kind(&["Term", "cdot"]))
}

fn matches_hygiene(syntax: &Syntax, hygiene: &Name) -> Result<bool, NatDefinitionElabError> {
    if !is_cdot(syntax) {
        return Ok(false);
    }
    let parts = expect_node(syntax, &parser_kind(&["Term", "cdot"]), 2, "cdot")?;
    Ok(hygiene_info_name(&parts[1])? == hygiene)
}

/// A fresh binder name: the atomic numeric name do-notation's generated binders use
/// (`do_control_name`). No source identifier can spell a numeric name, escaped or not, so it
/// never captures one; it stands in for the pin's macro-scoped `x` / `x1`, … , which differ
/// only in how they print.
fn hygienic(serial: u64) -> Name {
    Name::num(Name::anonymous(), serial)
}

impl Context {
    /// The pin's `expandParen` / `expandTuple` / `expandTypeAscription` cdot step on one rebuilt
    /// node; any other node, or one with no `·` in its scope, is returned unchanged.
    pub(super) fn expand_cdot_node(
        &mut self,
        syntax: Syntax,
        pattern: bool,
    ) -> Result<Syntax, NatDefinitionElabError> {
        if pattern || !syntax.kind().is_some_and(binds_cdots) {
            return Ok(syntax);
        }
        let (info, kind, mut args) = match parts(syntax) {
            Ok(parts) => parts,
            Err(other) => return Ok(other),
        };
        // `paren`: `( e )`; `tuple`: `( [e "," [es]] )`; `typeAscription`: `( e ":" [T] )`.
        // Index 0 is the hygienic `(`; index 1 is the scope in all three.
        let (count, hygiene) = match args.get(1) {
            Some(scope) => self.count_cdots(scope, args.first())?,
            None => (0, None),
        };
        if count == 0 {
            return Ok(Syntax::Node { info, kind, args });
        }
        let hygiene = hygiene.ok_or_else(|| failure(SourceInferenceError::Scope))?;
        let mut names = Vec::with_capacity(count);
        for _ in 0..count {
            let serial = self.next;
            self.fresh_name()?;
            names.push(hygienic(serial));
        }
        let scope = std::mem::replace(&mut args[1], null(Vec::new()));
        let scope = self.replace_cdots(scope, &names, &hygiene)?;
        if kind == parser_kind(&["Term", "paren"]) {
            // `(e)` is the function itself.
            return Ok(function(&names, scope));
        }
        if kind == parser_kind(&["Term", "typeAscription"]) {
            // `(e : T)` keeps its type; only its term becomes the function.
            args[1] = function(&names, scope);
            return Ok(Syntax::Node { info, kind, args });
        }
        // `(e, f)`: the function's body is the tuple.
        args[1] = scope;
        Ok(function(&names, Syntax::Node { info, kind, args }))
    }

    /// The `·` in `root`'s own scope: nested scopes are not entered. Iterative: a source tree is
    /// unbounded in depth. Native-generated ascriptions may have a bare opener;
    /// inspect its hygiene only when a dot actually needs a binding scope.
    fn count_cdots(
        &mut self,
        root: &Syntax,
        opener: Option<&Syntax>,
    ) -> Result<(usize, Option<Name>), NatDefinitionElabError> {
        let mut pending = vec![root];
        let mut count = 0usize;
        let mut hygiene = None;
        while let Some(node) = pending.pop() {
            self.tick()?;
            if is_cdot(node) {
                if hygiene.is_none() {
                    let opener = opener.ok_or_else(|| failure(SourceInferenceError::Scope))?;
                    hygiene = Some(parenthesis_hygiene_name(opener)?.clone());
                }
                let identity = hygiene
                    .as_ref()
                    .ok_or_else(|| failure(SourceInferenceError::Scope))?;
                if !matches_hygiene(node, identity)? {
                    // The pin visits enclosing binders before their children;
                    // hasCDot never crosses a tuple/parenthesis boundary. Our
                    // bottom-up lowering must not expose an unmatched dot by
                    // replacing a tuple with Prod.mk or parentheses with a
                    // lambda. Refuse it before removing that boundary. A later
                    // user macro consuming such syntax remains unsupported.
                    return Err(failure(SourceInferenceError::CdotOutsideParentheses));
                }
                count = count
                    .checked_add(1)
                    .ok_or_else(|| failure(SourceInferenceError::ResourceLimit))?;
            } else if let Syntax::Node { kind, args, .. } = node
                && !binds_cdots(kind)
            {
                pending.extend(args);
            }
        }
        Ok((count, hygiene))
    }

    /// Replace the `·` in `root`'s own scope, in source order, by `names`. Iterative, like the
    /// count; it visits exactly the nodes the count did, so the two agree.
    fn replace_cdots(
        &mut self,
        root: Syntax,
        names: &[Name],
        hygiene: &Name,
    ) -> Result<Syntax, NatDefinitionElabError> {
        enum Task {
            Visit(Syntax),
            Build(SourceInfo, Name, usize),
        }
        let mut tasks = vec![Task::Visit(root)];
        let mut built: Vec<Syntax> = Vec::new();
        let mut next = names.iter();
        while let Some(task) = tasks.pop() {
            self.tick()?;
            match task {
                Task::Visit(node) if matches_hygiene(&node, hygiene)? => {
                    let name = next
                        .next()
                        .ok_or_else(|| failure(SourceInferenceError::Scope))?;
                    built.push(identifier(name.clone()));
                }
                Task::Visit(node) if node.kind().is_some_and(|kind| !binds_cdots(kind)) => {
                    let (info, kind, args) = match parts(node) {
                        Ok(parts) => parts,
                        Err(other) => {
                            built.push(other);
                            continue;
                        }
                    };
                    tasks.push(Task::Build(info, kind, built.len()));
                    for argument in args.into_iter().rev() {
                        tasks.push(Task::Visit(argument));
                    }
                }
                Task::Visit(other) => built.push(other),
                Task::Build(info, kind, start) => {
                    let args = built.split_off(start);
                    built.push(Syntax::Node { info, kind, args });
                }
            }
        }
        if next.next().is_some() {
            return Err(failure(SourceInferenceError::Scope));
        }
        built
            .pop()
            .ok_or_else(|| failure(SourceInferenceError::Scope))
    }
}

/// `fun names* => body`, in the shape the parser gives `Term.fun`.
fn function(names: &[Name], body: Syntax) -> Syntax {
    Syntax::node(
        parser_kind(&["Term", "fun"]),
        vec![
            atom("fun"),
            Syntax::node(
                parser_kind(&["Term", "basicFun"]),
                vec![
                    null(names.iter().cloned().map(identifier).collect()),
                    null(Vec::new()),
                    atom("=>"),
                    body,
                ],
            ),
        ],
    )
}
