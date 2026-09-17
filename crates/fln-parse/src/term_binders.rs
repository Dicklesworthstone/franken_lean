//! Lambda and Pi telescopes use the ordinary term parser's heap frames. A
//! binder annotation is another frame phase, not a recursive parser invocation.
//! Leaves and wrappers follow the pinned Term funBinder/forall grammar.
use super::*;

pub(super) struct Prefix {
    keyword: usize,
    lambda: bool,
    dependent_arrow: bool,
    binders: Vec<Syntax>,
    annotation: Option<(usize, Syntax)>,
    separator: Option<usize>,
    phase: Phase,
}

enum Phase {
    Group(Group),
    SharedType(usize),
    Body,
}

struct Group {
    open: usize,
    names: std::ops::Range<usize>,
    colon: Option<usize>,
    kind: &'static str,
    close: &'static str,
}

fn symbol(tokens: &[LexedToken], at: usize, spelling: &str) -> bool {
    matches!(tokens.get(at).map(|t| &t.kind), Some(TokenKind::Symbol(s)) if s == spelling)
}

fn name(tokens: &[LexedToken], at: usize) -> bool {
    matches!(tokens.get(at).map(|t| &t.kind), Some(TokenKind::Ident(_))) || symbol(tokens, at, "_")
}

fn refuse(view: &SourceView, tokens: &[LexedToken], at: usize) -> NatDefinitionParseError {
    NatDefinitionParseError::OutsideSeedGrammar {
        at: original_position(view, tokens, at),
        expected: NatDefinitionExpectation::ParameterTypeAscription,
    }
}

fn binder_name(
    leaves: &Leaves,
    tokens: &[LexedToken],
    at: usize,
) -> Result<Syntax, NatDefinitionParseError> {
    if symbol(tokens, at, "_") {
        Ok(Syntax::node(
            parser_kind(&["Term", "hole"]),
            vec![leaves.leaf(at)?],
        ))
    } else {
        Ok(leaves.leaf(at)?)
    }
}

pub(super) fn frame(prefix: Prefix) -> BoundedTermFrame {
    BoundedTermFrame {
        record: None,
        ascription: None,
        open: None,
        prefix: Some(prefix),
        negation: None,
        application: Vec::new(),
        operands: Vec::new(),
        operators: Vec::new(),
    }
}

impl Prefix {
    pub(super) fn start(
        leaves: &Leaves,
        view: &SourceView,
        tokens: &[LexedToken],
        keyword: usize,
        cursor: &mut usize,
        end: usize,
    ) -> Result<Self, NatDefinitionParseError> {
        let dependent_arrow = matches!(&tokens[keyword].kind, TokenKind::Symbol(s) if matches!(s.as_str(), "(" | "{" | "[" | "⦃"));
        if dependent_arrow {
            *cursor = keyword;
        }
        let mut prefix = Self {
            keyword,
            lambda: symbol(tokens, keyword, "fun") || symbol(tokens, keyword, "λ"),
            dependent_arrow,
            binders: Vec::new(),
            annotation: None,
            separator: None,
            phase: Phase::Body,
        };
        prefix.header(leaves, view, tokens, cursor, end)?;
        Ok(prefix)
    }

    fn separator(&self, tokens: &[LexedToken], at: usize) -> bool {
        if self.dependent_arrow {
            symbol(tokens, at, "->") || symbol(tokens, at, "→")
        } else if self.lambda {
            symbol(tokens, at, "=>") || symbol(tokens, at, "↦")
        } else {
            symbol(tokens, at, ",")
        }
    }

    pub(super) fn body(&self) -> bool {
        matches!(self.phase, Phase::Body)
    }

    pub(super) fn closes_header(&self, tokens: &[LexedToken], at: usize) -> bool {
        match &self.phase {
            Phase::Group(group) => symbol(tokens, at, group.close),
            Phase::SharedType(_) => self.separator(tokens, at),
            Phase::Body => false,
        }
    }

    /// Read names and delimiters only. Stop at an annotation so the caller can
    /// parse its complete expression on the same explicit term-frame stack.
    fn header(
        &mut self,
        leaves: &Leaves,
        view: &SourceView,
        tokens: &[LexedToken],
        cursor: &mut usize,
        end: usize,
    ) -> Result<(), NatDefinitionParseError> {
        while *cursor < end {
            if self.dependent_arrow && !self.binders.is_empty() {
                if self.binders.len() != 1 || !self.separator(tokens, *cursor) {
                    return Err(refuse(view, tokens, *cursor));
                }
                self.separator = Some(*cursor);
                self.phase = Phase::Body;
                *cursor += 1;
                return Ok(());
            }
            if name(tokens, *cursor) {
                self.binders.push(binder_name(leaves, tokens, *cursor)?);
                *cursor += 1;
                continue;
            }
            let kind = match tokens.get(*cursor).map(|t| &t.kind) {
                Some(TokenKind::Symbol(s)) => match s.as_str() {
                    "(" => Some(("explicitBinder", ")")),
                    "{" => Some(("implicitBinder", "}")),
                    "⦃" => Some(("strictImplicitBinder", "⦄")),
                    "[" => Some(("instBinder", "]")),
                    _ => None,
                },
                _ => None,
            };
            if let Some((kind, close)) = kind {
                let open = *cursor;
                *cursor += 1;
                let start = *cursor;
                if kind == "instBinder" {
                    let named = name(tokens, *cursor) && symbol(tokens, *cursor + 1, ":");
                    let colon = named.then_some(*cursor + 1);
                    if named {
                        *cursor += 2;
                    }
                    self.phase = Phase::Group(Group {
                        open,
                        names: start..start + usize::from(named),
                        colon,
                        kind,
                        close,
                    });
                    return Ok(());
                }
                while *cursor < end && name(tokens, *cursor) {
                    *cursor += 1;
                }
                if *cursor == start {
                    return Err(refuse(view, tokens, *cursor));
                }
                let names = start..*cursor;
                if symbol(tokens, *cursor, ":") {
                    self.phase = Phase::Group(Group {
                        open,
                        names,
                        colon: Some(*cursor),
                        kind,
                        close,
                    });
                    *cursor += 1;
                    return Ok(());
                }
                if *cursor < end && symbol(tokens, *cursor, close) {
                    let group = Group {
                        open,
                        names,
                        colon: None,
                        kind,
                        close,
                    };
                    self.binders
                        .push(self.group_syntax(leaves, tokens, group, *cursor, None)?);
                    *cursor += 1;
                    continue;
                }
                return Err(refuse(view, tokens, *cursor));
            }
            if self.binders.is_empty() {
                return Err(refuse(view, tokens, *cursor));
            }
            if symbol(tokens, *cursor, ":") {
                self.phase = Phase::SharedType(*cursor);
                *cursor += 1;
                return Ok(());
            }
            if self.separator(tokens, *cursor) {
                self.separator = Some(*cursor);
                self.phase = Phase::Body;
                *cursor += 1;
                return Ok(());
            }
            return Err(refuse(view, tokens, *cursor));
        }
        Err(refuse(view, tokens, end))
    }

    fn group_syntax(
        &self,
        leaves: &Leaves,
        tokens: &[LexedToken],
        group: Group,
        at: usize,
        domain: Option<Syntax>,
    ) -> Result<Syntax, NatDefinitionParseError> {
        let names = group
            .names
            .map(|at| binder_name(leaves, tokens, at))
            .collect::<Result<Vec<_>, _>>()?;
        if group.kind == "instBinder" {
            let mut named = names;
            if let Some(colon) = group.colon {
                named.push(leaves.leaf(colon)?);
            }
            return Ok(Syntax::node(
                parser_kind(&["Term", "instBinder"]),
                vec![
                    leaves.leaf(group.open)?,
                    null_node(named),
                    domain.expect("instance domain"),
                    leaves.leaf(at)?,
                ],
            ));
        }
        // funBinder parses an explicit group as a term, unlike forall's
        // bracketedBinder. Preserve its hygienic parenthesis and ascription.
        if self.lambda && group.kind == "explicitBinder" {
            let mut names = names.into_iter();
            let head = names.next().expect("nonempty binder names");
            let rest: Vec<_> = names.collect();
            let value = if rest.is_empty() {
                head
            } else {
                Syntax::node(parser_kind(&["Term", "app"]), vec![head, null_node(rest)])
            };
            return Ok(if let Some(domain) = domain {
                Syntax::node(
                    parser_kind(&["Term", "typeAscription"]),
                    vec![
                        hygienic_lparen(leaves.leaf(group.open)?),
                        value,
                        leaves.leaf(group.colon.expect("typed group colon"))?,
                        null_node(vec![domain]),
                        leaves.leaf(at)?,
                    ],
                )
            } else {
                Syntax::node(
                    parser_kind(&["Term", "paren"]),
                    vec![
                        hygienic_lparen(leaves.leaf(group.open)?),
                        value,
                        leaves.leaf(at)?,
                    ],
                )
            });
        }
        let type_ = match domain {
            Some(domain) => null_node(vec![
                leaves.leaf(group.colon.expect("typed group colon"))?,
                domain,
            ]),
            None => null_node(vec![]),
        };
        let mut parts = vec![leaves.leaf(group.open)?, null_node(names), type_];
        if group.kind == "explicitBinder" {
            parts.push(null_node(vec![]));
        }
        parts.push(leaves.leaf(at)?);
        Ok(Syntax::node(parser_kind(&["Term", group.kind]), parts))
    }

    pub(super) fn finish_header(
        mut self,
        leaves: &Leaves,
        view: &SourceView,
        tokens: &[LexedToken],
        at: usize,
        domain: Syntax,
        end: usize,
    ) -> Result<(Self, usize), NatDefinitionParseError> {
        let mut cursor = at + 1;
        match std::mem::replace(&mut self.phase, Phase::Body) {
            Phase::Group(group) => {
                self.binders
                    .push(self.group_syntax(leaves, tokens, group, at, Some(domain))?);
                self.header(leaves, view, tokens, &mut cursor, end)?;
            }
            Phase::SharedType(colon) => {
                self.annotation = Some((colon, domain));
                self.separator = Some(at);
            }
            Phase::Body => unreachable!("only a header can finish here"),
        }
        Ok((self, cursor))
    }

    pub(super) fn finish(
        self,
        leaves: &Leaves,
        body: Syntax,
    ) -> Result<(Syntax, usize), NatDefinitionParseError> {
        let annotation = match self.annotation {
            Some((colon, type_)) => null_node(vec![Syntax::node(
                parser_kind(&["Term", "typeSpec"]),
                vec![leaves.leaf(colon)?, type_],
            )]),
            None => null_node(vec![]),
        };
        let separator = leaves.leaf(self.separator.expect("completed prefix separator"))?;
        let syntax = if self.dependent_arrow {
            Syntax::node(
                parser_kind(&["Term", "depArrow"]),
                vec![
                    self.binders
                        .into_iter()
                        .next()
                        .expect("single dependent binder"),
                    separator,
                    body,
                ],
            )
        } else if self.lambda {
            let basic = Syntax::node(
                parser_kind(&["Term", "basicFun"]),
                vec![null_node(self.binders), annotation, separator, body],
            );
            Syntax::node(
                parser_kind(&["Term", "fun"]),
                vec![leaves.leaf(self.keyword)?, basic],
            )
        } else {
            Syntax::node(
                parser_kind(&["Term", "forall"]),
                vec![
                    leaves.leaf(self.keyword)?,
                    null_node(self.binders),
                    annotation,
                    separator,
                    body,
                ],
            )
        };
        Ok((syntax, self.keyword))
    }
}

/// Resolve the bracket/term ambiguity once per input range, without repeated
/// scans of nested domains. A typed group immediately before an arrow is a Pi.
pub(super) fn arrow_openers(
    tokens: &[LexedToken],
    range: std::ops::Range<usize>,
) -> std::collections::HashSet<usize> {
    let mut stack = Vec::new();
    let mut result = std::collections::HashSet::new();
    let end = range.end;
    for at in range {
        let TokenKind::Symbol(s) = &tokens[at].kind else {
            continue;
        };
        match s.as_str() {
            "(" | "{" | "[" | "⦃" | ".{" => {
                let mut next = at + 1;
                while next < end && name(tokens, next) {
                    next += 1;
                }
                let typed = s == "[" || (next > at + 1 && next < end && symbol(tokens, next, ":"));
                stack.push((at, s.as_str(), typed));
            }
            ")" | "}" | "]" | "⦄" => {
                if let Some((open, opener, typed)) = stack.pop() {
                    let matches = matches!(
                        (opener, s.as_str()),
                        ("(", ")") | ("{", "}") | ("[", "]") | ("⦃", "⦄")
                    );
                    if matches
                        && typed
                        && at + 1 < end
                        && (symbol(tokens, at + 1, "->") || symbol(tokens, at + 1, "→"))
                    {
                        result.insert(open);
                    }
                }
            }
            _ => {}
        }
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn binder_telescopes_preserve_exact_source_bytes() {
        for source in [
            "def id := fun (x : Nat) => x\r\n",
            "def id := λ /- a -/ {A : Type} ⦃B : Type⦄ (x : A) ↦ x\r\n",
            "def f : ∀ (A : Type) (P : A -> Prop) (x : A), P x := fun A P x => _",
            "def f : {A : Type} -> (x : A) -> A := fun {A} x => x",
            "def f := fun [c : Inhabited Nat] => c.default",
            "def f := fun [Inhabited Nat] => 7",
            "def f := fun x y : Nat => x + y",
            "def f := forall x Nat, Nat",
            "def f := fun (_ x : Nat) => x",
            "def f := fun (f : (∀ x : Nat, Nat) -> Nat) => f (fun x => x)",
        ] {
            let parsed = parse_source_command(source.as_bytes())
                .unwrap_or_else(|e| panic!("{source}: {e:?}"));
            assert_eq!(parsed.reconstruct_original(), source.as_bytes());
        }
    }

    #[test]
    fn lambda_group_uses_the_pinned_ascription_not_a_declaration_binder() {
        let parsed = parse_source_command(b"def f := fun (x y : Nat) => x").unwrap();
        let mut pending = vec![&parsed.syntax];
        let mut ascriptions = 0;
        while let Some(syntax) = pending.pop() {
            if let Syntax::Node { kind, args, .. } = syntax {
                assert_ne!(kind, &parser_kind(&["Term", "explicitBinder"]));
                if kind == &parser_kind(&["Term", "typeAscription"]) {
                    ascriptions += 1;
                }
                pending.extend(args);
            }
        }
        assert_eq!(ascriptions, 1);
    }

    #[test]
    fn malformed_binder_headers_fail_without_accepting_a_prefix() {
        for source in [
            "def f := fun (x :) => x",
            "def f := fun (x : Nat => x",
            "def f := fun {x : Nat) => x",
            "def f := fun [x :] => x",
            "def f := fun [] => 0",
            "def f := fun (x : Nat := 7) => x",
            "def f := fun {x : Nat} x",
            "def f := fun (x : Nat) =>",
            "def f := forall (x : Nat),",
            "def f := forall (x : Nat) => Nat",
            "def f := (x : Nat) ->",
        ] {
            assert!(parse_source_command(source.as_bytes()).is_err(), "{source}");
        }
    }

    #[test]
    fn deeply_nested_binder_annotations_use_heap_frames() {
        std::thread::Builder::new()
            .stack_size(128 * 1024)
            .spawn(|| {
                let source = format!(
                    "def f := {}Nat{}",
                    "fun (x : ".repeat(600),
                    ") => Nat".repeat(600)
                );
                let parsed = parse_source_command(source.as_bytes()).unwrap();
                assert_eq!(parsed.reconstruct_original(), source.as_bytes());
            })
            .unwrap()
            .join()
            .unwrap();
    }

    #[test]
    fn nat_only_door_does_not_gain_term_binders() {
        assert!(parse_nat_definition(b"def f := fun (x : Nat) => x").is_err());
        assert!(parse_nat_definition(b"def f : (x : Nat) -> Nat := 0").is_err());
    }
}
