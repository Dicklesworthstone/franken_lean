//! Universe syntax uses the original token leaves and a heap Pratt stack.
//! This parser owns no type-level interpretation or declaration authority.
use super::*;
use std::ops::Range;

fn symbol(tokens: &[LexedToken], at: usize, text: &str) -> bool {
    matches!(tokens.get(at).map(|t| &t.kind), Some(TokenKind::Symbol(s)) if s == text)
}
fn refuse(view: &SourceView, tokens: &[LexedToken], at: usize) -> NatDefinitionParseError {
    NatDefinitionParseError::OutsideSeedGrammar {
        at: original_position(view, tokens, at),
        expected: NatDefinitionExpectation::ScalarType,
    }
}
fn starts(tokens: &[LexedToken], at: usize, end: usize) -> bool {
    at < end
        && (matches!(
            tokens[at].kind,
            TokenKind::Ident(_) | TokenKind::Literal(LiteralKind::Nat)
        ) || symbol(tokens, at, "(")
            || symbol(tokens, at, "_"))
}

/// Locate an optional explicit declaration-universe suffix before binder parsing.
/// Empty lists, missing commas, and whitespace before `.{` are not repaired.
pub(super) fn declaration_suffix(
    view: &SourceView,
    tokens: &[LexedToken],
    start: usize,
) -> Result<(Option<Range<usize>>, usize), NatDefinitionParseError> {
    if !symbol(tokens, start, ".{") {
        return Ok((None, start));
    }
    if start == 0 || tokens[start - 1].extent.end() != tokens[start].extent.start() {
        return Err(refuse(view, tokens, start));
    }
    let mut cursor = start + 1;
    loop {
        if !matches!(
            tokens.get(cursor).map(|t| &t.kind),
            Some(TokenKind::Ident(_))
        ) {
            return Err(refuse(view, tokens, cursor));
        }
        cursor += 1;
        if symbol(tokens, cursor, "}") {
            return Ok((Some(start..cursor + 1), cursor + 1));
        }
        if !symbol(tokens, cursor, ",") {
            return Err(refuse(view, tokens, cursor));
        }
        cursor += 1;
    }
}

pub(super) fn declaration_syntax(
    leaves: &Leaves,
    range: Option<Range<usize>>,
) -> Result<Syntax, NatDefinitionParseError> {
    let Some(range) = range else {
        return Ok(null_node(vec![]));
    };
    let names = (range.start + 1..range.end - 1)
        .map(|i| leaves.leaf(i))
        .collect::<Result<Vec<_>, _>>()?;
    Ok(null_node(vec![
        leaves.leaf(range.start)?,
        null_node(names),
        leaves.leaf(range.end - 1)?,
    ]))
}

pub(super) fn sort(
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    start: usize,
    end: usize,
) -> Result<(Syntax, usize), NatDefinitionParseError> {
    let mut cursor = start + 1;
    let level = if starts(tokens, cursor, end)
        && tokens[start].extent.end() < tokens[cursor].extent.start()
    {
        null_node(vec![expression(
            leaves,
            view,
            tokens,
            &mut cursor,
            end,
            1024,
        )?])
    } else {
        null_node(vec![])
    };
    Ok((
        Syntax::node(
            parser_kind(&[
                "Term",
                if symbol(tokens, start, "Type") {
                    "type"
                } else {
                    "sort"
                },
            ]),
            vec![leaves.leaf(start)?, level],
        ),
        cursor,
    ))
}

pub(super) fn explicit(
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    head: Syntax,
    start: usize,
    end: usize,
) -> Result<(Syntax, usize), NatDefinitionParseError> {
    if start == 0
        || tokens[start - 1].extent.end() != tokens[start].extent.start()
        || !(matches!(&head, Syntax::Ident { .. })
            || matches!(&head, Syntax::Node { kind, .. } if kind == &parser_kind(&["Term", "proj"])))
    {
        return Err(refuse(view, tokens, start));
    }
    let mut cursor = start + 1;
    let mut levels = Vec::new();
    loop {
        levels.push(expression(leaves, view, tokens, &mut cursor, end, 0)?);
        if cursor >= end {
            return Err(refuse(view, tokens, cursor));
        }
        if symbol(tokens, cursor, "}") {
            break;
        }
        if !symbol(tokens, cursor, ",") {
            return Err(refuse(view, tokens, cursor));
        }
        levels.push(leaves.leaf(cursor)?);
        cursor += 1;
    }
    Ok((
        Syntax::node(
            parser_kind(&["Term", "explicitUniv"]),
            vec![
                head,
                leaves.leaf(start)?,
                null_node(levels),
                leaves.leaf(cursor)?,
            ],
        ),
        cursor + 1,
    ))
}

/// Iterative Pratt parsing, including nested variadic `max`/`imax`. Addition of
/// a literal binds at 65, so `Type u + 1` remains a term-level addition while
/// `Type (u + 1)` contains a universe offset, as at the pinned parser.
fn expression(
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    cursor: &mut usize,
    end: usize,
    precedence: u16,
) -> Result<Syntax, NatDefinitionParseError> {
    enum Task {
        Visit(u16),
        Trailing(u16),
        Paren(usize),
        Maximum(usize, Vec<Syntax>),
    }
    let mut tasks = vec![Task::Visit(precedence)];
    let mut values = Vec::<Syntax>::new();
    while let Some(task) = tasks.pop() {
        match task {
            Task::Visit(precedence) => {
                let at = *cursor;
                if !starts(tokens, at, end) {
                    return Err(refuse(view, tokens, at));
                }
                *cursor += 1;
                tasks.push(Task::Trailing(precedence));
                match &tokens[at].kind {
                    TokenKind::Ident(_)
                        if matches!(
                            &view.normalized().as_str()
                                [tokens[at].extent.start().0..tokens[at].extent.end().0],
                            "max" | "imax"
                        ) =>
                    {
                        tasks.push(Task::Maximum(at, vec![]));
                        tasks.push(Task::Visit(1024));
                    }
                    TokenKind::Ident(_) => values.push(leaves.leaf(at)?),
                    TokenKind::Literal(LiteralKind::Nat) => values.push(Syntax::node(
                        Name::from_components(["num"]),
                        vec![leaves.leaf(at)?],
                    )),
                    TokenKind::Symbol(s) if s == "_" => values.push(Syntax::node(
                        parser_kind(&["Level", "hole"]),
                        vec![leaves.leaf(at)?],
                    )),
                    TokenKind::Symbol(s) if s == "(" => {
                        tasks.push(Task::Paren(at));
                        tasks.push(Task::Visit(0));
                    }
                    _ => return Err(refuse(view, tokens, at)),
                }
            }
            Task::Trailing(precedence) => {
                if precedence <= 65 && *cursor < end && symbol(tokens, *cursor, "+") {
                    let plus = *cursor;
                    if plus + 1 >= end
                        || !matches!(tokens[plus + 1].kind, TokenKind::Literal(LiteralKind::Nat))
                    {
                        return Err(refuse(view, tokens, plus + 1));
                    }
                    let base = values.pop().expect("completed level");
                    values.push(Syntax::node(
                        parser_kind(&["Level", "addLit"]),
                        vec![
                            base,
                            leaves.leaf(plus)?,
                            Syntax::node(
                                Name::from_components(["num"]),
                                vec![leaves.leaf(plus + 1)?],
                            ),
                        ],
                    ));
                    *cursor += 2;
                    tasks.push(Task::Trailing(precedence));
                }
            }
            Task::Paren(open) => {
                if *cursor >= end || !symbol(tokens, *cursor, ")") {
                    return Err(refuse(view, tokens, *cursor));
                }
                let inner = values.pop().expect("parenthesized level");
                values.push(Syntax::node(
                    parser_kind(&["Level", "paren"]),
                    vec![leaves.leaf(open)?, inner, leaves.leaf(*cursor)?],
                ));
                *cursor += 1;
            }
            Task::Maximum(at, mut args) => {
                args.push(values.pop().expect("maximum argument"));
                if starts(tokens, *cursor, end) {
                    tasks.push(Task::Maximum(at, args));
                    tasks.push(Task::Visit(1024));
                } else {
                    let leaf = leaves.leaf(at)?;
                    let Syntax::Ident { info, val, .. } = &leaf else {
                        unreachable!("max keyword");
                    };
                    let keyword = val.to_display_string();
                    values.push(Syntax::node(
                        parser_kind(&["Level", &keyword]),
                        vec![
                            Syntax::Atom {
                                info: *info,
                                val: keyword,
                            },
                            null_node(args),
                        ],
                    ));
                }
            }
        }
    }
    if values.len() != 1 {
        return Err(refuse(view, tokens, *cursor));
    }
    Ok(values.pop().expect("one level result"))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn universe_syntax_preserves_original_leaves_and_normalized_bytes() {
        for source in [
            "def id.{u} {A : Sort u} (x : A) : A := x",
            "theorem refl.{u,v} (A : Sort (max u v)) (x : A) : x = x := Eq.refl.{max u v} x",
            "structure Pair.{u, v} (A : Type u) (B : Type v) : Type (max u v) where\n  first : A\n  second : B",
            "inductive List.{u} (A : Type u) where\n  | nil\n  | cons (head : A) (tail : List A)",
            "-- comment\r\ndef lifted.{u} : Type (u + 1) := -- universe\r\n  Type u\r\n",
            "def maxIsAName.{«max»} (A : Sort «max») : Sort «max» := A",
            "def higher := f.{(max 0 (imax 1 2)), _} x",
        ] {
            let parsed =
                parse_definition(source.as_bytes()).unwrap_or_else(|e| panic!("{source}: {e:?}"));
            assert_eq!(parsed.reconstruct_original(), source.as_bytes());
            assert_eq!(
                parsed.reconstruct_normalized().unwrap(),
                source.replace("\r\n", "\n").as_bytes()
            );
            assert!(parse_nat_definition(source.as_bytes()).is_err());
        }
    }

    #[test]
    fn malformed_universe_lists_and_offsets_are_not_discarded() {
        for source in [
            "def x.{} := 0",
            "def x.{u,} := 0",
            "def x.{u v} := 0",
            "def x .{u} := 0",
            "def x.{1} := 0",
            "def x.{u := 0",
            "def x := f.{}",
            "def x := f.{1,}",
            "def x := f.{1 2}",
            "def x := f .{1}",
            "def x := f.{(max)}",
            "def x := Type (u + v)",
            "def x := Type (u +)",
            "def x := Sort (imax)",
            "def x := Sort (u",
            "structure X.{u,} where\n  value : Nat",
            "inductive X.{u v} where | x",
        ] {
            assert!(parse_definition(source.as_bytes()).is_err(), "{source}");
        }
    }

    #[test]
    fn nested_universe_parentheses_use_heap_frames() {
        let source = format!(
            "def higher : Type {}0{} := Nat",
            "(".repeat(4000),
            ")".repeat(4000)
        );
        std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(move || {
                let parsed = parse_definition(source.as_bytes()).unwrap();
                assert_eq!(parsed.reconstruct_normalized().unwrap(), source.as_bytes());
            })
            .unwrap()
            .join()
            .unwrap();
    }
}
