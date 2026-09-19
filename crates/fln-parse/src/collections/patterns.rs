//! List/cons patterns use the same constructor-pattern language as matching.
//! Delimiter pairing, cons association and nesting are planned without recursion.
use super::*;
use std::collections::HashMap;
use std::ops::Range;

fn symbol(tokens: &[LexedToken], at: usize, expected: &str) -> bool {
    matches!(tokens.get(at).map(|token| &token.kind), Some(TokenKind::Symbol(s)) if s == expected)
}
fn refusal(view: &SourceView, tokens: &[LexedToken], at: usize) -> NatDefinitionParseError {
    NatDefinitionParseError::OutsideSeedGrammar {
        at: original_position(view, tokens, at),
        expected: NatDefinitionExpectation::MatchAlternative,
    }
}

pub(crate) fn pattern(
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    range: Range<usize>,
) -> Result<Syntax, NatDefinitionParseError> {
    enum Task {
        Parse(Range<usize>),
        Group(usize, usize),
        Application(usize),
        Cons(usize, Vec<usize>),
        List(usize, usize, usize, Vec<usize>),
    }
    let mut pairs = HashMap::new();
    let mut opens = Vec::new();
    for at in range.clone() {
        if symbol(tokens, at, "(") || symbol(tokens, at, "[") {
            opens.push(at);
        } else if symbol(tokens, at, ")") || symbol(tokens, at, "]") {
            let open = opens.pop().ok_or_else(|| refusal(view, tokens, at))?;
            if symbol(tokens, open, "(") != symbol(tokens, at, ")") {
                return Err(refusal(view, tokens, at));
            }
            pairs.insert(open, at);
        }
    }
    if !opens.is_empty() {
        return Err(refusal(view, tokens, range.end));
    }
    let mut tasks = vec![Task::Parse(range)];
    let mut values = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            Task::Group(open, close) => {
                let inner = values.pop().expect("planned collection pattern group");
                values.push(Syntax::node(
                    parser_kind(&["Term", "paren"]),
                    vec![
                        hygienic_lparen(leaves.leaf(open)?),
                        inner,
                        leaves.leaf(close)?,
                    ],
                ));
            }
            Task::Application(start) => {
                let arguments = values.split_off(start + 1);
                let head = values.pop().expect("planned collection constructor head");
                values.push(Syntax::node(
                    parser_kind(&["Term", "app"]),
                    vec![head, null_node(arguments)],
                ));
            }
            Task::Cons(start, operators) => {
                let mut parts = values.split_off(start);
                if parts.len() != operators.len() + 1 {
                    return Err(refusal(view, tokens, operators[0]));
                }
                let mut tail = parts.pop().expect("nonempty cons chain");
                for (head, operator) in parts.into_iter().zip(operators).rev() {
                    tail = Syntax::node(
                        Name::from_components(["term_::_"]),
                        vec![head, leaves.leaf(operator)?, tail],
                    );
                }
                values.push(tail);
            }
            Task::List(start, open, close, separators) => {
                let elements = values.split_off(start);
                let mut args = Vec::new();
                for (index, element) in elements.into_iter().enumerate() {
                    args.push(element);
                    if let Some(separator) = separators.get(index) {
                        args.push(leaves.leaf(*separator)?);
                    }
                }
                values.push(Syntax::node(
                    list_kind(),
                    vec![leaves.leaf(open)?, null_node(args), leaves.leaf(close)?],
                ));
            }
            Task::Parse(range) => {
                if range.is_empty() {
                    return Err(refusal(view, tokens, range.start));
                }
                // An entire delimited atom is handled before the infix scan,
                // so nested singleton lists/groups do not rescan their interiors.
                if let Some(&close) = pairs.get(&range.start)
                    && close + 1 == range.end
                {
                    if symbol(tokens, range.start, "(") {
                        tasks.push(Task::Group(range.start, close));
                        tasks.push(Task::Parse(range.start + 1..close));
                    } else {
                        let mut parts = Vec::new();
                        let mut separators = Vec::new();
                        let mut start = range.start + 1;
                        let mut at = start;
                        while at < close {
                            if let Some(&end) = pairs.get(&at) {
                                at = end + 1;
                            } else if symbol(tokens, at, ",") {
                                if start == at {
                                    return Err(refusal(view, tokens, at));
                                }
                                parts.push(start..at);
                                separators.push(at);
                                start = at + 1;
                                at += 1;
                            } else {
                                at += 1;
                            }
                        }
                        if start < close {
                            parts.push(start..close);
                        }
                        tasks.push(Task::List(values.len(), range.start, close, separators));
                        tasks.extend(parts.into_iter().rev().map(Task::Parse));
                    }
                    continue;
                }
                let mut parts = Vec::new();
                let mut operators = Vec::new();
                let mut start = range.start;
                let mut at = start;
                while at < range.end {
                    if let Some(&end) = pairs.get(&at) {
                        if end >= range.end {
                            return Err(refusal(view, tokens, at));
                        }
                        at = end + 1;
                    } else if symbol(tokens, at, "::") {
                        if start == at {
                            return Err(refusal(view, tokens, at));
                        }
                        parts.push(start..at);
                        operators.push(at);
                        start = at + 1;
                        at += 1;
                    } else {
                        at += 1;
                    }
                }
                if !operators.is_empty() {
                    if start == range.end {
                        return Err(refusal(view, tokens, range.end));
                    }
                    parts.push(start..range.end);
                    tasks.push(Task::Cons(values.len(), operators));
                    tasks.extend(parts.into_iter().rev().map(Task::Parse));
                    continue;
                }
                let mut cursor = range.start;
                let dot = symbol(tokens, cursor, ".");
                if dot {
                    cursor += 1;
                }
                if cursor >= range.end {
                    return Err(refusal(view, tokens, cursor));
                }
                let head = if symbol(tokens, cursor, "_") && !dot {
                    Syntax::node(parser_kind(&["Term", "hole"]), vec![leaves.leaf(cursor)?])
                } else if !dot
                    && matches!(
                        tokens[cursor].kind,
                        TokenKind::Literal(LiteralKind::Nat | LiteralKind::Str)
                    )
                {
                    if cursor + 1 != range.end {
                        return Err(refusal(view, tokens, cursor + 1));
                    }
                    bounded_term_leaf(leaves, view, tokens, cursor, DefinitionGrammar::Scalar)?
                } else if matches!(tokens[cursor].kind, TokenKind::Ident(_)) {
                    if dot {
                        Syntax::node(
                            parser_kind(&["Term", "dotIdent"]),
                            vec![leaves.leaf(range.start)?, leaves.leaf(cursor)?],
                        )
                    } else {
                        leaves.leaf(cursor)?
                    }
                } else {
                    return Err(refusal(view, tokens, cursor));
                };
                cursor += 1;
                let start = values.len();
                values.push(head);
                let mut arguments = Vec::new();
                while cursor < range.end {
                    let begin = cursor;
                    if let Some(&close) = pairs.get(&cursor) {
                        cursor = close + 1;
                    } else if symbol(tokens, cursor, ".") {
                        cursor += 2;
                    } else {
                        cursor += 1;
                    }
                    if cursor > range.end {
                        return Err(refusal(view, tokens, begin));
                    }
                    arguments.push(begin..cursor);
                }
                if !arguments.is_empty() {
                    tasks.push(Task::Application(start));
                    tasks.extend(arguments.into_iter().rev().map(Task::Parse));
                }
            }
        }
    }
    if values.len() != 1 {
        return Err(refusal(view, tokens, tokens.len()));
    }
    Ok(values.pop().expect("one completed collection pattern"))
}
