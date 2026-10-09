//! Record initializers participate in the ordinary heap-based term parser.
//! Token leaves and the pinned structInst/structInstField wrappers are retained.
use super::*;

pub(super) struct RecordFrame {
    open: usize,
    rows: Vec<Syntax>,
    field: Option<Field>,
    colon: Option<usize>,
    sources: Vec<Syntax>,
    source_mode: bool,
    with_token: Option<usize>,
}
enum Field {
    Abbreviation(usize),
    Definition,
}
fn refuse(view: &SourceView, tokens: &[LexedToken], at: usize) -> NatDefinitionParseError {
    NatDefinitionParseError::OutsideSeedGrammar {
        at: original_position(view, tokens, at),
        expected: NatDefinitionExpectation::RecordField,
    }
}
fn symbol(tokens: &[LexedToken], at: usize, text: &str) -> bool {
    matches!(tokens.get(at).map(|t| &t.kind), Some(TokenKind::Symbol(s)) if s == text)
}
fn frame(record: RecordFrame) -> BoundedTermFrame {
    BoundedTermFrame {
        record: Some(record),
        ascription: None,
        open: None,
        prefix: None,
        negation: None,
        application: Vec::new(),
        operands: Vec::new(),
        operators: Vec::new(),
    }
}
fn push_field(
    mut record: RecordFrame,
    frames: &mut Vec<BoundedTermFrame>,
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    cursor: &mut usize,
    end: usize,
) -> Result<(), NatDefinitionParseError> {
    if record.source_mode
        || (*cursor < end && (symbol(tokens, *cursor, "}") || symbol(tokens, *cursor, ":")))
    {
        frames.push(frame(record));
        return Ok(());
    }
    let name = *cursor;
    if name >= end || !matches!(tokens[name].kind, TokenKind::Ident(_)) {
        return Err(refuse(view, tokens, name));
    }
    *cursor += 1;
    if *cursor < end
        && (symbol(tokens, *cursor, ",")
            || symbol(tokens, *cursor, "}")
            || symbol(tokens, *cursor, ":"))
    {
        // A colon after a field abbreviation is the enclosing record's type,
        // as in `{ value : Box Nat }`.
        record.field = Some(Field::Abbreviation(name));
        frames.push(frame(record));
    } else {
        let prefix = term_binders::Prefix::field(leaves, view, tokens, name, cursor, end)?;
        record.field = Some(Field::Definition);
        frames.push(frame(record));
        frames.push(term_binders::frame(prefix));
    }
    Ok(())
}
/// Classify update openers in one pass. A field assignment ends the ambiguous
/// prefix, and nested parentheses/braces cannot lend their `with` to a parent.
pub(super) fn update_openers(
    tokens: &[LexedToken],
    range: std::ops::Range<usize>,
) -> std::collections::HashSet<usize> {
    let mut stack = Vec::new();
    let mut updates = std::collections::HashSet::new();
    for index in range {
        if let TokenKind::Symbol(s) = &tokens[index].kind {
            match crate::canonical_bracket(s.as_str()) {
                "{" | ".{" => stack.push((index, "}", true)),
                "(" => stack.push((index, ")", false)),
                "[" => stack.push((index, "]", false)),
                "⦃" => stack.push((index, "⦄", false)),
                "⟨" => stack.push((index, "⟩", false)),
                "}" | ")" | "]" | "⦄" | "⟩" => {
                    stack.pop();
                }
                ":=" => {
                    if let Some((_, _, eligible)) = stack.last_mut() {
                        *eligible = false;
                    }
                }
                "with" => {
                    if let Some(&(open, "}", true)) = stack.last() {
                        updates.insert(open);
                    }
                }
                _ => {}
            }
        }
    }
    updates
}

#[allow(clippy::too_many_arguments)]
pub(super) fn open(
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    frames: &mut Vec<BoundedTermFrame>,
    open: usize,
    cursor: &mut usize,
    end: usize,
    source_mode: bool,
) -> Result<(), NatDefinitionParseError> {
    let record = RecordFrame {
        open,
        rows: Vec::new(),
        field: None,
        colon: None,
        sources: Vec::new(),
        source_mode,
        with_token: None,
    };
    push_field(record, frames, leaves, view, tokens, cursor, end)
}

pub(super) fn delimiter(
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    frames: &mut Vec<BoundedTermFrame>,
    at: usize,
    cursor: &mut usize,
    end: usize,
) -> Result<(), NatDefinitionParseError> {
    let mut current = frames.pop().expect("record term frame");
    let mut record = current.record.take().expect("record delimiter");
    if record.source_mode {
        if !symbol(tokens, at, ",") && !symbol(tokens, at, "with") {
            return Err(refuse(view, tokens, at));
        }
        record.sources.push(finish_bounded_frame(
            view,
            tokens,
            current,
            DefinitionGrammar::Scalar,
            at,
        )?);
        if symbol(tokens, at, ",") {
            record.sources.push(leaves.leaf(at)?);
        } else {
            record.source_mode = false;
            record.with_token = Some(at);
        }
        push_field(record, frames, leaves, view, tokens, cursor, end)?;
        return Ok(());
    }
    if symbol(tokens, at, "with") {
        return Err(refuse(view, tokens, at));
    }
    let mut annotation = null_node(Vec::new());
    if let Some(colon) = record.colon {
        if !symbol(tokens, at, "}") {
            return Err(refuse(view, tokens, at));
        }
        let type_ = finish_bounded_frame(view, tokens, current, DefinitionGrammar::Scalar, at)?;
        annotation = null_node(vec![leaves.leaf(colon)?, type_]);
    } else if let Some(field) = record.field.take() {
        let syntax = match field {
            Field::Definition => {
                let field =
                    finish_bounded_frame(view, tokens, current, DefinitionGrammar::Scalar, at)?;
                if field.kind() != Some(&parser_kind(&["Term", "structInstField"])) {
                    return Err(refuse(view, tokens, at));
                }
                field
            }
            Field::Abbreviation(name) => {
                if !current.application.is_empty()
                    || !current.operands.is_empty()
                    || !current.operators.is_empty()
                {
                    return Err(refuse(view, tokens, at));
                }
                Syntax::node(
                    parser_kind(&["Term", "structInstField"]),
                    vec![
                        Syntax::node(
                            parser_kind(&["Term", "structInstLVal"]),
                            vec![leaves.leaf(name)?, null_node(Vec::new())],
                        ),
                        null_node(Vec::new()),
                    ],
                )
            }
        };
        record.rows.push(syntax);
    } else if !current.application.is_empty()
        || !current.operands.is_empty()
        || !current.operators.is_empty()
    {
        return Err(refuse(view, tokens, at));
    }
    if symbol(tokens, at, ",") {
        if record.rows.is_empty()
            || record
                .rows
                .last()
                .is_some_and(|s| matches!(s, Syntax::Atom { .. }))
        {
            return Err(refuse(view, tokens, at));
        }
        record.rows.push(leaves.leaf(at)?);
        push_field(record, frames, leaves, view, tokens, cursor, end)?;
    } else if symbol(tokens, at, ":") {
        record.colon = Some(at);
        frames.push(frame(record));
    } else {
        let open = record.open;
        let term = Syntax::node(
            parser_kind(&["Term", "structInst"]),
            vec![
                leaves.leaf(open)?,
                match record.with_token {
                    Some(at) => null_node(vec![null_node(record.sources), leaves.leaf(at)?]),
                    None => null_node(Vec::new()),
                },
                Syntax::node(
                    parser_kind(&["Term", "structInstFields"]),
                    vec![null_node(record.rows)],
                ),
                Syntax::node(
                    parser_kind(&["Term", "optEllipsis"]),
                    vec![null_node(Vec::new())],
                ),
                annotation,
                leaves.leaf(at)?,
            ],
        );
        frames
            .last_mut()
            .expect("record frame has a parent")
            .application
            .push((term, open));
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn literal_syntax_preserves_all_source_leaves() {
        for text in [
            "-- comment\r\ndef x : Point := { y := 2, -- between\r\n x := 1, }\r\n",
            "def x := { inner := { value := 3 : Box Nat } : Outer }",
            "def x := ({ value := 7 } : Box Nat)",
            "def x (value : Nat) : Box Nat := { value }",
            "def x : Proof := { proof := by rfl, value := 1 }",
            "def x := ({ value := 7 } : Box Nat).value",
            "def x := (make 3).inner.value -- projection\r\n",
            "def x (p : Point) : Nat := p.chaînes",
            "def x : Printer := { reprPrec _ _ := \"text\" }",
            "def x : Methods := { f (x y : Nat) : Nat := x + y, identity {A : Type} (x : A) : A := x }",
            "def x : Selector := { select {A : Type} [d : Chosen A] : A := @Chosen.value A d }",
            "def x : Factory := { make (x : Nat) : Box := { value := x } }",
            "def x (value : Nat) := { value : Box Nat }",
            "def x := { prior with f x _ := x, g (n : Nat) := n + 1 }",
        ] {
            let parsed = parse_definition(text.as_bytes()).unwrap();
            assert_eq!(parsed.reconstruct_original(), text.as_bytes());
            assert_eq!(
                parsed.reconstruct_normalized().unwrap(),
                text.replace("\r\n", "\n").as_bytes()
            );
            assert!(parse_nat_definition(text.as_bytes()).is_err());
        }
    }

    #[test]
    fn nested_field_methods_keep_annotations_and_bodies_on_heap_frames() {
        std::thread::Builder::new()
            .stack_size(128 * 1024)
            .spawn(|| {
                let text = format!(
                    "def nested := {}0{}",
                    "{ make (x : Nat) := ".repeat(6000),
                    " }".repeat(6000)
                );
                let parsed = parse_definition(text.as_bytes()).unwrap();
                assert_eq!(parsed.reconstruct_original(), text.as_bytes());
                assert_eq!(parsed.reconstruct_normalized().unwrap(), text.as_bytes());
            })
            .unwrap()
            .join()
            .unwrap();
    }
    #[test]
    fn update_sources_roundtrip_without_recursive_lookahead() {
        for text in [
            "def p := { q with x := 1 }",
            "def p : XYZ := { q, r with x := 1, }",
            "def p := { (make 3) with }",
            "def p := { { q with x := 1 } with y := 2 }",
            "def p := { q with inner := { r with y := 2 } : Outer }",
        ] {
            let parsed = parse_definition(text.as_bytes()).unwrap();
            assert_eq!(parsed.reconstruct_original(), text.as_bytes());
            assert_eq!(parsed.reconstruct_normalized().unwrap(), text.as_bytes());
        }
    }
    #[test]
    fn deeply_nested_updates_use_one_classification_pass() {
        std::thread::Builder::new()
            .stack_size(128 * 1024)
            .spawn(|| {
                let text = format!(
                    "def nested := {}p{}",
                    "{ ".repeat(6000),
                    " with }".repeat(6000)
                );
                let parsed = parse_definition(text.as_bytes()).unwrap();
                assert_eq!(parsed.reconstruct_normalized().unwrap(), text.as_bytes());
            })
            .unwrap()
            .join()
            .unwrap();
    }
    #[test]
    fn malformed_delimiters_are_refused_without_panics() {
        for text in [
            "def x : Box Nat := { value := 3)",
            "def x : Box Nat := { value := 3",
            "def x : Box Nat := {,}",
            "def x : Box Nat := { value := }",
            "def x := { value := 1 : Box Nat : Box Nat }",
            "def x := (1 : Nat : Nat)",
            "def x : Box Nat := { value := 1,, }",
            "def x : Box Nat := { value other }",
        ] {
            assert!(
                parse_definition(text.as_bytes()).is_err(),
                "accepted {text}"
            );
        }
    }
    #[test]
    fn deeply_nested_literals_and_ascriptions_use_heap_frames() {
        std::thread::Builder::new()
            .stack_size(128 * 1024)
            .spawn(|| {
                for (open, close) in [("{ value := ", " }"), ("(", " : Nat)")] {
                    let text =
                        format!("def nested := {}0{}", open.repeat(6000), close.repeat(6000));
                    let parsed = parse_definition(text.as_bytes()).unwrap();
                    assert_eq!(parsed.reconstruct_normalized().unwrap(), text.as_bytes());
                }
            })
            .unwrap()
            .join()
            .unwrap();
    }
}
