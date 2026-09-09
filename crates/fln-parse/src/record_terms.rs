//! Record initializers participate in the ordinary heap-based term parser.
//! Token leaves and the pinned structInst/structInstField wrappers are retained.
use super::*;

pub(super) struct RecordFrame {
    open: usize,
    rows: Vec<Syntax>,
    field: Option<(usize, Option<usize>)>,
    colon: Option<usize>,
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
        lambda: None,
        application: Vec::new(),
        operands: Vec::new(),
        operators: Vec::new(),
    }
}
fn prefix(
    view: &SourceView,
    tokens: &[LexedToken],
    cursor: &mut usize,
    end: usize,
) -> Result<Option<(usize, Option<usize>)>, NatDefinitionParseError> {
    if *cursor < end && (symbol(tokens, *cursor, "}") || symbol(tokens, *cursor, ":")) {
        return Ok(None);
    }
    let name = *cursor;
    if name >= end || !matches!(tokens[name].kind, TokenKind::Ident(_)) {
        return Err(refuse(view, tokens, name));
    }
    *cursor += 1;
    let assignment = if *cursor < end && symbol(tokens, *cursor, ":=") {
        let assignment = *cursor;
        *cursor += 1;
        Some(assignment)
    } else {
        None
    };
    Ok(Some((name, assignment)))
}
pub(super) fn open(
    view: &SourceView,
    tokens: &[LexedToken],
    open: usize,
    cursor: &mut usize,
    end: usize,
) -> Result<BoundedTermFrame, NatDefinitionParseError> {
    Ok(frame(RecordFrame {
        open,
        rows: Vec::new(),
        field: prefix(view, tokens, cursor, end)?,
        colon: None,
    }))
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
    let mut annotation = null_node(Vec::new());
    if let Some(colon) = record.colon {
        if !symbol(tokens, at, "}") {
            return Err(refuse(view, tokens, at));
        }
        let type_ = finish_bounded_frame(view, tokens, current, DefinitionGrammar::Scalar, at)?;
        annotation = null_node(vec![leaves.leaf(colon)?, type_]);
    } else if let Some((name, assignment)) = record.field.take() {
        let payload = if let Some(assignment) = assignment {
            let value = finish_bounded_frame(view, tokens, current, DefinitionGrammar::Scalar, at)?;
            null_node(vec![
                null_node(Vec::new()),
                null_node(Vec::new()),
                Syntax::node(
                    parser_kind(&["Term", "structInstFieldDef"]),
                    vec![leaves.leaf(assignment)?, null_node(Vec::new()), value],
                ),
            ])
        } else {
            if !current.application.is_empty()
                || !current.operands.is_empty()
                || !current.operators.is_empty()
            {
                return Err(refuse(view, tokens, at));
            }
            null_node(Vec::new())
        };
        record.rows.push(Syntax::node(
            parser_kind(&["Term", "structInstField"]),
            vec![
                Syntax::node(
                    parser_kind(&["Term", "structInstLVal"]),
                    vec![leaves.leaf(name)?, null_node(Vec::new())],
                ),
                payload,
            ],
        ));
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
        record.field = prefix(view, tokens, cursor, end)?;
        frames.push(frame(record));
    } else if symbol(tokens, at, ":") {
        record.colon = Some(at);
        frames.push(frame(record));
    } else {
        let open = record.open;
        let term = Syntax::node(
            parser_kind(&["Term", "structInst"]),
            vec![
                leaves.leaf(open)?,
                null_node(Vec::new()),
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
