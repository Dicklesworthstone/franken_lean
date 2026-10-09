//! Syntax declarations as the pin's trees (`Lean/Parser/Syntax.lean`):
//!
//! ```text
//! syntax       := docComment? attributes? attrKind "syntax " optPrecedence optNamedName
//!                 optNamedPrio many1(syntaxParser argPrec) " : " ident
//! syntaxAbbrev := docComment? visibility? "syntax " ident " := " many1(syntaxParser)
//! ```
//!
//! `syntaxParser` reads the `stx` category: a string atom, `&"x"`, `unicode("a", "b")`, a
//! category or alias with an optional precedence (`term:max`), a parenthesized sequence, a
//! function `f(…)` of one or two sequences, `sepBy(…)` and `sepBy1(…)`, the prefix `!` and the
//! postfixes `*`, `+`, `?`, `,*`, `,+`, `,*,?`, `,+,?` (`syntax:arg stx:max "*" : stx` and the
//! rest, `Init/Notation.lean`), and `<|>` (`syntax:2 stx:2 " <|> " stx:1 : stx`). The checker does
//! not interpret a syntax declaration: it refuses the command.
//!
//! Notations are read here too, with the same precedences and names:
//!
//! ```text
//! mixfix   := docComment? attributes? attrKind mixfixKind precedence optNamedName optNamedPrio
//!             notationItem " => " term
//! notation := docComment? attributes? attrKind "notation" optPrecedence optNamedName optNamedPrio
//!             notationItem* " => " term
//! notationItem := strLit <|> unicodeAtom <|> identPrec
//! recommended_spelling := docComment? "recommended_spelling " str " for " str " in " "[" ident,* "]"
//! ```
use super::*;

/// The precedence of an `stx` atom (`maxPrec`), of `argPrec`, and `<|>`'s.
const MAX: u32 = 1024;
const ARG: u32 = 1023;
const ORELSE: u32 = 2;
/// Parenthesized sequences nest only this deep; deeper is refused rather than recursed into on a
/// small host stack.
const DEPTH: usize = 32;

struct Reader<'a> {
    view: &'a SourceView,
    tokens: &'a [LexedToken],
    leaves: &'a Leaves,
    at: usize,
    end: usize,
    depth: usize,
}

fn kind(name: &str) -> Name {
    Name::str(Name::anonymous(), name)
}

impl Reader<'_> {
    fn symbol(&self, at: usize, text: &str) -> bool {
        at < self.end
            && matches!(&self.tokens[at].kind, TokenKind::Symbol(symbol) if symbol == text)
    }

    /// The symbol `text`, or an unescaped identifier spelling it (`max`, `name`, `priority`).
    fn word(&self, at: usize, text: &str) -> bool {
        at < self.end
            && match &self.tokens[at].kind {
                TokenKind::Symbol(symbol) => symbol == text,
                TokenKind::Ident(_) => {
                    self.view.normalized().span_str(self.tokens[at].extent) == Some(text)
                }
                _ => false,
            }
    }

    fn ident(&self, at: usize) -> bool {
        at < self.end && matches!(&self.tokens[at].kind, TokenKind::Ident(_))
    }

    fn literal(&self, at: usize, kind: LiteralKind) -> bool {
        at < self.end
            && matches!(&self.tokens[at].kind, TokenKind::Literal(found) if *found == kind)
    }

    fn bad(&self) -> NatDefinitionParseError {
        NatDefinitionParseError::OutsideSeedGrammar {
            at: original_position(self.view, self.tokens, self.at),
            expected: NatDefinitionExpectation::DefinitionKeyword,
        }
    }

    fn take(&mut self) -> Result<Syntax, NatDefinitionParseError> {
        self.at += 1;
        Ok(self.leaves.leaf(self.at - 1)?)
    }

    /// The symbol `text` at the cursor (or the identifier spelling it), as an atom.
    fn atom(&mut self, text: &str) -> Result<Syntax, NatDefinitionParseError> {
        if !self.word(self.at, text) {
            return Err(self.bad());
        }
        let leaf = self.take()?;
        Ok(Syntax::Atom {
            info: leaf.info(),
            val: text.to_owned(),
        })
    }

    fn expect(&mut self, text: &str) -> Result<Syntax, NatDefinitionParseError> {
        if !self.symbol(self.at, text) {
            return Err(self.bad());
        }
        self.take()
    }

    fn string(&mut self) -> Result<Syntax, NatDefinitionParseError> {
        if !self.literal(self.at, LiteralKind::Str) {
            return Err(self.bad());
        }
        Ok(Syntax::node(kind("str"), vec![self.take()?]))
    }

    fn number(&mut self) -> Result<Syntax, NatDefinitionParseError> {
        if !self.literal(self.at, LiteralKind::Nat) {
            return Err(self.bad());
        }
        Ok(Syntax::node(kind("num"), vec![self.take()?]))
    }

    /// Whether a precedence starts at `at`: a numeral, a precedence word, or `(`.
    fn starts_precedence(&self, at: usize) -> bool {
        self.literal(at, LiteralKind::Nat)
            || ["max", "arg", "lead", "min", "min1"]
                .iter()
                .any(|word| self.word(at, word))
            || self.symbol(at, "(")
    }

    /// `precedence := ":" precedenceParser maxPrec`, from the cursor at `:`.
    fn precedence(&mut self) -> Result<Syntax, NatDefinitionParseError> {
        let colon = self.expect(":")?;
        let value = self.prec_leading()?;
        Ok(Syntax::node(
            parser_kind(&["precedence"]),
            vec![colon, value],
        ))
    }

    /// A leading `prec`: a numeral, `max`, `arg`, `lead`, `min`, `min1` (`Init/Prelude.lean`), or
    /// `(prec)` holding `prec + prec` and `prec - prec` (`Syntax.addPrec`, `Syntax.subPrec`).
    fn prec_leading(&mut self) -> Result<Syntax, NatDefinitionParseError> {
        if self.literal(self.at, LiteralKind::Nat) {
            return self.number();
        }
        for (word, name) in [
            ("max", "precMax"),
            ("arg", "precArg"),
            ("lead", "precLead"),
            ("min1", "precMin1"),
            ("min", "precMin"),
        ] {
            if self.word(self.at, word) {
                return Ok(Syntax::node(kind(name), vec![self.atom(word)?]));
            }
        }
        if !self.symbol(self.at, "(") {
            return Err(self.bad());
        }
        let open = self.take()?;
        let mut value = self.prec_leading()?;
        while let Some((symbol, name)) = [("+", "addPrec"), ("-", "subPrec")]
            .into_iter()
            .find(|(symbol, _)| self.symbol(self.at, symbol))
        {
            let operator = self.atom(symbol)?;
            let right = self.prec_leading()?;
            value = Syntax::node(parser_kind(&["Syntax", name]), vec![value, operator, right]);
        }
        let close = self.expect(")")?;
        Ok(Syntax::node(kind("prec(_)"), vec![open, value, close]))
    }

    /// A `prio`: a numeral, `default`, `low`, `mid`, `high` (`Init/Prelude.lean`), then
    /// `+ prio` and `- prio` (`Syntax.addPrio`, `Syntax.subPrio`).
    fn prio(&mut self) -> Result<Syntax, NatDefinitionParseError> {
        let leading = |reader: &mut Self| -> Result<Syntax, NatDefinitionParseError> {
            if reader.literal(reader.at, LiteralKind::Nat) {
                return reader.number();
            }
            for (word, name) in [
                ("default", "prioDefault"),
                ("low", "prioLow"),
                ("mid", "prioMid"),
                ("high", "prioHigh"),
            ] {
                if reader.word(reader.at, word) {
                    return Ok(Syntax::node(kind(name), vec![reader.atom(word)?]));
                }
            }
            Err(reader.bad())
        };
        let mut value = leading(self)?;
        while let Some((symbol, name)) = [("+", "addPrio"), ("-", "subPrio")]
            .into_iter()
            .find(|(symbol, _)| self.symbol(self.at, symbol))
        {
            let operator = self.atom(symbol)?;
            let right = leading(self)?;
            value = Syntax::node(parser_kind(&["Syntax", name]), vec![value, operator, right]);
        }
        Ok(value)
    }

    /// `" (" "name" " := " ident ")"` or `" (" "priority" " := " prio ")"`, if one is at the cursor.
    fn named(&mut self, word: &str, kind: &str) -> Result<Option<Syntax>, NatDefinitionParseError> {
        if !(self.symbol(self.at, "(")
            && self.word(self.at + 1, word)
            && self.symbol(self.at + 2, ":="))
        {
            return Ok(None);
        }
        let open = self.take()?;
        let word_atom = self.atom(word)?;
        let assign = self.take()?;
        let value = if word == "name" {
            if !self.ident(self.at) {
                return Err(self.bad());
            }
            self.take()?
        } else {
            self.prio()?
        };
        let close = self.expect(")")?;
        Ok(Some(Syntax::node(
            parser_kind(&["Command", kind]),
            vec![open, word_atom, assign, value, close],
        )))
    }

    /// `notationItem`: a string, `unicode(…)`, or an identifier with an optional precedence
    /// (`Command.identPrec`).
    fn notation_item(&mut self) -> Result<Syntax, NatDefinitionParseError> {
        if self.literal(self.at, LiteralKind::Str) {
            return self.string();
        }
        if self.symbol(self.at, "unicode(") {
            return Ok(self.stx_leading()?.0);
        }
        if !self.ident(self.at) {
            return Err(self.bad());
        }
        let name = self.take()?;
        let precedence = if self.symbol(self.at, ":") && self.starts_precedence(self.at + 1) {
            null_node(vec![self.precedence()?])
        } else {
            null_node(Vec::new())
        };
        Ok(Syntax::node(
            parser_kind(&["Command", "identPrec"]),
            vec![name, precedence],
        ))
    }

    /// One or more `stx` at `min` up to a `)` or `,` at this level (or the end of `items`).
    fn sequence(&mut self, min: u32) -> Result<Syntax, NatDefinitionParseError> {
        let mut items = Vec::new();
        while self.at < self.end && !self.symbol(self.at, ")") && !self.symbol(self.at, ",") {
            items.push(self.stx(min)?.0);
        }
        if items.is_empty() {
            return Err(self.bad());
        }
        Ok(null_node(items))
    }

    /// `"(" seq ")"`-shaped arguments of `sepBy(`, `unicode(` and the functions: entered once per
    /// nesting level, refused past [`DEPTH`].
    fn enter(&mut self) -> Result<(), NatDefinitionParseError> {
        self.depth += 1;
        if self.depth > DEPTH {
            return Err(self.bad());
        }
        Ok(())
    }

    /// One `stx` whose precedence is at least `min`, and that precedence.
    fn stx(&mut self, min: u32) -> Result<(Syntax, u32), NatDefinitionParseError> {
        let (mut left, mut prec) = self.stx_leading()?;
        if prec < min {
            return Err(self.bad());
        }
        loop {
            let postfix = [
                ("*", "stx_*"),
                ("+", "stx_+"),
                ("?", "stx_?"),
                (",*", "stx_,*"),
                (",+", "stx_,+"),
                (",*,?", "stx_,*,?"),
                (",+,?", "stx_,+,?"),
            ]
            .into_iter()
            .find(|(symbol, _)| self.symbol(self.at, symbol));
            if let Some((_, name)) = postfix
                && prec >= MAX
                && ARG >= min
            {
                let operator = self.take()?;
                left = Syntax::node(kind(name), vec![left, operator]);
                prec = ARG;
                continue;
            }
            if self.symbol(self.at, "<|>") && prec >= ORELSE && ORELSE >= min {
                let operator = self.take()?;
                let (right, _) = self.stx(1)?;
                left = Syntax::node(kind("stx_<|>_"), vec![left, operator, right]);
                prec = ORELSE;
                continue;
            }
            return Ok((left, prec));
        }
    }

    fn stx_leading(&mut self) -> Result<(Syntax, u32), NatDefinitionParseError> {
        let at = self.at;
        if self.literal(at, LiteralKind::Str) {
            let string = self.string()?;
            return Ok((
                Syntax::node(parser_kind(&["Syntax", "atom"]), vec![string]),
                MAX,
            ));
        }
        if self.symbol(at, "&") {
            let amp = self.take()?;
            let string = self.string()?;
            return Ok((
                Syntax::node(parser_kind(&["Syntax", "nonReserved"]), vec![amp, string]),
                MAX,
            ));
        }
        if self.symbol(at, "!") {
            let bang = self.take()?;
            let (operand, _) = self.stx(MAX)?;
            return Ok((Syntax::node(kind("stx!_"), vec![bang, operand]), ARG));
        }
        self.enter()?;
        let parsed = if self.symbol(at, "unicode(") {
            let open = self.take()?;
            let first = self.string()?;
            let comma = self.expect(",")?;
            let second = self.string()?;
            let preserve = if self.symbol(self.at, ",") && self.word(self.at + 1, "preserveForPP") {
                let comma = self.take()?;
                null_node(vec![comma, self.atom("preserveForPP")?])
            } else {
                null_node(Vec::new())
            };
            let close = self.expect(")")?;
            Syntax::node(
                parser_kind(&["Syntax", "unicodeAtom"]),
                vec![open, first, comma, second, preserve, close],
            )
        } else if self.symbol(at, "sepBy(") || self.symbol(at, "sepBy1(") {
            let name = if self.symbol(at, "sepBy(") {
                "sepBy"
            } else {
                "sepBy1"
            };
            let open = self.take()?;
            let items = self.sequence(0)?;
            let comma = self.expect(",")?;
            let separator = self.string()?;
            let mut printed = null_node(Vec::new());
            let mut trailing = null_node(Vec::new());
            if self.symbol(self.at, ",") && !self.word(self.at + 1, "allowTrailingSep") {
                let comma = self.take()?;
                printed = null_node(vec![comma, self.sequence(0)?]);
            }
            if self.symbol(self.at, ",") {
                let comma = self.take()?;
                trailing = null_node(vec![comma, self.atom("allowTrailingSep")?]);
            }
            let close = self.expect(")")?;
            Syntax::node(
                parser_kind(&["Syntax", name]),
                vec![open, items, comma, separator, printed, trailing, close],
            )
        } else if self.symbol(at, "(") {
            let open = self.take()?;
            let items = self.sequence(0)?;
            let close = self.expect(")")?;
            Syntax::node(parser_kind(&["Syntax", "paren"]), vec![open, items, close])
        } else if self.ident(at)
            && self.symbol(at + 1, "(")
            && self.tokens[at].extent.end() == self.tokens[at + 1].extent.start()
        {
            // `unary := ident noWs "(" many1 stx ")"`, `binary := … many1 stx ", " many1 stx …`.
            let function = self.take()?;
            let open = self.take()?;
            let first = self.sequence(0)?;
            if self.symbol(self.at, ",") {
                let comma = self.take()?;
                let second = self.sequence(0)?;
                let close = self.expect(")")?;
                Syntax::node(
                    parser_kind(&["Syntax", "binary"]),
                    vec![function, open, first, comma, second, close],
                )
            } else {
                let close = self.expect(")")?;
                Syntax::node(
                    parser_kind(&["Syntax", "unary"]),
                    vec![function, open, first, close],
                )
            }
        } else if self.ident(at) {
            let name = self.take()?;
            // `optPrecedence` is `atomic`: a `:` not followed by a precedence is the command's.
            let precedence = if self.symbol(self.at, ":") && self.starts_precedence(self.at + 1) {
                null_node(vec![self.precedence()?])
            } else {
                null_node(Vec::new())
            };
            Syntax::node(parser_kind(&["Syntax", "cat"]), vec![name, precedence])
        } else {
            return Err(self.bad());
        };
        self.depth -= 1;
        Ok((parsed, MAX))
    }
}

/// `namedPrio` (`" (" "priority" " := " prio ")"`) at `start`, as the pin builds it, and the
/// token after its `)`; `None` when no `(priority :=` starts there.
pub(crate) fn named_priority(
    view: &SourceView,
    tokens: &[LexedToken],
    leaves: &Leaves,
    start: usize,
) -> Result<Option<(Syntax, usize)>, DefinitionParseError> {
    let mut reader = Reader {
        view,
        tokens,
        leaves,
        at: start,
        end: tokens.len(),
        depth: 0,
    };
    Ok(reader
        .named("priority", "namedPrio")?
        .map(|node| (node, reader.at)))
}

/// A `syntax` or `syntax … :=` declaration, with its doc comment, attributes and `scoped`/`local`
/// or visibility, as the pin's tree; `None` for any other command. The checker refuses it.
pub(crate) fn declaration(
    source: &[u8],
) -> Result<Option<ParsedSourceCommand>, DefinitionParseError> {
    let original = SourceText::from_utf8(source).map_err(NatDefinitionParseError::Source)?;
    let view = SourceView::of(&original);
    let tokens = tokens(&view)?;
    let symbol = |at: usize, text: &str| matches!(tokens.get(at).map(|t| &t.kind), Some(TokenKind::Symbol(s)) if s == text);
    let doc = usize::from(symbol(0, "/--"));
    let attributes_end = attributes::inline_end(&view, &tokens, doc)?;
    let modifier = ["scoped", "local", "private", "protected"]
        .into_iter()
        .find(|word| symbol(attributes_end, word));
    let keyword = attributes_end + usize::from(modifier.is_some());
    let mixfix = ["infix", "infixl", "infixr", "prefix", "postfix"]
        .into_iter()
        .find(|word| symbol(keyword, word));
    if mixfix.is_some() || symbol(keyword, "notation") || symbol(keyword, "recommended_spelling") {
        return notation(view, tokens, doc, attributes_end, modifier, keyword, mixfix);
    }
    if !symbol(keyword, "syntax") {
        return Ok(None);
    }
    let leaves = Leaves::build(view.normalized(), &tokens)?;
    let doc_slot = if doc == 1 {
        crate::doc_comment_syntax(&view, &leaves, &tokens, 0)?
    } else {
        null_node(Vec::new())
    };
    let mut reader = Reader {
        view: &view,
        tokens: &tokens,
        leaves: &leaves,
        at: keyword + 1,
        end: tokens.len(),
        depth: 0,
    };
    let abbreviation = reader.ident(keyword + 1) && reader.symbol(keyword + 2, ":=");
    let syntax = if abbreviation {
        if attributes_end != doc || matches!(modifier, Some("scoped" | "local")) {
            return Err(reader.bad());
        }
        let visibility = match modifier {
            Some(word) => null_node(vec![Syntax::node(
                parser_kind(&["Command", word]),
                vec![leaves.leaf(attributes_end)?],
            )]),
            None => null_node(Vec::new()),
        };
        let name = reader.take()?;
        let assign = reader.take()?;
        let items = reader.sequence(0)?;
        if reader.at != reader.end {
            return Err(reader.bad());
        }
        Syntax::node(
            parser_kind(&["Command", "syntaxAbbrev"]),
            vec![
                doc_slot,
                visibility,
                leaves.leaf(keyword)?,
                name,
                assign,
                items,
            ],
        )
    } else {
        if matches!(modifier, Some("private" | "protected")) {
            return Err(reader.bad());
        }
        let attributes = attributes::inline_syntax(&view, &leaves, &tokens, doc)?;
        let kind_slot = match modifier {
            Some(word) => null_node(vec![Syntax::node(
                parser_kind(&["Term", word]),
                vec![leaves.leaf(attributes_end)?],
            )]),
            None => null_node(Vec::new()),
        };
        let precedence = if reader.symbol(reader.at, ":") {
            null_node(vec![reader.precedence()?])
        } else {
            null_node(Vec::new())
        };
        let name = reader.named("name", "namedName")?;
        let prio = reader.named("priority", "namedPrio")?;
        // The items end at the `:` before the category, the command's last token.
        let colon = reader.end.checked_sub(2).ok_or_else(|| reader.bad())?;
        if !reader.symbol(colon, ":") || !reader.ident(colon + 1) {
            return Err(reader.bad());
        }
        reader.end = colon;
        let mut items = Vec::new();
        while reader.at < colon {
            items.push(reader.stx(ARG)?.0);
        }
        if items.is_empty() {
            return Err(reader.bad());
        }
        Syntax::node(
            parser_kind(&["Command", "syntax"]),
            vec![
                doc_slot,
                attributes,
                Syntax::node(parser_kind(&["Term", "attrKind"]), vec![kind_slot]),
                leaves.leaf(keyword)?,
                precedence,
                null_node(name.into_iter().collect()),
                null_node(prio.into_iter().collect()),
                null_node(items),
                leaves.leaf(colon)?,
                leaves.leaf(colon + 1)?,
            ],
        )
    };
    let epilogue = leaves.attachment().epilogue();
    Ok(Some(ParsedSourceCommand {
        kind: SourceCommandKind::Definition,
        source_view: view,
        syntax,
        epilogue,
        query_term: None,
    }))
}

/// A `mixfix` (`infixl:65 " + " => HAdd.hAdd`), `notation` or `recommended_spelling` command from
/// its keyword at `keyword`, as the pin's tree. The checker refuses it.
#[inline(never)]
fn notation(
    view: SourceView,
    tokens: Vec<LexedToken>,
    doc: usize,
    attributes_end: usize,
    modifier: Option<&str>,
    keyword: usize,
    mixfix: Option<&str>,
) -> Result<Option<ParsedSourceCommand>, DefinitionParseError> {
    let leaves = Leaves::build(view.normalized(), &tokens)?;
    let doc_slot = if doc == 1 {
        crate::doc_comment_syntax(&view, &leaves, &tokens, 0)?
    } else {
        null_node(Vec::new())
    };
    let mut reader = Reader {
        view: &view,
        tokens: &tokens,
        leaves: &leaves,
        at: keyword + 1,
        end: tokens.len(),
        depth: 0,
    };
    if matches!(modifier, Some("private" | "protected")) {
        return Err(reader.bad());
    }
    if reader.symbol(keyword, "recommended_spelling") {
        if attributes_end != doc || modifier.is_some() {
            return Err(reader.bad());
        }
        let spelling = reader.string()?;
        let for_ = reader.atom("for")?;
        let notation = reader.string()?;
        let in_ = reader.atom("in")?;
        let open = reader.expect("[")?;
        // `ident,*`: no trailing separator.
        let mut names = Vec::new();
        if reader.ident(reader.at) {
            names.push(reader.take()?);
            while reader.symbol(reader.at, ",") {
                names.push(reader.take()?);
                if !reader.ident(reader.at) {
                    return Err(reader.bad());
                }
                names.push(reader.take()?);
            }
        }
        let close = reader.expect("]")?;
        if reader.at != reader.end {
            return Err(reader.bad());
        }
        let syntax = Syntax::node(
            parser_kind(&["Command", "recommended_spelling"]),
            vec![
                doc_slot,
                leaves.leaf(keyword)?,
                spelling,
                for_,
                notation,
                in_,
                open,
                null_node(names),
                close,
            ],
        );
        return finish(view, &leaves, syntax);
    }
    let attributes = attributes::inline_syntax(&view, &leaves, &tokens, doc)?;
    let kind_slot = match modifier {
        Some(word) => null_node(vec![Syntax::node(
            parser_kind(&["Term", word]),
            vec![leaves.leaf(attributes_end)?],
        )]),
        None => null_node(Vec::new()),
    };
    let attr_kind = Syntax::node(parser_kind(&["Term", "attrKind"]), vec![kind_slot]);
    let precedence = if reader.symbol(reader.at, ":") {
        Some(reader.precedence()?)
    } else {
        None
    };
    let name = null_node(reader.named("name", "namedName")?.into_iter().collect());
    let prio = null_node(reader.named("priority", "namedPrio")?.into_iter().collect());
    let arrow = (reader.at..reader.end)
        .find(|&at| reader.symbol(at, "=>"))
        .ok_or_else(|| reader.bad())?;
    reader.end = arrow;
    let mut items = Vec::new();
    while reader.at < arrow {
        items.push(reader.notation_item()?);
    }
    reader.end = tokens.len();
    if arrow + 1 >= tokens.len() {
        return Err(reader.bad());
    }
    let value = crate::nested_term(&leaves, &view, &tokens, arrow + 1..tokens.len())?;
    let syntax = match mixfix {
        Some(word) => {
            // `precedence` is not optional here, and the one item is the notation's atom.
            let (Some(precedence), [item]) = (precedence, items.as_slice()) else {
                return Err(reader.bad());
            };
            if !matches!(item, Syntax::Node { kind, .. } if *kind == Name::str(Name::anonymous(), "str"))
            {
                return Err(reader.bad());
            }
            Syntax::node(
                parser_kind(&["Command", "mixfix"]),
                vec![
                    doc_slot,
                    attributes,
                    attr_kind,
                    Syntax::node(parser_kind(&["Command", word]), vec![leaves.leaf(keyword)?]),
                    precedence,
                    name,
                    prio,
                    item.clone(),
                    leaves.leaf(arrow)?,
                    value,
                ],
            )
        }
        None => Syntax::node(
            parser_kind(&["Command", "notation"]),
            vec![
                doc_slot,
                attributes,
                attr_kind,
                leaves.leaf(keyword)?,
                null_node(precedence.into_iter().collect()),
                name,
                prio,
                null_node(items),
                leaves.leaf(arrow)?,
                value,
            ],
        ),
    };
    finish(view, &leaves, syntax)
}

fn finish(
    view: SourceView,
    leaves: &Leaves,
    syntax: Syntax,
) -> Result<Option<ParsedSourceCommand>, DefinitionParseError> {
    let epilogue = leaves.attachment().epilogue();
    Ok(Some(ParsedSourceCommand {
        kind: SourceCommandKind::Definition,
        source_view: view,
        syntax,
        epilogue,
        query_term: None,
    }))
}
