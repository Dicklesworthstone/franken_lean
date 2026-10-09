//! Bounded, standalone native simp-attribute commands. All syntax is lexed;
//! unsupported attributes and modifiers are errors rather than ignored effects.
use super::*;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SimpAttribute {
    pub declarations: Vec<Name>,
    /// `None` removes a rule; `Some` records (priority, reverse).
    pub rule: Option<(u32, bool)>,
}

/// One inline attribute list as the pin parses it, held as token indices until the leaves
/// exist. Vendored `src/Lean/Parser/Term.lean`:
///
/// ```text
/// attributes   := "@[" sepBy1 attrInstance ", " "]"
/// attrInstance := attrKind attr          attrKind := optional («scoped» <|> «local»)
/// ```
///
/// `attr` is a category whose leading identifier is read as the symbol it spells
/// (`LeadingIdentBehavior.symbol`, `src/Lean/Parser/Attr.lean`), so `simp`, `grind` and
/// `specialize` are identifiers to the lexer and atoms in the tree. The attributes read here are
/// the ones the pin syntax corpus shows over `Init` and `Std`, each with the tree the pin built
/// for it (bead `fln-pin-syntax-corpus-7b5b`). Any other attribute, and any argument form not
/// listed, is refused where it starts: an attribute is never dropped, and parsing one gives it
/// no meaning. The elaborator decides which attributes it implements.
#[derive(Debug)]
enum Shape {
    /// The token's own leaf.
    Leaf(usize),
    /// An identifier-shaped token in symbol position, as the atom `text`.
    Atom(usize, &'static str),
    /// Two touching tokens the pin lexes as the one symbol `text` (`grind!`).
    Joined(usize, usize, &'static str),
    /// A literal's atom under its `num` or `str` node.
    Literal(&'static str, usize),
    Node(Name, Vec<Shape>),
    Null(Vec<Shape>),
}

/// Attribute priorities nest only through parentheses; deeper nesting than this is refused
/// rather than recursed into on a small host stack.
const PRIORITY_DEPTH: usize = 16;

struct AttributeReader<'a> {
    view: &'a SourceView,
    tokens: &'a [LexedToken],
    at: usize,
}

impl AttributeReader<'_> {
    fn kind(&self, at: usize) -> Option<&TokenKind> {
        self.tokens.get(at).map(|token| &token.kind)
    }

    fn symbol(&self, text: &str) -> bool {
        matches!(self.kind(self.at), Some(TokenKind::Symbol(symbol)) if symbol == text)
    }

    /// The pin's symbol `text` at the cursor: the lexer's own symbol for it, or an unescaped
    /// identifier spelling it.
    fn word(&self, text: &str) -> bool {
        match self.kind(self.at) {
            Some(TokenKind::Symbol(symbol)) => symbol == text,
            Some(TokenKind::Ident(_)) => {
                self.view.normalized().span_str(self.tokens[self.at].extent) == Some(text)
            }
            _ => false,
        }
    }

    fn ident(&self) -> bool {
        matches!(self.kind(self.at), Some(TokenKind::Ident(_)))
    }

    fn literal(&self, kind: LiteralKind) -> bool {
        matches!(self.kind(self.at), Some(TokenKind::Literal(found)) if *found == kind)
    }

    fn touching(&self, left: usize, right: usize) -> bool {
        match (self.tokens.get(left), self.tokens.get(right)) {
            (Some(left), Some(right)) => left.extent.end() == right.extent.start(),
            _ => false,
        }
    }

    fn bad(&self) -> NatDefinitionParseError {
        NatDefinitionParseError::OutsideSeedGrammar {
            at: original_position(self.view, self.tokens, self.at),
            expected: NatDefinitionExpectation::Attribute,
        }
    }

    fn take(&mut self) -> usize {
        self.at += 1;
        self.at - 1
    }

    /// The symbol `text` at the cursor, as an atom.
    fn atom(&mut self, text: &'static str) -> Result<Shape, NatDefinitionParseError> {
        if !self.word(text) {
            return Err(self.bad());
        }
        Ok(Shape::Atom(self.take(), text))
    }

    /// The first of `texts` at the cursor, as an atom.
    fn one_of(&mut self, texts: &[&'static str]) -> Option<Shape> {
        let text = texts.iter().find(|text| self.word(text))?;
        Some(Shape::Atom(self.take(), text))
    }

    fn take_ident(&mut self) -> Result<Shape, NatDefinitionParseError> {
        if !self.ident() {
            return Err(self.bad());
        }
        Ok(Shape::Leaf(self.take()))
    }

    fn take_literal(&mut self, kind: LiteralKind) -> Result<Shape, NatDefinitionParseError> {
        if !self.literal(kind) {
            return Err(self.bad());
        }
        let node = if kind == LiteralKind::Str {
            "str"
        } else {
            "num"
        };
        Ok(Shape::Literal(node, self.take()))
    }

    /// `prio`: a numeral, `default`/`low`/`mid`/`high`, or a parenthesized priority
    /// (vendored `src/Init/Notation.lean`, `src/Lean/Parser/Attr.lean` `numPrio`).
    /// `numPrio` is not a `leading_parser`, so a numeral is its `num` node alone.
    fn priority(&mut self, depth: usize) -> Result<Shape, NatDefinitionParseError> {
        if self.literal(LiteralKind::Nat) {
            return self.take_literal(LiteralKind::Nat);
        }
        for (text, kind) in [
            ("default", "prioDefault"),
            ("low", "prioLow"),
            ("mid", "prioMid"),
            ("high", "prioHigh"),
        ] {
            if self.word(text) {
                return Ok(Shape::Node(
                    Name::from_components([kind]),
                    vec![Shape::Atom(self.take(), text)],
                ));
            }
        }
        if self.symbol("(") && depth < PRIORITY_DEPTH {
            let open = Shape::Leaf(self.take());
            let inner = self.priority(depth + 1)?;
            if !self.symbol(")") {
                return Err(self.bad());
            }
            let close = Shape::Leaf(self.take());
            return Ok(Shape::Node(
                Name::from_components(["prio(_)"]),
                vec![open, inner, close],
            ));
        }
        Err(self.bad())
    }

    fn starts_priority(&self) -> bool {
        self.literal(LiteralKind::Nat)
            || self.symbol("(")
            || ["default", "low", "mid", "high"]
                .iter()
                .any(|text| self.word(text))
    }

    fn optional_priority(&mut self) -> Result<Shape, NatDefinitionParseError> {
        Ok(Shape::Null(if self.starts_priority() {
            vec![self.priority(0)?]
        } else {
            Vec::new()
        }))
    }

    /// `"simp" (simpPre <|> simpPost)? unicode("← ", "<- ")? (prio)?` and the simp sets
    /// declared with the same grammar (vendored `src/Init/Tactics.lean`).
    fn simp_like(&mut self, keyword: &'static str) -> Result<Shape, NatDefinitionParseError> {
        let head = self.atom(keyword)?;
        let phase = Shape::Null(
            [("↓", "simpPre"), ("↑", "simpPost")]
                .into_iter()
                .find(|(text, _)| self.symbol(text))
                .map(|(text, kind)| {
                    vec![Shape::Node(
                        parser_kind(&["Tactic", kind]),
                        vec![Shape::Atom(self.take(), text)],
                    )]
                })
                .unwrap_or_default(),
        );
        let reverse = Shape::Null(self.one_of(&["←", "<-"]).into_iter().collect());
        let priority = self.optional_priority()?;
        Ok(Shape::Node(
            parser_kind(&["Attr", keyword]),
            vec![head, phase, reverse, priority],
        ))
    }

    /// `patternIgnore(a <|> b)` over single symbols: the alternative is a `token.<symbol>` node.
    fn pattern_ignore(&mut self, texts: &[&'static str]) -> Option<Shape> {
        let text = *texts.iter().find(|text| self.symbol(text))?;
        Some(Shape::Node(
            Name::from_components(["patternIgnore"]),
            vec![Shape::Node(
                Name::from_components(["token", text]),
                vec![Shape::Atom(self.take(), text)],
            )],
        ))
    }

    fn grind_gen(&mut self) -> Shape {
        Shape::Null(if self.word("gen") {
            vec![grind_node(
                "grindGen",
                vec![Shape::Atom(self.take(), "gen")],
            )]
        } else {
            Vec::new()
        })
    }

    /// `grindMod` (vendored `src/Init/Grind/Attr.lean`), its alternatives in the pin's order.
    fn grind_modifier(&mut self) -> Result<Option<Shape>, NatDefinitionParseError> {
        let next_is = |reader: &Self, offset: usize, text: &str| matches!(reader.kind(reader.at + offset), Some(TokenKind::Symbol(symbol)) if symbol == text);
        let modifier = if self.symbol("_") && next_is(self, 1, "=") && next_is(self, 2, "_") {
            let parts = vec![
                Shape::Atom(self.take(), "_"),
                Shape::Atom(self.take(), "="),
                Shape::Atom(self.take(), "_"),
                self.grind_gen(),
            ];
            grind_node("grindEqBoth", parts)
        } else if self.symbol("=") && next_is(self, 1, "_") {
            let parts = vec![
                Shape::Atom(self.take(), "="),
                Shape::Atom(self.take(), "_"),
                self.grind_gen(),
            ];
            grind_node("grindEqRhs", parts)
        } else if self.symbol("=") {
            let parts = vec![Shape::Atom(self.take(), "="), self.grind_gen()];
            grind_node("grindEq", parts)
        } else if (self.symbol("←") || self.symbol("<-")) && next_is(self, 1, "=") {
            let arrow = if self.symbol("←") { "←" } else { "<-" };
            let group = Shape::Node(
                Name::from_components(["group"]),
                vec![
                    Shape::Atom(self.take(), arrow),
                    Shape::Atom(self.take(), "="),
                ],
            );
            grind_node(
                "grindEqBwd",
                vec![Shape::Node(
                    Name::from_components(["patternIgnore"]),
                    vec![group],
                )],
            )
        } else if let Some(arrow) = self.pattern_ignore(&["←", "<-"]) {
            let generalize = self.grind_gen();
            grind_node("grindBwd", vec![arrow, generalize])
        } else if let Some(arrow) = self.pattern_ignore(&["→", "->"]) {
            grind_node("grindFwd", vec![arrow])
        } else if let Some(arrow) = self.pattern_ignore(&["⇐", "<="]) {
            grind_node("grindRL", vec![arrow])
        } else if let Some(arrow) = self.pattern_ignore(&["⇒", "=>"]) {
            grind_node("grindLR", vec![arrow])
        } else if self.word("cases") {
            let cases = Shape::Atom(self.take(), "cases");
            if self.word("eager") {
                grind_node(
                    "grindCasesEager",
                    vec![cases, Shape::Atom(self.take(), "eager")],
                )
            } else {
                grind_node("grindCases", vec![cases])
            }
        } else if let Some((text, kind)) = [
            ("usr", "grindUsr"),
            ("intro", "grindIntro"),
            ("ext", "grindExt"),
            ("gen", "grindGen"),
            ("inj", "grindInj"),
            ("funCC", "grindFunCC"),
            ("unfold", "grindUnfold"),
        ]
        .into_iter()
        .find(|(text, _)| self.word(text))
        {
            grind_node(kind, vec![Shape::Atom(self.take(), text)])
        } else if self.word("symbol") {
            let symbol = Shape::Atom(self.take(), "symbol");
            let priority = self.priority(0)?;
            grind_node("grindSym", vec![symbol, priority])
        } else if let Some(dot) = self.pattern_ignore(&[".", "·"]) {
            let generalize = self.grind_gen();
            grind_node("grindDef", vec![dot, generalize])
        } else {
            return Ok(None);
        };
        Ok(Some(grind_node("grindMod", vec![modifier])))
    }

    /// `"grind" (grindMod)?` and its `grind!` variant.
    fn grind(&mut self) -> Result<Shape, NatDefinitionParseError> {
        let bang = self.word("grind")
            && matches!(self.kind(self.at + 1), Some(TokenKind::Symbol(symbol)) if symbol == "!")
            && self.touching(self.at, self.at + 1);
        let (head, kind) = if bang {
            let first = self.take();
            (Shape::Joined(first, self.take(), "grind!"), "grind!")
        } else if self.word("grind!") {
            (Shape::Atom(self.take(), "grind!"), "grind!")
        } else {
            (self.atom("grind")?, "grind")
        };
        let modifier = Shape::Null(self.grind_modifier()?.into_iter().collect());
        Ok(Shape::Node(
            parser_kind(&["Attr", kind]),
            vec![head, modifier],
        ))
    }

    /// `"deprecated" (ident)? (str)? (" (" &"since" " := " str ")")?` (vendored
    /// `src/Init/Notation.lean`), whose kind is `Lean.deprecated`.
    fn deprecated(&mut self) -> Result<Shape, NatDefinitionParseError> {
        let head = self.atom("deprecated")?;
        let replacement = Shape::Null(if self.ident() {
            vec![Shape::Leaf(self.take())]
        } else {
            Vec::new()
        });
        let message = Shape::Null(if self.literal(LiteralKind::Str) {
            vec![self.take_literal(LiteralKind::Str)?]
        } else {
            Vec::new()
        });
        let since = Shape::Null(if self.symbol("(") {
            vec![
                Shape::Leaf(self.take()),
                self.atom("since")?,
                {
                    if !self.symbol(":=") {
                        return Err(self.bad());
                    }
                    Shape::Leaf(self.take())
                },
                self.take_literal(LiteralKind::Str)?,
                {
                    if !self.symbol(")") {
                        return Err(self.bad());
                    }
                    Shape::Leaf(self.take())
                },
            ]
        } else {
            Vec::new()
        });
        Ok(Shape::Node(
            Name::from_components(["Lean", "deprecated"]),
            vec![head, replacement, message, since],
        ))
    }

    /// `"extern" (externEntry)*`, `externEntry := (ident)? (&"inline")? str`.
    fn extern_attribute(&mut self) -> Result<Shape, NatDefinitionParseError> {
        let head = self.atom("extern")?;
        let mut entries = Vec::new();
        while self.ident() || self.literal(LiteralKind::Str) {
            let backend = Shape::Null(if self.ident() {
                vec![Shape::Leaf(self.take())]
            } else {
                Vec::new()
            });
            let inline = Shape::Null(self.one_of(&["inline"]).into_iter().collect());
            let name = self.take_literal(LiteralKind::Str)?;
            entries.push(Shape::Node(
                parser_kind(&["Attr", "externEntry"]),
                vec![backend, inline, name],
            ));
        }
        Ok(Shape::Node(
            parser_kind(&["Attr", "extern"]),
            vec![head, Shape::Null(entries)],
        ))
    }

    /// One `attr`, dispatched on the symbol its leading token spells.
    fn attribute(&mut self) -> Result<Shape, NatDefinitionParseError> {
        let keyword_then_ident = |reader: &mut Self, keyword: &'static str| {
            let head = reader.atom(keyword)?;
            let name = reader.take_ident()?;
            Ok(Shape::Node(
                parser_kind(&["Attr", keyword]),
                vec![head, name],
            ))
        };
        if self.word("simp") {
            return self.simp_like("simp");
        }
        if self.word("wf_preprocess") {
            return self.simp_like("wf_preprocess");
        }
        if self.word("grind") || self.word("grind!") {
            return self.grind();
        }
        if self.word("deprecated") {
            return self.deprecated();
        }
        if self.word("extern") {
            return self.extern_attribute();
        }
        // `syntax (name := coe) "coe" : attr`, declared in namespace `Lean.Attr`.
        if self.word("coe") {
            let head = self.atom("coe")?;
            return Ok(Shape::Node(
                Name::from_components(["Lean", "Attr", "coe"]),
                vec![head],
            ));
        }
        for keyword in ["instance", "default_instance"] {
            if self.word(keyword) {
                let head = self.atom(keyword)?;
                let priority = self.optional_priority()?;
                return Ok(Shape::Node(
                    parser_kind(&["Attr", keyword]),
                    vec![head, priority],
                ));
            }
        }
        for keyword in ["export", "macro", "tactic_alt"] {
            if self.word(keyword) {
                return keyword_then_ident(self, keyword);
            }
        }
        if self.word("specialize") {
            let head = self.atom("specialize")?;
            let mut arguments = Vec::new();
            while self.ident() || self.literal(LiteralKind::Nat) {
                arguments.push(if self.ident() {
                    Shape::Leaf(self.take())
                } else {
                    self.take_literal(LiteralKind::Nat)?
                });
            }
            return Ok(Shape::Node(
                parser_kind(&["Attr", "specialize"]),
                vec![head, Shape::Null(arguments)],
            ));
        }
        if self.word("suggest_for") {
            let head = self.atom("suggest_for")?;
            let mut names = vec![self.take_ident()?];
            while self.ident() {
                names.push(Shape::Leaf(self.take()));
            }
            return Ok(Shape::Node(
                Name::from_components(["Lean", "suggest_for"]),
                vec![head, Shape::Null(names)],
            ));
        }
        if self.word("cbv_eval") {
            let head = self.atom("cbv_eval")?;
            let reverse = Shape::Null(self.one_of(&["←", "<-"]).into_iter().collect());
            let name = Shape::Null(if self.ident() {
                vec![Shape::Leaf(self.take())]
            } else {
                Vec::new()
            });
            return Ok(Shape::Node(
                parser_kind(&["Attr", "cbv_eval"]),
                vec![head, reverse, name],
            ));
        }
        if self.word("ext") {
            // Only the bare form with an optional priority: `extIff`/`extFlat` are refused.
            let head = self.atom("ext")?;
            let priority = self.optional_priority()?;
            return Ok(Shape::Node(
                parser_kind(&["Attr", "ext"]),
                vec![
                    head,
                    Shape::Null(Vec::new()),
                    Shape::Null(Vec::new()),
                    priority,
                ],
            ));
        }
        if self.word("norm_cast") {
            // Only the bare form: a label or a numeral is refused.
            let head = self.atom("norm_cast")?;
            return Ok(Shape::Node(
                parser_kind(&["Attr", "norm_cast"]),
                vec![head, Shape::Null(Vec::new()), Shape::Null(Vec::new())],
            ));
        }
        // Builtin attribute keywords whose own parsers are not read here (`class`, `recursor`,
        // `tactic_tag`, …) must not fall through to `Attr.simple`, which the pin never tries for
        // a symbol-indexed attribute.
        if !self.ident()
            || [
                "class",
                "recursor",
                "tactic_tag",
                "tactic_name",
                "method_specs_simp",
                "simproc",
                "sevalproc",
                "builtin_simproc",
                "builtin_sevalproc",
                "grind?",
                "grind!?",
            ]
            .iter()
            .any(|text| self.word(text))
        {
            return Err(self.bad());
        }
        // An escaped name (`«simp»`) is refused: which parser the pin indexes it under is not
        // measured here.
        if self
            .view
            .normalized()
            .span_str(self.tokens[self.at].extent)
            .is_some_and(|text| text.starts_with('«'))
        {
            return Err(self.bad());
        }
        // `Attr.simple := ident (prio <|> ident)?`.
        let name = Shape::Leaf(self.take());
        let argument = if self.starts_priority() {
            vec![self.priority(0)?]
        } else if self.ident() {
            vec![Shape::Leaf(self.take())]
        } else {
            Vec::new()
        };
        Ok(Shape::Node(
            parser_kind(&["Attr", "simple"]),
            vec![name, Shape::Null(argument)],
        ))
    }

    /// `attrKind attr`.
    fn instance(&mut self) -> Result<Shape, NatDefinitionParseError> {
        let scope = [("scoped", "scoped"), ("local", "local")]
            .into_iter()
            .find(|(text, _)| self.word(text))
            .map(|(text, kind)| {
                vec![Shape::Node(
                    parser_kind(&["Term", kind]),
                    vec![Shape::Atom(self.take(), text)],
                )]
            })
            .unwrap_or_default();
        let kind = Shape::Node(parser_kind(&["Term", "attrKind"]), vec![Shape::Null(scope)]);
        let attribute = self.attribute()?;
        Ok(Shape::Node(
            parser_kind(&["Term", "attrInstance"]),
            vec![kind, attribute],
        ))
    }

    /// `"attribute" "[" sepBy1 (eraseAttr <|> attrInstance) ", " "]" ident+`, from the cursor at
    /// `attribute`, with `eraseAttr := "-" rawIdent` (`Lean/Parser/Command.lean`).
    fn command(&mut self) -> Result<Shape, NatDefinitionParseError> {
        let keyword = Shape::Leaf(self.take());
        if !self.symbol("[") {
            return Err(self.bad());
        }
        let open = Shape::Leaf(self.take());
        let mut instances = Vec::new();
        loop {
            if self.symbol("-") {
                let minus = Shape::Leaf(self.take());
                if !self.ident() {
                    return Err(self.bad());
                }
                instances.push(Shape::Node(
                    parser_kind(&["Command", "eraseAttr"]),
                    vec![minus, Shape::Leaf(self.take())],
                ));
            } else {
                instances.push(self.instance()?);
            }
            if !self.symbol(",") {
                break;
            }
            instances.push(Shape::Leaf(self.take()));
        }
        if !self.symbol("]") {
            return Err(self.bad());
        }
        let close = Shape::Leaf(self.take());
        let mut names = Vec::new();
        while self.ident() {
            names.push(Shape::Leaf(self.take()));
        }
        if names.is_empty() || self.at != self.tokens.len() {
            return Err(self.bad());
        }
        Ok(Shape::Node(
            parser_kind(&["Command", "attribute"]),
            vec![
                keyword,
                open,
                Shape::Null(instances),
                close,
                Shape::Null(names),
            ],
        ))
    }

    /// `"@[" sepBy1 attrInstance ", " "]"`, from the cursor at `@[`.
    fn attributes(&mut self) -> Result<Shape, NatDefinitionParseError> {
        let open = Shape::Leaf(self.take());
        let mut instances = vec![self.instance()?];
        while self.symbol(",") {
            instances.push(Shape::Leaf(self.take()));
            instances.push(self.instance()?);
        }
        if !self.symbol("]") {
            return Err(self.bad());
        }
        let close = Shape::Leaf(self.take());
        Ok(Shape::Node(
            parser_kind(&["Term", "attributes"]),
            vec![open, Shape::Null(instances), close],
        ))
    }
}

fn grind_node(kind: &str, parts: Vec<Shape>) -> Shape {
    Shape::Node(parser_kind(&["Attr", kind]), parts)
}

fn build(shape: &Shape, leaves: &Leaves) -> Result<Syntax, DefinitionParseError> {
    Ok(match shape {
        Shape::Leaf(at) => leaves.leaf(*at)?,
        Shape::Atom(at, text) => Syntax::Atom {
            info: leaves.leaf(*at)?.info(),
            val: (*text).into(),
        },
        Shape::Joined(first, last, text) => {
            let (
                SourceInfo::Original { leading, pos, .. },
                SourceInfo::Original {
                    trailing, end_pos, ..
                },
            ) = (leaves.leaf(*first)?.info(), leaves.leaf(*last)?.info())
            else {
                return Err(NatDefinitionParseError::OutsideSeedGrammar {
                    at: BytePos(0),
                    expected: NatDefinitionExpectation::Attribute,
                });
            };
            Syntax::Atom {
                info: SourceInfo::Original {
                    leading,
                    pos,
                    trailing,
                    end_pos,
                },
                val: (*text).into(),
            }
        }
        Shape::Literal(kind, at) => {
            Syntax::node(Name::from_components([*kind]), vec![leaves.leaf(*at)?])
        }
        Shape::Node(kind, parts) => Syntax::node(
            kind.clone(),
            parts
                .iter()
                .map(|part| build(part, leaves))
                .collect::<Result<_, _>>()?,
        ),
        Shape::Null(parts) => null_node(
            parts
                .iter()
                .map(|part| build(part, leaves))
                .collect::<Result<_, _>>()?,
        ),
    })
}

/// The pin's tree for an `attribute` command, or `None` for a form this grammar does not read.
pub(crate) fn command_syntax(
    view: &SourceView,
    tokens: &[LexedToken],
    leaves: &Leaves,
) -> Result<Option<Syntax>, DefinitionParseError> {
    let mut reader = AttributeReader {
        view,
        tokens,
        at: 0,
    };
    match reader.command() {
        Ok(shape) => build(&shape, leaves).map(Some),
        Err(_) => Ok(None),
    }
}

/// Read the attribute list at token `start`, if there is one: the token index after its `]` and
/// its tree as token indices.
fn read_inline(
    view: &SourceView,
    tokens: &[LexedToken],
    start: usize,
) -> Result<Option<(usize, Shape)>, NatDefinitionParseError> {
    let mut reader = AttributeReader {
        view,
        tokens,
        at: start,
    };
    if !reader.symbol("@[") {
        return Ok(None);
    }
    let shape = reader.attributes()?;
    Ok(Some((reader.at, shape)))
}

/// Where the declaration's attribute list, at token `start`, ends: the token index after its
/// `]`, or `start` when the declaration has none. Refuses an attribute this grammar does not
/// read, where it starts.
pub(crate) fn inline_end(
    view: &SourceView,
    tokens: &[LexedToken],
    start: usize,
) -> Result<usize, DefinitionParseError> {
    Ok(read_inline(view, tokens, start)?.map_or(start, |(end, _)| end))
}

/// The declaration's `declModifiers` attribute slot, from the original leaves: a null node
/// holding the `Term.attributes` node [`inline_end`] measured.
pub(crate) fn inline_syntax(
    view: &SourceView,
    leaves: &Leaves,
    tokens: &[LexedToken],
    start: usize,
) -> Result<Syntax, DefinitionParseError> {
    let Some((_, shape)) = read_inline(view, tokens, start)? else {
        return Ok(null_node(Vec::new()));
    };
    Ok(null_node(vec![build(&shape, leaves)?]))
}

pub fn parse(source: &[u8]) -> Result<Option<SimpAttribute>, DefinitionParseError> {
    let original = SourceText::from_utf8(source).map_err(NatDefinitionParseError::Source)?;
    let view = SourceView::of(&original);
    let tokens = tokens(&view)?;
    let is = |at: usize, text: &str| matches!(tokens.get(at).map(|t| &t.kind), Some(TokenKind::Symbol(s)) if s == text);
    if !is(0, "attribute") {
        return Ok(None);
    }
    let bad = |at: usize| NatDefinitionParseError::OutsideSeedGrammar {
        at: tokens.get(at).map_or(BytePos(source.len()), |t| {
            view.to_original(t.extent.start())
        }),
        expected: NatDefinitionExpectation::EndOfCommand,
    };
    if !is(1, "[") {
        return Err(bad(1));
    }
    let mut at = 2;
    let erase = is(at, "-");
    at += usize::from(erase);
    if !matches!(tokens.get(at).map(|t| &t.kind), Some(TokenKind::Ident(n)) if *n == Name::from_components(["simp"]))
    {
        return Err(bad(at));
    }
    at += 1;
    let reverse = is(at, "←") || is(at, "<-");
    if reverse && erase {
        return Err(bad(at));
    }
    at += usize::from(reverse);
    let mut priority = 1000;
    if matches!(
        tokens.get(at).map(|t| &t.kind),
        Some(TokenKind::Literal(LiteralKind::Nat))
    ) {
        if erase {
            return Err(bad(at));
        }
        let text = view
            .normalized()
            .span_str(tokens[at].extent)
            .ok_or_else(|| bad(at))?;
        if !text.bytes().all(|b| b.is_ascii_digit()) {
            return Err(bad(at));
        }
        priority = text.parse::<u32>().map_err(|_| bad(at))?;
        at += 1;
    }
    if !is(at, "]") {
        return Err(bad(at));
    }
    at += 1;
    let mut declarations = Vec::new();
    while at < tokens.len() {
        let TokenKind::Ident(name) = &tokens[at].kind else {
            return Err(bad(at));
        };
        declarations.push(name.clone());
        at += 1;
    }
    if declarations.is_empty() {
        return Err(bad(at));
    }
    Ok(Some(SimpAttribute {
        declarations,
        rule: (!erase).then_some((priority, reverse)),
    }))
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn inline_attributes_preserve_every_source_leaf_and_declaration_boundary() {
        let source = "/- 😀 -/ namespace N\r\n@[simp <- 700]\r\ntheorem flip (n : Nat) : n = n := by rfl\r\n@[simp] def wrap (n : Nat) := n\r\nend N\r\n";
        let commands = partition(source.as_bytes()).unwrap();
        assert_eq!(commands.len(), 4);
        let mut joined = Vec::new();
        for (offset, bytes) in &commands {
            assert_eq!(offset.0, joined.len());
            joined.extend_from_slice(bytes);
        }
        assert_eq!(joined, source.as_bytes());
        for (_, bytes) in &commands[1..3] {
            let parsed = parse_definition(bytes).unwrap();
            assert_eq!(parsed.reconstruct_original(), *bytes);
            let normalized = String::from_utf8_lossy(bytes).replace("\r\n", "\n");
            assert_eq!(
                parsed.reconstruct_normalized().unwrap(),
                normalized.as_bytes()
            );
        }
        for source in [
            "@[simp] theorem self.{u} {A : Sort u} (x : A) : x = x := by rfl",
            "@[simp /- phase -/ ← /- prio -/ 0] theorem self (x : Nat) : x = x := by rfl",
            "@[simp 4294967295] def «a.b» := 7",
        ] {
            let parsed = parse_definition(source.as_bytes()).unwrap();
            assert_eq!(parsed.reconstruct_normalized().unwrap(), source.as_bytes());
            assert!(parse_nat_definition(source.as_bytes()).is_err());
        }
    }

    #[test]
    fn unsupported_inline_attributes_never_disappear_from_the_command() {
        for source in [
            "@[«simp»] def x := 0",
            "@[simp][other] def x := 0",
            "@[simp] @[simp] def x := 0",
            "@[simp ← ←] def x := 0",
            "@[simp foo] def x := 0",
            "@[simp, ] def x := 0",
            "@[] def x := 0",
            "@[class] def x := 0",
            "@[ext (iff := false)] def x := 0",
            "@[simp]",
        ] {
            assert!(parse_definition(source.as_bytes()).is_err(), "{source}");
        }
        // Attributes the pin parses keep their place in `declModifiers`; the elaborator, not
        // the parser, refuses the ones it does not implement (`fln`'s source_default_simp).
        for source in [
            "@[simp] instance value : Inhabited Nat := Inhabited.mk 0",
            "@[simp] inductive T where | mk",
            "@[other] def x := 0",
            "@[simp, other] def x := 0",
            "@[simp 4294967296] def x := 0",
            "@[simp 0xff] def x := 0",
            "@[simp high] def x := 0",
            "@[local simp] def x := 0",
            "@[simp ↓] def x := 0",
        ] {
            let parsed = parse_definition(source.as_bytes())
                .unwrap_or_else(|error| panic!("{source}: {error:?}"));
            let Syntax::Node { args, .. } = parsed.syntax() else {
                panic!("a declaration node");
            };
            let Syntax::Node {
                args: modifiers, ..
            } = &args[0]
            else {
                panic!("declModifiers");
            };
            assert!(
                matches!(&modifiers[1], Syntax::Node { args, .. }
                    if matches!(args.as_slice(), [Syntax::Node { kind, .. }]
                        if kind == &parser_kind(&["Term", "attributes"]))),
                "{source}"
            );
            assert_eq!(parsed.reconstruct_normalized().unwrap(), source.as_bytes());
        }
        let source = b"def x := 0\n@[other]\ndef y := 1\n";
        let commands = partition(source).unwrap();
        assert_eq!(commands.len(), 2);
        let parsed = parse_definition(commands[1].1).unwrap();
        let Syntax::Node { args, .. } = parsed.syntax() else {
            panic!("a declaration node");
        };
        let Syntax::Node {
            args: modifiers, ..
        } = &args[0]
        else {
            panic!("declModifiers");
        };
        let Syntax::Node {
            args: attributes, ..
        } = &modifiers[1]
        else {
            panic!("the attribute slot");
        };
        assert_eq!(
            attributes.len(),
            1,
            "the attribute stays with its declaration"
        );

        // A modifier after the attribute is parsed into its own `declModifiers` slot
        // (`unsafe` is slot 5) rather than dropped; elaboration still refuses it.
        let parsed = parse_definition("@[simp] unsafe def x := 0".as_bytes()).unwrap();
        let Syntax::Node { args, .. } = parsed.syntax() else {
            panic!("a declaration node");
        };
        let Syntax::Node {
            args: modifiers, ..
        } = &args[0]
        else {
            panic!("declModifiers");
        };
        assert!(matches!(&modifiers[5], Syntax::Node { args, .. }
            if matches!(args.as_slice(), [Syntax::Node { kind, .. }]
                if kind == &parser_kind(&["Command", "unsafe"]))));
    }

    #[test]
    fn parses_priorities_erasure_and_structural_names() {
        let parsed = parse("/- note -/ attribute [simp ← 7] A.«b.c» d".as_bytes())
            .unwrap()
            .unwrap();
        assert_eq!(parsed.rule, Some((7, true)));
        assert_eq!(parsed.declarations[0], Name::from_components(["A", "b.c"]));
        assert_eq!(parse(b"attribute [-simp] x").unwrap().unwrap().rule, None);
        assert_eq!(
            parse(b"attribute [simp] x").unwrap().unwrap().rule,
            Some((1000, false))
        );
    }
    #[test]
    fn malformed_or_unsupported_commands_fail_closed() {
        for source in [
            "attribute",
            "attribute [simp]",
            "attribute [simp, foo] x",
            "attribute [unknown] x",
            "attribute [-simp 10] x",
            "attribute [simp 4294967296] x",
            "attribute [simp high] x",
            "attribute [simp] x in",
            "attribute [simp <- <-] x",
        ] {
            assert!(parse(source.as_bytes()).is_err(), "{source}");
        }
    }
    #[test]
    fn partition_keeps_commands_and_original_offsets() {
        let source = b"namespace A\r\ndef x := 3\r\nattribute [simp] x\r\ntheorem t : x = 3 := by simp\r\nattribute [-simp] x\r\nend A\r\n";
        let rows = partition(source).unwrap();
        assert_eq!(rows.len(), 6);
        let mut bytes = Vec::new();
        for (offset, row) in rows {
            assert_eq!(offset, BytePos(bytes.len()));
            bytes.extend_from_slice(row);
        }
        assert_eq!(bytes, source);
    }
}
