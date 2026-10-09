//! File-level scope commands. The ordinary declaration parser remains the only
//! declaration parser; this layer partitions original bytes without rewriting.
use super::*;
pub mod attributes;
pub mod imports;
pub mod instances;
pub mod modifiers;
pub mod mutual;
pub mod reducibility;
pub mod trees;
pub mod variables;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ScopeCommand {
    Namespace(Name),
    Section(Option<Name>),
    End(Option<Name>),
    Open(Vec<Name>),
    OpenScoped(Vec<Name>),
    Universe(Vec<Name>),
    Variable(Syntax),
    Include(Vec<Name>),
    Omit(Vec<Name>),
    Simp(attributes::SimpAttribute),
    Instance(instances::InstanceAttribute),
    Reducibility(reducibility::ReducibilityAttribute),
    /// `open A B in <command>` (`Lean.Parser.Command.in`): the pin's macro elaborates it as
    /// `section open A B <command> end`. `body` is the byte offset, within this command's own
    /// source, where the inner command starts.
    OpenIn {
        names: Vec<Name>,
        scoped: bool,
        body: usize,
    },
    /// `set_option <name> <value>` (`Lean.Parser.Command.«set_option»`): the option holds to the
    /// end of the enclosing `section` or `namespace`. `value` is the pin's `optionValue` (`true`,
    /// `false`, a string or a numeral) as read; whether it is admitted is the option table's
    /// decision, not the parser's.
    SetOption {
        name: Name,
        value: fln_core::options::DataValue,
    },
    /// `set_option <name> <value> in <command>`: the pin's `in` macro elaborates it as
    /// `section set_option <name> <value> <command> end`. `body` is as in [`ScopeCommand::OpenIn`].
    SetOptionIn {
        name: Name,
        value: fln_core::options::DataValue,
        body: usize,
    },
    Trivia,
}

/// The scope layer's table: the full implicit-Init table, the same one declaration bodies use.
/// Every scope keyword this layer recognises (`namespace`, `end`, `open`, `universe`, `scoped`,
/// `omit`, …) is a token at the pin, so nothing is added by hand; `prelude` is header-only and
/// lives in `imports`' header table.
fn table() -> &'static TokenTable {
    crate::reference_tokens::implicit_init_table()
}
fn tokens(view: &SourceView) -> Result<Vec<LexedToken>, DefinitionParseError> {
    let run = lex_run(view.normalized(), table());
    let diagnostics: Vec<_> = run
        .diagnostics()
        .into_iter()
        .map(|(message, at)| ParseDiagnostic {
            message,
            at: view.to_original(at),
        })
        .collect();
    if !diagnostics.is_empty() {
        return Err(NatDefinitionParseError::Lexical { diagnostics });
    }
    Ok(run
        .events
        .into_iter()
        .filter_map(|event| match event {
            Event::Token(token) => Some(token),
            _ => None,
        })
        .collect())
}
/// [`tokens`] for [`partition`], which goes past a refusal of one token: a symbol the table
/// does not have (a notation this table lacks, such as a scoped one) or a character literal with
/// no closing quote (`x#'lt` without the scoped `#'`). The pin's frontend reports such an error on
/// the command that holds it and goes on with the next command; here that command keeps its
/// bytes, so parsing it refuses it where the token starts. Every other refusal (an unterminated
/// comment, string or identifier escape, which runs on past the command) still refuses the whole
/// source.
fn partition_tokens(view: &SourceView) -> Result<Vec<LexedToken>, DefinitionParseError> {
    use fln_syntax::literal::LiteralError;
    use fln_syntax::run::RunError;
    use fln_syntax::token::TokenError;
    let run = lex_run(view.normalized(), table());
    let diagnostics: Vec<_> = run
        .events
        .iter()
        .filter_map(|event| match event {
            Event::Refused {
                error:
                    RunError::Token(
                        TokenError::NotAToken { .. }
                        | TokenError::Literal(LiteralError::MissingEndOfCharLiteral { .. }),
                    ),
                ..
            }
            | Event::Token(_)
            | Event::Trivia(_) => None,
            Event::Refused { error, .. } => Some(ParseDiagnostic {
                message: error.message(),
                at: view.to_original(error.at()),
            }),
        })
        .collect();
    if !diagnostics.is_empty() {
        return Err(NatDefinitionParseError::Lexical { diagnostics });
    }
    Ok(run
        .events
        .into_iter()
        .filter_map(|event| match event {
            Event::Token(token) => Some(token),
            _ => None,
        })
        .collect())
}
fn control(s: &str) -> bool {
    matches!(
        s,
        "namespace"
            | "section"
            | "end"
            | "open"
            | "universe"
            | "attribute"
            | "variable"
            | "include"
            | "omit"
            | "set_option"
    )
}
/// A command this grammar does not parse, at the head of a line where a declaration's body
/// cannot go on: it ends the declaration before it rather than becoming its tokens. (`set_option`
/// is a scope command, [`control`].)
fn line_command(s: &str) -> bool {
    !declaration(s)
        && !modifiers::is_modifier(s)
        && !matches!(s, "local" | "scoped")
        && (PIN_DOC_CARRIERS.contains(&s)
            || matches!(
                s,
                "grind_pattern" | "seal" | "unseal" | "export" | "init_grind_norm"
            ))
}
/// A doc comment: the lexer's one token for `/--` or `/-!` and its whole body.
fn doc_comment(token: &LexedToken) -> bool {
    matches!(&token.kind, TokenKind::Symbol(symbol) if symbol == "/--" || symbol == "/-!")
}

/// A declaration's doc comment whose reference-manual links the pin refuses. The pin attaches
/// the docstring through `addMarkdownDocString`, whose `validateDocComment` runs
/// `rewriteManualLinksCore` (vendored `src/Lean/DocString/Links.lean`) and reports every link it
/// cannot rewrite as an error. A module doc (`/-!`) is stored unvalidated. Out of line so its
/// temporaries stay out of `partition`'s frame (parsers run on small host stacks).
#[inline(never)]
fn unvalidated_manual_link(
    view: &SourceView,
    token: &LexedToken,
) -> Option<NatDefinitionParseError> {
    let TokenKind::Symbol(symbol) = &token.kind else {
        return None;
    };
    if symbol != "/--" {
        return None;
    }
    let text = view
        .normalized()
        .as_str()
        .get(token.extent.start().0..token.extent.end().0)?;
    // `getDocStringText`: the comment body after the opener's trailing whitespace, without `-/`.
    let body = text.get(3..)?.trim_start_matches([' ', '\n']);
    let docstring = body.strip_suffix("-/").unwrap_or(body);
    manual_link_refused(docstring).then(|| NatDefinitionParseError::OutsideSeedGrammar {
        at: view.to_original(token.extent.start()),
        expected: NatDefinitionExpectation::DocCommentWithoutManualLinks,
    })
}

/// Whether `rewriteManualLinksCore` reports an error on `docstring`, scanning exactly as it does:
/// at each `lean-manual://`, the URL runs over URL characters, and a URL character that ends the
/// string ends the URL without being part of it; the path must be `section/<id>` or
/// `errorExplanation/<name>`, one nonempty item after the kind.
fn manual_link_refused(docstring: &str) -> bool {
    const SCHEME: &str = "lean-manual://";
    let url_char = |c: char| {
        c.is_ascii_alphanumeric()
            || matches!(
                c,
                '-' | '.'
                    | '_'
                    | '~'
                    | ':'
                    | '/'
                    | '?'
                    | '#'
                    | '['
                    | ']'
                    | '@'
                    | '!'
                    | '$'
                    | '&'
                    | '\''
                    | '*'
                    | '+'
                    | ','
                    | ';'
                    | '='
            )
    };
    let mut at = 0;
    while let Some(found) = docstring[at..].find(SCHEME) {
        let start = at + found + SCHEME.len();
        let rest = &docstring[start..];
        let mut chars = rest.char_indices().peekable();
        let mut path_end = None;
        while let Some((offset, c)) = chars.next() {
            if url_char(c) && chars.peek().is_some() {
                continue;
            }
            path_end = Some(offset);
            break;
        }
        // At the very end of the string there is no character to end the URL: no rewrite and
        // no error.
        let Some(path_end) = path_end else {
            return false;
        };
        let path = &rest[..path_end];
        let mut parts = path.split('/');
        let kind = parts.next().unwrap_or("");
        let args: Vec<&str> = parts.collect();
        let valid = matches!(kind, "section" | "errorExplanation")
            && matches!(args.as_slice(), [item] if !item.is_empty());
        if !valid {
            return true;
        }
        at = start + path_end;
    }
    false
}

/// Refuses the doc comment at `tokens[index]` unless it is a module doc (a command of its own) or
/// leads what can carry it: a declaration this grammar parses, or a command only the pin parses
/// (`syntax`, `macro`, `add_decl_doc`, ...), with which the doc stays, so that one command is
/// refused where it is parsed rather than the whole file here. A declaration's doc must not need
/// manual-link validation, and the pin refuses `/-- d -/ #eval e` at the `#eval` and a doc at
/// end of input. Out of line, with the refusals built here, so they occupy nothing of
/// `partition`'s frame.
#[inline(never)]
fn doc_comment_is_carried(
    view: &SourceView,
    tokens: &[LexedToken],
    index: usize,
    source_len: usize,
) -> Result<(), NatDefinitionParseError> {
    let token = &tokens[index];
    if let Some(refusal) = unvalidated_manual_link(view, token) {
        return Err(refusal);
    }
    if !matches!(&token.kind, TokenKind::Symbol(symbol) if symbol == "/--") {
        return Ok(());
    }
    let next = tokens.get(index + 1);
    if next.is_some_and(|next| {
        carries_doc_comment(next)
            || matches!(&next.kind, TokenKind::Symbol(symbol)
                if PIN_DOC_CARRIERS.contains(&symbol.as_str()))
    }) {
        return Ok(());
    }
    Err(NatDefinitionParseError::OutsideSeedGrammar {
        at: next.map_or(BytePos(source_len), |next| {
            view.to_original(next.extent.start())
        }),
        expected: NatDefinitionExpectation::DefinitionKeyword,
    })
}

/// Every command keyword the pin accepts after a declaration's doc comment, as its parser lists
/// them when the doc is followed by anything else (measured 2026-10-07), with the attribute kinds
/// `scoped` and `local` that lead `syntax`, `notation` and `macro`.
const PIN_DOC_CARRIERS: &[&str] = &[
    "#guard_msgs",
    "abbrev",
    "add_decl_doc",
    "axiom",
    "binder_predicate",
    "builtin_cbv_simproc",
    "builtin_cbv_simproc_decl",
    "builtin_dsimproc",
    "builtin_dsimproc_decl",
    "builtin_grind_propagator",
    "builtin_initialize",
    "builtin_simproc",
    "builtin_simproc_decl",
    "cbv_simproc",
    "cbv_simproc_decl",
    "class",
    "coinductive",
    "declare_simp_like_tactic",
    "declare_syntax_cat",
    "def",
    "dsimproc",
    "dsimproc_decl",
    "elab",
    "elab_rules",
    "example",
    "grind_propagator",
    "inductive",
    "infix",
    "infixl",
    "infixr",
    "initialize",
    "instance",
    "local",
    "macro",
    "macro_rules",
    "notation",
    "opaque",
    "postfix",
    "prefix",
    "recommended_spelling",
    "register_error_explanation",
    "register_tactic_tag",
    "register_try?_tactic",
    "scoped",
    "simproc",
    "simproc_decl",
    "structure",
    "syntax",
    "tactic_extension",
    "theorem",
    "unif_hint",
];

/// Whether `token` can follow a declaration's doc comment: the declaration keywords and the
/// rest of `declModifiers` (attributes, then the modifiers), whose first slot the doc fills.
/// Whether a symbol opens (`Some(true)`) or closes (`Some(false)`) a bracket, for the
/// partition's nesting depth. The pin's tokens put brackets inside longer symbols: `#[`, `%[`,
/// `.(`, `-[`, `` `(tactic| ``, `wp⟦` open, and `]'` (`xs[i]'h`, `Init/GetElem.lean`) and
/// `+1]` close, so a symbol is read by the brackets it contains.
fn bracket(symbol: &str) -> Option<bool> {
    const OPEN: &[char] = &['(', '[', '{', '⟨', '⟦', '⦃'];
    const CLOSE: &[char] = &[')', ']', '}', '⟩', '⟧', '⦄'];
    match (symbol.contains(OPEN), symbol.contains(CLOSE)) {
        (true, false) => Some(true),
        (false, true) => Some(false),
        _ => None,
    }
}

fn carries_doc_comment(token: &LexedToken) -> bool {
    matches!(&token.kind, TokenKind::Symbol(symbol)
    if modifiers::is_modifier(symbol)
        || matches!(
            symbol.as_str(),
            "def" | "theorem" | "abbrev" | "opaque" | "axiom" | "example" | "instance"
                | "structure" | "class" | "inductive" | "@["
        ))
}

fn declaration(s: &str) -> bool {
    matches!(
        s,
        "def"
            | "theorem"
            | "example"
            | "instance"
            | "structure"
            | "class"
            | "inductive"
            | "#check"
            | "#eval"
    )
}

/// Recognize complete scope commands, including comments and escaped identifiers.
/// `open A in <command>` is recognized with its body; selective opens (`open A (x)`,
/// `hiding`, `renaming`) are never ignored.
pub fn parse(source: &[u8]) -> Result<Option<ScopeCommand>, DefinitionParseError> {
    let original = SourceText::from_utf8(source).map_err(NatDefinitionParseError::Source)?;
    let view = SourceView::of(&original);
    let tokens = tokens(&view)?;
    let Some(first) = tokens.first() else {
        return Ok(Some(ScopeCommand::Trivia));
    };
    // A module doc, or a declaration's doc comment that `partition` split off after checking
    // what follows it, changes no environment and prints nothing.
    if tokens.len() == 1 && doc_comment(first) {
        if let Some(refusal) = unvalidated_manual_link(&view, first) {
            return Err(refusal);
        }
        return Ok(Some(ScopeCommand::Trivia));
    }
    let TokenKind::Symbol(keyword) = &first.kind else {
        return Ok(None);
    };
    if keyword == "variable" {
        return variables::parse(&view, &tokens).map(|syntax| Some(ScopeCommand::Variable(syntax)));
    }
    if keyword == "attribute" {
        if let Some(attribute) = instances::parse(&view, &tokens)? {
            return Ok(Some(ScopeCommand::Instance(attribute)));
        }
        if let Some(attribute) = reducibility::parse(&view, &tokens)? {
            return Ok(Some(ScopeCommand::Reducibility(attribute)));
        }
        return attributes::parse(source).map(|attribute| attribute.map(ScopeCommand::Simp));
    }
    if keyword == "set_option" {
        return set_option(&view, &tokens, source.len()).map(Some);
    }
    if !control(keyword) {
        return Ok(None);
    }
    let bad = |index: usize| NatDefinitionParseError::OutsideSeedGrammar {
        at: tokens.get(index).map_or(BytePos(source.len()), |t| {
            view.to_original(t.extent.start())
        }),
        expected: NatDefinitionExpectation::EndOfCommand,
    };
    let scoped = keyword == "open"
        && tokens.get(1).is_some_and(
            |token| matches!(&token.kind, TokenKind::Symbol(symbol) if symbol == "scoped"),
        );
    let mut names = Vec::new();
    for (index, token) in tokens.iter().enumerate().skip(if scoped { 2 } else { 1 }) {
        let TokenKind::Ident(name) = &token.kind else {
            // `open A B in <command>`: everything after `in` is one more command.
            if keyword == "open"
                && !names.is_empty()
                && matches!(&token.kind, TokenKind::Symbol(symbol) if symbol == "in")
            {
                let Some(body) = tokens.get(index + 1) else {
                    return Err(bad(index + 1));
                };
                return Ok(Some(ScopeCommand::OpenIn {
                    names,
                    scoped,
                    body: view.to_original(body.extent.start()).0,
                }));
            }
            return Err(bad(index));
        };
        names.push(name.clone());
    }
    let command = match keyword.as_str() {
        "namespace" if names.len() == 1 => ScopeCommand::Namespace(names.remove(0)),
        "section" if names.len() <= 1 => ScopeCommand::Section(names.pop()),
        "end" if names.len() <= 1 => ScopeCommand::End(names.pop()),
        "open" if !names.is_empty() && scoped => ScopeCommand::OpenScoped(names),
        "open" if !names.is_empty() => ScopeCommand::Open(names),
        "include" if !names.is_empty() => ScopeCommand::Include(names),
        "omit" if !names.is_empty() => ScopeCommand::Omit(names),
        "universe" if !names.is_empty() && names.iter().all(|n| n.parent().is_anonymous()) => {
            ScopeCommand::Universe(names)
        }
        _ => return Err(bad(1)),
    };
    Ok(Some(command))
}

/// `set_option`'s operands, as the pin's `«set_option»` reads them: an identifier, then
/// `optionValue` (`nonReservedSymbol "true" <|> nonReservedSymbol "false" <|> strLit <|> numLit`,
/// vendored `src/Lean/Parser/Command.lean`), then the end of the command or `in` and one more
/// command. A numeral is read in its own radix and refused past `u64`, the width of the
/// `DataValue` it becomes. A string is read only without escapes or gaps, so nothing here decodes
/// one differently from the pin; one with a backslash is refused.
fn set_option(
    view: &SourceView,
    tokens: &[LexedToken],
    source_len: usize,
) -> Result<ScopeCommand, DefinitionParseError> {
    use fln_core::options::DataValue;
    let bad = |index: usize| NatDefinitionParseError::OutsideSeedGrammar {
        at: tokens
            .get(index)
            .map_or(BytePos(source_len), |t| view.to_original(t.extent.start())),
        expected: NatDefinitionExpectation::EndOfCommand,
    };
    let Some(TokenKind::Ident(name)) = tokens.get(1).map(|token| &token.kind) else {
        return Err(bad(1));
    };
    let Some(operand) = tokens.get(2) else {
        return Err(bad(2));
    };
    let text = view
        .normalized()
        .as_str()
        .get(operand.extent.start().0..operand.extent.end().0)
        .ok_or_else(|| bad(2))?;
    let value = match &operand.kind {
        TokenKind::Ident(word) if *word == Name::from_components(["true"]) => {
            DataValue::OfBool(true)
        }
        TokenKind::Ident(word) if *word == Name::from_components(["false"]) => {
            DataValue::OfBool(false)
        }
        TokenKind::Literal(LiteralKind::Nat) => {
            let (digits, radix) = match text.get(..2) {
                Some("0x" | "0X") => (&text[2..], 16),
                Some("0b" | "0B") => (&text[2..], 2),
                Some("0o" | "0O") => (&text[2..], 8),
                _ => (text, 10),
            };
            DataValue::OfNat(u64::from_str_radix(digits, radix).map_err(|_| bad(2))?)
        }
        TokenKind::Literal(LiteralKind::Str) => {
            let inner = text
                .strip_prefix('"')
                .and_then(|rest| rest.strip_suffix('"'))
                .filter(|inner| !inner.contains('\\'))
                .ok_or_else(|| bad(2))?;
            DataValue::OfString(inner.to_owned())
        }
        _ => return Err(bad(2)),
    };
    match tokens.get(3) {
        None => Ok(ScopeCommand::SetOption {
            name: name.clone(),
            value,
        }),
        Some(token) if matches!(&token.kind, TokenKind::Symbol(symbol) if symbol == "in") => {
            let body = tokens.get(4).ok_or_else(|| bad(4))?;
            Ok(ScopeCommand::SetOptionIn {
                name: name.clone(),
                value,
                body: view.to_original(body.extent.start()).0,
            })
        }
        Some(_) => Err(bad(3)),
    }
}

/// Partition both scope commands and declarations, preserving every source byte.
/// Delimiters protect nested terms and explicit universe argument lists; comments
/// and strings are lexer events, not text searched for command-looking words.
/// Scope directives must start a source line. Within a declaration they must
/// also leave its layout block; `end` is still a valid local name in a proof.
/// A token the table lacks ends only the command holding it ([`partition_tokens`]).
pub fn partition(source: &[u8]) -> Result<Vec<(BytePos, &[u8])>, DefinitionParseError> {
    let original = SourceText::from_utf8(source).map_err(NatDefinitionParseError::Source)?;
    let view = SourceView::of(&original);
    let tokens = partition_tokens(&view)?;
    let mut starts = Vec::new();
    let mut depth = 0_usize;
    let source_view = view.normalized();
    let column = |token: &LexedToken| {
        let start = token.extent.start();
        start.0
            - source_view
                .line_start(source_view.line_of(start))
                .expect("token line")
                .0
    };
    let mut declaration_column = None;
    let mut attribute_prefix = false;
    // The column of the attribute or modifier that opened the current declaration, so its
    // body's layout block is measured from the command's first token, not its keyword.
    let mut prefix_column = None;
    // `open A in <command>` is one command: after an `open`'s `in`, the next command that
    // starts belongs to it. `set_option o v in <command>` is the same `in`.
    let mut current_open = false;
    let mut open_in = false;
    let mut mutual_until = 0;
    for (index, token) in tokens.iter().enumerate() {
        if index < mutual_until {
            continue;
        }
        if let TokenKind::Symbol(symbol) = &token.kind {
            if depth == 0 && symbol == "mutual" {
                // A mutual group is one admission unit. In particular its end
                // cannot close the surrounding namespace or section, and no
                // member may be published before the entire group is checked.
                if !open_in {
                    starts.push(view.to_original(token.extent.start()).0);
                }
                open_in = false;
                current_open = false;
                mutual_until = mutual::block_end(&view, &tokens, index)? + 1;
                declaration_column = None;
                attribute_prefix = false;
                continue;
            }
            let command_line = (index == 0
                || source_view.line_of(token.extent.start())
                    > source_view.line_of(tokens[index - 1].extent.end()))
                && declaration_column.is_none_or(|base| column(token) <= base);
            // A module doc (`moduleDoc`) is its own command. A declaration's doc comment
            // (`declModifiers`' first slot) leads its declaration's command, as an attribute
            // does, and only before what can carry it, as at the pin, which refuses
            // `/-- d -/ #eval e` at the `#eval`.
            if depth == 0 && command_line && !open_in && doc_comment(token) {
                doc_comment_is_carried(&view, &tokens, index, source.len())?;
                starts.push(view.to_original(token.extent.start()).0);
                current_open = false;
                declaration_column = None;
                attribute_prefix = false;
                prefix_column = None;
                // The command after a declaration's doc continues the doc's command, whether
                // this grammar parses it or not.
                if symbol == "/--" {
                    attribute_prefix = true;
                    prefix_column = Some(column(token));
                }
                continue;
            }
            let scope_start = (control(symbol) || line_command(symbol)) && command_line;
            // Attributes and declaration modifiers (`private`, `protected`, `noncomputable`,
            // …) precede the declaration keyword in one command (`declModifiers`).
            // `local` and `scoped` (`attrKind`) lead `instance`, `notation`, `syntax`, … the same way.
            let prefix = symbol == "@["
                || modifiers::is_modifier(symbol)
                || (command_line || attribute_prefix) && (symbol == "local" || symbol == "scoped");
            let inline_start = prefix && command_line;
            // `class inductive` and `class abbrev` are one declaration keyword at the pin.
            let after_class = index > 0
                && matches!(&tokens[index - 1].kind, TokenKind::Symbol(previous) if previous == "class");
            // A command keyword after the prefix is its command's (`@[inherit_doc f]` then
            // `infixr:100 …` on the next line).
            let continues_prefix = (attribute_prefix
                && (declaration(symbol) || prefix || line_command(symbol)))
                || (after_class && declaration(symbol));
            if depth == 0 && current_open && symbol == "in" {
                open_in = true;
                current_open = false;
                continue;
            }
            if depth == 0
                && (scope_start || declaration(symbol) || inline_start || continues_prefix)
            {
                if !continues_prefix {
                    if !open_in {
                        starts.push(view.to_original(token.extent.start()).0);
                    }
                    open_in = false;
                    current_open = scope_start && (symbol == "open" || symbol == "set_option");
                    prefix_column = inline_start.then(|| column(token));
                }
                attribute_prefix = inline_start
                    || (continues_prefix && !declaration(symbol) && !line_command(symbol));
                declaration_column = declaration(symbol)
                    .then(|| prefix_column.map_or(column(token), |base| base.min(column(token))));
            } else if depth == 0 && attribute_prefix {
                // Any other keyword ends the prefix: it carries the prefix (`abbrev`, `opaque`,
                // `axiom`, …) and belongs to its command, and the next declaration starts anew.
                attribute_prefix = false;
            }
            match bracket(symbol) {
                Some(true) => depth = depth.saturating_add(1),
                Some(false) => depth = depth.saturating_sub(1),
                None => {}
            }
        }
    }
    let mut output = Vec::new();
    let mut start = 0;
    for next in starts.into_iter().skip(1) {
        output.push((BytePos(start), &source[start..next]));
        start = next;
    }
    output.push((BytePos(start), &source[start..]));
    Ok(output)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn scoped_openings_preserve_structural_names_without_becoming_name_opens() {
        let source = "-- 😀\r\nopen scoped A.«B.C» D";
        assert_eq!(
            parse(source.as_bytes()).unwrap(),
            Some(ScopeCommand::OpenScoped(vec![
                Name::from_components(["A", "B.C"]),
                Name::from_components(["D"]),
            ]))
        );
        assert_eq!(
            parse(b"open A").unwrap(),
            Some(ScopeCommand::Open(vec![Name::from_components(["A"])]))
        );
        for source in [
            "open scoped",
            "open scoped A hiding x",
            "open scoped A in",
            "open scoped A, B",
            "open scoped 4",
        ] {
            assert!(parse(source.as_bytes()).is_err(), "{source}");
        }
    }

    /// The pin's command boundaries (`Lines.lean`, dumped at the pin): a line-start command this
    /// grammar cannot parse ends the declaration before it, `set_option … in` leads the next
    /// command, and attributes and `noncomputable scoped`/`local` lead theirs.
    #[test]
    fn line_start_commands_end_the_declaration_before_them() {
        let source = "theorem a : True := by\n  trivial\n\ngrind_pattern Nat.add_zero => n + 0\n\
                      set_option pp.all true in\ntheorem b : True := trivial\n\
                      @[inherit_doc f]\ninfixr:100 \" <&&> \" => Nat.add\n\
                      noncomputable scoped instance i : Inhabited Nat := ⟨0⟩\n\
                      local notation \"xx\" => 1\n";
        let commands = partition(source.as_bytes()).unwrap();
        let heads: Vec<_> = commands
            .iter()
            .map(|(_, bytes)| std::str::from_utf8(bytes).unwrap().lines().next().unwrap())
            .collect();
        assert_eq!(
            heads,
            [
                "theorem a : True := by",
                "grind_pattern Nat.add_zero => n + 0",
                "set_option pp.all true in",
                "@[inherit_doc f]",
                "noncomputable scoped instance i : Inhabited Nat := ⟨0⟩",
                "local notation \"xx\" => 1",
            ]
        );
    }

    #[test]
    fn scopes_preserve_structural_names_and_original_offsets() {
        let source = b"-- namespace Fake\r\nnamespace Real\r\n-- end Real\r\ndef x := \"end Real\"\r\nsection\r\nuniverse u v\r\nend\r\nend Real\r\n";
        let commands = partition(source).unwrap();
        assert_eq!(commands.len(), 6);
        let mut joined = Vec::new();
        for (offset, bytes) in &commands {
            assert_eq!(*offset, BytePos(joined.len()));
            joined.extend_from_slice(bytes);
        }
        assert_eq!(joined, source);
        assert_eq!(
            parse(commands[0].1).unwrap(),
            Some(ScopeCommand::Namespace(Name::from_components(["Real"])))
        );
        assert_eq!(
            parse("namespace «A.B»".as_bytes()).unwrap(),
            Some(ScopeCommand::Namespace(Name::from_components(["A.B"])))
        );
        assert_eq!(
            parse(b"section").unwrap(),
            Some(ScopeCommand::Section(None))
        );
        assert_eq!(
            parse(b"/- only trivia -/").unwrap(),
            Some(ScopeCommand::Trivia)
        );
    }
    #[test]
    fn malformed_scope_commands_are_not_partially_accepted() {
        for source in [
            "namespace",
            "namespace A B",
            "end A B",
            "section A B",
            "open",
            "open A (x)",
            "open A in",
            "open scoped",
            "open scoped A in",
            "open A hiding x",
            "open A renaming x -> y",
            "universe A.u",
            "universe u, v",
            "end := 3",
        ] {
            assert!(parse(source.as_bytes()).is_err(), "{source}");
        }
        assert_eq!(parse(b"def value := 3").unwrap(), None);
    }
    /// `open A in <command>` (`Lean.Parser.Command.in`) is one command whose body is the next
    /// command; the pin's macro elaborates it as `section open A <command> end`.
    #[test]
    fn open_in_is_one_command_with_its_body() {
        let source = "open A B in\ndef x := 1";
        assert_eq!(
            parse(source.as_bytes()).unwrap(),
            Some(ScopeCommand::OpenIn {
                names: vec![Name::from_components(["A"]), Name::from_components(["B"])],
                scoped: false,
                body: source.find("def").unwrap(),
            })
        );
        let source = "open scoped A in def x := 1";
        assert!(matches!(
            parse(source.as_bytes()).unwrap(),
            Some(ScopeCommand::OpenIn { scoped: true, body, .. }) if body == source.find("def").unwrap()
        ));

        // The body belongs to the open; the command after it does not.
        let file = "namespace N\nopen A in\ndef x := 1\ndef y := 2\nend N";
        let commands = partition(file.as_bytes()).unwrap();
        let texts: Vec<_> = commands
            .iter()
            .map(|(_, bytes)| std::str::from_utf8(bytes).unwrap())
            .collect();
        assert_eq!(
            texts,
            [
                "namespace N\n",
                "open A in\ndef x := 1\n",
                "def y := 2\n",
                "end N"
            ]
        );

        // Nested opens are one command; each level's body is the rest.
        let file = "open A in\nopen B in\ndef x := 1\ndef y := 2";
        let commands = partition(file.as_bytes()).unwrap();
        assert_eq!(commands.len(), 2);
        let Some(ScopeCommand::OpenIn { body, .. }) = parse(commands[0].1).unwrap() else {
            panic!("open-in");
        };
        let inner = &commands[0].1[body..];
        assert!(matches!(
            parse(inner).unwrap(),
            Some(ScopeCommand::OpenIn { body, .. }) if parse_definition(&inner[body..]).is_ok()
        ));

        // An `in` inside a later declaration does not reach back to an earlier open.
        let file = "open A\ndef f := Id.run do\n  for x in [1] do pure ()\n  pure 0\ndef g := 1";
        assert_eq!(partition(file.as_bytes()).unwrap().len(), 3);
    }

    #[test]
    fn set_option_reads_the_pins_option_values_and_its_in_form() {
        use fln_core::options::DataValue;
        let option = |source: &str| match parse(source.as_bytes()).unwrap() {
            Some(ScopeCommand::SetOption { name, value }) => (name.to_display_string(), value),
            other => panic!("{source}: {other:?}"),
        };
        assert_eq!(
            option("set_option linter.unusedVariables false"),
            ("linter.unusedVariables".into(), DataValue::OfBool(false))
        );
        assert_eq!(
            option("set_option autoLift true"),
            ("autoLift".into(), DataValue::OfBool(true))
        );
        assert_eq!(
            option("set_option maxHeartbeats 400000 -- more"),
            ("maxHeartbeats".into(), DataValue::OfNat(400_000))
        );
        assert_eq!(option("set_option o 0x10").1, DataValue::OfNat(16));
        assert_eq!(option("set_option o 0b101").1, DataValue::OfNat(5));
        assert_eq!(
            option("set_option o \"text\"").1,
            DataValue::OfString("text".into())
        );

        let source = "set_option pp.all true in\n#check 1";
        assert_eq!(
            parse(source.as_bytes()).unwrap(),
            Some(ScopeCommand::SetOptionIn {
                name: Name::from_components(["pp", "all"]),
                value: DataValue::OfBool(true),
                body: source.find("#check").unwrap(),
            })
        );
        // The body belongs to the option; the command after it does not.
        let file =
            "set_option autoLift false in\ndef x := 1\ndef y := 2\nset_option autoLift true\n";
        let texts: Vec<_> = partition(file.as_bytes())
            .unwrap()
            .into_iter()
            .map(|(_, bytes)| std::str::from_utf8(bytes).unwrap())
            .collect();
        assert_eq!(
            texts,
            [
                "set_option autoLift false in\ndef x := 1\n",
                "def y := 2\n",
                "set_option autoLift true\n"
            ]
        );

        // Not the pin's `optionValue`, a value past `u64`, a string with an escape, no value,
        // trailing tokens, and `in` without a command: each refused, none ignored.
        for source in [
            "set_option",
            "set_option o",
            "set_option o maybe",
            "set_option o 1.5",
            "set_option o 18446744073709551616",
            "set_option o \"a\\nb\"",
            "set_option o true false",
            "set_option o true in",
            "set_option 3 true",
        ] {
            assert!(parse(source.as_bytes()).is_err(), "{source}");
        }
    }

    #[test]
    fn universe_commas_and_escaped_command_names_are_not_command_boundaries() {
        let commands = partition(
            "namespace A\ndef «end».{u,v} (x : Sort u) : Sort u := x\ndef q := f.{1,2} Nat\nend A"
                .as_bytes(),
        )
        .unwrap();
        assert_eq!(commands.len(), 4);
        assert!(parse_definition(commands[1].1).is_ok());
    }
    #[test]
    fn scope_words_inside_branch_binders_and_indented_terms_stay_in_the_declaration() {
        // Each bare scope word is a keyword, so the pinned Reference refuses the declaration;
        // escaped, each is an ordinary name and the Reference accepts it. Captured with the pin
        // (v4.32.0, 2026-10-05) on `namespace Example\n<declaration>\nend Example`:
        //   1. `let end := 7` -> 5:16 unexpected token 'end'; expected '(', ':=', '|' or term
        //   2. `Nat.succ end =>` -> 2:69 unexpected token 'end'; expected '=>'
        //   3. `(end : Nat)` -> 2:12 unexpected token 'end'; expected '_' or identifier
        //   4. `(namespace …` -> 2:12 unexpected token 'namespace'; expected '_' or identifier
        //   5. `«open» universe :` -> 2:40 unexpected token 'universe'; expected ')'
        //   6-9. the same with every word escaped: accepted.
        // Wherever the declaration is refused, the scope words inside it still never split it.
        for (source, accepted) in [
            (
                "def choose (x : Bool) : Nat := by\n  cases x with\n  | false => exact 0\n  | true => let end := 7; exact end",
                false,
            ),
            (
                "def choose (x : Nat) : Nat := match x with | Nat.zero => 0 | Nat.succ end => end",
                false,
            ),
            ("def choose (end : Nat) : Nat :=\n  end", false),
            (
                "def choose (namespace section open universe : Nat) : Nat := open",
                false,
            ),
            (
                "def choose («namespace» «section» «open» universe : Nat) : Nat := «open»",
                false,
            ),
            (
                "def choose (x : Bool) : Nat := by\n  cases x with\n  | false => exact 0\n  | true => let «end» := 7; exact «end»",
                true,
            ),
            (
                "def choose (x : Nat) : Nat := match x with | Nat.zero => 0 | Nat.succ «end» => «end»",
                true,
            ),
            ("def choose («end» : Nat) : Nat :=\n  «end»", true),
            (
                "def choose («namespace» «section» «open» «universe» : Nat) : Nat := «open»",
                true,
            ),
        ] {
            let file = format!("namespace Example\n{source}\nend Example");
            let commands = partition(file.as_bytes()).unwrap();
            assert_eq!(commands.len(), 3, "{file}");
            assert_eq!(parse_definition(commands[1].1).is_ok(), accepted, "{file}");
            assert_eq!(
                parse(commands[2].1).unwrap(),
                Some(ScopeCommand::End(Some(Name::from_components(["Example"]))))
            );
        }
        let source = include_bytes!("../../../examples/native_index_refinement.lean");
        let commands = partition(source).unwrap();
        assert_eq!(
            commands.len(),
            partition_definition_commands(source).unwrap().len()
        );
        for (_, command) in commands {
            assert!(
                parse_definition(command).is_ok(),
                "{}",
                String::from_utf8_lossy(command)
            );
        }
    }

    /// The pin's tokens carry brackets inside longer symbols (`]'` in `xs[i]'h`, `#[`, `⟦`).
    /// The partition's nesting depth reads them, so the next command starts where the pin
    /// starts it instead of inside the previous one.
    #[test]
    fn brackets_inside_longer_symbols_keep_the_nesting_depth() {
        for source in [
            "theorem a (xs : Array Nat) (i : Nat) (h : i < xs.size) : xs[i]'h = xs[i]'h := rfl\ntheorem b : 1 = 1 := rfl\n",
            "def a : Array Nat := #[1, 2]\ndef b : Nat := 1\n",
        ] {
            assert_eq!(partition(source.as_bytes()).unwrap().len(), 2, "{source}");
        }
        assert_eq!(bracket("]'"), Some(false));
        assert_eq!(bracket("#["), Some(true));
        assert_eq!(bracket("`(tactic|"), Some(true));
        assert_eq!(bracket("+1]"), Some(false));
        assert_eq!(bracket("=>"), None);
    }

    /// `class inductive` is one declaration (`Init/Prelude.lean`'s `Nonempty`): its constructors'
    /// docs belong to it, and the next declaration starts a command of its own.
    #[test]
    fn class_inductive_is_one_command() {
        let source = "/-- d -/\nclass inductive Nonempty (α : Sort u) : Prop where\n  /-- c -/\n  | intro (val : α) : Nonempty α\n\ndef x : Nat := 1\n";
        let commands = partition(source.as_bytes()).unwrap();
        assert_eq!(commands.len(), 2, "{commands:?}");
        assert!(commands[1].1.starts_with(b"def x"));
    }

    /// A module doc is a command of its own wherever a command may start; a declaration's doc
    /// leads its declaration's command, and only before what can carry it, the way the pin
    /// refuses `/-- d -/ #eval e`.
    #[test]
    fn doc_comments_lead_their_declarations_and_must_be_carried() {
        let source = "/-! A module doc with `code`; it's prose. -/\n/-- The answer. -/\ndef answer : Nat := 42\n/-- Inline. -/ private def other : Nat := 1\n#eval answer\n";
        let commands = partition(source.as_bytes()).unwrap();
        let texts: Vec<_> = commands
            .iter()
            .map(|(_, command)| std::str::from_utf8(command).unwrap().trim_end())
            .collect();
        assert_eq!(
            texts,
            [
                "/-! A module doc with `code`; it's prose. -/",
                "/-- The answer. -/\ndef answer : Nat := 42",
                "/-- Inline. -/ private def other : Nat := 1",
                "#eval answer",
            ]
        );
        assert_eq!(
            parse(texts[0].as_bytes()).unwrap(),
            Some(ScopeCommand::Trivia)
        );
        // A declaration's doc is the first slot of its `declModifiers`, as at the pin.
        for declaration in [texts[1], texts[2]] {
            assert_eq!(
                parse(declaration.as_bytes()).unwrap(),
                None,
                "{declaration}"
            );
            let parsed = crate::parse_source_command(declaration.as_bytes())
                .unwrap_or_else(|error| panic!("{declaration}: {error:?}"));
            let Syntax::Node { args, .. } = parsed.syntax() else {
                panic!("a declaration");
            };
            let Syntax::Node {
                args: modifiers, ..
            } = &args[0]
            else {
                panic!("declModifiers");
            };
            assert!(
                matches!(&modifiers[0], Syntax::Node { args, .. }
                    if matches!(args.as_slice(), [Syntax::Node { kind, .. }]
                        if kind == &parser_kind(&["Command", "docComment"]))),
                "{declaration}"
            );
        }
        for bad in [
            "/-- d -/\n#eval 1\n",
            "def x : Nat := 1\n/-- dangling -/\n",
            "/-- d -/\n/-- e -/\ndef x : Nat := 1\n",
        ] {
            assert!(partition(bad.as_bytes()).is_err(), "{bad}");
        }
        // A command the pin lets a doc lead and this grammar does not parse keeps its doc: the
        // file partitions, and that one command is refused where it is parsed.
        let unparsed = "/-- d -/\nscoped syntax \"x\" : term\ndef y : Nat := 1\n";
        let commands = partition(unparsed.as_bytes()).unwrap();
        assert_eq!(commands.len(), 2, "{commands:?}");
        assert!(
            std::str::from_utf8(commands[0].1)
                .unwrap()
                .starts_with("/-- d -/\nscoped syntax")
        );
        assert!(!matches!(
            parse(commands[0].1),
            Ok(Some(ScopeCommand::Trivia))
        ));
        assert!(crate::parse_source_command(commands[0].1).is_err());
        // The pin validates a declaration doc's manual links ("Unknown documentation type `f`")
        // and stores a module doc's unvalidated; both verdicts measured 2026-10-07.
        let linked = "/-- see [](lean-manual://f) -/\ndef x := 44\n";
        assert!(matches!(
            partition(linked.as_bytes()),
            Err(NatDefinitionParseError::OutsideSeedGrammar {
                at: BytePos(0),
                expected: NatDefinitionExpectation::DocCommentWithoutManualLinks,
            })
        ));
        assert!(parse(b"/-- see [](lean-manual://f) -/").is_err());
        // The links the pin rewrites pass, and the ones it reports refuse ("Expected one item
        // after `section`", "Empty section ID"); all four verdicts measured 2026-10-08.
        assert!(
            partition(
                b"/-- [s](lean-manual://section/foo) [e](lean-manual://errorExplanation/lean.x) -/\ndef x := 44\n"
            )
            .is_ok()
        );
        for bad in ["section/a/b", "section/", "f"] {
            assert!(
                manual_link_refused(&format!("see [s](lean-manual://{bad}) ")),
                "{bad}"
            );
        }
        // A link that reaches the end of the docstring has no character to end it: no error.
        assert!(!manual_link_refused("trailing lean-manual://"));
        let module = partition(b"/-! see [](lean-manual://f) -/\ndef x := 44\n").unwrap();
        assert_eq!(parse(module[0].1).unwrap(), Some(ScopeCommand::Trivia));
    }

    #[test]
    fn a_token_the_table_lacks_refuses_its_own_command_and_no_other() {
        // `#'` is BitVec's scoped notation and `✓` no table's: each command holding one is kept
        // whole and refused where it is parsed; the commands around it partition as before.
        for bad in ["theorem t : x#'lt = 1 := rfl", "def ok : Nat := ✓"] {
            let source = format!("def a : Nat := 1\n{bad}\ndef b : Nat := 2\n");
            let commands = partition(source.as_bytes()).unwrap();
            assert_eq!(commands.len(), 3, "{source}");
            assert_eq!(commands[1].1, format!("{bad}\n").as_bytes(), "{source}");
            assert!(
                matches!(
                    crate::parse_source_command(commands[1].1),
                    Err(NatDefinitionParseError::Lexical { .. })
                ),
                "{source}"
            );
            assert!(
                crate::parse_source_command(commands[2].1).is_ok(),
                "{source}"
            );
        }
        // A refusal that runs on past its command still refuses the whole source.
        for bad in [
            "def s := \"open\ndef b : Nat := 2\n",
            "def c := /- open\ndef b := 2\n",
        ] {
            assert!(partition(bad.as_bytes()).is_err(), "{bad}");
        }
    }
}
