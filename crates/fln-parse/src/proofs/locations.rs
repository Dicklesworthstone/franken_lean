//! Lossless named, goal, and wildcard locations for rewriting. `at` remains a
//! contextual word; occurrences inside rule terms or escaped identifiers are
//! not suffixes.
use super::*;

pub(super) fn split(
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    range: Range<usize>,
) -> Result<(Range<usize>, Syntax), NatDefinitionParseError> {
    let mut depth = 0usize;
    let mut suffix = None;
    for at in range.clone() {
        match &tokens[at].kind {
            TokenKind::Symbol(s)
                if matches!(
                    crate::canonical_bracket(s.as_str()),
                    "(" | "[" | "{" | ".{" | "⦃" | "⟨"
                ) =>
            {
                depth += 1;
            }
            TokenKind::Symbol(s)
                if matches!(
                    crate::canonical_bracket(s.as_str()),
                    ")" | "]" | "}" | "⦄" | "⟩"
                ) =>
            {
                depth = depth
                    .checked_sub(1)
                    .ok_or_else(|| refusal(view, tokens, at))?;
            }
            // `at` is a token at the pin, so an escaped `«at»` is an identifier and never this.
            TokenKind::Symbol(s) if depth == 0 && s == "at" => {
                suffix = Some(at);
                break;
            }
            _ => {}
        }
    }
    let Some(at) = suffix else {
        return Ok((range, null_node(Vec::new())));
    };
    if at + 1 == range.end {
        return Err(refusal(view, tokens, at));
    }
    let selection = if matches!(&tokens[at + 1].kind, TokenKind::Symbol(s) if s == "*") {
        // A wildcard is the entire location, never a spelling of a local.
        // Escaped `«*»` is an identifier and goes through the named branch.
        if at + 2 != range.end {
            return Err(refusal(view, tokens, at + 2));
        }
        Syntax::node(
            parser_kind(&["Tactic", "locationWildcard"]),
            vec![leaves.leaf(at + 1)?],
        )
    } else {
        let mut names = Vec::new();
        let mut index = at + 1;
        while index < range.end {
            let leaf = leaves.leaf(index)?;
            names.push(match &tokens[index].kind {
                TokenKind::Ident(_) => leaf,
                TokenKind::Symbol(symbol) if symbol == "⊢" => {
                    Syntax::node(parser_kind(&["Tactic", "locationType"]), vec![leaf])
                }
                // The pin's `locationType := patternIgnore(atomic("|" noWs "-") <|> "⊢")`:
                // `|-` is not a token, it is `|` and `-` with nothing between them. The
                // goal marker keeps its one-atom shape, spanning both tokens exactly.
                TokenKind::Symbol(symbol)
                    if symbol == "|"
                        && index + 1 < range.end
                        && matches!(&tokens[index + 1].kind, TokenKind::Symbol(s) if s == "-")
                        && tokens[index].extent.end() == tokens[index + 1].extent.start() =>
                {
                    let (
                        SourceInfo::Original { leading, pos, .. },
                        SourceInfo::Original {
                            trailing, end_pos, ..
                        },
                    ) = (leaf.info(), leaves.leaf(index + 1)?.info())
                    else {
                        return Err(refusal(view, tokens, index));
                    };
                    index += 1;
                    Syntax::node(
                        parser_kind(&["Tactic", "locationType"]),
                        vec![Syntax::atom(
                            SourceInfo::Original {
                                leading,
                                pos,
                                trailing,
                                end_pos,
                            },
                            "|-",
                        )],
                    )
                }
                _ => return Err(refusal(view, tokens, index)),
            });
            index += 1;
        }
        Syntax::node(
            parser_kind(&["Tactic", "locationHyp"]),
            vec![null_node(names)],
        )
    };
    let keyword = leaves.leaf(at)?;
    let location = Syntax::node(
        parser_kind(&["Tactic", "location"]),
        vec![
            Syntax::Atom {
                info: keyword.info(),
                val: "at".into(),
            },
            selection,
        ],
    );
    Ok((range.start..at, null_node(vec![location])))
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn named_rewrite_locations_preserve_comments_unicode_and_rule_terms() {
        for source in [
            "theorem t : True := by rw [h] at hx",
            "theorem t : True := by rw [h] at ⊢",
            "theorem t : True := by rewrite [h] at hx |-",
            "theorem t : True := by simp only [h] at ⊢ hx",
            "theorem t : True := by\r\n  simp only [h] /- goal -/ at «⊢» ⊢ h₂\r\n  assumption",
            "theorem t : True := by rewrite [← h, k] at hx hy",
            "theorem t : True := by simp only [h] at hx",
            // `at` is a token at the pin, so a rule naming a local called `at` escapes it.
            "theorem t : True := by\r\n  simp only [f («at»), ← h] /- suffix -/ at «h.x» h₂\r\n  assumption",
            "theorem t : True := by\r\n  rw [«at», f («at»)] /- location -/ at «h.x» h₂\r\n  assumption",
        ] {
            let parsed = parse_source_command(source.as_bytes()).unwrap();
            assert_eq!(parsed.reconstruct_original(), source.as_bytes());
        }
    }
    #[test]
    fn wildcard_locations_are_lossless_and_distinct_from_escaped_names() {
        for source in [
            "theorem t : True := by rw [h] at *",
            "theorem t : True := by rewrite [← h, k] at *",
            "theorem t : True := by simp at *",
            "theorem t : True := by simp only [h] at *",
            "theorem t : True := by simp only [*] at *",
            "theorem t : True := by\r\n  rw [h] at /- all -/ *\r\n  assumption",
            "theorem t : True := by rw [h] at «*»",
        ] {
            let parsed = parse_source_command(source.as_bytes()).unwrap();
            assert_eq!(parsed.reconstruct_original(), source.as_bytes());
        }
    }
    #[test]
    fn malformed_locations_are_not_ignored() {
        for tail in [
            "rw [h] at",
            "rw [h] at 3",
            "rw [h] «at» hx",
            "rw [h] at ⊢ 3",
            "rw [h] at | -",
            "rw [h] at hx, ⊢",
            "rw [h] at (hx)",
            "rw [h] at hx, hy",
            "rw [h] at * hx",
            "rw [h] at hx *",
            "rw [h] at * ⊢",
            "rw [h] at * *",
            "simp only [h] at",
            "simp only [h] at (hx)",
            "simp only [h] at hx, hy",
            "simp only [h] at * hx",
        ] {
            let source = format!("theorem t : True := by {tail}");
            assert!(parse_source_command(source.as_bytes()).is_err(), "{tail}");
        }
    }
}
