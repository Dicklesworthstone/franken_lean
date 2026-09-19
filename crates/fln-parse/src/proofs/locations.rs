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
            TokenKind::Symbol(s) if matches!(s.as_str(), "(" | "[" | "{" | ".{" | "⦃") => {
                depth += 1;
            }
            TokenKind::Symbol(s) if matches!(s.as_str(), ")" | "]" | "}" | "⦄") => {
                depth = depth
                    .checked_sub(1)
                    .ok_or_else(|| refusal(view, tokens, at))?;
            }
            TokenKind::Ident(name)
                if depth == 0
                    && name == &Name::from_components(["at"])
                    && &view.normalized().as_str()
                        [tokens[at].extent.start().0..tokens[at].extent.end().0]
                        == "at" =>
            {
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
        for index in at + 1..range.end {
            let leaf = leaves.leaf(index)?;
            names.push(match &tokens[index].kind {
                TokenKind::Ident(_) => leaf,
                TokenKind::Symbol(symbol) if symbol == "⊢" || symbol == "|-" => {
                    Syntax::node(parser_kind(&["Tactic", "locationType"]), vec![leaf])
                }
                _ => return Err(refusal(view, tokens, index)),
            });
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
            "theorem t : True := by\r\n  simp only [f (at), ← h] /- suffix -/ at «h.x» h₂\r\n  assumption",
            "theorem t : True := by\r\n  rw [at, f (at)] /- location -/ at «h.x» h₂\r\n  assumption",
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
