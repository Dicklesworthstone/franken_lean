//! Equality calculations are planned on the same heap as nested tactic proofs.
//! Each row retains its written relation and its proof. No source text is
//! generated, and the parser does not claim that adjacent endpoints agree.
use super::*;

pub(super) struct Step {
    pub relation: Range<usize>,
    pub assign: usize,
    pub proof: Range<usize>,
}
pub(super) struct Calculation {
    pub start: usize,
    pub steps: Vec<Step>,
    pub end: usize,
}

pub(super) fn plan(
    view: &SourceView,
    tokens: &[LexedToken],
    start: usize,
    limit: usize,
) -> Result<Calculation, NatDefinitionParseError> {
    let first = start + 1;
    if first >= limit {
        return Err(refusal(view, tokens, first));
    }
    let baseline = column(view, tokens, first);
    if newline(view, tokens, first) && baseline == 0 {
        return Err(refusal(view, tokens, first));
    }
    let mut rows = vec![first];
    let mut end = limit;
    let mut depth = 0;
    for at in first..limit {
        if depth == 0 {
            if matches!(&tokens[at].kind, TokenKind::Symbol(s) if matches!(s.as_str(), ")" | "]" | "}" | "⦄"))
                || at > first && newline(view, tokens, at) && column(view, tokens, at) < baseline
            {
                end = at;
                break;
            }
            if at > first && newline(view, tokens, at) && column(view, tokens, at) == baseline {
                rows.push(at);
            }
        }
        delimiter_depth(&tokens[at], &mut depth);
    }
    if depth != 0 {
        return Err(refusal(view, tokens, end));
    }
    let mut steps = Vec::with_capacity(rows.len());
    for (index, row) in rows.iter().copied().enumerate() {
        let stop = rows.get(index + 1).copied().unwrap_or(end);
        let mut depth = 0;
        let mut assign = None;
        let mut equality = None;
        for at in row..stop {
            if depth == 0 && symbol(tokens, at, ":=") {
                assign = Some(at);
                break;
            }
            if depth == 0 && symbol(tokens, at, "=") && equality.replace(at).is_some() {
                return Err(refusal(view, tokens, at));
            }
            delimiter_depth(&tokens[at], &mut depth);
        }
        let assign = assign.ok_or_else(|| refusal(view, tokens, row))?;
        let equality = equality.ok_or_else(|| refusal(view, tokens, row))?;
        if equality == row || equality + 1 == assign || assign + 1 == stop || depth != 0 {
            return Err(refusal(view, tokens, assign));
        }
        steps.push(Step {
            relation: row..assign,
            assign,
            proof: assign + 1..stop,
        });
    }
    Ok(Calculation { start, steps, end })
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn calculation_preserves_comments_unicode_and_original_line_endings() {
        for source in [
            "theorem chain (a b c : Nat) (h : a = b) (k : b = c) : a = c := calc\n  a = b := h -- first\n  _ = c := by exact k\n",
            "theorem chain (α : Type) (a : α) : a = a := by\r\n  calc\r\n    a = a := by\r\n      calc\r\n        a = a := by rfl -- end\r\n",
            "theorem chain (a : Nat) : a = a := by\n  exact calc\n    a = a := by rfl\n",
            "theorem chain (a : Nat) : a = a := (calc\n  a = a := by rfl)\n",
        ] {
            let parsed =
                parse_definition(source.as_bytes()).unwrap_or_else(|e| panic!("{source}\n{e:?}"));
            assert_eq!(parsed.reconstruct_original(), source.as_bytes());
        }
    }
    #[test]
    fn malformed_calculations_are_not_truncated_to_a_valid_prefix() {
        for source in [
            "theorem bad (a : Nat) : a = a := calc",
            "theorem bad (a : Nat) : a = a := calc\n  a = a := by rfl\n  _ = a :=",
            "theorem bad (a : Nat) : a = a := calc\n  a = a := by rfl\n  _ = a",
            "theorem bad (a : Nat) : a = a := calc\n  a = a = a := by rfl",
            "theorem bad (a : Nat) : a = a := calc\n  a := by rfl",
        ] {
            assert!(parse_definition(source.as_bytes()).is_err(), "{source}");
        }
    }
}
