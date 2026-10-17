//! `funBinder` consumes a maximal-precedence pattern, not an entire telescope.
//! Reuse the match parser so aliases never become explicit applications here.
use super::*;

pub(super) fn binder(
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    start: usize,
    end: usize,
) -> Result<Option<(Syntax, usize)>, NatDefinitionParseError> {
    let next = if symbol(tokens, start, "(") {
        let mut head = start + 1;
        while head < end && symbol(tokens, head, "(") {
            head += 1;
        }
        if !crate::matching::named_prefix(tokens, head, end) {
            return Ok(None);
        }
        pattern_close(tokens, start, end).ok_or_else(|| refuse(view, tokens, start))? + 1
    } else {
        if !crate::matching::named_prefix(tokens, start, end) {
            return Ok(None);
        }
        let atom = start + 2;
        if atom >= end {
            return Err(refuse(view, tokens, atom));
        }
        if symbol(tokens, atom, "(") || symbol(tokens, atom, "⟨") {
            pattern_close(tokens, atom, end).ok_or_else(|| refuse(view, tokens, atom))? + 1
        } else if symbol(tokens, atom, ".") {
            if atom + 1 >= end || !matches!(tokens[atom + 1].kind, TokenKind::Ident(_)) {
                return Err(refuse(view, tokens, atom));
            }
            atom + 2
        } else {
            atom + 1
        }
    };
    let syntax = crate::matching::parse_named_binding(leaves, view, tokens, start..next)?
        .ok_or_else(|| refuse(view, tokens, start))?;
    Ok(Some((syntax, next)))
}
