//! Identifier spelling shared by the lexer and native metaprogram constructors.
//!
//! Anchored in `Init/Meta/Defs.lean`: character classes and the private
//! `Name.Internal.Meta.toString` used by `mkIdent` / `mkCIdent`. This is not
//! the unescaped diagnostic display form and does not consult parser tokens.

use super::{Name, Repr};

/// A spelling cannot silently replace a lost numeric component or exceed its
/// caller's output budget. Neither condition is a successful partial spelling.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum NameRenderError {
    OverflowedComponent,
    ByteBudgetExceeded { limit: usize, observed: usize },
}

/// The pin's `Name.Internal.Meta.toString`, with its default escaping enabled.
///
/// Keywords are deliberately not escaped: this API has no token-table argument.
/// A numeric component remains numeric, while a string such as `"42"` is quoted.
/// Macro scopes, inaccessible names and delaborator pseudo-syntax disable
/// escaping for the whole name. Walking both the name and its output is bounded
/// and iterative, so a deep input does not consume the host call stack.
pub fn to_identifier_string(name: &Name, max_bytes: usize) -> Result<String, NameRenderError> {
    let mut parts = Vec::new();
    let mut cursor = name;
    let mut last_string = None;
    while !cursor.is_anonymous() {
        match &cursor.0 {
            Repr::Str(node) => {
                last_string.get_or_insert(node.component.as_str());
                parts.push(cursor);
                cursor = &node.pre;
            }
            Repr::Num(node) => {
                if node.overflowed {
                    return Err(NameRenderError::OverflowedComponent);
                }
                parts.push(cursor);
                cursor = &node.pre;
            }
            Repr::Anonymous => unreachable!("the loop excludes anonymous"),
        }
        // Every component contributes at least one byte, including its
        // separator (except a single empty component, which renders as «»).
        if parts.len() > max_bytes.saturating_add(1) {
            return Err(NameRenderError::ByteBudgetExceeded {
                limit: max_bytes,
                observed: parts.len().saturating_sub(1),
            });
        }
    }
    let pseudo = parts.last().is_some_and(|root| match &root.0 {
        Repr::Str(node) => {
            node.component.starts_with('#')
                || node.component.starts_with('?')
                || (parts.len() == 1 && node.component == "_")
        }
        _ => false,
    });
    let inaccessible =
        last_string.is_some_and(|text| text.contains('✝') || text == "_inaccessible");
    let escape = !pseudo && !inaccessible && !name.has_macro_scopes();
    let mut result = String::new();
    if parts.is_empty() {
        append_bounded(&mut result, "[anonymous]", max_bytes)?;
    }
    for (index, part) in parts.into_iter().rev().enumerate() {
        if index > 0 {
            append_bounded(&mut result, ".", max_bytes)?;
        }
        match &part.0 {
            Repr::Str(node) => {
                let text = &node.component;
                let mut chars = text.chars();
                let plain = chars.next().is_some_and(is_id_first) && chars.all(is_id_rest);
                let quote = escape && !plain && !text.contains(ID_END_ESCAPE);
                if quote {
                    append_bounded(&mut result, "«", max_bytes)?;
                }
                append_bounded(&mut result, text, max_bytes)?;
                if quote {
                    append_bounded(&mut result, "»", max_bytes)?;
                }
            }
            Repr::Num(node) => {
                append_bounded(&mut result, &node.component.to_string(), max_bytes)?;
            }
            Repr::Anonymous => unreachable!("only name components are retained"),
        }
    }
    Ok(result)
}

fn append_bounded(
    output: &mut String,
    text: &str,
    max_bytes: usize,
) -> Result<(), NameRenderError> {
    let observed = output.len().saturating_add(text.len());
    if observed > max_bytes {
        return Err(NameRenderError::ByteBudgetExceeded {
            limit: max_bytes,
            observed,
        });
    }
    output.push_str(text);
    Ok(())
}

/// `«` — upstream `idBeginEscape`.
pub const ID_BEGIN_ESCAPE: char = '«';
/// `»` — upstream `idEndEscape`.
pub const ID_END_ESCAPE: char = '»';

/// Upstream `isIdFirst` (`Init/Meta/Defs.lean:120`): ASCII alpha, `_`, or letter-like.
///
/// `Char.isAlpha` upstream is **ASCII only** (`isUpper || isLower`, each a range check on
/// `A-Z`/`a-z`), so every non-ASCII identifier character arrives through `is_letter_like` —
/// not through Rust's `char::is_alphabetic`, which accepts vastly more. Using the Rust
/// predicate here would accept identifiers the Reference rejects, which is a silent
/// widening of the accepted language.
pub fn is_id_first(c: char) -> bool {
    c.is_ascii_alphabetic() || c == '_' || is_letter_like(c)
}

/// Upstream `isIdRest` (`Init/Meta/Defs.lean:133`).
///
/// Note `!` and `?` and `'`: `foo!`, `foo?` and `h'` are each **one identifier**, not an
/// identifier followed by a symbol. This is where a from-scratch lexer usually diverges,
/// because `!` and `?` look like operators everywhere else.
pub fn is_id_rest(c: char) -> bool {
    c.is_ascii_alphanumeric()
        || c == '_'
        || c == '\''
        || c == '!'
        || c == '?'
        || is_letter_like(c)
        || is_subscript_alnum(c)
}

/// Upstream `isLetterLike` (`Init/Meta/Defs.lean:101`), ranges transcribed exactly.
///
/// The exclusions are the interesting part and are not decorative: lower-case lambda
/// (U+03BB) is excluded because `λ` is a *token*, and upper-case Pi (U+03A0) and Sigma
/// (U+03A3) are excluded for the same reason. Include them and `λ x => x` lexes as one
/// identifier named `λ` and nothing works.
pub fn is_letter_like(c: char) -> bool {
    let v = c as u32;
    (0x3b1..=0x3c9).contains(&v) && v != 0x3bb // lower Greek, but not λ
        || (0x391..=0x3A9).contains(&v) && v != 0x3A0 && v != 0x3A3 // upper Greek, but not Π Σ
        || (0x3ca..=0x3fb).contains(&v) // Coptic
        || (0x1f00..=0x1ffe).contains(&v) // polytonic Greek
        || (0x2100..=0x214f).contains(&v) // letter-like block
        || (0x1d49c..=0x1d59f).contains(&v) // script / double-struck / fraktur
        || (0x00c0..=0x00ff).contains(&v) && v != 0x00d7 && v != 0x00f7 // Latin-1, but not × ÷
        || (0x0100..=0x017f).contains(&v) // Latin Extended-A
}

/// Upstream `isSubScriptAlnum` (`Init/Meta/Defs.lean:114`).
pub fn is_subscript_alnum(c: char) -> bool {
    let v = c as u32;
    (0x2080..=0x2089).contains(&v)
        || (0x2090..=0x209c).contains(&v)
        || (0x1d62..=0x1d6a).contains(&v)
        || v == 0x2c7c
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn identifier_output_budgets_count_utf8_and_never_publish_truncated_names() {
        let name = Name::from_components(["λ", ""]);
        assert_eq!(to_identifier_string(&name, 11).unwrap(), "«λ».«»");
        assert!(matches!(
            to_identifier_string(&name, 10),
            Err(NameRenderError::ByteBudgetExceeded { limit: 10, .. })
        ));
        assert!(matches!(
            to_identifier_string(&Name::anonymous(), 0),
            Err(NameRenderError::ByteBudgetExceeded { .. })
        ));
        assert_eq!(
            to_identifier_string(&Name::num_overflowing(Name::anonymous(), u64::MAX), 100),
            Err(NameRenderError::OverflowedComponent)
        );
    }

    #[test]
    fn deep_identifier_rendering_uses_no_recursive_host_frames() {
        let mut name = Name::anonymous();
        for _ in 0..20_000 {
            name = Name::str(name, "a");
        }
        let result = to_identifier_string(&name, 40_000).unwrap();
        assert_eq!(result.len(), 39_999);
        assert_eq!(result.split('.').count(), 20_000);
        assert!(matches!(
            to_identifier_string(&name, 200),
            Err(NameRenderError::ByteBudgetExceeded { limit: 200, .. })
        ));
    }
}
