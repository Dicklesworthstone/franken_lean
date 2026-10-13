//! Declaration modifiers after the attributes: the pin's `declModifiers` slots 2..6
//! (bead `franken_lean-z8j.1.10`, stage 2).
//!
//! `Lean/Parser/Command.lean:114` at the pin:
//!
//! ```text
//! def declModifiers (inline : Bool) := leading_parser
//!   optional docComment >>
//!   optional (Term.«attributes» >> ...) >>
//!   optional visibility >>               -- «private» <|> «public»
//!   optional «protected» >>
//!   optional («meta» <|> «noncomputable») >>
//!   optional «unsafe» >>
//!   optional («partial» <|> «nonrec»)
//! ```
//!
//! Each keyword is its own `leading_parser` node holding one atom (`Command.protected
//! "protected"`), and each slot is a null node holding that node or nothing. The order is fixed:
//! a modifier out of order is not consumed, so the declaration keyword is expected there and the
//! parse refuses at it, as the pin does.
//!
//! This module only parses. Every elaborator path still refuses a non-empty slot other than the
//! attributes, so a modifier is never silently dropped: `private` mangling, `protected` name
//! resolution, `noncomputable`, `unsafe`, `partial` and `nonrec` each need their own semantics
//! before they can be admitted.
use super::*;

/// The five modifier slots after the attributes, in the pin's order. Each slot accepts
/// exactly these keywords, and the node kind is `Lean.Parser.Command.<keyword>`.
const SLOTS: [&[&str]; 5] = [
    &["private", "public"],
    &["protected"],
    &["meta", "noncomputable"],
    &["unsafe"],
    &["partial", "nonrec"],
];

/// Every keyword that may start a modifier slot.
pub(crate) fn is_modifier(word: &str) -> bool {
    SLOTS.iter().any(|slot| slot.contains(&word))
}

/// The keyword text of `token`, when it is one of the modifier keywords. Every modifier is a
/// keyword at the pin, so it is always a symbol; an escaped `«partial»` is an identifier and
/// never a modifier.
fn keyword(token: &LexedToken) -> Option<&str> {
    match &token.kind {
        TokenKind::Symbol(symbol) if is_modifier(symbol) => Some(symbol.as_str()),
        _ => None,
    }
}

/// The modifier tokens found after the attributes: for each slot, the token index of its
/// keyword, if present.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Modifiers {
    slots: [Option<usize>; 5],
    end: usize,
}

impl Modifiers {
    /// The token index just after the last modifier: where the declaration keyword must be.
    pub(crate) fn end(&self) -> usize {
        self.end
    }

    /// Write the five slot nodes (`declModifiers` children 2..=6) into `parts`, from the
    /// original leaves. Out of line and writing in place: the declaration parser runs on small
    /// host stacks (its deep-nesting tests use 96 KiB threads), so these nodes never live in its
    /// frame.
    #[inline(never)]
    pub(crate) fn fill(
        &self,
        view: &SourceView,
        leaves: &Leaves,
        tokens: &[LexedToken],
        parts: &mut [Syntax],
    ) -> Result<(), DefinitionParseError> {
        for (part, slot) in parts.iter_mut().zip(self.slots) {
            let Some(at) = slot else {
                continue;
            };
            let word = tokens.get(at).and_then(keyword).ok_or(
                NatDefinitionParseError::OutsideSeedGrammar {
                    at: original_position(view, tokens, at),
                    expected: NatDefinitionExpectation::DefinitionKeyword,
                },
            )?;
            *part = null_node(vec![Syntax::node(
                parser_kind(&["Command", word]),
                vec![leaves.leaf(at)?],
            )]);
        }
        Ok(())
    }
}

/// Whether `token` is a modifier keyword, so the command it starts is a declaration.
pub(crate) fn leads(token: &LexedToken) -> bool {
    keyword(token).is_some()
}

/// Scan the modifier keywords starting at token `start` (just after any attributes). Slots
/// are taken in order and each at most once; scanning stops at the first token that does not
/// fill the next possible slot.
pub(crate) fn scan(tokens: &[LexedToken], start: usize) -> Modifiers {
    let mut slots = [None; 5];
    let mut at = start;
    let mut next_slot = 0;
    while let Some(word) = tokens.get(at).and_then(keyword) {
        let Some(offset) = SLOTS[next_slot..]
            .iter()
            .position(|slot| slot.contains(&word))
        else {
            break;
        };
        slots[next_slot + offset] = Some(at);
        next_slot += offset + 1;
        at += 1;
        if next_slot == SLOTS.len() {
            break;
        }
    }
    Modifiers { slots, end: at }
}

/// Visibility at an unfinished declaration or material control's head. This is a query hint only:
/// no signature, body, modifier effect, or declaration has been validated.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DeclarationPrefix {
    pub public: Option<bool>,
    pub is_example: bool,
}

/// The instance's `attrKind` precedes its keyword, after `declModifiers`.
/// Match the same two-token prefix as the full declaration parser so visibility
/// and an unfinished proof's boundary keep their ordinary declaration meaning.
fn instance_keyword(tokens: &[LexedToken], start: usize) -> usize {
    if matches!(tokens.get(start).map(|token| &token.kind),
        Some(TokenKind::Symbol(kind)) if kind == "scoped" || kind == "local")
        && matches!(tokens.get(start + 1).map(|token| &token.kind),
            Some(TokenKind::Symbol(kind)) if kind == "instance")
    {
        start + 1
    } else {
        start
    }
}

/// Read only the declaration prefix, reusing the ordinary parser's attribute
/// grammar and fixed modifier slots. Variable/attribute controls inherit the
/// section's visibility too. The body may end at an incomplete name or binder.
/// Query/lexical scope commands and unrecognized heads return `None`; a keyword
/// in a body, string, comment, or escaped identifier never supplies visibility.
pub fn prefix(source: &[u8]) -> Result<Option<DeclarationPrefix>, DefinitionParseError> {
    let original = SourceText::from_utf8(source).map_err(NatDefinitionParseError::Source)?;
    let view = SourceView::of(&original);
    let tokens = super::tokens(&view)?;
    let (_, attributes_end, declaration_start) =
        crate::declaration_prefix(&view, &tokens, DefinitionGrammar::Scalar)?;
    let declaration_start = instance_keyword(&tokens, declaration_start);
    let Some(TokenKind::Symbol(kind)) = tokens.get(declaration_start).map(|token| &token.kind)
    else {
        return Ok(None);
    };
    if !matches!(
        kind.as_str(),
        "def"
            | "theorem"
            | "abbrev"
            | "opaque"
            | "example"
            | "instance"
            | "structure"
            | "class"
            | "inductive"
            | "axiom"
            | "variable"
            | "attribute"
    ) {
        return Ok(None);
    }
    let modifiers = scan(&tokens, attributes_end);
    Ok(Some(DeclarationPrefix {
        public: modifiers.slots[0].map(|at| keyword(&tokens[at]) == Some("public")),
        is_example: kind == "example",
    }))
}

/// Locate a theorem's value opener without parsing its unfinished proof. This
/// uses the ordinary declaration header boundaries: a binder default or a local
/// binding in the result type does not start the proof. An unfinished header
/// has no value boundary yet. The returned position is in the original bytes.
pub fn theorem_body_start(source: &[u8]) -> Result<Option<usize>, DefinitionParseError> {
    declaration_body_start(source, false)
}

/// Locate a named or anonymous instance's value opener without parsing its
/// unfinished body. This establishes a syntax boundary only: the elaborator
/// must classify the header before a private proof world may be selected.
pub fn instance_body_start(source: &[u8]) -> Result<Option<usize>, DefinitionParseError> {
    declaration_body_start(source, true)
}

fn declaration_body_start(
    source: &[u8],
    instance: bool,
) -> Result<Option<usize>, DefinitionParseError> {
    let original = SourceText::from_utf8(source).map_err(NatDefinitionParseError::Source)?;
    let view = SourceView::of(&original);
    let tokens = super::tokens(&view)?;
    let (_, _, declaration_start) =
        crate::declaration_prefix(&view, &tokens, DefinitionGrammar::Scalar)?;
    let declaration_start = instance_keyword(&tokens, declaration_start);
    if !matches!(tokens.get(declaration_start).map(|token| &token.kind),
        Some(TokenKind::Symbol(kind)) if kind == if instance { "instance" } else { "theorem" })
    {
        return Ok(None);
    }
    let mut cursor = declaration_start + 1;
    if instance
        && matches!(tokens.get(cursor).map(|token| &token.kind),
            Some(TokenKind::Symbol(kind)) if kind == "(")
        && matches!(tokens.get(cursor + 2).map(|token| &token.kind),
            Some(TokenKind::Symbol(kind)) if kind == ":=")
    {
        let leaves = Leaves::build(view.normalized(), &tokens)?;
        let Ok(Some((_, end))) =
            super::syntax_decls::named_priority(&view, &tokens, &leaves, cursor)
        else {
            return Ok(None);
        };
        cursor = end;
    }
    if matches!(
        tokens.get(cursor).map(|token| &token.kind),
        Some(TokenKind::Ident(_))
    ) {
        let Ok((_, end)) = crate::levels::declaration_suffix(&view, &tokens, cursor + 1) else {
            return Ok(None);
        };
        cursor = end;
    } else if !instance {
        return Ok(None);
    }
    let Ok((_, cursor)) =
        crate::signature_binders(&view, &tokens, cursor, DefinitionGrammar::Scalar)
    else {
        return Ok(None);
    };
    if !matches!(tokens.get(cursor).map(|token| &token.kind),
        Some(TokenKind::Symbol(kind)) if kind == ":")
    {
        return Ok(None);
    }
    let start = cursor + 1;
    let mut end =
        crate::type_end(&tokens, start, ":=").min(crate::type_end(&tokens, start, "where"));
    let pipe = crate::type_end(&tokens, start, "|");
    if !crate::top_level_match(&tokens, start, pipe) {
        end = end.min(pipe);
    }
    Ok((start < end && end < tokens.len()).then(|| view.to_original(tokens[end].extent.start()).0))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn completion_visibility_reads_modifiers_without_requiring_a_finished_body() {
        for (source, public) in [
            (
                "@[expose] public def use (A : Type) (x : A) : A :=",
                Some(true),
            ),
            (
                "/-- API -/\nprivate def use (A : Type) (x : A) : A :=",
                Some(false),
            ),
            ("def use (A : Type) (x : A) : A :=", None),
            ("@[expose] public def use (", Some(true)),
            ("variable (x :", None),
            ("attribute [instance]", None),
        ] {
            assert_eq!(
                prefix(source.as_bytes()).unwrap(),
                Some(DeclarationPrefix {
                    public,
                    is_example: false
                }),
                "{source}"
            );
        }
        assert_eq!(
            prefix(b"example (P : Prop) : P :=").unwrap(),
            Some(DeclarationPrefix {
                public: None,
                is_example: true
            })
        );
        for source in [
            "#check",
            "#eval",
            "@[expose] public section",
            "«public» def use :=",
            "-- public def hidden :=\n#check",
        ] {
            assert_eq!(prefix(source.as_bytes()).unwrap(), None, "{source}");
        }
    }

    #[test]
    fn theorem_completion_switches_only_after_the_actual_header() {
        for header in [
            "public theorem",
            "public theorem t (x :",
            "public theorem t.{u",
            "public theorem t (x : Nat := 0) : x = x",
            "public theorem t : let P := True; P",
            "public theorem t : letI : C := value; P",
            "public theorem t : (\" := \" = \" := \")",
            "public theorem t («:=» : Prop) : «:=»",
            "public theorem t : match true with | true => True | false => False",
        ] {
            assert_eq!(
                theorem_body_start(header.as_bytes()).unwrap(),
                None,
                "{header}"
            );
        }
        for source in [
            "public theorem t : True :=",
            "public theorem t.{u} (A : Sort u) (x : A) : x = x := by",
            "public theorem t (x : Nat := 0) : x = x := by exact (",
            "public theorem t : let P := True; P := by exact",
            "@[simp] public theorem t : True /- := is trivia -/ := by",
            "/-- proof -/\r\npublic theorem t : True := by\r\n  exact",
        ] {
            assert_eq!(
                theorem_body_start(source.as_bytes()).unwrap(),
                source.rfind(":="),
                "{source}"
            );
        }
        for (source, marker) in [
            ("public theorem t (n : Nat) : n = n\n| .zero =>", "|"),
            ("public theorem t : True where", "where"),
        ] {
            assert_eq!(
                theorem_body_start(source.as_bytes()).unwrap(),
                source.find(marker)
            );
        }
        assert_eq!(theorem_body_start(b"public def t : Nat :=").unwrap(), None);
    }

    #[test]
    fn instance_completion_locates_named_anonymous_and_priority_headers() {
        for header in [
            "public instance",
            "public instance named.{u",
            "public instance (priority := 12",
            "public instance named (x : Nat := 0) : Law (x = x)",
            "public instance : let P := True; Law P",
            "public instance : Law (\" := \" = \" := \")",
            "public instance : match true with | true => Law True | false => Law False",
            "public theorem named : True := by",
        ] {
            assert_eq!(
                instance_body_start(header.as_bytes()).unwrap(),
                None,
                "{header}"
            );
        }
        for source in [
            "public instance : Law True :=",
            "public instance named : Law True := by exact",
            "public instance (priority := 23) : Law True := by",
            "public instance (priority := 23) named.{u} (A : Sort u) : Law (A = A) := by",
            "public instance (x : Nat := 0) : Law (x = x) := by",
            "public instance : let P := True; Law P := by",
            "@[no_expose] public instance named : Law True /- := -/ := by",
            "/-- proof -/\r\npublic instance : Law True := by\r\n exact",
        ] {
            assert_eq!(
                instance_body_start(source.as_bytes()).unwrap(),
                source.rfind(":="),
                "{source}"
            );
        }
        for (source, marker) in [
            ("public instance (n : Nat) : Law (n = n)\n| .zero =>", "|"),
            ("public instance : Law True where", "where"),
        ] {
            assert_eq!(
                instance_body_start(source.as_bytes()).unwrap(),
                source.find(marker)
            );
        }
    }

    #[test]
    fn scoped_instance_visibility_and_proof_boundaries_preserve_the_header() {
        for source in [
            "public scoped instance named : Law True := by exact",
            "@[no_expose] public scoped instance (priority := 23) : Law True := by",
            "/-- proof -/\r\npublic scoped instance : Law True := by\r\n exact",
        ] {
            assert_eq!(
                prefix(source.as_bytes()).unwrap(),
                Some(DeclarationPrefix {
                    public: Some(true),
                    is_example: false,
                }),
                "{source}"
            );
            assert_eq!(
                instance_body_start(source.as_bytes()).unwrap(),
                source.rfind(":="),
                "{source}"
            );
        }
        for header in [
            "public scoped instance",
            "public scoped instance (priority := 23",
            "public scoped instance (x : Nat := 0) : Law (x = x)",
        ] {
            assert_eq!(instance_body_start(header.as_bytes()).unwrap(), None);
        }
        for source in [
            "scoped notation",
            "public «scoped» instance named : Law True :=",
            "scoped theorem proof : True :=",
        ] {
            assert_eq!(prefix(source.as_bytes()).unwrap(), None, "{source}");
            assert_eq!(instance_body_start(source.as_bytes()).unwrap(), None);
        }
    }
}
