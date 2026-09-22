//! Section variable telescopes use the declaration binder parser unchanged.
//! The syntax keeps original leaves and positions; no synthetic source prefix
//! is reparsed, so command boundaries and diagnostics remain byte-accurate.
use super::*;

pub(super) fn parse(
    view: &SourceView,
    tokens: &[LexedToken],
) -> Result<Syntax, DefinitionParseError> {
    let (groups, end) = bounded_binders(view, tokens, 1, DefinitionGrammar::Scalar)?;
    if groups.is_empty() || end != tokens.len() {
        return Err(NatDefinitionParseError::OutsideSeedGrammar {
            at: original_position(view, tokens, end),
            expected: NatDefinitionExpectation::EndOfCommand,
        });
    }
    let leaves = Leaves::build(view.normalized(), tokens)?;
    Ok(null_node(bounded_binder_syntax(
        &leaves,
        view,
        tokens,
        groups,
        DefinitionGrammar::Scalar,
    )?))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn variable_telescopes_preserve_layout_comments_and_escaped_names() {
        let source = "/- 😀 -/ section\r\nvariable {α : Type u}\r\n  (a «b.c» : α) [Inhabited α]\r\ndef keep := a\r\nend\r\n";
        let commands = partition(source.as_bytes()).unwrap();
        assert_eq!(commands.len(), 4);
        let Some(ScopeCommand::Variable(Syntax::Node { ref args, .. })) =
            super::super::parse(commands[1].1).unwrap()
        else {
            panic!("variable telescope expected")
        };
        assert_eq!(args.len(), 3);
        let joined: Vec<_> = commands
            .iter()
            .flat_map(|(_, bytes)| bytes.iter().copied())
            .collect();
        assert_eq!(joined, source.as_bytes());
    }

    #[test]
    fn malformed_variables_and_trailing_commands_are_not_dropped() {
        for source in [
            "variable",
            "variable x",
            "variable (x : Nat",
            "variable (x : Nat) garbage",
            "variable (x : Nat) := 0",
            "variable (x : Nat) in",
        ] {
            assert!(super::super::parse(source.as_bytes()).is_err(), "{source}");
        }
    }

    #[test]
    fn selections_keep_source_boundaries_and_reject_unsupported_suffixes() {
        let source =
            "variable (p : Prop) (h «h.p» : p)\ninclude h «h.p»\ntheorem t : p := h\nomit h\n";
        let commands = partition(source.as_bytes()).unwrap();
        assert_eq!(commands.len(), 4);
        assert_eq!(
            super::super::parse(commands[1].1).unwrap(),
            Some(ScopeCommand::Include(vec![
                Name::from_components(["h"]),
                Name::from_components(["h.p"])
            ]))
        );
        assert_eq!(
            super::super::parse(commands[3].1).unwrap(),
            Some(ScopeCommand::Omit(vec![Name::from_components(["h"])]))
        );
        for source in [
            "include",
            "omit",
            "include h in",
            "omit h garbage := 0",
            "include 0",
            "omit [Inhabited Nat]",
        ] {
            assert!(super::super::parse(source.as_bytes()).is_err(), "{source}");
        }
    }
}
