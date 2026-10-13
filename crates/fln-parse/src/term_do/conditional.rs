//! Statement conditionals are already planned with their complete do sequences.
//! Do not reclassify ordinary term branches here: doing so can lose a loop's
//! control scope or reinterpret a term-level let separator as a do statement.
use super::*;

pub(super) fn element(
    syntax: Syntax,
    position: BytePos,
) -> Result<Syntax, NatDefinitionParseError> {
    if matches!(&syntax, Syntax::Node { kind, args, .. }
        if kind == &parser_kind(&["Term", "doIf"]) && args.len() == 6)
    {
        Ok(syntax)
    } else {
        Err(NatDefinitionParseError::OutsideSeedGrammar {
            at: position,
            expected: NatDefinitionExpectation::ScalarValue,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn count(syntax: &Syntax, label: &str) -> usize {
        // The pin's term `if` is the root-namespace notation `termIfThenElse`.
        let expected = if label == "termIfThenElse" {
            Name::from_components([label])
        } else {
            parser_kind(&["Term", label])
        };
        let mut pending = vec![syntax];
        let mut found = 0;
        while let Some(syntax) = pending.pop() {
            if let Syntax::Node { kind, args, .. } = syntax {
                found += usize::from(kind == &expected);
                pending.extend(args);
            }
        }
        found
    }
    #[test]
    fn conditional_loop_jumps_and_action_branches_preserve_source() {
        for source in [
            "def run : Nat := do { for x in xs do { if x == 1 then continue else visit x; after x }; return 7 }",
            "def run : Nat := do\r\n  for «𝒙» in xs do\r\n    if flag then break else visit «𝒙»\r\n    after «𝒙»\r\n  return 7",
        ] {
            let parsed = parse_definition(source.as_bytes()).unwrap();
            assert_eq!(count(parsed.syntax(), "doIf"), 1);
            assert_eq!(count(parsed.syntax(), "doIfProp"), 1);
            assert_eq!(
                count(parsed.syntax(), "doBreak") + count(parsed.syntax(), "doContinue"),
                1
            );
            assert_eq!(parsed.reconstruct_original(), source.as_bytes());
            assert_eq!(
                parsed.reconstruct_normalized().unwrap(),
                parsed.source_view().normalized().as_bytes()
            );
        }
    }
    #[test]
    fn nested_statement_conditionals_do_not_reclassify_parenthesized_terms() {
        let source = "def run : Nat := do { if a then if b then break else continue else (if c then «break» else «continue»); return 7 }";
        let parsed = parse_definition(source.as_bytes()).unwrap();
        assert_eq!(count(parsed.syntax(), "doIf"), 2);
        assert_eq!(count(parsed.syntax(), "termIfThenElse"), 1);
        assert_eq!(count(parsed.syntax(), "doBreak"), 1);
        assert_eq!(count(parsed.syntax(), "doContinue"), 1);
    }
    #[test]
    fn unsupported_or_malformed_branch_control_is_not_an_ordinary_application() {
        for branch in ["break 1", "continue x", "return 7; unreachable"] {
            let source =
                format!("def run : Nat := do {{ if flag then {branch} else action; return 7 }}");
            assert!(parse_definition(source.as_bytes()).is_err(), "{source}");
        }
        let missing_else = "def run : Nat := do { if flag then action; return 7 }";
        let parsed = parse_definition(missing_else.as_bytes()).unwrap();
        assert_eq!(count(parsed.syntax(), "doIf"), 1);
    }
}
