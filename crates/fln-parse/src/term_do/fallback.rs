//! Complete a planned refutable binding without growing ordinary bind frames.
use super::*;

fn invalid() -> NatDefinitionParseError {
    NatDefinitionParseError::OutsideSeedGrammar {
        at: BytePos(0),
        expected: NatDefinitionExpectation::ScalarValue,
    }
}

impl Prefix {
    // A branch plan carries a potentially deep success suffix. Its ownership
    // moves directly into the canonical node; no source subtree is cloned.
    #[inline(never)]
    pub(super) fn failure_binding(
        &mut self,
        leaves: &Leaves,
        mut value: Syntax,
    ) -> Result<Syntax, NatDefinitionParseError> {
        let Statement::Binding {
            keyword,
            name,
            colon,
            assignment,
        } = self.statement
        else {
            return Err(invalid());
        };
        let assignment = assignment.ok_or_else(invalid)?;
        let annotation = match (colon, self.annotation.take()) {
            (Some(colon), Some(type_)) => null_node(vec![Syntax::node(
                parser_kind(&["Term", "typeSpec"]),
                vec![leaves.leaf(colon)?, type_],
            )]),
            (None, None) => null_node(vec![]),
            _ => return Err(invalid()),
        };
        let pure = matches!(&leaves.leaf(assignment)?, Syntax::Atom { val, .. } if val == ":=");
        let pattern = match self.pattern.take() {
            Some(pattern) => pattern,
            // A bare identifier followed by an arrow is doIdDecl at the pin,
            // which has no failure slot. Do not silently reclassify that bind.
            None if pure => leaves.leaf(name)?,
            None => return Err(invalid()),
        };
        let Syntax::Node { args, .. } = &mut value else {
            return Err(invalid());
        };
        if args.len() != 4 {
            return Err(invalid());
        }
        let continuation = args.pop().expect("failure continuation");
        let otherwise = args.pop().expect("failure sequence");
        let pipe = args.pop().expect("failure pipe");
        let value = args.pop().expect("failure subject");
        let config = Syntax::node(parser_kind(&["Term", "letConfig"]), vec![null_node(vec![])]);
        if pure {
            // doLetElse parses a term pattern, not letPatDecl's separate type
            // slot. Until typed term patterns are supported, never drop it.
            if !matches!(&annotation, Syntax::Node { args, .. } if args.is_empty()) {
                return Err(invalid());
            }
            Ok(Syntax::node(
                parser_kind(&["Term", "doLetElse"]),
                vec![
                    leaves.leaf(keyword)?,
                    null_node(vec![]),
                    config,
                    pattern,
                    leaves.leaf(assignment)?,
                    value,
                    pipe,
                    otherwise,
                    continuation,
                ],
            ))
        } else {
            let declaration = Syntax::node(
                parser_kind(&["Term", "doPatDecl"]),
                vec![
                    pattern,
                    annotation,
                    leaves.leaf(assignment)?,
                    Syntax::node(parser_kind(&["Term", "doExpr"]), vec![value]),
                    null_node(vec![pipe, otherwise, continuation]),
                ],
            );
            Ok(Syntax::node(
                parser_kind(&["Term", "doLetArrow"]),
                vec![
                    leaves.leaf(keyword)?,
                    null_node(vec![]),
                    config,
                    declaration,
                ],
            ))
        }
    }
}
