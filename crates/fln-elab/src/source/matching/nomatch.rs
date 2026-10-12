//! Empty source matches use the ordinary checked case-equation backend.
//!
//! An empty alternative list is not evidence that a type is empty. The backend
//! must either find no constructors or discharge every constructor branch with
//! a retained contradiction proof. A surviving branch remains a coverage error.
//! This does not weaken ordinary match syntax or introduce a new kernel rule.

use super::*;

impl Context {
    pub(in crate::source) fn nomatch_parts<'a>(
        &mut self,
        syntax: &'a Syntax,
    ) -> Result<MatchParts<'a>, NatDefinitionElabError> {
        self.tick()?;
        let parts = expect_node(syntax, &parser_kind(&["Term", "nomatch"]), 2, "empty match")?;
        expect_atom(&parts[0], "nomatch", "empty match keyword")?;
        let discriminants = expect_null_args(&parts[1], "empty match discriminants")?;
        // Multiple columns require their own dependent matrix lowering. Never
        // discard a comma or an unelaborated later expression.
        let [discriminant] = discriminants else {
            return Err(error(MatchError::InvalidPattern));
        };
        Ok(MatchParts {
            discriminant,
            equation: None,
            alternatives: &[],
            generated: true,
            written: false,
            conditional: None,
        })
    }
}
