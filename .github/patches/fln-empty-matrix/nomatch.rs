//! Validate every discriminant before empty-matrix elaboration.
use super::*;

impl Context {
    pub(in crate::source) fn nomatch_discriminants<'a>(
        &mut self,
        syntax: &'a Syntax,
    ) -> Result<&'a [Syntax], NatDefinitionElabError> {
        self.tick()?;
        let parts = expect_node(
            syntax, &parser_kind(&["Term", "nomatch"]), 2, "empty match",
        )?;
        expect_atom(&parts[0], "nomatch", "empty match keyword")?;
        let items = expect_null_args(&parts[1], "empty match discriminants")?;
        if items.is_empty() || items.len() % 2 == 0 {
            return Err(error(MatchError::InvalidPattern));
        }
        for separator in items.iter().skip(1).step_by(2) {
            self.tick()?;
            expect_atom(separator, ",", "empty match separator")?;
        }
        Ok(items)
    }
}
