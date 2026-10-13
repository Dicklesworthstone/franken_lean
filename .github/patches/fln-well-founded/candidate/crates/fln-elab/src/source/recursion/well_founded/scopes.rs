//! Lexical cache boundaries for nullary Boolean branches. Such branches have
//! no constructor fields to distinguish their local contexts. Private tokens
//! express ancestry without introducing artificial proof or term binders.
use super::*;

impl Context {
    pub(in crate::source) fn well_founded_branch_depth(&self) -> Option<usize> {
        self.well_founded
            .as_ref()
            .filter(|state| !state.proving)
            .map(|state| state.branch_scopes.len())
    }

    pub(in crate::source) fn enter_well_founded_branch(
        &mut self,
        depth: usize,
    ) -> Result<(), NatDefinitionElabError> {
        if self.well_founded_branch_depth() != Some(depth) {
            return Err(failure(SourceInferenceError::Scope));
        }
        let token = self.fresh_name()?;
        self.well_founded
            .as_mut()
            .expect("active well-founded branch")
            .branch_scopes
            .push(token);
        Ok(())
    }

    pub(in crate::source) fn leave_well_founded_branch(
        &mut self,
        depth: usize,
    ) -> Result<(), NatDefinitionElabError> {
        self.tick()?;
        if depth.checked_add(1) != self.well_founded_branch_depth() {
            return Err(failure(SourceInferenceError::Scope));
        }
        self.well_founded
            .as_mut()
            .expect("active well-founded branch")
            .branch_scopes
            .truncate(depth);
        Ok(())
    }

    /// A globally minted token occurs on the active stack exactly when its
    /// branch is the current scope or an ancestor. An outside call can be
    /// reused inside a branch; sibling and expired branch calls cannot escape.
    pub(super) fn well_founded_cached_scope(
        &mut self,
        token: Option<&Name>,
    ) -> Result<bool, NatDefinitionElabError> {
        let Some(token) = token else {
            return Ok(true);
        };
        let depth = self
            .well_founded_branch_depth()
            .ok_or_else(|| failure(SourceInferenceError::Scope))?;
        for index in (0..depth).rev() {
            self.tick()?;
            if self
                .well_founded
                .as_ref()
                .expect("active well-founded call")
                .branch_scopes[index]
                == *token
            {
                return Ok(true);
            }
        }
        Ok(false)
    }
}
