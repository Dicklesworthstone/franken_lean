//! Resolve admitted partial definitions to their actual executable bodies.
//!
//! The pin's `Compiler.LCNF.getDeclInfo?` selects a `._unsafe_rec` sibling.
//! A partial definition's logical opaque body is only an inhabitant and must
//! never run in its place. This bridge is confined to post-admission codegen:
//! type reduction and inert dictionary evaluation retain their safe-only path.
use super::*;
use fln_core::name::LeafView;
use fln_env::constants::DefinitionSafety;

impl Preparation<'_> {
    pub(crate) fn executable_definition(
        &mut self,
        requested: &Name,
    ) -> Result<Option<DefinitionVal>, IngressError> {
        self.tick()?;
        let replacement = self.implementation_target(requested)?;
        let requested = replacement.as_ref().unwrap_or(requested);
        let logical = match self.environment.find(requested) {
            Some(ConstantInfo::Defn(definition)) if definition.safety == DefinitionSafety::Safe => {
                return Ok(Some(definition.clone()));
            }
            Some(ConstantInfo::Defn(definition))
                if definition.safety == DefinitionSafety::Partial
                    && matches!(requested.leaf_view(), LeafView::Str("_unsafe_rec")) =>
            {
                requested.parent()
            }
            Some(ConstantInfo::Opaque(opaque)) if !opaque.is_unsafe => requested.clone(),
            Some(_) => return Ok(None),
            None => return Ok(self.specialized_definition(requested)),
        };
        let Some(ConstantInfo::Opaque(opaque)) = self.environment.find(&logical) else {
            return Ok(None);
        };
        if opaque.is_unsafe || opaque.all.is_empty() || !opaque.all.contains(&logical) {
            return Ok(None);
        }
        let implementation_name = Name::str(logical.clone(), "_unsafe_rec");
        let Some(ConstantInfo::Defn(implementation)) = self.environment.find(&implementation_name)
        else {
            return Ok(None);
        };
        let group = opaque.all.clone();
        let implementation = implementation.clone();
        if group.len() > self.limits.fir.max_functions {
            return Err(IngressError::ResourceLimit {
                resource: IngressResource::ProgramTables,
                limit: self.limits.fir.max_functions,
                observed: group.len(),
            });
        }
        // Matching a suffix is not authority. Every member must be an admitted
        // safe opaque paired with an admitted Partial definition, with the same
        // exact telescope, universe parameters, and complete mutual group.
        for member in &group {
            self.tick()?;
            let Some(ConstantInfo::Opaque(logical_member)) = self.environment.find(member) else {
                return Ok(None);
            };
            let executable_name = Name::str(member.clone(), "_unsafe_rec");
            let Some(ConstantInfo::Defn(executable_member)) =
                self.environment.find(&executable_name)
            else {
                return Ok(None);
            };
            if logical_member.is_unsafe
                || logical_member.all != group
                || executable_member.safety != DefinitionSafety::Partial
                || executable_member.base.type_ != logical_member.base.type_
                || executable_member.base.level_params != logical_member.base.level_params
                || executable_member.all.len() != group.len()
            {
                return Ok(None);
            }
            for (actual, logical_peer) in executable_member.all.iter().zip(&group) {
                self.tick()?;
                if actual != &Name::str(logical_peer.clone(), "_unsafe_rec") {
                    return Ok(None);
                }
            }
        }
        Ok(Some(implementation))
    }
}

#[cfg(test)]
mod tests;
