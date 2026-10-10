//! Resolve admitted recursive definitions to their actual executable bodies.
//!
//! The pin's `Compiler.LCNF.getDeclInfo?` selects a `._unsafe_rec` sibling.
//! Structural and well-founded definitions have a safe logical definition;
//! partial definitions have a safe opaque inhabitant. Both may have an admitted
//! Partial executable companion. This bridge is confined to post-admission
//! codegen: type reduction and inert dictionaries keep their logical bodies.
use super::*;
use fln_core::name::LeafView;
use fln_env::constants::DefinitionSafety;

/// The logical half remains either a checked safe definition or a safe opaque.
/// A theorem, axiom, unsafe definition, or another Partial body cannot authorize
/// the executable companion, even when it has the expected spelling.
fn logical_interface(info: &ConstantInfo) -> Option<(&ConstantVal, &[Name])> {
    match info {
        ConstantInfo::Defn(value) if value.safety == DefinitionSafety::Safe => {
            Some((&value.base, &value.all))
        }
        ConstantInfo::Opaque(value) if !value.is_unsafe => Some((&value.base, &value.all)),
        _ => None,
    }
}

impl Preparation<'_> {
    pub(crate) fn executable_definition(
        &mut self,
        requested: &Name,
    ) -> Result<Option<DefinitionVal>, IngressError> {
        let replacement = self.implementation_target(requested)?;
        let requested = replacement.as_ref().unwrap_or(requested);
        self.recursive_definition(requested)
    }

    /// Validate companion linkage without following any executable replacement.
    /// Keeping this separate also makes parent-name normalization in attribute
    /// lookup iterative, including cycles involving a companion's spelling.
    pub(super) fn recursive_definition(
        &mut self,
        requested: &Name,
    ) -> Result<Option<DefinitionVal>, IngressError> {
        self.tick()?;
        let environment = self.environment;
        let (logical, fallback) = match environment.find(requested) {
            Some(ConstantInfo::Defn(definition)) if definition.safety == DefinitionSafety::Safe => {
                (requested.clone(), Some(definition))
            }
            Some(ConstantInfo::Defn(definition))
                if definition.safety == DefinitionSafety::Partial
                    && matches!(requested.leaf_view(), LeafView::Str("_unsafe_rec")) =>
            {
                (requested.parent(), None)
            }
            Some(ConstantInfo::Opaque(opaque)) if !opaque.is_unsafe => (requested.clone(), None),
            Some(_) => return Ok(None),
            None => return Ok(self.specialized_definition(requested)),
        };
        let implementation_name = Name::str(logical.clone(), "_unsafe_rec");
        let Some(candidate) = environment.find(&implementation_name) else {
            // An ordinary safe definition needs no executable companion. Once
            // one is present, failed linkage must not silently run its logical
            // body instead of the implementation the pin would select.
            return Ok(fallback.cloned());
        };
        let ConstantInfo::Defn(implementation) = candidate else {
            return Ok(None);
        };
        let Some((_, group)) = environment.find(&logical).and_then(logical_interface) else {
            return Ok(None);
        };
        if group.len() > self.limits.fir.max_functions {
            return Err(IngressError::ResourceLimit {
                resource: IngressResource::ProgramTables,
                limit: self.limits.fir.max_functions,
                observed: group.len(),
            });
        }
        if group.is_empty() || !group.contains(&logical) {
            return Ok(None);
        }
        let group = group.to_vec();
        // Matching a suffix is not authority. Every member must be an admitted
        // safe logical half paired with an admitted Partial definition, with
        // the same exact telescope, universes, and complete mutual group.
        for member in &group {
            self.tick()?;
            let Some((logical_base, logical_group)) =
                environment.find(member).and_then(logical_interface)
            else {
                return Ok(None);
            };
            let executable_name = Name::str(member.clone(), "_unsafe_rec");
            let Some(ConstantInfo::Defn(executable_member)) = environment.find(&executable_name)
            else {
                return Ok(None);
            };
            if logical_group != group.as_slice()
                || executable_member.safety != DefinitionSafety::Partial
                || executable_member.base.type_ != logical_base.type_
                || executable_member.base.level_params != logical_base.level_params
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
        Ok(Some(implementation.clone()))
    }

    pub(super) fn has_recursive_companion(&mut self, name: &Name) -> Result<bool, IngressError> {
        self.tick()?;
        Ok(self
            .environment
            .contains(&Name::str(name.clone(), "_unsafe_rec")))
    }

    /// The pin restores logical names inside companion bodies before looking
    /// up attributes. Only a fully linked Partial declaration permits that
    /// normalization here; an arbitrary name suffix supplies no authority.
    pub(super) fn recursive_parent(&mut self, name: &Name) -> Result<Option<Name>, IngressError> {
        let Some(parent) = self.recursive_parent_candidate(name) else {
            return Ok(None);
        };
        let Some(definition) = self.recursive_definition(name)? else {
            return Err(unsupported("invalid recursive executable companion"));
        };
        if definition.base.name != *name {
            return Err(unsupported("invalid recursive executable companion"));
        }
        Ok(Some(parent))
    }

    /// A cheap lookup filter only. Callers must use `recursive_parent` before
    /// this proposed parent can select any executable attribute or declaration.
    pub(super) fn recursive_parent_candidate(&self, name: &Name) -> Option<Name> {
        (matches!(name.leaf_view(), LeafView::Str("_unsafe_rec"))
            && matches!(self.environment.find(name), Some(ConstantInfo::Defn(value))
                if value.safety == DefinitionSafety::Partial))
        .then(|| name.parent())
    }

    /// Explicit native implementations belong to the logical declaration and
    /// precede its companion, as in the pin's ToDecl. Unknown externs never
    /// disappear when an executable head acquires a different name.
    fn companion_has_native_parent(&mut self, logical: &Name) -> Result<bool, IngressError> {
        source_intrinsics::check_selected_extern_attribute(
            self.environment,
            logical,
            &mut self.externs,
            &mut self.visited,
            self.limits,
        )?;
        if !self
            .externs
            .as_ref()
            .is_some_and(|table| table.get(logical).is_some())
        {
            return Ok(false);
        }
        let native = self.native_intrinsic_binding(logical)?.is_some()
            || match source_intrinsics::io::fs::Operation::from_name(logical) {
                Some(operation) => source_intrinsics::io::fs::primitive_matches(
                    self.environment,
                    operation,
                    &mut self.externs,
                    &mut self.visited,
                    self.limits,
                )?,
                None => false,
            };
        if !native {
            return Err(unsupported(
                "recursive companion extern has no supported native implementation",
            ));
        }
        Ok(true)
    }

    /// Select before executable inlining, while retaining the source telescope.
    /// A direct companion reference stays stable unless its logical parent's
    /// native extern has precedence; ordinary parent references select the
    /// checked companion exactly once.
    pub(super) fn recursive_companion_target(
        &mut self,
        requested: &Name,
    ) -> Result<Option<Name>, IngressError> {
        if let Some(parent) = self.recursive_parent(requested)? {
            return Ok(self.companion_has_native_parent(&parent)?.then_some(parent));
        }
        if self
            .environment
            .find(requested)
            .and_then(logical_interface)
            .is_none()
            || !self.has_recursive_companion(requested)?
        {
            return Ok(None);
        }
        let Some(implementation) = self.recursive_definition(requested)? else {
            return Err(unsupported("invalid recursive executable companion"));
        };
        if self.companion_has_native_parent(requested)? {
            return Ok(None);
        }
        Ok(Some(implementation.base.name))
    }
}

#[cfg(test)]
mod tests;

#[cfg(test)]
mod total_tests;
