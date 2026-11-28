//! Actual member identities are chosen before constructing any expression.
//! Renaming a completed term could capture an authored reference to an existing
//! public helper with the same user-facing spelling.
use super::*;
use fln_core::name::LeafView;
use std::collections::BTreeMap;

pub(super) struct MemberNames {
    record: Name,
    projections: BTreeMap<Name, Name>,
}

impl MemberNames {
    pub(super) fn new(record: Name) -> Self {
        Self {
            record,
            projections: BTreeMap::new(),
        }
    }

    pub(super) fn insert(&mut self, field: Name, projection: Name) {
        self.projections.insert(field, projection);
    }

    pub(super) fn projection(&self, field: &Name) -> Name {
        self.projections
            .get(field)
            .cloned()
            .unwrap_or_else(|| self.record.append_core(field))
    }

    pub(super) fn helper(&self, field: &Name, suffix: &str) -> Name {
        Name::str(self.projection(field), suffix)
    }
}

impl Context {
    /// Copied parent fields currently retain the parent's ordinary projection
    /// spelling. Until that path carries per-field visibility through copying,
    /// refuse a noncanonical projection anywhere in the ancestry instead of
    /// publishing a private parent field under a public child name.
    pub(super) fn check_record_parent_member_names(
        &mut self,
        inheritance: &parents::Inheritance,
    ) -> Result<(), NatDefinitionElabError> {
        if inheritance.direct.is_empty() {
            return Ok(());
        }
        let structures = crate::records::imported::ImportedStructures::read(&self.txn.env)
            .map_err(|error| failure(SourceInferenceError::Record(error)))?;
        let mut pending: Vec<_> = inheritance
            .direct
            .iter()
            .map(|(name, _, _)| name.clone())
            .collect();
        let mut seen = std::collections::BTreeSet::new();
        while let Some(parent) = pending.pop() {
            self.tick()?;
            if !seen.insert(parent.clone()) {
                continue;
            }
            let Some(structure) = structures.get(&parent) else {
                continue;
            };
            for field in &structure.fields {
                self.tick()?;
                if field.projection != parent.append_core(&field.name) {
                    return Err(NatDefinitionElabError::UnexpectedSyntax {
                        expected: "record inheritance with ordinary parent projection names",
                    });
                }
            }
            pending.extend(structure.parents.iter().map(|parent| parent.name.clone()));
        }
        Ok(())
    }

    /// Recover aliases only for this source module's generated private members.
    /// Preserve numeric hygiene components while removing precisely the checked
    /// private prefix; foreign private names never acquire local aliases.
    pub(super) fn record_private_members(
        &mut self,
        members: impl IntoIterator<Item = Name>,
    ) -> Result<Vec<(Name, Name)>, NatDefinitionElabError> {
        if self.source_scope.private_identity().is_none() {
            return Ok(Vec::new());
        }
        let prefix = self.source_scope.private_name(&Name::anonymous());
        let mut aliases = BTreeMap::new();
        for actual in members {
            self.tick()?;
            let mut cursor = actual.clone();
            let mut suffix = Vec::new();
            while cursor != prefix && !cursor.is_anonymous() {
                self.tick()?;
                suffix.push(cursor.clone());
                cursor = cursor.parent();
            }
            if cursor != prefix || suffix.is_empty() {
                continue;
            }
            let mut user = Name::anonymous();
            for component in suffix.iter().rev() {
                self.tick()?;
                user = match component.leaf_view() {
                    LeafView::Str(value) => Name::str(user, value),
                    LeafView::Num(value) if component.component_overflowed() => {
                        Name::num_overflowing(user, value)
                    }
                    LeafView::Num(value) => Name::num(user, value),
                    LeafView::Anonymous => return Err(failure(SourceInferenceError::Scope)),
                };
            }
            if let Some(previous) = aliases.insert(user, actual.clone())
                && previous != actual
            {
                return Err(failure(SourceInferenceError::Record(
                    crate::records::RecordError::DuplicateField,
                )));
            }
        }
        Ok(aliases.into_iter().collect())
    }
}
