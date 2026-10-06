//! Only class parent projections are registered as instances by `extends`.
//!
//! Pinned `Lean/Elab/Structure.lean::addParentInstances` registers the existing
//! projection from a child class to its parent class. It does not synthesize
//! `Coe` or `CoeDep` dictionaries for values of structures or classes. Those
//! conversions require ordinary user instances, just like other coercions.
use super::*;

impl Context {
    pub(in crate::source::record) fn record_parent_instances(
        &mut self,
        spec: &RecordSpec,
        parents: &[RecordParent],
    ) -> Result<Vec<Name>, NatDefinitionElabError> {
        let mut output = Vec::new();
        if !spec.is_class {
            return Ok(output);
        }
        let registry = self.instance_registry()?;
        for parent in parents {
            self.tick()?;
            if parent.record != spec.name {
                return Err(failure(SourceInferenceError::Scope));
            }
            let field = spec
                .fields
                .get(parent.field as usize)
                .ok_or_else(|| failure(SourceInferenceError::Scope))?;
            if registry.is_class(&parent.parent) {
                output.push(spec.name.append_core(&field.user_name));
            }
        }
        Ok(output)
    }
}
