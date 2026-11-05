//! Checked implementation availability at the source compiler boundary.
//!
//! Modern imports can expose a logical axiom while retaining checked executable
//! code. Only compiler dependency analysis may borrow that implementation view.
//! The provider does not grant name resolution, reduction, instance search or
//! declaration admission access to private constants, and it does not authorize
//! native execution. The runtime independently verifies its own capabilities.

use std::sync::Arc;

use fln_env::environment::Environment;

use crate::NatDefinitionElabError;

/// The embedding engine's exact checked import implementation and local suffix.
///
/// `logical` is the current transaction, including speculative declarations and
/// deferred noncomputable tags. Implementations must authenticate their retained
/// public prefix before overlaying its checked private implementation, preserve
/// current declaration and metadata changes, refuse collisions, and charge all
/// traversal and replay through `charge`. They must never use a metadata-only
/// validation snapshot as evidence that executable code exists.
pub trait ComputabilityEnvironment: Send + Sync {
    fn environment(
        &self,
        logical: &Environment,
        charge: &mut dyn FnMut(usize) -> Result<(), NatDefinitionElabError>,
    ) -> Result<Environment, NatDefinitionElabError>;
}

/// Per-engine plumbing carried by source scopes, never exported into an artifact.
#[derive(Clone)]
pub struct ComputabilityProvider(pub Arc<dyn ComputabilityEnvironment>);

impl std::fmt::Debug for ComputabilityProvider {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("ComputabilityProvider")
    }
}

impl PartialEq for ComputabilityProvider {
    fn eq(&self, other: &Self) -> bool {
        // Unlike optional proof evaluators, losing this provider changes
        // ordinary definition acceptance. SourceScope therefore includes it in
        // equality so its default-scope fast path cannot discard the import.
        Arc::ptr_eq(&self.0, &other.0)
    }
}

impl Eq for ComputabilityProvider {}
