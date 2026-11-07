//! Checked executable implementations, separate from logical source visibility.
//!
//! Module imports and paired source predecessors bind immutable checked views.
//! Compiler dependency analysis may inspect their complete implementations;
//! logical elaboration and admission keep using the exported declarations.
use super::*;
use fln_env::extensions::{MergeSemantics, PayloadProvenance};
use std::sync::Arc;

#[derive(Debug, Clone)]
pub(crate) struct CheckedRuntimeImports {
    public: Environment,
    private: RuntimeEnvironment,
}

/// One public source command may depend on earlier hidden local bodies as well
/// as imported implementations. These checked predecessor snapshots supply only
/// advisory compiler dependency analysis, never logical elaboration or admission.
#[derive(Debug, Clone)]
struct CheckedSourceComputability {
    public: Environment,
    private: Environment,
    private_imports: Option<Arc<CheckedRuntimeImports>>,
}

#[derive(Debug, Clone)]
pub(crate) struct RuntimeEnvironment {
    pub(crate) environment: Environment,
    pub(crate) executable_opaques: Arc<BTreeSet<Name>>,
    pub(crate) runtime_initializers: Arc<BTreeSet<Name>>,
}

struct Meter {
    limits: IngressLimits,
    work: usize,
    bytes: usize,
}

impl Meter {
    fn work(&mut self, amount: usize) -> Result<(), IngressError> {
        self.work = self.work.saturating_add(amount);
        if self.work > self.limits.max_nodes {
            return Err(IngressError::ResourceLimit {
                resource: IngressResource::Nodes,
                limit: self.limits.max_nodes,
                observed: self.work,
            });
        }
        Ok(())
    }

    fn bytes(&mut self, bytes: usize) -> Result<(), IngressError> {
        self.bytes = self.bytes.saturating_add(bytes);
        if self.bytes > self.limits.max_literal_bytes {
            return Err(IngressError::ResourceLimit {
                resource: IngressResource::LiteralBytes,
                limit: self.limits.max_literal_bytes,
                observed: self.bytes,
            });
        }
        Ok(())
    }
}

fn unsupported(kind: &'static str) -> IngressError {
    IngressError::UnsupportedNode { kind }
}

impl Engine {
    pub(crate) fn computability_provider(
        &self,
    ) -> Option<fln_elab::source::scope::computability::ComputabilityProvider> {
        self.checked_runtime_imports.as_ref().map(|imports| {
            let provider: Arc<
                dyn fln_elab::source::scope::computability::ComputabilityEnvironment,
            > = imports.clone();
            fln_elab::source::scope::computability::ComputabilityProvider(provider)
        })
    }

    /// Bind the exact checked public/private predecessors for one source
    /// admission. The caller retains the public logical environment throughout
    /// elaboration; only dependency analysis may inspect hidden implementations.
    pub(crate) fn public_computability_provider(
        &self,
        private: &Engine,
    ) -> fln_elab::source::scope::computability::ComputabilityProvider {
        fln_elab::source::scope::computability::ComputabilityProvider(Arc::new(
            CheckedSourceComputability {
                public: self.environment.clone(),
                private: private.environment.clone(),
                private_imports: private.checked_runtime_imports.clone(),
            },
        ))
    }

    pub(crate) fn has_checked_runtime_imports(&self) -> bool {
        self.checked_runtime_imports.is_some()
    }

    /// Inspect a reached execution dependency in its complete checked view.
    /// Public module interfaces can hide definition and theorem bodies, so
    /// dependency checks such as `#eval`'s axiom walk must read the same private
    /// implementation that execution will use. This never changes the logical
    /// environment or grants a private name to source elaboration.
    ///
    /// Reuse the overlay's exact declaration-identity and collision rules on
    /// the reached name. Unrelated imported declarations need not be scanned
    /// again for every dependency query.
    pub(crate) fn execution_dependency(
        &self,
        name: &Name,
    ) -> Result<Option<&ConstantInfo>, IngressError> {
        let logical = self.environment.find(name);
        let Some(imports) = &self.checked_runtime_imports else {
            return Ok(logical);
        };
        let private = imports.private.environment.find(name);
        if let Some(imported) = imports.public.find(name) {
            let Some(logical) = logical else {
                return Err(unsupported("removed checked runtime import declaration"));
            };
            if !std::ptr::eq(imported, logical) {
                return Err(unsupported("changed checked runtime import declaration"));
            }
            return private
                .map(Some)
                .ok_or_else(|| unsupported("missing checked runtime import implementation"));
        }
        if logical.is_some() && private.is_some() {
            return Err(unsupported(
                "local declaration collides with a private runtime import",
            ));
        }
        Ok(logical.or(private))
    }

    /// `public_base` is the exact projected import prefix of `self`; `private`
    /// is the independently checked complete implementation of that same
    /// selected transitive closure. No receipt's unrelated roots belong here.
    pub(crate) fn with_checked_runtime_imports(
        mut self,
        public_base: Environment,
        private: &Engine,
    ) -> Self {
        self.checked_runtime_imports = Some(Arc::new(CheckedRuntimeImports {
            public: public_base,
            private: RuntimeEnvironment {
                environment: private.environment.clone(),
                executable_opaques: Arc::clone(&private.executable_opaques),
                runtime_initializers: Arc::clone(&private.runtime_initializers),
            },
        }));
        self
    }

    /// Overlay only subsequently checked local declarations and journal rows.
    /// Unchanged exported headers keep their checked private implementations;
    /// a local declaration colliding with a hidden import is never substituted.
    pub(crate) fn runtime_environment(
        &self,
        limits: IngressLimits,
    ) -> Result<RuntimeEnvironment, IngressError> {
        let Some(imports) = &self.checked_runtime_imports else {
            return Ok(RuntimeEnvironment {
                environment: self.environment.clone(),
                executable_opaques: Arc::clone(&self.executable_opaques),
                runtime_initializers: Arc::clone(&self.runtime_initializers),
            });
        };
        let mut meter = Meter {
            limits,
            work: 0,
            bytes: 0,
        };
        let mut result = imports.private.clone();
        result.environment = imports
            .overlay(&self.environment, &mut |work, bytes| {
                meter.work(work)?;
                meter.bytes(bytes)
            })
            .map_err(|error| match error {
                OverlayError::Budget(error) => error,
                OverlayError::Unsupported(kind) => unsupported(kind),
            })?;
        for name in self.executable_opaques.iter() {
            meter.work(1)?;
            if !result.executable_opaques.contains(name) {
                Arc::make_mut(&mut result.executable_opaques).insert(name.clone());
            }
        }
        for name in self.runtime_initializers.iter() {
            meter.work(1)?;
            if !result.runtime_initializers.contains(name) {
                Arc::make_mut(&mut result.runtime_initializers).insert(name.clone());
            }
        }
        Ok(result)
    }
}

enum OverlayError<E> {
    Budget(E),
    Unsupported(&'static str),
}

impl CheckedRuntimeImports {
    /// Shared by executable preparation and advisory compiler dependency checks.
    /// This returned view never replaces the source context's logical environment.
    fn overlay<E>(
        &self,
        logical: &Environment,
        charge: &mut dyn FnMut(usize, usize) -> Result<(), E>,
    ) -> Result<Environment, OverlayError<E>> {
        overlay_environment(&self.public, &self.private.environment, logical, charge)
    }
}

fn overlay_environment<E>(
    public: &Environment,
    private: &Environment,
    logical: &Environment,
    charge: &mut dyn FnMut(usize, usize) -> Result<(), E>,
) -> Result<Environment, OverlayError<E>> {
    let mut environment = private.clone();
    let mut retained = 0;
    for (name, declaration) in logical.constants() {
        charge(1, 0).map_err(OverlayError::Budget)?;
        if let Some(imported) = public.find(name) {
            // Ordinary immutable admission shares this exact declaration.
            // A rebuilt or replaced prefix needs a fresh checked import
            // binding; a digest does not authorize implementation reuse.
            if !std::ptr::eq(imported, declaration) {
                return Err(OverlayError::Unsupported(
                    "changed checked runtime import declaration",
                ));
            }
            retained += 1;
            continue;
        }
        if environment.contains(name) {
            return Err(OverlayError::Unsupported(
                "local declaration collides with a private runtime import",
            ));
        }
        let entry = logical.entry(name).ok_or_else(|| {
            OverlayError::Unsupported("missing checked local runtime declaration")
        })?;
        environment = environment.with_entry(entry).map_err(|_| {
            OverlayError::Unsupported("could not overlay checked local runtime declaration")
        })?;
    }
    if retained != public.len() {
        return Err(OverlayError::Unsupported(
            "removed checked runtime import declaration",
        ));
    }
    for (name, _) in public.extensions() {
        charge(1, 0).map_err(OverlayError::Budget)?;
        if logical.extension(name).is_none() {
            return Err(OverlayError::Unsupported(
                "removed checked runtime import journal",
            ));
        }
    }
    for (name, current) in logical.extensions() {
        charge(1, 0).map_err(OverlayError::Budget)?;
        let prior = public.extension(name);
        let base_len = prior.map_or(0, |state| state.len());
        if let Some(prior) = prior {
            if current.descriptor != prior.descriptor || current.len() < base_len {
                return Err(OverlayError::Unsupported(
                    "changed checked runtime import journal",
                ));
            }
            for (old, new) in prior.entries().zip(current.entries()) {
                charge(1, 0).map_err(OverlayError::Budget)?;
                if Arc::ptr_eq(&old.payload, &new.payload) {
                    continue;
                }
                charge(0, old.payload.len()).map_err(OverlayError::Budget)?;
                charge(0, new.payload.len()).map_err(OverlayError::Budget)?;
                if old != new {
                    return Err(OverlayError::Unsupported(
                        "rewritten checked runtime import metadata",
                    ));
                }
            }
        }
        if prior.is_some() && current.len() == base_len {
            continue;
        }
        if current.descriptor.merge != MergeSemantics::AppendOrdered
            || current.descriptor.provenance != PayloadProvenance::Understood
        {
            return Err(OverlayError::Unsupported(
                "runtime import journal is not native append-ordered data",
            ));
        }
        match environment.extension(name) {
            Some(private) if private.descriptor != current.descriptor => {
                return Err(OverlayError::Unsupported(
                    "runtime import journal descriptor conflict",
                ));
            }
            Some(_) => {}
            None => {
                environment = environment
                    .register_extension(current.descriptor.clone())
                    .map_err(|_| {
                        OverlayError::Unsupported("could not register local runtime journal")
                    })?;
            }
        }
        for entry in current.entries().skip(base_len) {
            charge(1, 0).map_err(OverlayError::Budget)?;
            charge(0, entry.payload.len()).map_err(OverlayError::Budget)?;
            environment = environment
                .push_extension_entry(name, Arc::clone(&entry.payload))
                .map_err(|_| {
                    OverlayError::Unsupported("could not append local runtime metadata")
                })?;
        }
    }
    Ok(environment)
}

impl fln_elab::source::scope::computability::ComputabilityEnvironment for CheckedRuntimeImports {
    fn environment(
        &self,
        logical: &Environment,
        charge: &mut dyn FnMut(usize) -> Result<(), fln_elab::NatDefinitionElabError>,
    ) -> Result<Environment, fln_elab::NatDefinitionElabError> {
        self.overlay(logical, &mut |work, bytes| {
            charge(work.saturating_add(bytes))
        })
        .map_err(|error| match error {
            OverlayError::Budget(error) => error,
            OverlayError::Unsupported(expected) => {
                fln_elab::NatDefinitionElabError::UnexpectedSyntax { expected }
            }
        })
    }
}

impl CheckedSourceComputability {
    fn overlay<E>(
        &self,
        logical: &Environment,
        charge: &mut dyn FnMut(usize, usize) -> Result<(), E>,
    ) -> Result<Environment, OverlayError<E>> {
        // The private source predecessor may itself expose only imported
        // headers. Recover that exact checked closure before adding local
        // implementations; never substitute an unrelated receipt's roots.
        let private = match &self.private_imports {
            Some(imports) => imports.overlay(&self.private, charge)?,
            None => self.private.clone(),
        };
        // Preserve the public predecessor's exact declarations and journal
        // prefix. Current checked candidates and compiler metadata suffixes
        // enter through the same guarded overlay used by runtime preparation.
        overlay_environment(&self.public, &private, logical, charge)
    }
}

impl fln_elab::source::scope::computability::ComputabilityEnvironment
    for CheckedSourceComputability
{
    fn environment(
        &self,
        logical: &Environment,
        charge: &mut dyn FnMut(usize) -> Result<(), fln_elab::NatDefinitionElabError>,
    ) -> Result<Environment, fln_elab::NatDefinitionElabError> {
        self.overlay(logical, &mut |work, bytes| {
            charge(work.saturating_add(bytes))
        })
        .map_err(|error| match error {
            OverlayError::Budget(error) => error,
            OverlayError::Unsupported(expected) => {
                fln_elab::NatDefinitionElabError::UnexpectedSyntax { expected }
            }
        })
    }
}
