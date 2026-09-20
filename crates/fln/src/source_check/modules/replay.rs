use super::*;
use fln_env::extensions::{ExtensionDescriptor, MergeSemantics, PayloadProvenance};
use std::sync::Arc;

struct ExtensionSuffix {
    descriptor: ExtensionDescriptor,
    entries: Vec<Arc<[u8]>>,
}

/// Only this module's successful ordinary source checker can construct an export.
/// No public API accepts a caller-authored declaration or metadata inventory here.
pub(super) struct Export {
    pub(super) declarations: Vec<Declaration>,
    extensions: Vec<ExtensionSuffix>,
}
fn extension_error(
    module: &Name,
    extension: &Name,
    reason: &'static str,
) -> SourceModuleCheckError {
    SourceModuleCheckError::Extension {
        module: module.clone(),
        extension: extension.clone(),
        reason,
    }
}
impl Export {
    pub(super) fn capture(
        module: &Name,
        base: &Environment,
        result: &Environment,
        declarations: Vec<Declaration>,
        meter: &mut Meter,
    ) -> Result<Self, SourceModuleCheckError> {
        meter.work(declarations.len())?;
        for (name, _) in base.extensions() {
            meter.work(1)?;
            if result.extension(name).is_none() {
                return Err(extension_error(
                    module,
                    name,
                    "source checking removed an imported extension",
                ));
            }
        }
        let mut extensions = Vec::new();
        for (name, state) in result.extensions() {
            meter.work(1)?;
            let prior = base.extension(name);
            let base_len = prior.map_or(0, |state| state.len());
            if let Some(prior) = prior {
                if state.descriptor != prior.descriptor || state.len() < base_len {
                    return Err(extension_error(
                        module,
                        name,
                        "source checking replaced an imported extension",
                    ));
                }
                // Equality is the exact payload prefix, never a digest-only claim.
                for (old, new) in prior.entries().zip(state.entries()) {
                    meter.work(1)?;
                    meter.bytes(old.payload.len())?;
                    meter.bytes(new.payload.len())?;
                    if old != new {
                        return Err(extension_error(
                            module,
                            name,
                            "source checking rewrote imported metadata",
                        ));
                    }
                }
            }
            if prior.is_some() && state.len() == base_len {
                continue;
            }
            if state.descriptor.merge != MergeSemantics::AppendOrdered
                || state.descriptor.provenance != PayloadProvenance::Understood
            {
                return Err(extension_error(
                    module,
                    name,
                    "extension is not native append-ordered import data",
                ));
            }
            let mut entries = Vec::new();
            for entry in state.entries().skip(base_len) {
                meter.work(1)?;
                meter.bytes(entry.payload.len())?;
                entries.push(Arc::clone(&entry.payload));
            }
            extensions.push(ExtensionSuffix {
                descriptor: state.descriptor.clone(),
                entries,
            });
        }
        Ok(Self {
            declarations,
            extensions,
        })
    }

    pub(super) fn replay(
        &self,
        mut engine: Engine,
        module: &Name,
        options: &KVMap,
        meter: &mut Meter,
        cancellation: Option<&dyn CancellationProbe>,
    ) -> Result<Outcome<Engine>, SourceModuleCheckError> {
        for declaration in &self.declarations {
            meter.work(1)?;
            if cancellation.is_some_and(CancellationProbe::is_cancelled) {
                return Ok(Outcome::Inconclusive(Inconclusive::cancelled(
                    "source-modules/replay-declaration",
                )));
            }
            engine = match engine
                .admit_declaration(declaration.clone(), options, meter.limits.source.admission)
                .map_err(|error| SourceModuleCheckError::Replay {
                    module: module.clone(),
                    error: Box::new(error.into()),
                })? {
                Outcome::Complete(admitted) => admitted.engine,
                Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
                Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
            };
        }
        for suffix in &self.extensions {
            meter.work(1)?;
            let name = &suffix.descriptor.name;
            match engine.environment.extension(name) {
                Some(existing) if existing.descriptor != suffix.descriptor => {
                    return Err(extension_error(
                        module,
                        name,
                        "import extension descriptor conflict",
                    ));
                }
                Some(_) => {}
                None => {
                    engine.environment = engine
                        .environment
                        .register_extension(suffix.descriptor.clone())
                        .map_err(|_| {
                            extension_error(module, name, "could not register imported extension")
                        })?;
                }
            }
            for entry in &suffix.entries {
                meter.work(1)?;
                meter.bytes(entry.len())?;
                if cancellation.is_some_and(CancellationProbe::is_cancelled) {
                    return Ok(Outcome::Inconclusive(Inconclusive::cancelled(
                        "source-modules/replay-extension",
                    )));
                }
                engine.environment = engine
                    .environment
                    .push_extension_entry(name, Arc::clone(entry))
                    .map_err(|_| {
                        extension_error(module, name, "could not replay imported extension")
                    })?;
            }
        }
        Ok(Outcome::Complete(engine))
    }
}
