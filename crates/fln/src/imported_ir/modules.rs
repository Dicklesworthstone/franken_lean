//! Resolve a transitive module-artifact closure before selecting executable IR.
//!
//! The `.olean` import table is discovery data, not execution authority. This
//! loader neither admits its declarations nor replays extensions/initializers.
//! Only [`super::compile`] with a verified partition can authorize the selected
//! code. In particular, a module's name never classifies its declarations.

use super::{IrModule, Name};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

/// A module's public import metadata and optional compiled-code companion.
/// Missing IR is recorded explicitly; it does not fabricate executable bodies.
#[derive(Debug, Clone)]
pub struct ModuleArtifacts {
    pub olean: Vec<u8>,
    pub ir: Option<Vec<u8>>,
}

/// Cumulative bounds for one complete load, independent of execution budgets.
#[derive(Debug, Clone, Copy)]
pub struct ModuleLoadLimits {
    pub max_modules: usize,
    pub max_bytes: usize,
    pub max_imports: usize,
    pub max_declarations: usize,
}

impl Default for ModuleLoadLimits {
    fn default() -> Self {
        Self {
            max_modules: 4096,
            max_bytes: 256 * 1024 * 1024,
            max_imports: 1 << 20,
            max_declarations: 1 << 20,
        }
    }
}

#[derive(Debug)]
pub enum ModuleLoadError {
    NoRoots,
    MissingModule(Name),
    ImportCycle(Name),
    Resolve {
        module: Name,
        detail: String,
    },
    Decode {
        module: Name,
        artifact: &'static str,
        detail: String,
        resource: bool,
    },
    Limit(&'static str),
}

impl ModuleLoadError {
    pub fn is_resource(&self) -> bool {
        matches!(self, Self::Limit(_) | Self::Decode { resource: true, .. })
    }
}

impl fmt::Display for ModuleLoadError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NoRoots => f.write_str("IR module loading requires a root module"),
            Self::MissingModule(name) => {
                write!(f, "missing IR import module {}", name.to_display_string())
            }
            Self::ImportCycle(name) => {
                write!(f, "IR import cycle through {}", name.to_display_string())
            }
            Self::Resolve { module, detail } => {
                write!(
                    f,
                    "resolving IR module {}: {detail}",
                    module.to_display_string()
                )
            }
            Self::Decode {
                module,
                artifact,
                detail,
                ..
            } => write!(
                f,
                "reading {artifact} for IR module {}: {detail}",
                module.to_display_string()
            ),
            Self::Limit(resource) => write!(f, "IR module loading exhausted {resource}"),
        }
    }
}

impl std::error::Error for ModuleLoadError {}

/// A fully loaded, structurally decoded candidate closure, NOT an admission.
/// Names and code are in the same structural-name order, independent of root
/// order, import order and diamond-shaped sharing in the dependency graph.
#[derive(Debug)]
pub struct LoadedModules {
    names: Vec<Name>,
    modules: Vec<IrModule>,
    missing_ir: Vec<Name>,
    bytes_read: usize,
}

impl LoadedModules {
    pub fn module_names(&self) -> &[Name] {
        &self.names
    }

    pub fn modules(&self) -> &[IrModule] {
        &self.modules
    }

    pub fn missing_ir_modules(&self) -> &[Name] {
        &self.missing_ir
    }

    pub fn bytes_read(&self) -> usize {
        self.bytes_read
    }

    pub fn into_modules(self) -> Vec<IrModule> {
        self.modules
    }
}

fn charge(
    total: &mut usize,
    amount: usize,
    limit: usize,
    what: &'static str,
) -> Result<(), ModuleLoadError> {
    *total = total
        .checked_add(amount)
        .ok_or(ModuleLoadError::Limit(what))?;
    if *total > limit {
        return Err(ModuleLoadError::Limit(what));
    }
    Ok(())
}

/// Load every transitive import once, using the actual public `.olean` table.
///
/// `resolve` receives the *remaining cumulative byte allowance* for both
/// companions. File/network implementations must enforce it while reading,
/// before allocating an entire unbounded artifact. Returned sizes are checked
/// again here before either decoder runs. `None` means the module is absent;
/// an absent `.ir` alone is represented by [`ModuleArtifacts::ir`] instead.
///
/// The traversal is iterative, detects cycles, charges duplicate import edges,
/// and returns no partial closure after any failure. No resolver, artifact path
/// or imported declaration can create a verified execution partition here.
pub fn load(
    roots: &[Name],
    limits: ModuleLoadLimits,
    mut resolve: impl FnMut(&Name, usize) -> Result<Option<ModuleArtifacts>, ModuleLoadError>,
) -> Result<LoadedModules, ModuleLoadError> {
    if roots.is_empty() {
        return Err(ModuleLoadError::NoRoots);
    }
    if roots.len() > limits.max_modules {
        return Err(ModuleLoadError::Limit("root modules"));
    }
    enum Work {
        Enter(Name),
        Leave(Name),
    }
    let roots: BTreeSet<_> = roots.iter().cloned().collect();
    let mut pending: Vec<_> = roots.into_iter().rev().map(Work::Enter).collect();
    let mut active = BTreeSet::new();
    let mut modules = BTreeMap::new();
    let mut missing_ir = BTreeSet::new();
    let mut bytes_read = 0usize;
    let mut imports_read = 0usize;
    let mut declarations_read = 0usize;
    while let Some(work) = pending.pop() {
        let name = match work {
            Work::Leave(name) => {
                active.remove(&name);
                continue;
            }
            Work::Enter(name) => name,
        };
        if active.contains(&name) {
            return Err(ModuleLoadError::ImportCycle(name));
        }
        if modules.contains_key(&name) {
            continue;
        }
        if modules.len() >= limits.max_modules {
            return Err(ModuleLoadError::Limit("modules"));
        }
        let remaining = limits.max_bytes - bytes_read;
        let artifacts = resolve(&name, remaining)?
            .ok_or_else(|| ModuleLoadError::MissingModule(name.clone()))?;
        charge(
            &mut bytes_read,
            artifacts.olean.len(),
            limits.max_bytes,
            "artifact bytes",
        )?;
        charge(
            &mut bytes_read,
            artifacts.ir.as_ref().map_or(0, Vec::len),
            limits.max_bytes,
            "artifact bytes",
        )?;
        let imports = crate::olean_module_imports(
            &artifacts.olean,
            crate::OleanDecodeLimits::new(artifacts.olean.len()),
        )
        .map_err(|error| ModuleLoadError::Decode {
            module: name.clone(),
            artifact: ".olean import table",
            detail: error.to_string(),
            resource: error.is_resource_exhaustion(),
        })?;
        charge(
            &mut imports_read,
            imports.len(),
            limits.max_imports,
            "import edges",
        )?;
        let module = match artifacts.ir {
            Some(bytes) => crate::decode_ir_artifact(&bytes, bytes.len()).map_err(|error| {
                ModuleLoadError::Decode {
                    module: name.clone(),
                    artifact: ".ir code",
                    detail: error.to_string(),
                    resource: error.is_resource(),
                }
            })?,
            None => {
                missing_ir.insert(name.clone());
                IrModule::default()
            }
        };
        charge(
            &mut declarations_read,
            module
                .decls
                .len()
                .checked_add(module.initializers.len())
                .ok_or(ModuleLoadError::Limit("IR declarations and initializers"))?,
            limits.max_declarations,
            "declarations",
        )?;
        modules.insert(name.clone(), module);
        active.insert(name.clone());
        pending.push(Work::Leave(name));
        // Sort only discovery, never statements or declaration bodies. Repeated
        // edges were charged above even though their target is loaded once.
        let imports: BTreeSet<_> = imports.into_iter().collect();
        pending.extend(imports.into_iter().rev().map(Work::Enter));
    }
    let (names, modules) = modules.into_iter().unzip();
    Ok(LoadedModules {
        names,
        modules,
        missing_ir: missing_ir.into_iter().collect(),
        bytes_read,
    })
}

#[cfg(test)]
mod tests;
