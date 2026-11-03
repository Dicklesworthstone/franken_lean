//! Closed parser descriptions from the same artifacts that passed admission.
//!
//! The journal supplies registration order and scope; checked declarations
//! supply data, never executable parser closures. Every selected row is prepared
//! before a grammar is published. A source module then projects this immutable
//! product to its own dependency order and rechecks its declaration bindings.

use crate::{CheckedOleanModule, Engine, Environment};
use fln_core::expr::{Expr, ExprNode};
use fln_core::name::Name;
use fln_env::constants::{ConstantInfo, DefinitionSafety};
use fln_olean::region::OpaqueExtensionBlock;
use fln_olean::source_extensions::{DecodeError, DecodeLimits, parsers};
use fln_parse::extensions::{ImportedSyntaxEntry, ImportedSyntaxModule, SyntaxDecl};
use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

mod data;
mod descriptions;

#[cfg(test)]
mod reference;

#[cfg(test)]
mod tests;

#[cfg(test)]
#[path = "../../fln-olean/src/source_extension_format.rs"]
pub(crate) mod test_wire;

#[cfg(test)]
pub(crate) use data::tests::fixture_declarations;

/// Complete selected journals, in dependency-first artifact replay order.
pub struct ParserRegistrationModule<'a> {
    pub checked: &'a CheckedOleanModule,
    pub extensions: &'a [OpaqueExtensionBlock],
}

/// All allowances are cumulative across the supplied artifact closure, except
/// the depth ceiling. Data reduction performs only native delta, beta, zeta and
/// structure projection; it has no VM, recursor or executable parser fallback.
#[derive(Debug, Clone, Copy)]
pub struct ParserRegistryLimits {
    pub max_modules: usize,
    pub max_declarations: usize,
    pub max_steps: usize,
    pub max_depth: usize,
    pub max_bytes: usize,
    pub max_description_nodes: usize,
    pub metadata: DecodeLimits,
}

impl Default for ParserRegistryLimits {
    fn default() -> Self {
        Self {
            max_modules: 4096,
            max_declarations: 1 << 20,
            max_steps: 1 << 22,
            max_depth: 64,
            max_bytes: 16 << 20,
            max_description_nodes: 1 << 18,
            metadata: DecodeLimits::default(),
        }
    }
}

#[derive(Debug)]
pub enum ParserRegistrationError {
    Limit(&'static str),
    DuplicateModule(Name),
    ImportOrder {
        module: Name,
        dependency: Name,
    },
    MissingImport {
        module: Name,
        dependency: Name,
    },
    MissingPrivateJournal(Name),
    Decode {
        module: Name,
        error: DecodeError,
    },
    Owner {
        module: Name,
        declaration: Name,
        reason: &'static str,
    },
    Description {
        module: Name,
        declaration: Name,
        reason: &'static str,
    },
}

impl ParserRegistrationError {
    pub fn is_resource(&self) -> bool {
        matches!(self, Self::Limit(_))
            || matches!(self, Self::Decode { error, .. } if error.is_resource())
    }
}

impl std::fmt::Display for ParserRegistrationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Limit(resource) => write!(f, "imported parser preparation exhausted {resource}"),
            Self::DuplicateModule(module) => {
                write!(f, "duplicate parser module {}", module.to_display_string())
            }
            Self::ImportOrder { module, dependency } => write!(
                f,
                "parser module {} precedes dependency {}",
                module.to_display_string(),
                dependency.to_display_string()
            ),
            Self::MissingImport { module, dependency } => write!(
                f,
                "parser module {} is missing retained import {}",
                module.to_display_string(),
                dependency.to_display_string()
            ),
            Self::MissingPrivateJournal(module) => write!(
                f,
                "parser module {} requires its complete private journal",
                module.to_display_string()
            ),
            Self::Decode { module, error } => write!(
                f,
                "parser metadata in {}: {error}",
                module.to_display_string()
            ),
            Self::Owner {
                module,
                declaration,
                reason,
            } => write!(
                f,
                "parser owner {} in {}: {reason}",
                declaration.to_display_string(),
                module.to_display_string()
            ),
            Self::Description {
                module,
                declaration,
                reason,
            } => write!(
                f,
                "parser description {} in {}: {reason}",
                declaration.to_display_string(),
                module.to_display_string()
            ),
        }
    }
}

impl std::error::Error for ParserRegistrationError {}

fn name(label: &str) -> Name {
    Name::from_components(label.split('.'))
}

fn owner_error(module: &Name, declaration: &Name, reason: &'static str) -> ParserRegistrationError {
    ParserRegistrationError::Owner {
        module: module.clone(),
        declaration: declaration.clone(),
        reason,
    }
}

fn data_error(
    module: &Name,
    declaration: &Name,
    error: data::DataError,
) -> ParserRegistrationError {
    match error {
        data::DataError::Resource(resource) => ParserRegistrationError::Limit(resource),
        data::DataError::Missing(missing) => owner_error(
            module,
            &missing,
            "description dependency has no admitted declaration",
        ),
        data::DataError::NotPermitted(missing) => owner_error(
            module,
            &missing,
            "description dependency is outside its checked import closure",
        ),
        data::DataError::Unsupported(reason) => ParserRegistrationError::Description {
            module: module.clone(),
            declaration: declaration.clone(),
            reason,
        },
    }
}

#[derive(Debug, Clone)]
struct PreparedModule {
    imports: Vec<Name>,
    syntax: ImportedSyntaxModule,
    /// Includes literal helpers and constructor interfaces, not just the parser
    /// owner. Rebinding any one of them invalidates the prepared product.
    bindings: BTreeMap<Name, ConstantInfo>,
}

/// Immutable checked descriptions; no source scope activation is retained here.
#[derive(Debug, Clone)]
pub struct RegisteredParsers {
    modules: Arc<BTreeMap<Name, PreparedModule>>,
}

impl RegisteredParsers {
    /// Reconstruct the complete selected journals. Owners must be definitions
    /// in the exact checked module named by the row; references may use only
    /// that module's actual checked dependencies and the admitted base.
    pub fn prepare(
        ordered_modules: &[ParserRegistrationModule<'_>],
        admitted: &Environment,
        limits: ParserRegistryLimits,
    ) -> Result<Self, ParserRegistrationError> {
        if ordered_modules.len() > limits.max_modules {
            return Err(ParserRegistrationError::Limit("modules"));
        }
        let mut positions = BTreeMap::new();
        let mut owners = BTreeMap::new();
        let mut remaining = data::DataLimits {
            max_steps: limits.max_steps,
            max_depth: limits.max_depth,
            max_bytes: limits.max_bytes,
        };
        for (index, input) in ordered_modules.iter().enumerate() {
            let checked = input.checked;
            if positions.insert(checked.name.clone(), index).is_some() {
                return Err(ParserRegistrationError::DuplicateModule(
                    checked.name.clone(),
                ));
            }
            if checked.decoded.module.is_module && !checked.decoded.companion_parts_loaded {
                return Err(ParserRegistrationError::MissingPrivateJournal(
                    checked.name.clone(),
                ));
            }
            for constant in &checked.decoded.constants {
                charge(&mut remaining)?;
                if owners.len() >= limits.max_declarations {
                    return Err(ParserRegistrationError::Limit("owner declarations"));
                }
                if owners
                    .insert(constant.name().clone(), (index, constant))
                    .is_some()
                {
                    return Err(owner_error(
                        &checked.name,
                        constant.name(),
                        "declaration has multiple checked owners",
                    ));
                }
            }
        }
        let mut base = BTreeSet::new();
        for (declaration, _) in admitted.constants() {
            charge(&mut remaining)?;
            if !owners.contains_key(declaration) {
                if base.len().saturating_add(owners.len()) >= limits.max_declarations {
                    return Err(ParserRegistrationError::Limit("admitted declarations"));
                }
                base.insert(declaration.clone());
            }
        }
        let mut decoder = parsers::Decoder::new(limits.metadata);
        let mut nodes = limits.max_description_nodes;
        let mut modules = BTreeMap::new();
        let mut closures: Vec<BTreeSet<usize>> = Vec::new();
        for (index, input) in ordered_modules.iter().enumerate() {
            let module = &input.checked.name;
            let mut closure = BTreeSet::from([index]);
            let mut imports = Vec::new();
            for import in &input.checked.decoded.module.imports {
                charge(&mut remaining)?;
                let Some(&dependency) = positions.get(&import.module) else {
                    return Err(ParserRegistrationError::MissingImport {
                        module: module.clone(),
                        dependency: import.module.clone(),
                    });
                };
                if dependency >= index {
                    return Err(ParserRegistrationError::ImportOrder {
                        module: module.clone(),
                        dependency: import.module.clone(),
                    });
                }
                for &member in &closures[dependency] {
                    charge(&mut remaining)?;
                    closure.insert(member);
                }
                imports.push(import.module.clone());
            }
            let rows = decoder.decode(input.extensions).map_err(|error| {
                ParserRegistrationError::Decode {
                    module: module.clone(),
                    error,
                }
            })?;
            closures.push(closure);
            // Empty journals retain dependency identity without scanning every
            // unrelated declaration or allocating an unnecessary literal world.
            if rows.is_empty() {
                modules.insert(
                    module.clone(),
                    PreparedModule {
                        imports,
                        syntax: ImportedSyntaxModule::default(),
                        bindings: BTreeMap::new(),
                    },
                );
                continue;
            }
            remaining.max_steps = remaining.max_steps.checked_sub(base.len()).ok_or(
                ParserRegistrationError::Limit("description preparation steps"),
            )?;
            let mut allowed = base.clone();
            for &member in &closures[index] {
                for constant in &ordered_modules[member].checked.decoded.constants {
                    charge(&mut remaining)?;
                    if admitted.find(constant.name()) != Some(constant) {
                        return Err(owner_error(
                            module,
                            constant.name(),
                            "admitted declaration differs from checked dependency",
                        ));
                    }
                    allowed.insert(constant.name().clone());
                }
            }
            let mut reader = data::Reader::new(admitted, &allowed, remaining).with_owner_worlds(
                data::OwnerWorlds {
                    owners: &owners,
                    imports: &closures,
                    base: &base,
                },
            );
            let mut syntax = ImportedSyntaxModule::default();
            let mut bindings = BTreeMap::new();
            for row in rows.entries {
                let scope = row.scope;
                let entry = match row.kind {
                    parsers::ParserEntryKind::Token(token) => {
                        ImportedSyntaxEntry::Token { scope, token }
                    }
                    parsers::ParserEntryKind::Kind(kind) => {
                        ImportedSyntaxEntry::Kind { scope, kind }
                    }
                    parsers::ParserEntryKind::Category {
                        category,
                        declaration,
                        behavior,
                    } => {
                        let owner = checked_owner(module, &declaration, index, &owners, admitted)?;
                        checked_category(module, &declaration, owner)?;
                        reader
                            .bind_declaration(&declaration)
                            .and_then(|()| reader.expected_type("Lean.Parser.Category"))
                            .map_err(|error| data_error(module, &declaration, error))?;
                        bindings.insert(declaration.clone(), owner.clone());
                        let behavior = match behavior {
                            parsers::LeadingIdentBehavior::Default => {
                                fln_parse::extensions::IdentBehavior::Default
                            }
                            parsers::LeadingIdentBehavior::Symbol => {
                                fln_parse::extensions::IdentBehavior::Symbol
                            }
                            parsers::LeadingIdentBehavior::Both => {
                                fln_parse::extensions::IdentBehavior::Both
                            }
                        };
                        ImportedSyntaxEntry::Category {
                            scope,
                            category,
                            declaration,
                            behavior,
                        }
                    }
                    parsers::ParserEntryKind::Parser {
                        category,
                        declaration,
                        priority,
                    } => {
                        let owner = checked_owner(module, &declaration, index, &owners, admitted)?;
                        let (leading, body) = description_body(module, &declaration, owner)?;
                        reader
                            .bind_declaration(&declaration)
                            .map_err(|error| data_error(module, &declaration, error))?;
                        // Keep the original type spelling for dispatch, but
                        // independently bind and validate its actual definition.
                        // In particular the trailing abbreviation is an input
                        // dependency even when it never occurs in the body.
                        reader
                            .expected_type(if leading {
                                parsers::PARSER_DESCR_TYPE
                            } else {
                                parsers::TRAILING_PARSER_DESCR_TYPE
                            })
                            .map_err(|error| data_error(module, &declaration, error))?;
                        bindings.insert(declaration.clone(), owner.clone());
                        let descr = descriptions::read(
                            &mut reader,
                            body,
                            admitted,
                            module,
                            &declaration,
                            &mut nodes,
                            limits.max_depth,
                        )?;
                        ImportedSyntaxEntry::Parser(Arc::new(SyntaxDecl {
                            module: module.clone(),
                            decl: declaration,
                            category: Some(category),
                            leading,
                            priority,
                            scope,
                            descr,
                        }))
                    }
                };
                syntax
                    .entries
                    .try_reserve(1)
                    .map_err(|_| ParserRegistrationError::Limit("journal allocation"))?;
                syntax.entries.push(entry);
            }
            remaining = reader.remaining_limits();
            for declaration in reader.into_used() {
                let owner = admitted.find(&declaration).ok_or_else(|| {
                    owner_error(module, &declaration, "description dependency disappeared")
                })?;
                bindings.insert(declaration, owner.clone());
            }
            modules.insert(
                module.clone(),
                PreparedModule {
                    imports,
                    syntax,
                    bindings,
                },
            );
        }
        Ok(Self {
            modules: Arc::new(modules),
        })
    }

    /// Select exactly a source module's dependency-first external import order.
    /// Lexical scopes start inactive; registration order is rebuilt, not filtered
    /// from another module's already activated grammar.
    pub fn project_imports(
        &self,
        ordered_imports: &[Name],
        engine: &Engine,
    ) -> Result<ImportedSyntaxModule, ParserRegistrationError> {
        if ordered_imports.len() > self.modules.len() {
            return Err(ParserRegistrationError::Limit("projected modules"));
        }
        let mut seen = BTreeSet::new();
        let mut result = ImportedSyntaxModule::default();
        for module in ordered_imports {
            let Some(prepared) = self.modules.get(module) else {
                return Err(owner_error(
                    module,
                    &Name::anonymous(),
                    "projected module has no retained parser journal",
                ));
            };
            if !seen.insert(module.clone()) {
                return Err(ParserRegistrationError::DuplicateModule(module.clone()));
            }
            if !engine.imported_modules().contains(module) {
                return Err(owner_error(
                    module,
                    &Name::anonymous(),
                    "parser module is not an admitted import of the source engine",
                ));
            }
            for dependency in &prepared.imports {
                if !seen.contains(dependency) {
                    return Err(ParserRegistrationError::MissingImport {
                        module: module.clone(),
                        dependency: dependency.clone(),
                    });
                }
            }
            for (declaration, owner) in &prepared.bindings {
                if engine.environment().find(declaration) != Some(owner) {
                    return Err(owner_error(
                        module,
                        declaration,
                        "source engine differs from the checked parser dependency",
                    ));
                }
            }
            result
                .entries
                .try_reserve(prepared.syntax.entries.len())
                .map_err(|_| ParserRegistrationError::Limit("projected journal allocation"))?;
            result
                .entries
                .extend(prepared.syntax.entries.iter().cloned());
        }
        Ok(result)
    }
}

fn charge(remaining: &mut data::DataLimits) -> Result<(), ParserRegistrationError> {
    remaining.max_steps =
        remaining
            .max_steps
            .checked_sub(1)
            .ok_or(ParserRegistrationError::Limit(
                "description preparation steps",
            ))?;
    Ok(())
}

fn checked_owner<'a>(
    module: &Name,
    declaration: &Name,
    index: usize,
    owners: &BTreeMap<Name, (usize, &'a ConstantInfo)>,
    admitted: &Environment,
) -> Result<&'a ConstantInfo, ParserRegistrationError> {
    let Some(&(owner_index, owner)) = owners.get(declaration) else {
        return Err(owner_error(
            module,
            declaration,
            "registration has no checked declaration owner",
        ));
    };
    if owner_index != index {
        return Err(owner_error(
            module,
            declaration,
            "registration is not owned by this checked module",
        ));
    }
    if admitted.find(declaration) != Some(owner) {
        return Err(owner_error(
            module,
            declaration,
            "admitted declaration differs from checked owner",
        ));
    }
    Ok(owner)
}

fn description_body<'a>(
    module: &Name,
    declaration: &Name,
    owner: &'a ConstantInfo,
) -> Result<(bool, &'a Expr), ParserRegistrationError> {
    let ConstantInfo::Defn(definition) = owner else {
        return Err(owner_error(
            module,
            declaration,
            "parser description is not a safe definition",
        ));
    };
    if definition.safety != DefinitionSafety::Safe || !definition.base.level_params.is_empty() {
        return Err(owner_error(
            module,
            declaration,
            "parser description is unsafe, partial or polymorphic",
        ));
    }
    // The pin intentionally classifies by this spelling before unfolding the
    // TrailingParserDescr abbreviation. Normalizing it would reverse dispatch.
    let leading = match definition.base.type_.node() {
        ExprNode::Const { name: ty, levels }
            if levels.is_empty() && *ty == name(parsers::PARSER_DESCR_TYPE) =>
        {
            true
        }
        ExprNode::Const { name: ty, levels }
            if levels.is_empty() && *ty == name(parsers::TRAILING_PARSER_DESCR_TYPE) =>
        {
            false
        }
        _ => {
            return Err(owner_error(
                module,
                declaration,
                "owner is not of exact type ParserDescr or TrailingParserDescr; executable parsers are unsupported",
            ));
        }
    };
    Ok((leading, &definition.value))
}

fn checked_category(
    module: &Name,
    declaration: &Name,
    owner: &ConstantInfo,
) -> Result<(), ParserRegistrationError> {
    if matches!(owner, ConstantInfo::Defn(definition)
        if definition.safety == DefinitionSafety::Safe
            && definition.base.level_params.is_empty()
            && matches!(definition.base.type_.node(), ExprNode::Const { name: ty, levels }
                if levels.is_empty() && *ty == name("Lean.Parser.Category")))
    {
        Ok(())
    } else {
        Err(owner_error(
            module,
            declaration,
            "category owner is not a safe monomorphic Lean.Parser.Category definition",
        ))
    }
}
