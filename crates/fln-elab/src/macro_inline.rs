//! Declarations tagged `@[macro_inline]`: the pin's `inlineAttrs` entries of kind
//! `macroInline` (vendored `src/Lean/Compiler/InlineAttrs.lean`). The pin's compiler unfolds
//! every application of such a definition before it evaluates anything (`macroInline`, vendored
//! `src/Lean/Compiler/LCNF/ToDecl.lean:22`), so an argument the body does not select is never
//! evaluated: `true || x`, `false && x`, `cond`, `Option.getD`, the `Decidable` instances of `∧`
//! and `∨`.
//!
//! One journal entry per tagged declaration, written once the council has admitted it, from an
//! imported module's own entries or from a source declaration. The tag changes no declaration and
//! grants no authority: it only selects where the runtime unfolds an admitted definition's own
//! value. The pin's `isValidMacroInline` admits only a definition that is not mutual and not
//! recursive; the journal requires a definition alone in its `all` group. A definition's value
//! can mention only declarations admitted before it, so unfolding tagged definitions terminates.
//! A malformed or foreign journal is refused, never read as empty.
use crate::instances::{InstanceRegistryError, read_name, write_name};
use fln_core::name::Name;
use fln_env::constants::ConstantInfo;
use fln_env::environment::Environment;
use fln_env::extensions::{
    CheckpointSemantics, ExtensionDescriptor, MergeSemantics, PayloadProvenance,
};
use std::collections::BTreeSet;

pub mod export;

const MAGIC: &[u8] = b"FLNMACROINL\x01";
/// Native tag journal row capacity.
pub const MAX_ROWS: usize = 65_536;
const MAX_ENTRY_BYTES: usize = 65_536;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MacroInlineError {
    Malformed,
    Limit,
    UnknownDeclaration(Name),
    /// The pin's "This attribute does not support this kind of declaration": not a definition,
    /// or a definition in a mutual group.
    NotADefinition(Name),
    Duplicate(Name),
}

impl std::fmt::Display for MacroInlineError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Malformed => f.write_str("malformed native macro_inline journal"),
            Self::Limit => f.write_str("native macro_inline journal resource limit"),
            Self::UnknownDeclaration(name) => write!(
                f,
                "a macro_inline tag names {}, which is not admitted",
                name.to_display_string()
            ),
            Self::NotADefinition(name) => write!(
                f,
                "a macro_inline tag names {}, which is not a non-mutual definition",
                name.to_display_string()
            ),
            Self::Duplicate(name) => write!(
                f,
                "{} is tagged macro_inline twice",
                name.to_display_string()
            ),
        }
    }
}
impl std::error::Error for MacroInlineError {}

fn codec(error: InstanceRegistryError) -> MacroInlineError {
    match error {
        InstanceRegistryError::Limit => MacroInlineError::Limit,
        _ => MacroInlineError::Malformed,
    }
}

/// The native journal's extension name.
pub fn journal_name() -> Name {
    Name::from_components(["FrankenLean", "sourceMacroInline", "v1"])
}

fn descriptor() -> ExtensionDescriptor {
    ExtensionDescriptor {
        name: journal_name(),
        merge: MergeSemantics::AppendOrdered,
        checkpoint: CheckpointSemantics::FullJournal,
        provenance: PayloadProvenance::Understood,
    }
}

/// Exact native journal written by [`register`].
pub fn supports(candidate: &ExtensionDescriptor) -> bool {
    *candidate == descriptor()
}

fn eligible(env: &Environment, name: &Name) -> Result<(), MacroInlineError> {
    match env.find(name) {
        None => Err(MacroInlineError::UnknownDeclaration(name.clone())),
        Some(ConstantInfo::Defn(definition)) if definition.all.len() == 1 => Ok(()),
        Some(_) => Err(MacroInlineError::NotADefinition(name.clone())),
    }
}

/// Tag one admitted definition `@[macro_inline]`.
pub fn register(env: &Environment, name: &Name) -> Result<Environment, MacroInlineError> {
    if name.is_anonymous() {
        return Err(MacroInlineError::Malformed);
    }
    eligible(env, name)?;
    let mut payload = MAGIC.to_vec();
    write_name(name, &mut payload).map_err(codec)?;
    if payload.len() > MAX_ENTRY_BYTES {
        return Err(MacroInlineError::Limit);
    }
    let env = match env.extension(&journal_name()) {
        Some(state) if !supports(&state.descriptor) => return Err(MacroInlineError::Malformed),
        Some(state) if state.len() >= MAX_ROWS => return Err(MacroInlineError::Limit),
        Some(_) => env.clone(),
        None => env
            .register_extension(descriptor())
            .map_err(|_| MacroInlineError::Malformed)?,
    };
    env.push_extension_entry(&journal_name(), payload)
        .map_err(|_| MacroInlineError::Malformed)
}

/// Every tagged definition. A name the environment does not hold as a non-mutual definition,
/// or one tagged twice, is refused, never kept or dropped quietly.
pub fn read(env: &Environment) -> Result<BTreeSet<Name>, MacroInlineError> {
    let Some(extension) = env.extension(&journal_name()) else {
        return Ok(BTreeSet::new());
    };
    if !supports(&extension.descriptor) {
        return Err(MacroInlineError::Malformed);
    }
    if extension.len() > MAX_ROWS {
        return Err(MacroInlineError::Limit);
    }
    let mut names = BTreeSet::new();
    for entry in extension.entries() {
        if entry.payload.len() > MAX_ENTRY_BYTES {
            return Err(MacroInlineError::Limit);
        }
        let mut bytes = entry
            .payload
            .strip_prefix(MAGIC)
            .ok_or(MacroInlineError::Malformed)?;
        let name = read_name(&mut bytes).map_err(codec)?;
        if !bytes.is_empty() {
            return Err(MacroInlineError::Malformed);
        }
        eligible(env, &name)?;
        if !names.insert(name.clone()) {
            return Err(MacroInlineError::Duplicate(name));
        }
    }
    Ok(names)
}

#[cfg(test)]
mod tests {
    use super::*;
    use fln_core::expr::Expr;
    use fln_core::level::Level;
    use fln_env::constants::{
        AxiomVal, ConstantVal, DefinitionSafety, DefinitionVal, ReducibilityHints,
    };

    fn n(text: &str) -> Name {
        Name::from_components(text.split('.'))
    }

    fn environment() -> Environment {
        let sort = Expr::sort(Level::one());
        let env = Environment::new()
            .add_decl(ConstantInfo::Axiom(AxiomVal {
                base: ConstantVal {
                    name: n("T"),
                    level_params: Vec::new(),
                    type_: sort.clone(),
                },
                is_unsafe: false,
            }))
            .unwrap();
        let definition = |name: &str, all: Vec<Name>| {
            ConstantInfo::Defn(DefinitionVal {
                base: ConstantVal {
                    name: n(name),
                    level_params: Vec::new(),
                    type_: sort.clone(),
                },
                value: Expr::const_(n("T"), Vec::new()),
                hints: ReducibilityHints::Abbrev,
                safety: DefinitionSafety::Safe,
                all,
            })
        };
        env.add_decl(definition("d", vec![n("d")]))
            .unwrap()
            .add_decl(definition("m", vec![n("m"), n("other")]))
            .unwrap()
    }

    #[test]
    fn tags_are_admitted_non_mutual_definitions_recorded_once() {
        let env = environment();
        assert!(read(&env).unwrap().is_empty());
        let env = register(&env, &n("d")).unwrap();
        assert_eq!(read(&env).unwrap(), BTreeSet::from([n("d")]));
        assert_eq!(
            register(&env, &n("missing")),
            Err(MacroInlineError::UnknownDeclaration(n("missing")))
        );
        assert_eq!(
            register(&env, &n("T")),
            Err(MacroInlineError::NotADefinition(n("T")))
        );
        assert_eq!(
            register(&env, &n("m")),
            Err(MacroInlineError::NotADefinition(n("m")))
        );
        let twice = register(&env, &n("d")).unwrap();
        assert_eq!(read(&twice), Err(MacroInlineError::Duplicate(n("d"))));
    }

    #[test]
    fn a_foreign_or_malformed_journal_is_refused_not_read_as_empty() {
        let env = register(&environment(), &n("d")).unwrap();
        let broken = env
            .push_extension_entry(&journal_name(), b"broken".to_vec())
            .unwrap();
        assert_eq!(read(&broken), Err(MacroInlineError::Malformed));
        let mut forged = MAGIC.to_vec();
        write_name(&n("T"), &mut forged).unwrap();
        let forged = env.push_extension_entry(&journal_name(), forged).unwrap();
        assert_eq!(read(&forged), Err(MacroInlineError::NotADefinition(n("T"))));
    }
}
