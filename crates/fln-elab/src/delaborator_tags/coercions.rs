//! The pin's `Lean.Meta.coeExt` map (`Lean/Meta/CoeAttr.lean`). These rows
//! select coercion notation in the printer; they never supply Coe instances.
//! Source and imported registrations share one chronological journal so that
//! a later module can replace metadata for an already admitted function.
use super::{DelaboratorTagError as Error, codec};
use crate::constraint::unify::{UnificationBudget, UnificationError, UnificationTransparency};
use crate::instances::{read_name, write_name};
use crate::{ElabTxn, LocalContext};
use fln_core::expr::{BinderInfo, Expr, ExprNode, FVarId};
use fln_core::name::Name;
use fln_core::options::KVMap;
use fln_env::environment::Environment;
use fln_env::extensions::{
    CheckpointSemantics, ExtensionDescriptor, MergeSemantics, PayloadProvenance,
};
use fln_kernel::verdict::Budget;

const MAGIC: &[u8] = b"FLNCOEF\x01";
pub const MAX_ROWS: usize = 65_536;
const MAX_ENTRY_BYTES: usize = 65_536;
const MAX_PARAMETERS: u32 = 4096;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CoeFnKind {
    Coe,
    CoeFun,
    CoeSort,
}

/// Absolute argument positions, including implicit and instance arguments.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CoeFnInfo {
    pub num_args: u32,
    pub coercee: u32,
    pub kind: CoeFnKind,
}

pub fn journal_name() -> Name {
    Name::from_components(["FrankenLean", "coercionFunctions", "v1"])
}

fn descriptor() -> ExtensionDescriptor {
    ExtensionDescriptor {
        name: journal_name(),
        merge: MergeSemantics::AppendOrdered,
        checkpoint: CheckpointSemantics::FullJournal,
        provenance: PayloadProvenance::Understood,
    }
}

pub fn supports(candidate: &ExtensionDescriptor) -> bool {
    *candidate == descriptor()
}

fn validate(env: &Environment, name: &Name, info: CoeFnInfo) -> Result<(), Error> {
    if name.is_anonymous() || info.coercee >= info.num_args {
        return Err(Error::Malformed);
    }
    if !env.contains(name) {
        return Err(Error::UnknownDeclaration(name.clone()));
    }
    Ok(())
}

fn reduction_error(name: &Name, error: UnificationError) -> Error {
    match error {
        UnificationError::StepLimit { .. }
        | UnificationError::NodeLimit { .. }
        | UnificationError::AssignmentLimit { .. }
        | UnificationError::HeartbeatLimit => Error::Limit,
        _ => Error::UnsupportedTelescope(name.clone()),
    }
}

/// The function telescope used by `getFunInfo`, including binders exposed by
/// reducible type aliases, opened in a temporary native elaboration context.
fn parameter_infos(env: &Environment, name: &Name) -> Result<Vec<BinderInfo>, Error> {
    let declaration = env
        .find(name)
        .ok_or_else(|| Error::UnknownDeclaration(name.clone()))?;
    let mut current = declaration.constant_val().type_.clone();
    let mut txn = ElabTxn::new(env.clone(), KVMap::new(), 0);
    let mut locals = LocalContext::new();
    let mut budget = UnificationBudget::new(Budget::for_stack_bytes(1024 * 1024));
    budget.transparency = UnificationTransparency::Default;
    let mut infos = Vec::new();
    for index in 0..MAX_PARAMETERS {
        current = txn
            .whnf_with(&current, &locals, budget)
            .map_err(|error| reduction_error(name, error))?;
        let ExprNode::ForallE {
            binder_name,
            binder_type,
            body,
            binder_info,
        } = current.node()
        else {
            return Ok(infos);
        };
        infos.push(*binder_info);
        let id = FVarId(Name::num(Name::anonymous(), u64::from(index)));
        locals.add_param(
            id.clone(),
            binder_name.clone(),
            binder_type.clone(),
            *binder_info,
        );
        current = body
            .subst_loose(0, &[Expr::fvar(id)])
            .map_err(|_| Error::Limit)?;
    }
    Err(Error::Limit)
}

/// Called only after source has checked the global attribute kind and target.
/// An unsuccessful registration publishes no extension or declaration changes.
/// The native reducer's checker budget requires at least 1 MiB of caller stack.
pub fn register_source(env: &Environment, name: &Name) -> Result<Environment, Error> {
    let coercee = parameter_infos(env, name)?
        .iter()
        .position(|info| *info == BinderInfo::Default)
        .ok_or_else(|| Error::NoExplicitArgument(name.clone()))?;
    let coercee = u32::try_from(coercee).map_err(|_| Error::Limit)?;
    let info = CoeFnInfo {
        num_args: coercee + 1,
        coercee,
        kind: CoeFnKind::Coe,
    };
    register(env, &[(name.clone(), info)])
}

/// Record already decoded metadata after checking its target against the
/// recording module's admitted import closure. Explicit info need not equal
/// today's inferred telescope: the pin allows `registerCoercion name (some info)`.
pub fn register(env: &Environment, rows: &[(Name, CoeFnInfo)]) -> Result<Environment, Error> {
    if rows.is_empty() {
        return Ok(env.clone());
    }
    // Validate the inherited journal, even when a new row would overwrite it.
    read(env)?;
    let existing = env
        .extension(&journal_name())
        .map_or(0, |state| state.len());
    if rows.len() > MAX_ROWS.saturating_sub(existing) {
        return Err(Error::Limit);
    }
    let mut result = if existing == 0 && env.extension(&journal_name()).is_none() {
        env.register_extension(descriptor())
            .map_err(|_| Error::Malformed)?
    } else {
        env.clone()
    };
    for (name, info) in rows {
        validate(env, name, *info)?;
        let mut payload = MAGIC.to_vec();
        write_name(name, &mut payload).map_err(codec)?;
        payload.extend(info.num_args.to_le_bytes());
        payload.extend(info.coercee.to_le_bytes());
        payload.push(match info.kind {
            CoeFnKind::Coe => 0,
            CoeFnKind::CoeFun => 1,
            CoeFnKind::CoeSort => 2,
        });
        if payload.len() > MAX_ENTRY_BYTES {
            return Err(Error::Limit);
        }
        result = result
            .push_extension_entry(&journal_name(), payload)
            .map_err(|_| Error::Malformed)?;
    }
    Ok(result)
}

/// Keep repeated registrations in order; the map consumer applies last-write
/// semantics. Hidden declarations are validated in the row's original view,
/// then omitted from the projected public view.
pub fn read(env: &Environment) -> Result<Vec<(Name, CoeFnInfo)>, Error> {
    let Some(extension) = env.extension(&journal_name()) else {
        return Ok(Vec::new());
    };
    if extension.descriptor != descriptor() {
        return Err(Error::Malformed);
    }
    if extension.len() > MAX_ROWS {
        return Err(Error::Limit);
    }
    let mut rows = Vec::new();
    for (entry, validation) in env.metadata_validation_entries(&journal_name()) {
        if entry.payload.len() > MAX_ENTRY_BYTES {
            return Err(Error::Limit);
        }
        let mut bytes = entry.payload.strip_prefix(MAGIC).ok_or(Error::Malformed)?;
        let name = read_name(&mut bytes).map_err(codec)?;
        let (arguments, rest) = bytes.split_at_checked(4).ok_or(Error::Malformed)?;
        let (coercee, kind) = rest.split_at_checked(4).ok_or(Error::Malformed)?;
        let info = CoeFnInfo {
            num_args: u32::from_le_bytes(arguments.try_into().map_err(|_| Error::Malformed)?),
            coercee: u32::from_le_bytes(coercee.try_into().map_err(|_| Error::Malformed)?),
            kind: match kind {
                [0] => CoeFnKind::Coe,
                [1] => CoeFnKind::CoeFun,
                [2] => CoeFnKind::CoeSort,
                _ => return Err(Error::Malformed),
            },
        };
        validate(validation, &name, info)?;
        if env.contains(&name) {
            rows.push((name, info));
        }
    }
    Ok(rows)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::delaborator_tags::DelaboratorTags;
    use fln_core::level::Level;
    use fln_env::constants::{AxiomVal, ConstantInfo, ConstantVal};

    fn fixture() -> (Environment, Name) {
        let name = Name::from_components(["cast"]);
        let type_ = Expr::forall_e(
            Name::from_components(["A"]),
            Expr::sort(Level::zero()),
            Expr::forall_e(
                Name::from_components(["value"]),
                Expr::bvar(0).unwrap(),
                Expr::bvar(1).unwrap(),
                BinderInfo::Default,
            ),
            BinderInfo::Implicit,
        );
        let env = Environment::new()
            .add_decl(ConstantInfo::Axiom(AxiomVal {
                base: ConstantVal {
                    name: name.clone(),
                    level_params: vec![],
                    type_,
                },
                is_unsafe: false,
            }))
            .unwrap();
        (env, name)
    }

    #[test]
    fn source_registration_finds_explicit_position_and_later_rows_replace_metadata() {
        let (env, name) = fixture();
        let registered = register_source(&env, &name).unwrap();
        let source = CoeFnInfo {
            num_args: 2,
            coercee: 1,
            kind: CoeFnKind::Coe,
        };
        assert_eq!(
            DelaboratorTags::read(&registered).unwrap().coercion(&name),
            Some(&source)
        );
        assert!(read(&env).unwrap().is_empty());
        let replacement = CoeFnInfo {
            kind: CoeFnKind::CoeFun,
            ..source
        };
        let updated = register(&registered, &[(name.clone(), replacement)]).unwrap();
        assert_eq!(
            read(&updated).unwrap(),
            [(name.clone(), source), (name.clone(), replacement)]
        );
        assert_eq!(
            DelaboratorTags::read(&updated).unwrap().coercion(&name),
            Some(&replacement)
        );
    }

    #[test]
    fn malformed_or_unknown_rows_do_not_publish_a_partial_journal() {
        let (env, name) = fixture();
        let valid = CoeFnInfo {
            num_args: 2,
            coercee: 1,
            kind: CoeFnKind::Coe,
        };
        assert!(matches!(
            register(
                &env,
                &[
                    (name.clone(), valid),
                    (Name::from_components(["missing"]), valid)
                ]
            ),
            Err(Error::UnknownDeclaration(_))
        ));
        assert!(env.extension(&journal_name()).is_none());
        assert_eq!(
            register(
                &env,
                &[(
                    name,
                    CoeFnInfo {
                        coercee: 2,
                        ..valid
                    }
                )]
            )
            .unwrap_err(),
            Error::Malformed
        );
        let poisoned = env
            .register_extension(descriptor())
            .unwrap()
            .push_extension_entry(&journal_name(), MAGIC.to_vec())
            .unwrap();
        assert_eq!(read(&poisoned).unwrap_err(), Error::Malformed);
    }
}
