//! Convert checked source simp registrations to the pin's persistent entries.
//!
//! ScopedEnvExtension exports additions in source order, not the priority-sorted
//! active set. Erasure changes its current state without removing exported
//! entries. Native module replay currently retains erasures, so such suffixes
//! remain unsupported rather than producing different physical-import results.
use super::*;
use crate::instances::discr_tree::Key;
use std::sync::Arc;

mod keys;
mod theorems;

pub fn journal_name() -> Name {
    descriptor().name
}

pub fn supports(candidate: &ExtensionDescriptor) -> bool {
    *candidate == descriptor()
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Theorem {
    pub proof: Expr,
    pub level_params: Vec<Name>,
    pub origin: Name,
    pub origin_reverse: bool,
    pub priority: u32,
    pub post: bool,
    pub permutation: bool,
    pub reflexive: bool,
    pub backward_reflexive: bool,
    pub keys: Vec<Key>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Kind {
    Unfold(Name),
    Theorem(Theorem),
    UnfoldTheorems {
        declaration: Name,
        theorems: Vec<Name>,
    },
}

/// Capability at the instant of registration. Even an unsupported or exhausted
/// export projection is recorded, without narrowing ordinary source simp.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) enum Snapshot {
    Unsupported,
    ResourceLimit,
    Unfold,
    Theorem {
        keys: Vec<Key>,
        permutation: bool,
        reflexive: bool,
        backward_reflexive: bool,
    },
}

fn codec(error: crate::instances::InstanceRegistryError) -> SimpSetError {
    match error {
        crate::instances::InstanceRegistryError::Limit => SimpSetError::Limit,
        _ => SimpSetError::Malformed,
    }
}

impl Snapshot {
    pub(super) fn is_supported(&self) -> bool {
        matches!(self, Self::Unfold | Self::Theorem { .. })
    }

    fn capture(env: &Environment, entry: &SimpEntry) -> Result<Self, SimpSetError> {
        let mut meter = Meter {
            remaining: 1 << 20,
            bytes: 0,
        };
        match derive_registration(env, entry, &mut meter) {
            Ok(Kind::Unfold(_)) => Ok(Self::Unfold),
            Ok(Kind::Theorem(theorem)) => Ok(Self::Theorem {
                keys: theorem.keys,
                permutation: theorem.permutation,
                reflexive: theorem.reflexive,
                backward_reflexive: theorem.backward_reflexive,
            }),
            // Association rows have their own journal operation; an ordinary
            // registration never manufactures a theorem group snapshot.
            Ok(Kind::UnfoldTheorems { .. }) => Err(SimpSetError::Malformed),
            Err(SimpSetError::UnsupportedDeclaration(_)) => Ok(Self::Unsupported),
            Err(SimpSetError::Limit) => Ok(Self::ResourceLimit),
            Err(error) => Err(error),
        }
    }

    fn write(&self, bytes: &mut Vec<u8>) -> Result<(), SimpSetError> {
        match self {
            Self::Unsupported => bytes.push(0),
            Self::ResourceLimit => bytes.push(1),
            Self::Unfold => bytes.push(2),
            Self::Theorem {
                keys,
                permutation,
                reflexive,
                backward_reflexive,
            } => {
                bytes.push(3);
                bytes.push(
                    u8::from(*permutation)
                        | u8::from(*reflexive) << 1
                        | u8::from(*backward_reflexive) << 2,
                );
                crate::instances::discr_tree::write_keys(keys, bytes).map_err(codec)?;
            }
        }
        Ok(())
    }

    pub(super) fn read(bytes: &mut &[u8]) -> Result<Self, SimpSetError> {
        match take(bytes, 1)?[0] {
            0 => Ok(Self::Unsupported),
            1 => Ok(Self::ResourceLimit),
            2 => Ok(Self::Unfold),
            3 => {
                let flags = take(bytes, 1)?[0];
                if flags & !7 != 0 {
                    return Err(SimpSetError::Malformed);
                }
                let keys = crate::instances::discr_tree::read_keys(bytes).map_err(codec)?;
                Ok(Self::Theorem {
                    keys,
                    permutation: flags & 1 != 0,
                    reflexive: flags & 2 != 0,
                    backward_reflexive: flags & 4 != 0,
                })
            }
            _ => Err(SimpSetError::Malformed),
        }
    }

    fn into_kind(self, entry: &SimpEntry) -> Result<Kind, SimpSetError> {
        match self {
            Self::Unsupported => Err(SimpSetError::UnsupportedDeclaration(
                entry.declaration.clone(),
            )),
            Self::ResourceLimit => Err(SimpSetError::Limit),
            Self::Unfold => Ok(Kind::Unfold(entry.declaration.clone())),
            Self::Theorem {
                keys,
                permutation,
                reflexive,
                backward_reflexive,
            } => Ok(Kind::Theorem(Theorem {
                proof: Expr::const_(entry.declaration.clone(), Vec::new()),
                level_params: Vec::new(),
                origin: entry.declaration.clone(),
                origin_reverse: false,
                priority: entry.priority,
                post: true,
                permutation,
                reflexive,
                backward_reflexive,
                keys,
            })),
        }
    }
}

pub(super) fn snapshot_payload(
    env: &Environment,
    declaration: &Name,
    priority: u32,
    reverse: bool,
) -> Result<Vec<u8>, SimpSetError> {
    let entry = SimpEntry {
        declaration: declaration.clone(),
        proof: None,
        priority,
        reverse,
        order: 0,
    };
    encode_snapshot(
        declaration,
        priority,
        reverse,
        &Snapshot::capture(env, &entry)?,
    )
}

fn encode_snapshot(
    declaration: &Name,
    priority: u32,
    reverse: bool,
    snapshot: &Snapshot,
) -> Result<Vec<u8>, SimpSetError> {
    let mut payload = SNAPSHOT_MAGIC.to_vec();
    payload.push(0);
    crate::instances::write_name(declaration, &mut payload).map_err(codec)?;
    payload.extend(priority.to_le_bytes());
    payload.push(u8::from(reverse));
    let prefix = payload.len();
    // The name and capability byte must fit even when the index does not.
    if prefix >= MAX_BYTES {
        return Err(SimpSetError::Limit);
    }
    match snapshot.write(&mut payload) {
        Ok(()) if payload.len() <= MAX_BYTES => {}
        Ok(()) | Err(SimpSetError::Limit) => {
            payload.truncate(prefix);
            Snapshot::ResourceLimit.write(&mut payload)?;
        }
        Err(error) => return Err(error),
    }
    Ok(payload)
}

fn derive_registration(
    env: &Environment,
    entry: &SimpEntry,
    meter: &mut Meter,
) -> Result<Kind, SimpSetError> {
    let info = env
        .find(&entry.declaration)
        .ok_or_else(|| SimpSetError::UnknownDeclaration(entry.declaration.clone()))?;
    if let ConstantInfo::Defn(definition) = info
        && definition.safety == DefinitionSafety::Safe
        && entry.proof.is_none()
        && !definition_type_is_proposition(env, &definition.base.type_, meter)?
    {
        if entry.reverse {
            return Err(SimpSetError::UnsupportedDeclaration(
                entry.declaration.clone(),
            ));
        }
        // Simp.ignoreEquations applies to reducible definitions and registered
        // projections, including semireducible class fields. Other definitions
        // need their actual generated equations before a bare unfolding is
        // sufficient for persistent registration.
        if !known_reducible(env, &entry.declaration, meter)?
            && !registered_projection(env, &entry.declaration, meter)?
            && !super::equations::generated(env, &entry.declaration, meter)?
        {
            return Err(SimpSetError::UnsupportedDeclaration(
                entry.declaration.clone(),
            ));
        }
        Ok(Kind::Unfold(entry.declaration.clone()))
    } else {
        theorems::derive(env, entry, meter).map(Kind::Theorem)
    }
}

/// Both equation realization and export must classify the complete declaration
/// type by its inferred sort. A syntactic check cannot distinguish data from a
/// beta-headed proposition, and must never authorize equation generation.
pub(super) fn definition_type_is_proposition(
    env: &Environment,
    type_: &Expr,
    meter: &mut Meter,
) -> Result<bool, SimpSetError> {
    keys::is_proposition(env, type_, meter)
}

pub(super) fn known_reducible(
    env: &Environment,
    declaration: &Name,
    meter: &mut Meter,
) -> Result<bool, SimpSetError> {
    Ok(
        known_status(env, declaration, meter)?
            == Some(crate::reducibility::Reducibility::Reducible),
    )
}

/// The pin's projection exception is an environment registration, not a name
/// pattern or a lambda/proj shape. First skip impossible bodies cheaply, then
/// require the actual validated physical-field identity. The structure exporter
/// supplies bounded declaration/body validation and charges its complete work.
pub(super) fn registered_projection(
    env: &Environment,
    declaration: &Name,
    meter: &mut Meter,
) -> Result<bool, SimpSetError> {
    let Some(ConstantInfo::Defn(definition)) = env.find(declaration) else {
        return Ok(false);
    };
    let mut body = &definition.value;
    while let ExprNode::Lam { body: inner, .. } = body.node() {
        meter.work(1)?;
        body = inner;
    }
    meter.work(1)?;
    if !matches!(body.node(), ExprNode::Proj { .. }) {
        return Ok(false);
    }
    let structures =
        crate::records::imported::export::registrations(&Environment::new(), env, meter.remaining)
            .map_err(|error| match error {
                crate::records::RecordError::ResourceLimit => SimpSetError::Limit,
                _ => SimpSetError::Malformed,
            })?;
    meter.work(structures.work)?;
    meter.bytes(structures.bytes_examined)?;
    for structure in &structures.structures {
        meter.work(1 + structure.fields.len())?;
        if structure
            .fields
            .iter()
            .any(|field| &field.projection == declaration)
        {
            return Ok(true);
        }
    }
    Ok(false)
}

pub(super) fn known_status(
    env: &Environment,
    declaration: &Name,
    meter: &mut Meter,
) -> Result<Option<crate::reducibility::Reducibility>, SimpSetError> {
    // One lookup in the environment's effective table, which `reducibility::table` reads once
    // per change of the journals it consumes, within their own row and entry limits. Hints alone
    // do not establish an imported declaration's status. The lookup is this declaration's work;
    // the journals are the library's. Charging their bytes here refused every equation
    // preparation and simp registration once an import world's journals outgrew one
    // declaration's allowance, as full `Init`'s do (fln-simp-equation-set-limit-regression-re4l).
    meter.work(1)?;
    let table = crate::reducibility::table(env).map_err(|error| match error {
        crate::reducibility::ReducibilityError::Limit => SimpSetError::Limit,
        crate::reducibility::ReducibilityError::Instances(error) => codec(error),
        _ => SimpSetError::Malformed,
    })?;
    Ok(table.get(declaration))
}

#[derive(Debug, Default, PartialEq, Eq)]
pub struct Registrations {
    pub entries: Vec<Kind>,
    pub work: usize,
    pub bytes_examined: usize,
}

pub(super) struct Meter {
    pub(super) remaining: usize,
    pub(super) bytes: usize,
}

impl Meter {
    pub(super) fn work(&mut self, amount: usize) -> Result<(), SimpSetError> {
        self.remaining = self
            .remaining
            .checked_sub(amount)
            .ok_or(SimpSetError::Limit)?;
        Ok(())
    }

    pub(super) fn bytes(&mut self, amount: usize) -> Result<(), SimpSetError> {
        self.bytes = self.bytes.checked_add(amount).ok_or(SimpSetError::Limit)?;
        Ok(())
    }

    fn payload(&mut self, payload: &[u8]) -> Result<(), SimpSetError> {
        if payload.len() > MAX_BYTES {
            return Err(SimpSetError::Limit);
        }
        self.work(payload.len())?;
        self.bytes(payload.len())
    }
}

/// Serialize only the appended journal. The immutable inherited prefix is
/// checked exactly, with byte comparison when its allocation is not shared.
/// Existing imported theorems never have their proof/index/flags guessed again.
pub fn registrations(
    base: &Environment,
    result: &Environment,
    max_work: usize,
) -> Result<Registrations, SimpSetError> {
    let expected = descriptor();
    let prior = base.extension(&expected.name);
    let Some(current) = result.extension(&expected.name) else {
        return if prior.is_some() {
            Err(SimpSetError::Malformed)
        } else {
            Ok(Registrations::default())
        };
    };
    if current.descriptor != expected
        || prior
            .is_some_and(|old| old.descriptor != current.descriptor || old.len() > current.len())
    {
        return Err(SimpSetError::Malformed);
    }
    check_journal_capacity(current.len(), current.payload_bytes())?;
    let inherited_count = prior.map_or(0, |old| old.len());
    let mut inherited = prior.map(|old| old.entries());
    let mut meter = Meter {
        remaining: max_work,
        bytes: 0,
    };
    let mut entries = Vec::new();
    for (index, row) in current.entries().enumerate() {
        meter.work(1)?;
        if index < inherited_count {
            let old = inherited
                .as_mut()
                .and_then(Iterator::next)
                .ok_or(SimpSetError::Malformed)?;
            if !Arc::ptr_eq(&old.payload, &row.payload) {
                meter.payload(&old.payload)?;
                meter.payload(&row.payload)?;
                if old != row {
                    return Err(SimpSetError::Malformed);
                }
            }
            // The checked import base already activated this immutable row.
            // Re-decoding its proof on every module would charge a large Init
            // simp set against each module's own metadata budget.
            continue;
        }
        meter.payload(&row.payload)?;
        let decoded = decode_entry(&row.payload, index)?;
        let (entry, snapshot) = match decoded {
            JournalEntry::UnfoldTheorems {
                declaration,
                theorems,
            } => {
                super::imports::validate_unfold_theorems(result, &declaration, &theorems)?;
                for theorem in &theorems {
                    meter.work(1)?;
                    if !matches!(result.find(theorem), Some(ConstantInfo::Thm(_))) {
                        return Err(SimpSetError::UnsupportedDeclaration(theorem.clone()));
                    }
                }
                entries.push(Kind::UnfoldTheorems {
                    declaration,
                    theorems,
                });
                continue;
            }
            JournalEntry::Erase(declaration) => {
                if !result.contains(&declaration) {
                    return Err(SimpSetError::UnknownDeclaration(declaration));
                }
                return Err(SimpSetError::UnsupportedDeclaration(declaration));
            }
            JournalEntry::Add { entry, snapshot } => (entry, snapshot),
        };
        let selected = entry.proof.as_ref().unwrap_or(&entry.declaration);
        let info = result
            .find(selected)
            .ok_or_else(|| SimpSetError::UnknownDeclaration(selected.clone()))?;
        if !result.contains(&entry.declaration) {
            return Err(SimpSetError::UnknownDeclaration(entry.declaration));
        }
        let kind = match snapshot {
            Some(snapshot) => snapshot.into_kind(&entry)?,
            None => {
                // Historical/imported unfolding rows remain interpretable,
                // but old proof rows have no registration-time index/flags.
                if entry.proof.is_some()
                    || !matches!(info, ConstantInfo::Defn(definition)
                        if definition.safety == DefinitionSafety::Safe
                            && !definition_type_is_proposition(result, &definition.base.type_, &mut meter)?)
                {
                    return Err(SimpSetError::UnsupportedDeclaration(entry.declaration));
                }
                let kind = derive_registration(result, &entry, &mut meter)?;
                if !matches!(kind, Kind::Unfold(_)) {
                    return Err(SimpSetError::UnsupportedDeclaration(entry.declaration));
                }
                kind
            }
        };
        // The imported simp view does not retain every backward-defeq flag.
        // Re-registering an imported proof needs those original flags; a
        // guessed default would silently change the pin's simplifier.
        if matches!(kind, Kind::Theorem(_)) && base.contains(selected) {
            return Err(SimpSetError::UnsupportedDeclaration(selected.clone()));
        }
        entries.push(kind);
    }
    Ok(Registrations {
        entries,
        work: max_work - meter.remaining,
        bytes_examined: meter.bytes,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use fln_core::expr::BinderInfo;
    use fln_env::constants::{AxiomVal, ConstantVal, DefinitionVal, ReducibilityHints, TheoremVal};

    fn n(text: &str) -> Name {
        Name::from_components(text.split('.'))
    }

    fn definitions() -> Environment {
        ["first", "second"]
            .into_iter()
            .fold(Environment::new(), |env, text| {
                let name = n(text);
                let env = env
                    .add_decl(ConstantInfo::Defn(DefinitionVal {
                        base: ConstantVal {
                            name: name.clone(),
                            level_params: vec![],
                            type_: Expr::sort(Level::one()),
                        },
                        value: Expr::sort(Level::zero()),
                        hints: ReducibilityHints::Abbrev,
                        safety: DefinitionSafety::Safe,
                        all: vec![name.clone()],
                    }))
                    .unwrap();
                crate::reducibility::register(
                    &env,
                    &name,
                    crate::reducibility::Reducibility::Reducible,
                )
                .unwrap()
            })
    }

    // Metadata fixtures only. End-to-end tests separately check the actual
    // source proof and every emitted declaration with both admission engines.
    fn proof_model() -> Environment {
        let fln_kernel::Declaration::Inductive(equality) = crate::seed::eq_seed_declaration()
        else {
            unreachable!()
        };
        let mut env = Environment::new();
        for info in equality
            .types
            .into_iter()
            .map(ConstantInfo::Induct)
            .chain(equality.ctors.into_iter().map(ConstantInfo::Ctor))
            .chain(equality.recursors.into_iter().map(ConstantInfo::Rec))
        {
            env = env.add_decl(info).unwrap();
        }
        let constant = |text| Expr::const_(n(text), vec![]);
        for (name, type_) in [
            ("Carrier", Expr::sort(Level::one())),
            ("value", constant("Carrier")),
            (
                "outer",
                Expr::forall_e(
                    n("x"),
                    constant("Carrier"),
                    constant("Carrier"),
                    BinderInfo::Default,
                ),
            ),
        ] {
            env = env
                .add_decl(ConstantInfo::Axiom(AxiomVal {
                    base: ConstantVal {
                        name: n(name),
                        level_params: vec![],
                        type_,
                    },
                    is_unsafe: false,
                }))
                .unwrap();
        }
        env = env
            .add_decl(ConstantInfo::Defn(DefinitionVal {
                base: ConstantVal {
                    name: n("hidden"),
                    level_params: vec![],
                    type_: constant("Carrier"),
                },
                value: constant("value"),
                hints: ReducibilityHints::Abbrev,
                safety: DefinitionSafety::Safe,
                all: vec![n("hidden")],
            }))
            .unwrap();
        let lhs = Expr::app(constant("outer"), constant("hidden"));
        let rhs = Expr::app(constant("outer"), constant("value"));
        let type_ = [constant("Carrier"), lhs, rhs.clone()]
            .into_iter()
            .fold(Expr::const_(n("Eq"), vec![Level::one()]), Expr::app);
        let value = [constant("Carrier"), rhs]
            .into_iter()
            .fold(Expr::const_(n("Eq.refl"), vec![Level::one()]), Expr::app);
        env.add_decl(ConstantInfo::Thm(TheoremVal {
            base: ConstantVal {
                name: n("rule"),
                level_params: vec![],
                type_,
            },
            value,
            all: vec![n("rule")],
        }))
        .unwrap()
    }

    #[test]
    fn snapshots_freeze_keys_and_flags_and_repeated_registration_refreshes_them() {
        let initial = proof_model();
        let first = update(&initial, &n("rule"), Some((600, false))).unwrap();
        let opaque = crate::reducibility::register(
            &first,
            &n("hidden"),
            crate::reducibility::Reducibility::Irreducible,
        )
        .unwrap();
        let tagged = super::super::defeq::register_imported(&opaque, &n("rule")).unwrap();
        let frozen = registrations(&Environment::new(), &tagged, usize::MAX).unwrap();
        let [Kind::Theorem(theorem)] = frozen.entries.as_slice() else {
            panic!("one captured rule")
        };
        assert_eq!(
            theorem.keys,
            [Key::Const(n("outer"), 1), Key::Const(n("value"), 0)]
        );
        assert!(!theorem.reflexive);
        assert!(!theorem.backward_reflexive);

        let repeated = update(&tagged, &n("rule"), Some((600, false))).unwrap();
        let rows = registrations(&Environment::new(), &repeated, usize::MAX)
            .unwrap()
            .entries;
        assert_eq!(rows[0], frozen.entries[0]);
        let [_, Kind::Theorem(refreshed)] = rows.as_slice() else {
            panic!("both registration events")
        };
        assert_eq!(
            refreshed.keys,
            [Key::Const(n("outer"), 1), Key::Const(n("hidden"), 0)]
        );
        assert!(refreshed.reflexive);
        assert!(refreshed.backward_reflexive);
        assert_eq!(refreshed.priority, 600);
        assert_eq!(read(&repeated).unwrap().len(), 1);
        assert_eq!(read(&first).unwrap().len(), 1);
    }

    #[test]
    fn unsupported_and_exhausted_snapshots_preserve_native_source_acceptance() {
        let initial = definitions();
        let oversized = Snapshot::Theorem {
            keys: vec![Key::Lit(fln_core::expr::Literal::Str(
                "x".repeat(MAX_BYTES),
            ))],
            permutation: false,
            reflexive: false,
            backward_reflexive: false,
        };
        for (snapshot, expected) in [
            (
                Snapshot::Unsupported,
                SimpSetError::UnsupportedDeclaration(n("first")),
            ),
            (oversized, SimpSetError::Limit),
        ] {
            let payload = encode_snapshot(&n("first"), 1000, false, &snapshot).unwrap();
            assert!(payload.len() <= MAX_BYTES);
            let recorded = append(&initial, payload.clone()).unwrap();
            assert_eq!(read(&recorded).unwrap().len(), 1);
            assert_eq!(
                registrations(&initial, &recorded, usize::MAX),
                Err(expected)
            );
            let mut malformed = payload;
            *malformed.last_mut().unwrap() = 255;
            assert!(matches!(
                decode_entry(&malformed, 0),
                Err(SimpSetError::Malformed)
            ));
        }
    }

    #[test]
    fn historical_theorem_rows_need_registration_metadata_before_export() {
        let initial = proof_model();
        let legacy = append(
            &initial,
            source_payload(&n("rule"), Some((1000, false))).unwrap(),
        )
        .unwrap();
        assert_eq!(read(&legacy).unwrap().len(), 1);
        assert_eq!(
            registrations(&Environment::new(), &legacy, usize::MAX),
            Err(SimpSetError::UnsupportedDeclaration(n("rule")))
        );
        assert!(
            registrations(&legacy, &legacy, usize::MAX)
                .unwrap()
                .entries
                .is_empty()
        );
    }

    #[test]
    fn beta_headed_proof_types_never_become_unfold_entries() {
        let env = proof_model();
        let equality = env.find(&n("rule")).unwrap().constant_val().type_.clone();
        let beta_type = Expr::app(
            Expr::lam(
                n("P"),
                Expr::sort(Level::zero()),
                Expr::bvar(0).unwrap(),
                BinderInfo::Default,
            ),
            equality,
        );
        // This quick classifier is sufficient only: its false result cannot
        // establish that a fully admitted definition is data-valued.
        assert!(!is_proposition(&env, &beta_type).unwrap());
        let env = env
            .add_decl(ConstantInfo::Defn(DefinitionVal {
                base: ConstantVal {
                    name: n("betaProof"),
                    level_params: vec![],
                    type_: beta_type,
                },
                value: Expr::const_(n("rule"), vec![]),
                hints: ReducibilityHints::Regular(1),
                safety: DefinitionSafety::Safe,
                all: vec![n("betaProof")],
            }))
            .unwrap();
        let recorded = update(&env, &n("betaProof"), Some((1000, false))).unwrap();
        assert_eq!(
            super::super::equations::prepare_owned(
                &env,
                &n("betaProof"),
                fln_kernel::verdict::Budget::for_stack_bytes(2 * 1024 * 1024),
            ),
            Ok(super::super::equations::Preparation::NotRequired)
        );
        let exported = registrations(&Environment::new(), &recorded, usize::MAX).unwrap();
        let [Kind::Theorem(theorem)] = exported.entries.as_slice() else {
            panic!("a beta-headed proposition is proof evidence")
        };
        assert_eq!(theorem.proof, Expr::const_(n("betaProof"), vec![]));
    }

    #[test]
    fn ordinary_definitions_require_the_pins_equation_theorems() {
        let env = definitions();
        for status in [
            crate::reducibility::Reducibility::Semireducible,
            crate::reducibility::Reducibility::ImplicitReducible,
        ] {
            let env = crate::reducibility::register(&env, &n("first"), status).unwrap();
            let recorded = update(&env, &n("first"), Some((1000, false))).unwrap();
            assert_eq!(read(&recorded).unwrap().len(), 1);
            assert_eq!(
                registrations(&env, &recorded, usize::MAX),
                Err(SimpSetError::UnsupportedDeclaration(n("first")))
            );
        }
    }

    #[test]
    fn unfolding_exports_preserve_addition_order_and_priority_updates() {
        let base = update(&definitions(), &n("first"), Some((1000, false))).unwrap();
        let changed = update(&base, &n("second"), Some((2000, false))).unwrap();
        let changed = update(&changed, &n("first"), Some((100, false))).unwrap();
        assert_eq!(
            registrations(&base, &changed, usize::MAX).unwrap().entries,
            [Kind::Unfold(n("second")), Kind::Unfold(n("first"))]
        );
        assert!(
            registrations(&changed, &changed, usize::MAX)
                .unwrap()
                .entries
                .is_empty()
        );
    }

    #[test]
    fn erasures_never_silently_change_imported_or_owned_simp_rules() {
        let empty = definitions();
        let base = update(&empty, &n("first"), Some((1000, false))).unwrap();
        let erased = update(&base, &n("first"), None).unwrap();
        for before in [&empty, &base] {
            assert_eq!(
                registrations(before, &erased, usize::MAX),
                Err(SimpSetError::UnsupportedDeclaration(n("first")))
            );
        }
        assert_eq!(read(&base).unwrap().len(), 1);
    }

    #[test]
    fn exact_prefix_and_resource_boundaries_fail_closed() {
        let empty = definitions();
        let base = update(&empty, &n("first"), Some((1000, false))).unwrap();
        let replaced = update(&empty, &n("second"), Some((1000, false))).unwrap();
        assert_eq!(
            registrations(&base, &empty, usize::MAX),
            Err(SimpSetError::Malformed)
        );
        assert_eq!(
            registrations(&base, &replaced, usize::MAX),
            Err(SimpSetError::Malformed)
        );
        let complete = registrations(&empty, &base, usize::MAX).unwrap();
        assert!(complete.bytes_examined > 0);
        assert_eq!(
            registrations(&empty, &base, complete.work).unwrap(),
            complete
        );
        assert_eq!(
            registrations(&empty, &base, complete.work - 1),
            Err(SimpSetError::Limit)
        );
        let malformed = base
            .push_extension_entry(&descriptor().name, MAGIC.to_vec())
            .unwrap();
        assert_eq!(
            registrations(&base, &malformed, usize::MAX),
            Err(SimpSetError::Malformed)
        );
    }

    /// A status lookup costs the declaration one unit, however large the journals behind the
    /// table are. Before, every row was charged to the caller's allowance (2^20 for an equation
    /// preparation or a simp snapshot), and full `Init`'s journals exhausted it on their own
    /// (fln-simp-equation-set-limit-regression-re4l).
    #[test]
    fn a_status_lookup_charges_the_declaration_not_the_library_journals() {
        let long = n(&"x".repeat(1024));
        let env = Environment::new()
            .add_decl(ConstantInfo::Axiom(AxiomVal {
                base: ConstantVal {
                    name: long.clone(),
                    level_params: vec![],
                    type_: Expr::sort(Level::one()),
                },
                is_unsafe: false,
            }))
            .unwrap();
        let reducible = crate::reducibility::Reducibility::Reducible;
        let small = crate::reducibility::register(&env, &long, reducible).unwrap();
        let mut large = small.clone();
        for _ in 0..1100 {
            large = crate::reducibility::register(&large, &long, reducible).unwrap();
        }
        let journal = Name::from_components(["FrankenLean", "sourceReducibility", "v1"]);
        let rows: usize = large
            .extension(&journal)
            .unwrap()
            .entries()
            .map(|row| 1 + row.payload.len())
            .sum();
        assert!(rows > 1 << 20, "{rows}");
        let price = |env: &Environment| {
            let mut meter = Meter {
                remaining: 1 << 20,
                bytes: 0,
            };
            let status = known_status(env, &long, &mut meter);
            (status, (1 << 20) - meter.remaining)
        };
        assert_eq!(price(&small), (Ok(Some(reducible)), 1));
        assert_eq!(price(&large), (Ok(Some(reducible)), 1));
    }
}
