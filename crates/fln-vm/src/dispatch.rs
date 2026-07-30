//! The dispatch foundation for the W5 intrinsic families (bead
//! `franken_lean-pw6t`): the registry that binds extern rows to their native
//! implementations, with the refusal algebra spelled out as types.
//!
//! # What this is, and what arrives later
//!
//! The foundation owns the **table** (the generated extern rows), the
//! **registry** (one implementation slot per row), and the **refusal algebra**
//! (unknown row, duplicate registration, re-registration of an occupied slot).
//! It owns no execution semantics: the value model, budgets, and the FL-INV-07
//! outcome algebra arrive with the families (`52h0`, `65t5`, `m7vm`, `zm78`),
//! which is why an implementation here is a name plus a row id — the callable
//! shape is the families' contract, not this one.
//!
//! Every fallible operation is a typed `Result`; nothing panics on unknown or
//! duplicate input. An unknown row id is a refusal with the id in it, never a
//! silent miss and never a guessed row.

use crate::extern_table_generated::EXTERN_ROWS;
use std::collections::BTreeMap;
use std::fmt;

/// One registered native implementation, keyed by the row it implements.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct IntrinsicImpl {
    /// The row id this implementation is registered against (`extern:<name>`).
    pub row: &'static str,
    /// The implementation's own name, for diagnostics and provenance.
    pub name: &'static str,
}

/// The verdict of looking a row up in the registry.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ResolveVerdict<'a> {
    /// The row has a registered implementation.
    Resolved(&'a IntrinsicImpl),
    /// The row exists in the table but no implementation is registered — an
    /// honest absence the families fill, never an error.
    NotImplemented,
}

/// Why a registration or lookup was refused.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum DispatchRefusal {
    /// The row id is not in the generated table. Carries the offending id so
    /// the report names it.
    UnknownRow { row: String },
    /// The row's slot is already occupied. Carries both names so the conflict
    /// report says who holds the slot and who asked for it.
    Duplicate {
        row: String,
        existing: String,
        attempted: String,
    },
    /// An unregister was attempted against a slot that holds nothing.
    NotRegistered { row: String },
}

impl fmt::Display for DispatchRefusal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            DispatchRefusal::UnknownRow { row } => {
                write!(f, "unknown extern row id {row:?}")
            }
            DispatchRefusal::Duplicate {
                row,
                existing,
                attempted,
            } => write!(
                f,
                "extern row {row:?} already has an implementation registered ({existing}); \
                 {attempted} was refused"
            ),
            DispatchRefusal::NotRegistered { row } => {
                write!(
                    f,
                    "extern row {row:?} has no registered implementation to remove"
                )
            }
        }
    }
}

impl std::error::Error for DispatchRefusal {}

/// The both-directions accounting between the table and the registry: rows
/// with no implementation, and implementations whose row vanished (the second
/// is empty by construction here — registration refuses unknown rows — and the
/// query exists so a future path that could produce one is caught, not hoped).
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct BijectionReport {
    pub rows_without_impls: Vec<String>,
    pub impls_without_rows: Vec<String>,
}

/// The registry: one implementation slot per generated row. Seeding from the
/// generated table is what makes an unknown row id refusable at all.
#[derive(Clone, Debug, Default)]
pub struct IntrinsicRegistry {
    impls: BTreeMap<&'static str, IntrinsicImpl>,
}

impl IntrinsicRegistry {
    /// An empty registry over the generated table.
    pub fn new() -> Self {
        IntrinsicRegistry::default()
    }

    /// Register an implementation against its row. Refuses an unknown row id
    /// (not in the generated table) and a duplicate (the slot is occupied);
    /// replacing deliberately is `unregister` then `register`, so every
    /// replacement is an auditable pair, never a silent overwrite.
    pub fn register(&mut self, implementation: IntrinsicImpl) -> Result<(), DispatchRefusal> {
        let row = implementation.row;
        if !EXTERN_ROWS.iter().any(|generated| generated.id == row) {
            return Err(DispatchRefusal::UnknownRow {
                row: row.to_string(),
            });
        }
        if let Some(existing) = self.impls.get(row) {
            return Err(DispatchRefusal::Duplicate {
                row: row.to_string(),
                existing: existing.name.to_string(),
                attempted: implementation.name.to_string(),
            });
        }
        self.impls.insert(row, implementation);
        Ok(())
    }

    /// Remove the implementation holding a row's slot, returning it. Refuses
    /// an unknown row id and an empty slot, so a balance bug in a caller is a
    /// typed refusal rather than a quiet no-op.
    pub fn unregister(&mut self, row: &str) -> Result<IntrinsicImpl, DispatchRefusal> {
        if !EXTERN_ROWS.iter().any(|generated| generated.id == row) {
            return Err(DispatchRefusal::UnknownRow {
                row: row.to_string(),
            });
        }
        self.impls
            .remove(row)
            .ok_or_else(|| DispatchRefusal::NotRegistered {
                row: row.to_string(),
            })
    }

    /// Look a row up. An out-of-table id is a typed refusal; an in-table row
    /// with no implementation is `NotImplemented`, the families' to fill.
    pub fn resolve(&self, row: &str) -> Result<ResolveVerdict<'_>, DispatchRefusal> {
        if !EXTERN_ROWS.iter().any(|generated| generated.id == row) {
            return Err(DispatchRefusal::UnknownRow {
                row: row.to_string(),
            });
        }
        Ok(match self.impls.get(row) {
            Some(implementation) => ResolveVerdict::Resolved(implementation),
            None => ResolveVerdict::NotImplemented,
        })
    }

    /// The both-directions accounting. `rows_without_impls` is the families'
    /// work queue at any instant; `impls_without_rows` is structurally empty
    /// today and asserted so a future hole is loud.
    pub fn bijection(&self) -> BijectionReport {
        let rows_without_impls = EXTERN_ROWS
            .iter()
            .filter(|generated| !self.impls.contains_key(generated.id))
            .map(|generated| generated.id.to_string())
            .collect();
        let impls_without_rows = self
            .impls
            .keys()
            .filter(|row| !EXTERN_ROWS.iter().any(|generated| generated.id == **row))
            .map(|row| (*row).to_string())
            .collect();
        BijectionReport {
            rows_without_impls,
            impls_without_rows,
        }
    }

    /// How many slots are occupied.
    pub fn registered_count(&self) -> usize {
        self.impls.len()
    }
}
