//! Universe metavariable store (`UniverseStore`) for Athanor (plan §10.1).

use fln_core::level::{LMVarId, Level, LevelTooDeep, LevelView};
use std::collections::HashMap;

/// Tracks universe metavariable assignments and instantiation.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct UniverseStore {
    assignments: HashMap<LMVarId, Level>,
}

impl UniverseStore {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn is_empty(&self) -> bool {
        self.assignments.is_empty()
    }

    pub fn len(&self) -> usize {
        self.assignments.len()
    }

    pub fn is_assigned(&self, uvar: &LMVarId) -> bool {
        self.assignments.contains_key(uvar)
    }

    pub fn get_assignment(&self, uvar: &LMVarId) -> Option<&Level> {
        self.assignments.get(uvar)
    }

    pub fn assign(&mut self, uvar: LMVarId, level: Level) -> Option<Level> {
        self.assignments.insert(uvar, level)
    }

    pub fn remove(&mut self, uvar: &LMVarId) -> Option<Level> {
        self.assignments.remove(uvar)
    }

    pub fn assignments(&self) -> &HashMap<LMVarId, Level> {
        &self.assignments
    }

    /// Instantiate all assigned universe metavariables in `level`.
    pub fn instantiate(&self, level: &Level) -> Result<Level, LevelTooDeep> {
        if self.assignments.is_empty() || !level.has_mvar() {
            return Ok(level.clone());
        }
        match level.view() {
            LevelView::Zero => Ok(Level::zero()),
            LevelView::Succ(inner) => self.instantiate(inner)?.succ(),
            LevelView::Max(l1, l2) => {
                let inst1 = self.instantiate(l1)?;
                let inst2 = self.instantiate(l2)?;
                Level::max(inst1, inst2)
            }
            LevelView::IMax(l1, l2) => {
                let inst1 = self.instantiate(l1)?;
                let inst2 = self.instantiate(l2)?;
                Level::imax(inst1, inst2)
            }
            LevelView::Param(name) => Ok(Level::param(name.clone())),
            LevelView::MVar(id) => {
                if let Some(assigned) = self.assignments.get(id) {
                    self.instantiate(assigned)
                } else {
                    Ok(Level::mvar(id.clone()))
                }
            }
        }
    }
}
