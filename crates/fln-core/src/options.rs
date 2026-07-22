//! Options: `KVMap`/`DataValue` and the canonical resource limits (plan §1.1, §21).
//!
//! Semantics anchors (vendor/lean4-src at the SUITE.lock pin):
//! * `DataValue` — src/Lean/Data/KVMap.lean:17-24 (six variants);
//! * `KVMap` — KVMap.lean:70-72: an association list (`List (Name × DataValue)`),
//!   deliberately not a tree map; first-match lookup, in-place replace or append on
//!   insert (KVMap.lean:87-100), filter-based erase;
//! * typed getters return their per-type defaults on absence OR type mismatch
//!   (KVMap.lean:108-135);
//! * resource limits — `maxHeartbeats` default 200000 in thousand-units with the
//!   effective ×1000 (src/Lean/CoreM.lean:30-33, 175-176); `maxRecDepth` default
//!   `defaultMaxRecDepth` = 512 (src/Lean/Util/RecDepth.lean:15-18,
//!   src/Init/Prelude.lean:4804); the newer resource-limit surface is enumerated in
//!   [`limits`].

use crate::name::Name;

/// Opaque handle for a `DataValue.ofSyntax` payload. `Syntax` lives in fln-syntax
/// (rank 7); fln-core (rank 0) records only the identity. fln-syntax owns the arena
/// that resolves handles; a dangling handle renders as `Syntax.missing`, matching the
/// upstream getter default.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct SyntaxHandle(pub u64);

/// `DataValue` (KVMap.lean:17-24).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DataValue {
    OfString(String),
    OfBool(bool),
    OfName(Name),
    OfNat(u64),
    OfInt(i64),
    OfSyntax(SyntaxHandle),
}

impl DataValue {
    /// `DataValue.sameCtor` (KVMap.lean:36-44).
    pub fn same_ctor(&self, other: &DataValue) -> bool {
        std::mem::discriminant(self) == std::mem::discriminant(other)
    }
}

/// `KVMap` (KVMap.lean:70-72): an insertion-ordered association list.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct KVMap {
    entries: Vec<(Name, DataValue)>,
}

impl KVMap {
    pub fn new() -> KVMap {
        KVMap::default()
    }

    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    pub fn len(&self) -> usize {
        self.entries.len()
    }

    pub fn entries(&self) -> &[(Name, DataValue)] {
        &self.entries
    }

    /// `KVMap.findCore`: linear first-match scan.
    pub fn find(&self, key: &Name) -> Option<&DataValue> {
        self.entries.iter().find(|(k, _)| k == key).map(|(_, v)| v)
    }

    pub fn contains(&self, key: &Name) -> bool {
        self.find(key).is_some()
    }

    /// `KVMap.insertCore`: replace in place when present, else append.
    pub fn insert(&mut self, key: Name, value: DataValue) {
        match self.entries.iter_mut().find(|(k, _)| *k == key) {
            Some(entry) => entry.1 = value,
            None => self.entries.push((key, value)),
        }
    }

    /// `KVMap.erase`: filter by key.
    pub fn erase(&mut self, key: &Name) {
        self.entries.retain(|(k, _)| k != key);
    }

    /// `KVMap.getString` — default `""` on absence or type mismatch.
    pub fn get_string(&self, key: &Name, default: &str) -> String {
        match self.find(key) {
            Some(DataValue::OfString(v)) => v.clone(),
            _ => default.to_string(),
        }
    }

    /// `KVMap.getNat` — default on absence or type mismatch.
    pub fn get_nat(&self, key: &Name, default: u64) -> u64 {
        match self.find(key) {
            Some(DataValue::OfNat(v)) => *v,
            _ => default,
        }
    }

    /// `KVMap.getInt`.
    pub fn get_int(&self, key: &Name, default: i64) -> i64 {
        match self.find(key) {
            Some(DataValue::OfInt(v)) => *v,
            _ => default,
        }
    }

    /// `KVMap.getBool`.
    pub fn get_bool(&self, key: &Name, default: bool) -> bool {
        match self.find(key) {
            Some(DataValue::OfBool(v)) => *v,
            _ => default,
        }
    }

    /// `KVMap.getName`.
    pub fn get_name(&self, key: &Name, default: &Name) -> Name {
        match self.find(key) {
            Some(DataValue::OfName(v)) => v.clone(),
            _ => default.clone(),
        }
    }

    /// `KVMap.getSyntax` — the upstream default is `Syntax.missing`; here `None`
    /// stands for that missing syntax until fln-syntax provides the arena.
    pub fn get_syntax(&self, key: &Name) -> Option<SyntaxHandle> {
        match self.find(key) {
            Some(DataValue::OfSyntax(v)) => Some(*v),
            _ => None,
        }
    }
}

/// `Options` is a `KVMap` upstream (`def Options := KVMap`).
pub type Options = KVMap;

/// The canonical resource-limit surface, each anchored to its registration site.
pub mod limits {
    /// `maxHeartbeats` default (CoreM.lean:30-33). Thousand-unit heartbeats;
    /// `0` means no limit.
    pub const MAX_HEARTBEATS_DEFAULT: u64 = 200_000;
    /// `getMaxHeartbeats` multiplies the option by 1000 (CoreM.lean:175-176).
    pub const HEARTBEAT_UNIT: u64 = 1000;
    /// `defaultMaxRecDepth` (Init/Prelude.lean:4804). `0` means no limit.
    pub const MAX_REC_DEPTH_DEFAULT: u64 = 512;
    /// `synthInstance.maxHeartbeats` default (Meta/SynthInstance.lean:19); also
    /// thousand-units.
    pub const SYNTH_INSTANCE_MAX_HEARTBEATS_DEFAULT: u64 = 20_000;
    /// `synthInstance.maxSize` default (Meta/SynthInstance.lean:24).
    pub const SYNTH_INSTANCE_MAX_SIZE_DEFAULT: u64 = 128;
    /// `maxSynthPendingDepth` default (Meta/Basic.lean:456) — newer surface.
    pub const MAX_SYNTH_PENDING_DEPTH_DEFAULT: u64 = 1;
    /// `maxUniverseOffset` default (Elab/Level.lean:48) — newer surface.
    pub const MAX_UNIVERSE_OFFSET_DEFAULT: u64 = 32;
    /// `exponentiation.threshold` default (Util/SafeExponentiation.lean:15).
    pub const EXPONENTIATION_THRESHOLD_DEFAULT: u64 = 256;
    /// `maxErrors` default (Language/Basic.lean:305).
    pub const MAX_ERRORS_DEFAULT: u64 = 100;

    /// The effective heartbeat budget for an option value (0 stays 0 = unlimited).
    pub const fn effective_heartbeats(option_value: u64) -> u64 {
        option_value * HEARTBEAT_UNIT
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn key(s: &str) -> Name {
        Name::str(Name::anonymous(), s)
    }

    #[test]
    fn insert_replaces_in_place_and_preserves_order() {
        let mut m = KVMap::new();
        m.insert(key("a"), DataValue::OfNat(1));
        m.insert(key("b"), DataValue::OfBool(true));
        m.insert(key("a"), DataValue::OfNat(2));
        assert_eq!(m.len(), 2);
        assert_eq!(
            m.entries()[0].0,
            key("a"),
            "replaced in place, not re-appended"
        );
        assert_eq!(m.get_nat(&key("a"), 0), 2);
    }

    #[test]
    fn getters_default_on_absence_and_type_mismatch() {
        let mut m = KVMap::new();
        m.insert(key("s"), DataValue::OfString("x".into()));
        assert_eq!(m.get_string(&key("s"), ""), "x");
        assert_eq!(m.get_nat(&key("s"), 9), 9, "type mismatch yields default");
        assert_eq!(m.get_nat(&key("missing"), 7), 7);
        assert!(!m.get_bool(&key("missing"), false));
        assert_eq!(m.get_int(&key("missing"), -3), -3);
        assert_eq!(
            m.get_name(&key("missing"), &Name::anonymous()),
            Name::anonymous()
        );
        assert_eq!(m.get_syntax(&key("missing")), None);
    }

    #[test]
    fn erase_and_same_ctor() {
        let mut m = KVMap::new();
        m.insert(key("a"), DataValue::OfNat(1));
        m.erase(&key("a"));
        assert!(m.is_empty());
        assert!(DataValue::OfNat(1).same_ctor(&DataValue::OfNat(2)));
        assert!(!DataValue::OfNat(1).same_ctor(&DataValue::OfInt(1)));
    }

    #[test]
    fn resource_limit_constants_match_the_pin() {
        assert_eq!(limits::MAX_HEARTBEATS_DEFAULT, 200_000);
        assert_eq!(
            limits::effective_heartbeats(limits::MAX_HEARTBEATS_DEFAULT),
            200_000_000
        );
        assert_eq!(limits::effective_heartbeats(0), 0, "0 means no limit");
        assert_eq!(limits::MAX_REC_DEPTH_DEFAULT, 512);
        assert_eq!(limits::SYNTH_INSTANCE_MAX_HEARTBEATS_DEFAULT, 20_000);
        assert_eq!(limits::MAX_SYNTH_PENDING_DEPTH_DEFAULT, 1);
        assert_eq!(limits::MAX_UNIVERSE_OFFSET_DEFAULT, 32);
    }
}
