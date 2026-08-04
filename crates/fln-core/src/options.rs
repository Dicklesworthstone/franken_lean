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

    /// The raw structure constructor (`KVMap.mk` / a `⟨[...]⟩` literal upstream).
    ///
    /// **Duplicate keys are legal here and are preserved**, because they are legal and
    /// preserved upstream (bead franken_lean-l84f). `insert` cannot create one — it
    /// mirrors `insertCore` and replaces the first match — so this is the only way to
    /// build a value the Reference can build, and refusing it here would make our
    /// representation strictly narrower than the pin's. That matters on the artifact
    /// path, not only in theory: `MData` *is* `KVMap` (`Lean/Expr.lean:116`), so a
    /// duplicate-keyed map rides inside any `Expr::MData`, and the module codec has no
    /// key-aware normalization anywhere in it.
    ///
    /// What a duplicate does and does not affect, measured against the pinned toolchain
    /// rather than inferred — `find` returns the first match and the shadowed entry is
    /// unreachable by lookup, while `len` (`size`), the entry list, rendering, and
    /// upstream's own `eqv` all observe it, and `erase` removes every entry for the key.
    /// So this is not a value that merely looks different; upstream's semantic comparison
    /// separates it.
    pub fn from_entries(entries: Vec<(Name, DataValue)>) -> KVMap {
        KVMap { entries }
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

    /// `KVMap.findCore` is only reached transitively through the typed getters in the
    /// other tests; the Parity Ledger rows it as its own symbol, so it gets its own
    /// direct evidence: first match wins, absence is `None`, and a re-insert replaces
    /// in place rather than shadowing.
    #[test]
    fn find_core_returns_the_first_match_and_none_for_absent_keys() {
        let key = Name::str(Name::anonymous(), "k");
        let other = Name::str(Name::anonymous(), "absent");
        let mut map = KVMap::new();
        assert_eq!(map.find(&key), None);

        map.insert(key.clone(), DataValue::OfNat(1));
        assert_eq!(map.find(&key), Some(&DataValue::OfNat(1)));
        assert_eq!(map.find(&other), None);

        map.insert(key.clone(), DataValue::OfNat(2));
        assert_eq!(map.find(&key), Some(&DataValue::OfNat(2)));
        assert_eq!(map.len(), 1, "a re-insert replaces rather than shadows");
    }

    /// A duplicate-keyed `KVMap` is representable and behaves exactly as the pinned
    /// Reference does (bead franken_lean-l84f).
    ///
    /// Every expectation below is a value MEASURED by running
    /// leanprover--lean4---v4.32.0 on the same fixture, not derived from reading
    /// KVMap.lean — the run corrected one prediction of mine, so the source-reading was
    /// demonstrably not sufficient. Fixture: `[(k,1), (k,2), (other,true)]`.
    #[test]
    fn duplicate_keys_are_representable_and_match_reference_semantics() {
        let key = Name::str(Name::anonymous(), "k");
        let other = Name::str(Name::anonymous(), "other");
        let dup = KVMap::from_entries(vec![
            (key.clone(), DataValue::OfNat(1)),
            (key.clone(), DataValue::OfNat(2)),
            (other.clone(), DataValue::OfBool(true)),
        ]);

        // `find` => some (ofNat 1): first match wins, the shadowed entry is unreachable.
        assert_eq!(dup.find(&key), Some(&DataValue::OfNat(1)));
        assert!(dup.contains(&key));
        // `size` => 3: entries.length, so the duplicate IS observable by length.
        assert_eq!(dup.len(), 3);
        // The entry list keeps both, in order.
        assert_eq!(
            dup.entries(),
            &[
                (key.clone(), DataValue::OfNat(1)),
                (key.clone(), DataValue::OfNat(2)),
                (other.clone(), DataValue::OfBool(true)),
            ]
        );

        // `insert k 9` => [(k,9),(k,2),(other,true)]: replaces the FIRST match in place
        // and does NOT fold the shadowed one. Mirrors `insertCore`.
        let mut inserted = dup.clone();
        inserted.insert(key.clone(), DataValue::OfNat(9));
        assert_eq!(inserted.len(), 3, "insert folded a shadowed entry");
        assert_eq!(inserted.entries()[0].1, DataValue::OfNat(9));
        assert_eq!(inserted.entries()[1].1, DataValue::OfNat(2));

        // `erase k` => [(other,true)]: filter removes EVERY entry for the key.
        let mut erased = dup.clone();
        erased.erase(&key);
        assert_eq!(erased.entries(), &[(other, DataValue::OfBool(true))]);

        // Structurally distinct from the map without the shadowed entry, even though the
        // two agree on every lookup. Upstream's own `eqv` also separates them (measured),
        // so this is not a distinction only our representation makes.
        let visible_only = KVMap::from_entries(vec![
            (key.clone(), DataValue::OfNat(1)),
            (
                Name::str(Name::anonymous(), "other"),
                DataValue::OfBool(true),
            ),
        ]);
        assert_eq!(dup.find(&key), visible_only.find(&key));
        assert_ne!(
            dup, visible_only,
            "the shadowed entry must not be erasable by equality"
        );

        // `insert` still cannot CREATE a duplicate — that is what makes `from_entries`
        // the only route, and why removing it would narrow us below the pin.
        let mut built = KVMap::new();
        built.insert(key.clone(), DataValue::OfNat(1));
        built.insert(key.clone(), DataValue::OfNat(2));
        assert_eq!(built.len(), 1);
    }
}
