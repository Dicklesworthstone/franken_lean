//! Hierarchical names with the Reference-observable hash (plan §1.1, §21).
//!
//! Semantics anchor: `Name` in vendor/lean4-src/src/Init/Prelude.lean:4693-4718 —
//! `anonymous | str (pre : Name) (str : String) | num (pre : Name) (i : Nat)` with the
//! `@[computed_field] hash`:
//!
//! ```text
//! | .anonymous => 1723
//! | .str p s   => mixHash p.hash s.hash
//! | .num p v   => mixHash p.hash (if v < UInt64.size then v else 17)
//! ```
//!
//! The hash is stored at construction exactly as upstream stores its computed field, so
//! `hash` is O(1) and observably identical. Macro-scope decoration (Quill) rides the
//! ordinary `num`/`str` constructors per upstream convention; fln-syntax owns those
//! conventions — this type only guarantees the substrate observables.

use std::sync::Arc;

use crate::lean_hash::{mix_hash, string_hash};

/// Hash of `Name.anonymous` (Prelude:4714).
const ANONYMOUS_HASH: u64 = 1723;
/// `num` component fallback when the literal exceeds `UInt64.size` (Prelude:4717).
const NUM_OVERFLOW_HASH: u64 = 17;

/// A hierarchical name. Immutable and cheaply clonable; component sharing mirrors the
/// upstream persistent structure (a name is its parent plus one component).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Name(Repr);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum Repr {
    Anonymous,
    Str(Arc<StrNode>),
    Num(Arc<NumNode>),
}

#[derive(Debug, PartialEq, Eq, Hash)]
struct StrNode {
    pre: Name,
    component: String,
    hash: u64,
}

#[derive(Debug, PartialEq, Eq, Hash)]
struct NumNode {
    pre: Name,
    component: u64,
    /// `true` when the source literal exceeded `u64` — upstream `Nat` is unbounded and
    /// such names hash with the 17 fallback; we preserve the observable and record the
    /// saturation honestly rather than silently wrapping.
    overflowed: bool,
    hash: u64,
}

impl Name {
    /// `Name.anonymous`.
    pub const fn anonymous() -> Name {
        Name(Repr::Anonymous)
    }

    /// `Name.str pre s`.
    pub fn str(pre: Name, component: impl Into<String>) -> Name {
        let component = component.into();
        let hash = mix_hash(pre.hash(), string_hash(&component));
        Name(Repr::Str(Arc::new(StrNode {
            pre,
            component,
            hash,
        })))
    }

    /// `Name.num pre v` for a component that fits `u64` (every name the toolchain
    /// itself generates does).
    pub fn num(pre: Name, component: u64) -> Name {
        let hash = mix_hash(pre.hash(), component);
        Name(Repr::Num(Arc::new(NumNode {
            pre,
            component,
            overflowed: false,
            hash,
        })))
    }

    /// `Name.num pre v` where `v >= UInt64.size` (decoded from source or artifacts):
    /// hashes with the upstream overflow constant 17. The saturated component value is
    /// retained for display; `component_overflowed` reports the loss.
    pub fn num_overflowing(pre: Name, saturated: u64) -> Name {
        let hash = mix_hash(pre.hash(), NUM_OVERFLOW_HASH);
        Name(Repr::Num(Arc::new(NumNode {
            pre,
            component: saturated,
            overflowed: true,
            hash,
        })))
    }

    /// The Reference-observable hash (`Name.hash`), O(1).
    pub fn hash(&self) -> u64 {
        match &self.0 {
            Repr::Anonymous => ANONYMOUS_HASH,
            Repr::Str(node) => node.hash,
            Repr::Num(node) => node.hash,
        }
    }

    pub fn is_anonymous(&self) -> bool {
        matches!(self.0, Repr::Anonymous)
    }

    /// The parent name (`Name.getPrefix`); anonymous for the root.
    pub fn parent(&self) -> Name {
        match &self.0 {
            Repr::Anonymous => Name::anonymous(),
            Repr::Str(node) => node.pre.clone(),
            Repr::Num(node) => node.pre.clone(),
        }
    }

    pub fn component_overflowed(&self) -> bool {
        matches!(&self.0, Repr::Num(node) if node.overflowed)
    }

    /// Build `a.b.c`-style names from string components (test/tooling convenience).
    pub fn from_components<'a>(components: impl IntoIterator<Item = &'a str>) -> Name {
        components.into_iter().fold(Name::anonymous(), Name::str)
    }

    /// Dot-rendered form; anonymous renders as `[anonymous]` (upstream convention).
    pub fn to_display_string(&self) -> String {
        fn go(name: &Name, out: &mut String) {
            match &name.0 {
                Repr::Anonymous => {}
                Repr::Str(node) => {
                    go(&node.pre, out);
                    if !out.is_empty() {
                        out.push('.');
                    }
                    out.push_str(&node.component);
                }
                Repr::Num(node) => {
                    go(&node.pre, out);
                    if !out.is_empty() {
                        out.push('.');
                    }
                    out.push_str(&node.component.to_string());
                }
            }
        }
        let mut out = String::new();
        go(self, &mut out);
        if out.is_empty() {
            "[anonymous]".to_string()
        } else {
            out
        }
    }
}

impl Default for Name {
    fn default() -> Name {
        Name::anonymous()
    }
}

/// `Name.cmp` (vendor: src/Lean/Data/Name.lean:67-81) IS this type's `Ord`:
/// prefix-first lexicographic order; `anonymous` least; at equal prefixes a `num`
/// component sorts before a `str` component. String components compare byte-wise,
/// which equals Lean's codepoint-lexicographic `compare` because UTF-8 is
/// order-preserving. `Name.lt` is `<` via this order. The hash-first `quickCmp`
/// order is deliberately separate — see [`Name::quick_cmp`].
impl Ord for Name {
    fn cmp(&self, other: &Name) -> std::cmp::Ordering {
        use std::cmp::Ordering;
        match (&self.0, &other.0) {
            (Repr::Anonymous, Repr::Anonymous) => Ordering::Equal,
            (Repr::Anonymous, _) => Ordering::Less,
            (_, Repr::Anonymous) => Ordering::Greater,
            (Repr::Num(a), Repr::Num(b)) => a
                .pre
                .cmp(&b.pre)
                .then_with(|| (a.component, a.overflowed).cmp(&(b.component, b.overflowed))),
            (Repr::Num(_), Repr::Str(_)) => Ordering::Less,
            (Repr::Str(_), Repr::Num(_)) => Ordering::Greater,
            (Repr::Str(a), Repr::Str(b)) => a
                .pre
                .cmp(&b.pre)
                .then_with(|| a.component.cmp(&b.component)),
        }
    }
}

impl PartialOrd for Name {
    fn partial_cmp(&self, other: &Name) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Name {
    /// `Name.quickCmpAux` (Name.lean:85-98): leaf component first, then the prefix —
    /// deliberately NOT the same total order as [`Name::cmp`].
    fn quick_cmp_aux(&self, other: &Name) -> std::cmp::Ordering {
        use std::cmp::Ordering;
        match (&self.0, &other.0) {
            (Repr::Anonymous, Repr::Anonymous) => Ordering::Equal,
            (Repr::Anonymous, _) => Ordering::Less,
            (_, Repr::Anonymous) => Ordering::Greater,
            (Repr::Num(a), Repr::Num(b)) => (a.component, a.overflowed)
                .cmp(&(b.component, b.overflowed))
                .then_with(|| a.pre.quick_cmp_aux(&b.pre)),
            (Repr::Num(_), Repr::Str(_)) => Ordering::Less,
            (Repr::Str(_), Repr::Num(_)) => Ordering::Greater,
            (Repr::Str(a), Repr::Str(b)) => a
                .component
                .cmp(&b.component)
                .then_with(|| a.pre.quick_cmp_aux(&b.pre)),
        }
    }

    /// `Name.quickCmp` (Name.lean:107-110): stored-hash comparison first, structural
    /// tiebreak via [`Name::quick_cmp_aux`]. The order every upstream `NameMap`/
    /// `NameSet`-class container observes.
    pub fn quick_cmp(&self, other: &Name) -> std::cmp::Ordering {
        self.hash()
            .cmp(&other.hash())
            .then_with(|| self.quick_cmp_aux(other))
    }

    /// `Name.quickLt`.
    pub fn quick_lt(&self, other: &Name) -> bool {
        self.quick_cmp(other) == std::cmp::Ordering::Less
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn anonymous_hash_is_the_pin_constant() {
        assert_eq!(Name::anonymous().hash(), 1723);
    }

    #[test]
    fn str_hash_is_mix_of_parent_and_component() {
        let lean = Name::str(Name::anonymous(), "Lean");
        assert_eq!(lean.hash(), mix_hash(1723, string_hash("Lean")));
        let meta = Name::str(lean.clone(), "Meta");
        assert_eq!(meta.hash(), mix_hash(lean.hash(), string_hash("Meta")));
    }

    #[test]
    fn num_hash_mixes_value_and_overflow_uses_17() {
        let uniq = Name::str(Name::anonymous(), "_uniq");
        let n = Name::num(uniq.clone(), 231);
        assert_eq!(n.hash(), mix_hash(uniq.hash(), 231));
        assert!(!n.component_overflowed());

        let big = Name::num_overflowing(uniq.clone(), u64::MAX);
        assert_eq!(big.hash(), mix_hash(uniq.hash(), 17));
        assert!(big.component_overflowed());
    }

    #[test]
    fn structural_equality_and_display() {
        let a = Name::from_components(["Lean", "Meta", "run"]);
        let b = Name::str(
            Name::str(Name::str(Name::anonymous(), "Lean"), "Meta"),
            "run",
        );
        assert_eq!(a, b);
        assert_eq!(a.hash(), b.hash());
        assert_eq!(a.to_display_string(), "Lean.Meta.run");
        assert_eq!(Name::anonymous().to_display_string(), "[anonymous]");
        assert_eq!(a.parent().to_display_string(), "Lean.Meta");
        assert!(Name::anonymous().parent().is_anonymous());
    }
}
