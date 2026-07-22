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
#[derive(Clone)]
pub struct Name(Repr);

#[derive(Clone)]
enum Repr {
    Anonymous,
    Str(Arc<StrNode>),
    Num(Arc<NumNode>),
}

struct StrNode {
    pre: Name,
    component: String,
    hash: u64,
}

struct NumNode {
    pre: Name,
    component: u64,
    /// `true` when the source literal exceeded `u64` — upstream `Nat` is unbounded and
    /// such names hash with the 17 fallback; we preserve the observable and record the
    /// saturation honestly rather than silently wrapping.
    overflowed: bool,
    hash: u64,
}

enum NameDebugTask<'a> {
    Name(&'a Name, usize),
    Repr(&'a Repr, usize),
    StrNode(&'a StrNode, usize),
    NumNode(&'a NumNode, usize),
    Text(&'static str),
    Indent(usize),
    Str(&'a str),
    U64(u64),
    Bool(bool),
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

    /// Borrowed view of the leaf component — the structural access canonical codecs
    /// and pretty-printers need without exposing the internal representation.
    pub fn leaf_view(&self) -> LeafView<'_> {
        match &self.0 {
            Repr::Anonymous => LeafView::Anonymous,
            Repr::Str(node) => LeafView::Str(&node.component),
            Repr::Num(node) => LeafView::Num(node.component),
        }
    }

    /// Build `a.b.c`-style names from string components (test/tooling convenience).
    pub fn from_components<'a>(components: impl IntoIterator<Item = &'a str>) -> Name {
        components.into_iter().fold(Name::anonymous(), Name::str)
    }

    /// Dot-rendered form; anonymous renders as `[anonymous]` (upstream convention).
    pub fn to_display_string(&self) -> String {
        let mut chain = Vec::new();
        let mut cursor = self;
        while !cursor.is_anonymous() {
            chain.push(cursor);
            cursor = match &cursor.0 {
                Repr::Str(node) => &node.pre,
                Repr::Num(node) => &node.pre,
                Repr::Anonymous => unreachable!("loop excludes anonymous"),
            };
        }
        let mut out = String::new();
        for name in chain.into_iter().rev() {
            if !out.is_empty() {
                out.push('.');
            }
            match &name.0 {
                Repr::Str(node) => out.push_str(&node.component),
                Repr::Num(node) => out.push_str(&node.component.to_string()),
                Repr::Anonymous => unreachable!("chain excludes anonymous"),
            }
        }
        if out.is_empty() {
            "[anonymous]".to_string()
        } else {
            out
        }
    }
}

impl std::fmt::Debug for Name {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let pretty = formatter.alternate();
        let mut tasks = vec![NameDebugTask::Name(self, 0)];

        while let Some(task) = tasks.pop() {
            match task {
                NameDebugTask::Name(name, indent) if pretty => {
                    tasks.push(NameDebugTask::Text(")"));
                    tasks.push(NameDebugTask::Indent(indent));
                    tasks.push(NameDebugTask::Text(",\n"));
                    tasks.push(NameDebugTask::Repr(&name.0, indent + 1));
                    tasks.push(NameDebugTask::Indent(indent + 1));
                    tasks.push(NameDebugTask::Text("Name(\n"));
                }
                NameDebugTask::Name(name, indent) => {
                    tasks.push(NameDebugTask::Text(")"));
                    tasks.push(NameDebugTask::Repr(&name.0, indent));
                    tasks.push(NameDebugTask::Text("Name("));
                }
                NameDebugTask::Repr(Repr::Anonymous, _) => {
                    formatter.write_str("Anonymous")?;
                }
                NameDebugTask::Repr(Repr::Str(node), indent) if pretty => {
                    tasks.push(NameDebugTask::Text(")"));
                    tasks.push(NameDebugTask::Indent(indent));
                    tasks.push(NameDebugTask::Text(",\n"));
                    tasks.push(NameDebugTask::StrNode(node, indent + 1));
                    tasks.push(NameDebugTask::Indent(indent + 1));
                    tasks.push(NameDebugTask::Text("Str(\n"));
                }
                NameDebugTask::Repr(Repr::Str(node), indent) => {
                    tasks.push(NameDebugTask::Text(")"));
                    tasks.push(NameDebugTask::StrNode(node, indent));
                    tasks.push(NameDebugTask::Text("Str("));
                }
                NameDebugTask::Repr(Repr::Num(node), indent) if pretty => {
                    tasks.push(NameDebugTask::Text(")"));
                    tasks.push(NameDebugTask::Indent(indent));
                    tasks.push(NameDebugTask::Text(",\n"));
                    tasks.push(NameDebugTask::NumNode(node, indent + 1));
                    tasks.push(NameDebugTask::Indent(indent + 1));
                    tasks.push(NameDebugTask::Text("Num(\n"));
                }
                NameDebugTask::Repr(Repr::Num(node), indent) => {
                    tasks.push(NameDebugTask::Text(")"));
                    tasks.push(NameDebugTask::NumNode(node, indent));
                    tasks.push(NameDebugTask::Text("Num("));
                }
                NameDebugTask::StrNode(node, indent) if pretty => {
                    tasks.push(NameDebugTask::Text("}"));
                    tasks.push(NameDebugTask::Indent(indent));
                    tasks.push(NameDebugTask::Text(",\n"));
                    tasks.push(NameDebugTask::U64(node.hash));
                    tasks.push(NameDebugTask::Text("hash: "));
                    tasks.push(NameDebugTask::Indent(indent + 1));
                    tasks.push(NameDebugTask::Text(",\n"));
                    tasks.push(NameDebugTask::Str(&node.component));
                    tasks.push(NameDebugTask::Text("component: "));
                    tasks.push(NameDebugTask::Indent(indent + 1));
                    tasks.push(NameDebugTask::Text(",\n"));
                    tasks.push(NameDebugTask::Name(&node.pre, indent + 1));
                    tasks.push(NameDebugTask::Text("pre: "));
                    tasks.push(NameDebugTask::Indent(indent + 1));
                    tasks.push(NameDebugTask::Text("StrNode {\n"));
                }
                NameDebugTask::StrNode(node, _) => {
                    tasks.push(NameDebugTask::Text(" }"));
                    tasks.push(NameDebugTask::U64(node.hash));
                    tasks.push(NameDebugTask::Text(", hash: "));
                    tasks.push(NameDebugTask::Str(&node.component));
                    tasks.push(NameDebugTask::Text(", component: "));
                    tasks.push(NameDebugTask::Name(&node.pre, 0));
                    tasks.push(NameDebugTask::Text("StrNode { pre: "));
                }
                NameDebugTask::NumNode(node, indent) if pretty => {
                    tasks.push(NameDebugTask::Text("}"));
                    tasks.push(NameDebugTask::Indent(indent));
                    tasks.push(NameDebugTask::Text(",\n"));
                    tasks.push(NameDebugTask::U64(node.hash));
                    tasks.push(NameDebugTask::Text("hash: "));
                    tasks.push(NameDebugTask::Indent(indent + 1));
                    tasks.push(NameDebugTask::Text(",\n"));
                    tasks.push(NameDebugTask::Bool(node.overflowed));
                    tasks.push(NameDebugTask::Text("overflowed: "));
                    tasks.push(NameDebugTask::Indent(indent + 1));
                    tasks.push(NameDebugTask::Text(",\n"));
                    tasks.push(NameDebugTask::U64(node.component));
                    tasks.push(NameDebugTask::Text("component: "));
                    tasks.push(NameDebugTask::Indent(indent + 1));
                    tasks.push(NameDebugTask::Text(",\n"));
                    tasks.push(NameDebugTask::Name(&node.pre, indent + 1));
                    tasks.push(NameDebugTask::Text("pre: "));
                    tasks.push(NameDebugTask::Indent(indent + 1));
                    tasks.push(NameDebugTask::Text("NumNode {\n"));
                }
                NameDebugTask::NumNode(node, _) => {
                    tasks.push(NameDebugTask::Text(" }"));
                    tasks.push(NameDebugTask::U64(node.hash));
                    tasks.push(NameDebugTask::Text(", hash: "));
                    tasks.push(NameDebugTask::Bool(node.overflowed));
                    tasks.push(NameDebugTask::Text(", overflowed: "));
                    tasks.push(NameDebugTask::U64(node.component));
                    tasks.push(NameDebugTask::Text(", component: "));
                    tasks.push(NameDebugTask::Name(&node.pre, 0));
                    tasks.push(NameDebugTask::Text("NumNode { pre: "));
                }
                NameDebugTask::Text(text) => formatter.write_str(text)?,
                NameDebugTask::Indent(indent) => {
                    for _ in 0..indent {
                        formatter.write_str("    ")?;
                    }
                }
                NameDebugTask::Str(value) => std::fmt::Debug::fmt(&value, formatter)?,
                NameDebugTask::U64(value) => std::fmt::Debug::fmt(&value, formatter)?,
                NameDebugTask::Bool(value) => std::fmt::Debug::fmt(&value, formatter)?,
            }
        }

        Ok(())
    }
}

impl PartialEq for Name {
    fn eq(&self, other: &Self) -> bool {
        let mut left = &self.0;
        let mut right = &other.0;

        loop {
            match (left, right) {
                (Repr::Anonymous, Repr::Anonymous) => return true,
                (Repr::Str(a), Repr::Str(b)) => {
                    if Arc::ptr_eq(a, b) {
                        return true;
                    }
                    if a.component != b.component || a.hash != b.hash {
                        return false;
                    }
                    left = &a.pre.0;
                    right = &b.pre.0;
                }
                (Repr::Num(a), Repr::Num(b)) => {
                    if Arc::ptr_eq(a, b) {
                        return true;
                    }
                    if a.component != b.component
                        || a.overflowed != b.overflowed
                        || a.hash != b.hash
                    {
                        return false;
                    }
                    left = &a.pre.0;
                    right = &b.pre.0;
                }
                _ => return false,
            }
        }
    }
}

impl Eq for Name {}

impl std::hash::Hash for Name {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        enum HashTask<'a> {
            Repr(&'a Repr),
            Str(&'a String),
            U64(u64),
            Bool(bool),
        }

        let mut tasks = vec![HashTask::Repr(&self.0)];
        while let Some(task) = tasks.pop() {
            match task {
                HashTask::Repr(repr) => {
                    std::hash::Hash::hash(&std::mem::discriminant(repr), state);
                    match repr {
                        Repr::Anonymous => {}
                        Repr::Str(node) => {
                            tasks.push(HashTask::U64(node.hash));
                            tasks.push(HashTask::Str(&node.component));
                            tasks.push(HashTask::Repr(&node.pre.0));
                        }
                        Repr::Num(node) => {
                            tasks.push(HashTask::U64(node.hash));
                            tasks.push(HashTask::Bool(node.overflowed));
                            tasks.push(HashTask::U64(node.component));
                            tasks.push(HashTask::Repr(&node.pre.0));
                        }
                    }
                }
                HashTask::Str(value) => std::hash::Hash::hash(value, state),
                HashTask::U64(value) => std::hash::Hash::hash(&value, state),
                HashTask::Bool(value) => std::hash::Hash::hash(&value, state),
            }
        }
    }
}

impl Drop for Name {
    fn drop(&mut self) {
        // `Name` is itself a persistent Arc chain.  An Expr/Level node containing
        // one deeply qualified name must not reintroduce a recursive destructor
        // cascade after those outer structures have been drained iteratively.
        let mut repr = std::mem::replace(&mut self.0, Repr::Anonymous);
        let mut drained = 0usize;
        loop {
            repr = match repr {
                Repr::Anonymous => break,
                Repr::Str(node) => {
                    let Some(StrNode { mut pre, .. }) = Arc::into_inner(node) else {
                        break;
                    };
                    drained += 1;
                    if drained.is_multiple_of(4096) {
                        std::thread::yield_now();
                    }
                    std::mem::replace(&mut pre.0, Repr::Anonymous)
                }
                Repr::Num(node) => {
                    let Some(NumNode { mut pre, .. }) = Arc::into_inner(node) else {
                        break;
                    };
                    drained += 1;
                    if drained.is_multiple_of(4096) {
                        std::thread::yield_now();
                    }
                    std::mem::replace(&mut pre.0, Repr::Anonymous)
                }
            };
        }
    }
}

impl Default for Name {
    fn default() -> Name {
        Name::anonymous()
    }
}

/// Borrowed leaf-component view (see [`Name::leaf_view`]). An overflowed `num`
/// component still reports [`Name::component_overflowed`] separately.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LeafView<'a> {
    Anonymous,
    Str(&'a str),
    Num(u64),
}

/// `Name.cmp` (vendor: src/Lean/Data/Name.lean:67-81) IS this type's `Ord`:
/// `anonymous` is least; equal leaf constructors compare their prefixes first and
/// then their components, while different leaf constructors order `num` before
/// `str` immediately. String components compare byte-wise, which equals Lean's
/// codepoint-lexicographic `compare` because UTF-8 is order-preserving. `Name.lt`
/// is `<` via this order. The hash-first `quickCmp` order is deliberately separate
/// — see [`Name::quick_cmp`].
impl Ord for Name {
    fn cmp(&self, other: &Name) -> std::cmp::Ordering {
        use std::cmp::Ordering;

        let mut left = &self.0;
        let mut right = &other.0;
        let mut equal_constructor_pairs = Vec::new();
        loop {
            match (left, right) {
                (Repr::Anonymous, Repr::Anonymous) => break,
                (Repr::Anonymous, _) => return Ordering::Less,
                (_, Repr::Anonymous) => return Ordering::Greater,
                (Repr::Num(a), Repr::Num(b)) => {
                    if Arc::ptr_eq(a, b) {
                        break;
                    }
                    equal_constructor_pairs.push((left, right));
                    left = &a.pre.0;
                    right = &b.pre.0;
                }
                (Repr::Num(_), Repr::Str(_)) => return Ordering::Less,
                (Repr::Str(_), Repr::Num(_)) => return Ordering::Greater,
                (Repr::Str(a), Repr::Str(b)) => {
                    if Arc::ptr_eq(a, b) {
                        break;
                    }
                    equal_constructor_pairs.push((left, right));
                    left = &a.pre.0;
                    right = &b.pre.0;
                }
            }
        }

        for (left, right) in equal_constructor_pairs.into_iter().rev() {
            let order = match (left, right) {
                (Repr::Num(a), Repr::Num(b)) => {
                    (a.component, a.overflowed).cmp(&(b.component, b.overflowed))
                }
                (Repr::Str(a), Repr::Str(b)) => a.component.cmp(&b.component),
                _ => unreachable!("the descent records only equal constructors"),
            };
            if order != Ordering::Equal {
                return order;
            }
        }

        Ordering::Equal
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

        let mut left = &self.0;
        let mut right = &other.0;
        loop {
            match (left, right) {
                (Repr::Anonymous, Repr::Anonymous) => return Ordering::Equal,
                (Repr::Anonymous, _) => return Ordering::Less,
                (_, Repr::Anonymous) => return Ordering::Greater,
                (Repr::Num(a), Repr::Num(b)) => {
                    if Arc::ptr_eq(a, b) {
                        return Ordering::Equal;
                    }
                    let order = (a.component, a.overflowed).cmp(&(b.component, b.overflowed));
                    if order != Ordering::Equal {
                        return order;
                    }
                    left = &a.pre.0;
                    right = &b.pre.0;
                }
                (Repr::Num(_), Repr::Str(_)) => return Ordering::Less,
                (Repr::Str(_), Repr::Num(_)) => return Ordering::Greater,
                (Repr::Str(a), Repr::Str(b)) => {
                    if Arc::ptr_eq(a, b) {
                        return Ordering::Equal;
                    }
                    let order = a.component.cmp(&b.component);
                    if order != Ordering::Equal {
                        return order;
                    }
                    left = &a.pre.0;
                    right = &b.pre.0;
                }
            }
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
    use std::fmt::Write as _;
    use std::hash::{DefaultHasher, Hasher as _};

    #[derive(Debug, Clone, PartialEq, Eq, Hash)]
    struct LegacyName(LegacyRepr);

    #[derive(Debug, Clone, PartialEq, Eq, Hash)]
    enum LegacyRepr {
        Anonymous,
        Str(Box<LegacyStrNode>),
        Num(Box<LegacyNumNode>),
    }

    #[derive(Debug, Clone, PartialEq, Eq, Hash)]
    struct LegacyStrNode {
        pre: LegacyName,
        component: String,
        hash: u64,
    }

    #[derive(Debug, Clone, PartialEq, Eq, Hash)]
    struct LegacyNumNode {
        pre: LegacyName,
        component: u64,
        overflowed: bool,
        hash: u64,
    }

    impl LegacyName {
        fn anonymous() -> Self {
            Self(LegacyRepr::Anonymous)
        }

        fn str(pre: Self, component: &str) -> Self {
            let hash = mix_hash(pre.pin_hash(), string_hash(component));
            Self(LegacyRepr::Str(Box::new(LegacyStrNode {
                pre,
                component: component.to_owned(),
                hash,
            })))
        }

        fn num(pre: Self, component: u64) -> Self {
            let hash = mix_hash(pre.pin_hash(), component);
            Self(LegacyRepr::Num(Box::new(LegacyNumNode {
                pre,
                component,
                overflowed: false,
                hash,
            })))
        }

        fn num_overflowing(pre: Self, component: u64) -> Self {
            let hash = mix_hash(pre.pin_hash(), NUM_OVERFLOW_HASH);
            Self(LegacyRepr::Num(Box::new(LegacyNumNode {
                pre,
                component,
                overflowed: true,
                hash,
            })))
        }

        fn pin_hash(&self) -> u64 {
            match &self.0 {
                LegacyRepr::Anonymous => ANONYMOUS_HASH,
                LegacyRepr::Str(node) => node.hash,
                LegacyRepr::Num(node) => node.hash,
            }
        }
    }

    fn standard_hash(value: &impl std::hash::Hash) -> u64 {
        let mut hasher = DefaultHasher::new();
        value.hash(&mut hasher);
        hasher.finish()
    }

    fn normalized_legacy_debug(value: &LegacyName, pretty: bool) -> String {
        let rendered = if pretty {
            format!("{value:#?}")
        } else {
            format!("{value:?}")
        };
        rendered
            .replace("LegacyName", "Name")
            .replace("LegacyStrNode", "StrNode")
            .replace("LegacyNumNode", "NumNode")
    }

    fn recursive_cmp(left: &Name, right: &Name) -> std::cmp::Ordering {
        use std::cmp::Ordering;
        match (&left.0, &right.0) {
            (Repr::Anonymous, Repr::Anonymous) => Ordering::Equal,
            (Repr::Anonymous, _) => Ordering::Less,
            (_, Repr::Anonymous) => Ordering::Greater,
            (Repr::Num(a), Repr::Num(b)) => recursive_cmp(&a.pre, &b.pre)
                .then_with(|| (a.component, a.overflowed).cmp(&(b.component, b.overflowed))),
            (Repr::Num(_), Repr::Str(_)) => Ordering::Less,
            (Repr::Str(_), Repr::Num(_)) => Ordering::Greater,
            (Repr::Str(a), Repr::Str(b)) => {
                recursive_cmp(&a.pre, &b.pre).then_with(|| a.component.cmp(&b.component))
            }
        }
    }

    fn recursive_quick_cmp_aux(left: &Name, right: &Name) -> std::cmp::Ordering {
        use std::cmp::Ordering;
        match (&left.0, &right.0) {
            (Repr::Anonymous, Repr::Anonymous) => Ordering::Equal,
            (Repr::Anonymous, _) => Ordering::Less,
            (_, Repr::Anonymous) => Ordering::Greater,
            (Repr::Num(a), Repr::Num(b)) => (a.component, a.overflowed)
                .cmp(&(b.component, b.overflowed))
                .then_with(|| recursive_quick_cmp_aux(&a.pre, &b.pre)),
            (Repr::Num(_), Repr::Str(_)) => Ordering::Less,
            (Repr::Str(_), Repr::Num(_)) => Ordering::Greater,
            (Repr::Str(a), Repr::Str(b)) => a
                .component
                .cmp(&b.component)
                .then_with(|| recursive_quick_cmp_aux(&a.pre, &b.pre)),
        }
    }

    fn mixed_name(depth: usize) -> Name {
        let mut name = Name::anonymous();
        for index in 0..depth {
            name = match index % 3 {
                0 => Name::str(name, "segment"),
                1 => Name::num(name, index as u64),
                _ => Name::num_overflowing(name, index as u64),
            };
        }
        name
    }

    #[derive(Default)]
    struct CountingWriter {
        bytes: usize,
    }

    impl std::fmt::Write for CountingWriter {
        fn write_str(&mut self, text: &str) -> std::fmt::Result {
            self.bytes = self.bytes.checked_add(text.len()).ok_or(std::fmt::Error)?;
            Ok(())
        }
    }

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

    #[test]
    fn shallow_traits_match_the_previous_derived_and_recursive_behavior() {
        let pairs = [
            (Name::anonymous(), LegacyName::anonymous()),
            (
                Name::str(Name::anonymous(), "Lean"),
                LegacyName::str(LegacyName::anonymous(), "Lean"),
            ),
            (
                Name::str(Name::str(Name::anonymous(), "Lean"), "Meta"),
                LegacyName::str(LegacyName::str(LegacyName::anonymous(), "Lean"), "Meta"),
            ),
            (
                Name::num(Name::str(Name::anonymous(), "_uniq"), 231),
                LegacyName::num(LegacyName::str(LegacyName::anonymous(), "_uniq"), 231),
            ),
            (
                Name::num_overflowing(Name::str(Name::anonymous(), "_uniq"), u64::MAX),
                LegacyName::num_overflowing(
                    LegacyName::str(LegacyName::anonymous(), "_uniq"),
                    u64::MAX,
                ),
            ),
            (
                Name::str(Name::num(Name::anonymous(), 7), "tail\nquoted"),
                LegacyName::str(LegacyName::num(LegacyName::anonymous(), 7), "tail\nquoted"),
            ),
        ];

        for (actual, legacy) in &pairs {
            assert_eq!(
                format!("{actual:?}"),
                normalized_legacy_debug(legacy, false)
            );
            assert_eq!(
                format!("{actual:#?}"),
                normalized_legacy_debug(legacy, true)
            );
            assert_eq!(standard_hash(actual), standard_hash(legacy));
        }

        for (left_index, (left, legacy_left)) in pairs.iter().enumerate() {
            for (right_index, (right, legacy_right)) in pairs.iter().enumerate() {
                assert_eq!(left == right, legacy_left == legacy_right);
                assert_eq!(left.cmp(right), recursive_cmp(left, right));
                assert_eq!(
                    left.quick_cmp_aux(right),
                    recursive_quick_cmp_aux(left, right),
                    "quickCmpAux mismatch at ({left_index}, {right_index})"
                );
            }
        }
    }

    #[test]
    fn deep_name_operations_and_randomized_clone_drops_are_stack_bounded() {
        let outcome = std::thread::Builder::new()
            .stack_size(1024 * 1024)
            .spawn(|| {
                const DEPTH: usize = 100_000;
                let left = mixed_name(DEPTH);
                let right = mixed_name(DEPTH);

                assert!(left == right, "independently built deep names differ");
                assert_eq!(standard_hash(&left), standard_hash(&right));
                assert_eq!(left.cmp(&right), std::cmp::Ordering::Equal);
                assert_eq!(left.quick_cmp(&right), std::cmp::Ordering::Equal);
                assert_eq!(left.quick_cmp_aux(&right), std::cmp::Ordering::Equal);

                let mut debug_sink = CountingWriter::default();
                write!(&mut debug_sink, "{left:?}").expect("counting writer is infallible");
                assert!(debug_sink.bytes > DEPTH);

                let shared = left.clone();
                let earlier = Name::str(shared.clone(), "a");
                let later = Name::str(shared, "b");
                assert!(earlier != later);
                assert_eq!(earlier.cmp(&later), std::cmp::Ordering::Less);
                assert_eq!(earlier.quick_cmp_aux(&later), std::cmp::Ordering::Less);

                let mut cursor = right.clone();
                let mut clones = Vec::with_capacity(128);
                for _ in 0..128 {
                    clones.push(cursor.clone());
                    for _ in 0..257 {
                        cursor = cursor.parent();
                    }
                }
                let mut state = 0x4d59_5df4_d0f3_3173_u64;
                for index in (1..clones.len()).rev() {
                    state = state
                        .wrapping_mul(6364136223846793005)
                        .wrapping_add(1442695040888963407);
                    clones.swap(index, state as usize % (index + 1));
                }
                while let Some(name) = clones.pop() {
                    drop(name);
                }
            })
            .expect("spawn bounded-stack Name worker")
            .join();
        assert!(
            outcome.is_ok(),
            "deep Name operations exhausted the bounded worker stack"
        );
    }

    #[test]
    fn concurrent_final_owner_drop_is_stack_bounded_and_recovers() {
        let root = mixed_name(100_000);
        let clone = root.clone();
        let barrier = Arc::new(std::sync::Barrier::new(3));
        let spawn = |name, barrier: Arc<std::sync::Barrier>| {
            std::thread::Builder::new()
                .stack_size(1024 * 1024)
                .spawn(move || {
                    barrier.wait();
                    drop(name);
                })
                .expect("spawn concurrent Name dropper")
        };
        let first = spawn(root, barrier.clone());
        let second = spawn(clone, barrier.clone());
        barrier.wait();
        first.join().expect("first Name dropper completes");
        second.join().expect("second Name dropper completes");

        let recovery = Name::str(Name::anonymous(), "recovery");
        assert_eq!(recovery.to_display_string(), "recovery");
        assert_eq!(recovery, recovery.clone());
    }
}
