//! Distinct semantic-kind newtypes (plan §8.2b): **no integer is accepted as two
//! semantic kinds anywhere in the workspace.** Constructors are public — these are
//! vocabulary, not capabilities — but nothing converts between kinds implicitly, and
//! none of them implement arithmetic beyond what its semantics justify.

macro_rules! semantic_id {
    ($(#[$doc:meta])* $name:ident($repr:ty)) => {
        $(#[$doc])*
        #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
        pub struct $name(pub $repr);

        impl $name {
            pub const fn get(self) -> $repr {
                self.0
            }
        }
    };
}

semantic_id! {
    /// Identity of a declaration name interned in an environment (plan §8.2b).
    DeclNameId(u64)
}
semantic_id! {
    /// Identity of an expression node in a decoded term graph (plan §8.2b).
    ExprNodeId(u64)
}
semantic_id! {
    /// A de Bruijn binder depth. Distinct from a loose-bvar *range* and from any
    /// other counter; see [`crate::expr`] for where each is meaningful.
    BinderDepth(u32)
}
semantic_id! {
    /// Reduction fuel (heartbeat-class budget). Exhaustion is a typed
    /// `Inconclusive`, never a rejection (FL-INV-07).
    ReductionFuel(u64)
}
semantic_id! {
    /// Identity of a committed environment state (a logical root in the Ledger).
    EnvCommitId(u64)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ids_are_distinct_types_with_value_semantics() {
        let a = DeclNameId(7);
        let b = DeclNameId(7);
        assert_eq!(a, b);
        assert_eq!(a.get(), 7);
        // Distinctness across kinds is enforced at compile time: DeclNameId(7) and
        // ExprNodeId(7) do not unify. This test documents the value semantics only.
        assert_eq!(BinderDepth(0).get(), 0);
        assert!(ReductionFuel(1) > ReductionFuel(0));
        assert_eq!(EnvCommitId(u64::MAX).get(), u64::MAX);
    }
}
