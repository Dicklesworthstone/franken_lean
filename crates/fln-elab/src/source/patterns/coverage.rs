//! Constructor inventories for eliminating unreachable matrix fallbacks.
use super::*;

impl Context {
    /// A fallback is unreachable only when the resolved heads are exactly the
    /// constructors of one admitted family. This is a decision-tree fact, not
    /// a typing judgment: the ordinary match backend must still check every
    /// generated constructor branch against the actual discriminant.
    pub(super) fn matrix_constructors_exhaustive(
        &mut self,
        heads: &[usize],
        arena: &[Pattern<'_>],
        canonical: &HashMap<Head, Head>,
    ) -> Result<bool, NatDefinitionElabError> {
        let Some(&first) = heads.first() else {
            return Ok(false);
        };
        let Pattern::Constructor(constructor) = &arena[first] else {
            return Ok(false);
        };
        let first = &canonical[&constructor.head];
        if first.relative {
            return Ok(false);
        }
        let Some(ConstantInfo::Ctor(constructor)) = self.txn.env.find(&first.name) else {
            return Ok(false);
        };
        let family = constructor.induct.clone();
        let Some(ConstantInfo::Induct(inductive)) = self.txn.env.find(&family) else {
            return Ok(false);
        };
        // Bound the inventory copy by the already bounded source matrix. Do
        // not scan or copy an arbitrarily large family to decide a small match.
        if inductive.ctors.len() != heads.len() {
            return Ok(false);
        }
        let constructors = inductive.ctors.clone();
        let mut missing = HashSet::new();
        for constructor in constructors {
            self.tick()?;
            missing.insert(constructor);
        }
        for &pattern in heads {
            self.tick()?;
            let Pattern::Constructor(constructor) = &arena[pattern] else {
                return Ok(false);
            };
            let head = &canonical[&constructor.head];
            if head.relative || !missing.remove(&head.name) {
                return Ok(false);
            }
            let Some(ConstantInfo::Ctor(constructor)) = self.txn.env.find(&head.name) else {
                return Ok(false);
            };
            if constructor.induct != family {
                return Ok(false);
            }
        }
        Ok(missing.is_empty())
    }
}
