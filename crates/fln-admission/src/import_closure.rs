//! Transitive module-index sets for the admission schedulers. Store only
//! occupied 64-module blocks. Dense imports share a word, while isolated
//! modules cost one block regardless of their position in the input.
use std::collections::{BTreeMap, BTreeSet};

#[derive(Default)]
pub(super) struct ImportClosure {
    blocks: Box<[(usize, u64)]>,
    members: usize,
}

impl ImportClosure {
    /// Preserve the scheduler's original treatment of cyclic rows: an
    /// unprocessed dependency contributes its empty slot, and self is included.
    pub(super) fn new(index: usize, imports: &BTreeSet<usize>, previous: &[Self]) -> Self {
        let mut blocks = BTreeMap::from([(index / 64, 1_u64 << (index % 64))]);
        for &dependency in imports {
            if dependency != index {
                for &(block, bits) in &previous[dependency].blocks {
                    *blocks.entry(block).or_default() |= bits;
                }
            }
        }
        let members = blocks.values().map(|bits| bits.count_ones() as usize).sum();
        Self {
            blocks: blocks.into_iter().collect(),
            members,
        }
    }

    pub(super) fn len(&self) -> usize {
        self.members
    }

    pub(super) fn contains(&self, index: usize) -> bool {
        self.blocks
            .binary_search_by_key(&(index / 64), |&(block, _)| block)
            .is_ok_and(|at| self.blocks[at].1 & (1 << (index % 64)) != 0)
    }

    /// Visit indices in ascending input order, exactly as a BTreeSet would.
    pub(super) fn iter(&self) -> impl Iterator<Item = usize> + '_ {
        self.blocks.iter().flat_map(|&(block, mut bits)| {
            std::iter::from_fn(move || {
                if bits == 0 {
                    return None;
                }
                let bit = bits.trailing_zeros() as usize;
                bits &= bits - 1;
                Some(block * 64 + bit)
            })
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn closure_matches_ordered_sets_across_word_boundaries_and_diamonds() {
        // Permute input indices independently of topological order. The graph
        // mixes isolated modules, chains and diamonds with overlapping imports.
        let count = 263;
        let index = |order: usize| order * 67 % count;
        let mut compact: Vec<_> = (0..count).map(|_| ImportClosure::default()).collect();
        let mut reference = vec![BTreeSet::new(); count];
        for order in 0..count {
            let module = index(order);
            let mut imports = BTreeSet::new();
            if order > 0 && order % 7 != 0 {
                imports.insert(index(order - 1));
            }
            if order > 4 {
                imports.insert(index(order / 2));
                imports.insert(index(order - 3));
            }
            let mut expected = BTreeSet::from([module]);
            for &parent in &imports {
                expected.extend(reference[parent].iter().copied());
            }
            let actual = ImportClosure::new(module, &imports, &compact);
            assert_eq!(actual.len(), expected.len());
            assert!(actual.iter().eq(expected.iter().copied()));
            for candidate in 0..=count {
                assert_eq!(actual.contains(candidate), expected.contains(&candidate));
            }
            reference[module] = expected;
            compact[module] = actual;
        }
    }

    #[test]
    fn dense_dependencies_pack_into_words_and_sparse_roots_skip_empty_ranges() {
        let high = 1_000_000;
        let sparse = ImportClosure::new(high, &BTreeSet::new(), &[]);
        assert_eq!(sparse.blocks.len(), 1);
        assert!(sparse.iter().eq([high]));
        let mut chain = Vec::new();
        for index in 0_usize..1024 {
            let parents = index.checked_sub(1).into_iter().collect();
            chain.push(ImportClosure::new(index, &parents, &chain));
        }
        let last = chain.last().unwrap();
        assert_eq!(last.blocks.len(), 16);
        assert!(last.iter().eq(0..1024));
    }
}
