//! `Lean.aliasExtension` is a chronological array of pairs, not a sorted map.
//! Its SimplePersistentEnvExtension exports entries in insertion order.
use super::*;

impl Encoder {
    pub(super) fn alias_block(&mut self, aliases: &[AliasEntry]) -> WResult<Obj> {
        self.source_array_bound(aliases.len())?;
        let mut entries = Vec::with_capacity(aliases.len());
        for row in aliases {
            if row.alias.is_anonymous() || row.declaration.is_anonymous() {
                return Err(WriteError::Contract {
                    what: "anonymous alias or target declaration",
                });
            }
            let alias = self.name(&row.alias)?;
            let declaration = self.name(&row.declaration)?;
            let mut fields: Vec<_> = (0..layout::PROD_POINTERS).map(|_| Obj::mk_nat(0)).collect();
            fields[layout::PROD_FST] = alias;
            fields[layout::PROD_SND] = declaration;
            entries.push(self.ctor(0, fields, &[0; layout::PROD_SCALAR_BYTES])?);
        }
        let entries = self.array(entries)?;
        let name = self.name(&Name::from_components(layout::ALIAS_EXTENSION.split('.')))?;
        self.ctor(0, vec![name, entries], &[])
    }
}

#[cfg(test)]
mod tests;
