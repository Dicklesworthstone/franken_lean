//! The pin's global user-pattern journal. No native-private codec is emitted.
//! Caller-supplied patterns are already normalized, including ground and
//! don't-care gadgets; writing them does not grant logical authority.
use super::*;

impl Encoder {
    fn grind_theorem(&mut self, row: &GrindPatternEntry) -> WResult<Obj> {
        self.source_array_bound(row.patterns.len())?;
        self.source_array_bound(row.symbols.len())?;
        row.validate()
            .map_err(|what| WriteError::Contract { what })?;
        let mut patterns = Vec::with_capacity(row.patterns.len());
        for pattern in &row.patterns {
            patterns.push(self.expression(pattern)?);
        }
        let patterns = self.list(patterns)?;
        let mut symbols = Vec::with_capacity(row.symbols.len());
        for symbol in &row.symbols {
            let mut fields = (0..layout::GRIND_HEAD_CONST_POINTERS)
                .map(|_| Obj::mk_nat(0))
                .collect::<Vec<_>>();
            fields[layout::GRIND_HEAD_CONST_CONST_NAME] = self.name(symbol)?;
            symbols.push(self.ctor(layout::GRIND_HEAD_CONST, fields, &[])?);
        }
        let symbols = self.list(symbols)?;
        let mut origin_fields = (0..layout::GRIND_ORIGIN_DECL_POINTERS)
            .map(|_| Obj::mk_nat(0))
            .collect::<Vec<_>>();
        origin_fields[layout::GRIND_ORIGIN_DECL_DECL_NAME] = self.name(&row.declaration)?;
        let origin = self.ctor(layout::GRIND_ORIGIN_DECL, origin_fields, &[])?;
        let mut fields = (0..layout::GRIND_THM_POINTERS)
            .map(|_| Obj::mk_nat(0))
            .collect::<Vec<_>>();
        // Global constant proofs use the declaration's universe parameters;
        // the theorem's separate levelParams array is empty at the pin.
        fields[layout::GRIND_THM_LEVEL_PARAMS] = self.array(vec![])?;
        fields[layout::GRIND_THM_PROOF] = self.expression(&row.proof)?;
        fields[layout::GRIND_THM_NUM_PARAMS] = self.nat_u64(u64::from(row.num_params))?;
        fields[layout::GRIND_THM_PATTERNS] = patterns;
        fields[layout::GRIND_THM_SYMBOLS] = symbols;
        fields[layout::GRIND_THM_ORIGIN] = origin;
        fields[layout::GRIND_THM_KIND] = Obj::mk_nat(usize::from(layout::GRIND_KIND_USER));
        fields[layout::GRIND_THM_CNSTRS] = Obj::mk_nat(usize::from(layout::LIST_NIL));
        let mut scalars = [0; layout::GRIND_THM_SCALAR_BYTES];
        scalars[layout::GRIND_THM_MIN_INDEXABLE_SCALAR] = 0;
        self.ctor(0, fields, &scalars)
    }

    pub(super) fn grind_block(&mut self, rows: &[GrindPatternEntry]) -> WResult<Obj> {
        self.source_array_bound(rows.len())?;
        let mut entries = Vec::with_capacity(rows.len());
        for row in rows {
            let theorem = self.grind_theorem(row)?;
            let mut fields = (0..layout::GRIND_ENTRY_EMATCH_POINTERS)
                .map(|_| Obj::mk_nat(0))
                .collect::<Vec<_>>();
            fields[layout::GRIND_ENTRY_EMATCH_THM] = theorem;
            let entry = self.ctor(layout::GRIND_ENTRY_EMATCH, fields, &[])?;
            entries.push(self.ctor(layout::SCOPE_GLOBAL, vec![entry], &[])?);
        }
        let entries = self.array(entries)?;
        let name = self.name(&Name::from_components(layout::GRIND_EXTENSION.split('.')))?;
        self.ctor(0, vec![name, entries], &[])
    }
}

#[cfg(test)]
mod tests;
