//! Pin projection function metadata, using generated declaration layouts.
use super::*;

impl Encoder {
    fn projection_entry(&mut self, row: &ProjectionEntry) -> WResult<Obj> {
        let mut fields = (0..layout::PROJECTION_POINTERS)
            .map(|_| Obj::mk_nat(0))
            .collect::<Vec<_>>();
        fields[layout::PROJECTION_CTOR_NAME] = self.name(&row.constructor)?;
        fields[layout::PROJECTION_NUM_PARAMS] = self.nat_u64(u64::from(row.num_params))?;
        fields[layout::PROJECTION_I] = self.nat_u64(u64::from(row.field_index))?;
        let mut scalars = [0; layout::PROJECTION_SCALAR_BYTES];
        scalars[layout::PROJECTION_FROM_CLASS_SCALAR] = u8::from(row.from_class);
        let info = self.ctor(0, fields, &scalars)?;
        let mut pair = (0..layout::PROD_POINTERS)
            .map(|_| Obj::mk_nat(0))
            .collect::<Vec<_>>();
        pair[layout::PROD_FST] = self.name(&row.declaration)?;
        pair[layout::PROD_SND] = info;
        self.ctor(0, pair, &[])
    }

    pub(super) fn projection_block(&mut self, rows: &[ProjectionEntry]) -> WResult<Obj> {
        self.source_array_bound(rows.len())?;
        let mut sorted = rows.iter().collect::<Vec<_>>();
        sorted.sort_by(|left, right| left.declaration.quick_cmp(&right.declaration));
        if sorted
            .iter()
            .any(|row| row.declaration.is_anonymous() || row.constructor.is_anonymous())
            || sorted
                .windows(2)
                .any(|rows| rows[0].declaration == rows[1].declaration)
        {
            return Err(WriteError::Contract {
                what: "anonymous or duplicate projection function metadata",
            });
        }
        let mut entries = Vec::with_capacity(sorted.len());
        for row in sorted {
            entries.push(self.projection_entry(row)?);
        }
        let entries = self.array(entries)?;
        let name = self.name(&Name::from_components(
            layout::PROJECTION_EXTENSION.split('.'),
        ))?;
        self.ctor(0, vec![name, entries], &[])
    }
}

#[cfg(test)]
mod tests;
