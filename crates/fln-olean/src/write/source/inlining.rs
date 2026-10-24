//! `registerEnumAttributes` exports a sorted, module-owned `Name × InlineAttributeKind` map.
use super::*;
use crate::source_extensions::InlineKind;

impl Encoder {
    pub(super) fn inline_block(&mut self, rows: &[InlineEntry]) -> WResult<Obj> {
        self.source_array_bound(rows.len())?;
        let mut sorted: Vec<_> = rows.iter().collect();
        // EnumAttributes.getValue binary-searches imported entries by Name.quickLt.
        sorted.sort_by(|left, right| left.declaration.quick_cmp(&right.declaration));
        if sorted.iter().any(|row| row.declaration.is_anonymous())
            || sorted
                .windows(2)
                .any(|pair| pair[0].declaration == pair[1].declaration)
        {
            return Err(WriteError::Contract {
                what: "anonymous or duplicate inlining declaration",
            });
        }
        let mut entries = Vec::with_capacity(sorted.len());
        for row in sorted {
            let name = self.name(&row.declaration)?;
            let tag = match row.kind {
                InlineKind::Inline => layout::INLINE_INLINE,
                InlineKind::NoInline => layout::INLINE_NOINLINE,
                InlineKind::MacroInline => layout::INLINE_MACRO_INLINE,
                InlineKind::InlineIfReduce => layout::INLINE_INLINE_IF_REDUCE,
                InlineKind::AlwaysInline => layout::INLINE_ALWAYS_INLINE,
            };
            let mut fields = (0..layout::PROD_POINTERS)
                .map(|_| Obj::mk_nat(0))
                .collect::<Vec<_>>();
            fields[layout::PROD_FST] = name;
            fields[layout::PROD_SND] = Obj::mk_nat(tag);
            entries.push(self.ctor(0, fields, &[])?);
        }
        let entries = self.array(entries)?;
        let name = self.name(&Name::from_components(layout::INLINE_EXTENSION.split('.')))?;
        self.ctor(0, vec![name, entries], &[])
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::source_extensions::{self, DecodeLimits};

    fn metadata() -> SourceMetadata {
        SourceMetadata {
            inline: [
                ("Foo.bar", InlineKind::Inline),
                ("Foo.baz", InlineKind::NoInline),
                ("A.B.c", InlineKind::MacroInline),
                ("Nat.add", InlineKind::InlineIfReduce),
                ("Foo.qux", InlineKind::AlwaysInline),
            ]
            .into_iter()
            .map(|(name, kind)| InlineEntry {
                declaration: Name::from_components(name.split('.')),
                kind,
            })
            .collect(),
            ..SourceMetadata::default()
        }
    }

    #[test]
    fn every_inline_kind_roundtrips_in_pin_order_under_exact_writer_limits() {
        let metadata = metadata();
        let mut expected = metadata.inline.clone();
        expected.sort_by(|left, right| left.declaration.quick_cmp(&right.declaration));
        assert_ne!(metadata.inline, expected);
        for version in [2, 3] {
            let encode = |metadata: &SourceMetadata, budget| {
                let mut header = super::super::tests::header();
                header.version = version;
                encode_module_with_source_metadata(
                    super::super::tests::input(),
                    metadata,
                    header,
                    budget,
                )
            };
            let encoded = encode(&metadata, WriteBudget::default()).unwrap();
            let view = crate::region::OleanView::parse(&encoded.bytes).unwrap();
            let blocks = view
                .extension_payloads(crate::region::WalkBudget::default(), 1024 * 1024)
                .unwrap();
            let decoded = source_extensions::decode(&blocks, DecodeLimits::default()).unwrap();
            assert_eq!(decoded.inline, expected);
            assert!(decoded.uninterpreted.is_empty());
            let exact = WriteBudget {
                max_bytes: encoded.report.file_bytes,
                max_objects: encoded.report.runtime_objects,
            };
            assert_eq!(encode(&metadata, exact).unwrap().bytes, encoded.bytes);
            for budget in [
                WriteBudget {
                    max_bytes: exact.max_bytes - 1,
                    ..exact
                },
                WriteBudget {
                    max_objects: exact.max_objects - 1,
                    ..exact
                },
            ] {
                assert!(matches!(
                    encode(&metadata, budget),
                    Err(WriteError::Budget { .. })
                ));
            }
        }
    }

    #[test]
    fn duplicate_and_anonymous_inline_entries_are_refused() {
        let mut repeated = metadata();
        repeated.inline.push(repeated.inline[0].clone());
        let mut anonymous = metadata();
        anonymous.inline[0].declaration = Name::anonymous();
        for bad in [repeated, anonymous] {
            assert!(matches!(
                encode_module_with_source_metadata(
                    super::super::tests::input(),
                    &bad,
                    super::super::tests::header(),
                    WriteBudget::default()
                ),
                Err(WriteError::Contract { .. })
            ));
        }
    }
}
