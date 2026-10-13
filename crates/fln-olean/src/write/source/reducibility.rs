//! The pin's sorted module-local reducibilityCore map.
use super::*;
use crate::source_extensions::{ReducibilityEntry, ReducibilityStatus};

impl Encoder {
    pub(super) fn reducibility_block(&mut self, rows: &[ReducibilityEntry]) -> WResult<Obj> {
        self.source_array_bound(rows.len())?;
        let mut sorted: Vec<_> = rows.iter().collect();
        // getReducibilityStatusCore binary-searches a module's entries using
        // Name.quickLt, matching reducibilityCoreExt.exportEntriesFn exactly.
        sorted.sort_by(|left, right| left.declaration.quick_cmp(&right.declaration));
        if sorted.iter().any(|row| row.declaration.is_anonymous())
            || sorted
                .windows(2)
                .any(|pair| pair[0].declaration == pair[1].declaration)
        {
            return Err(WriteError::Contract {
                what: "anonymous or duplicate reducibility declaration",
            });
        }
        let mut entries = Vec::with_capacity(sorted.len());
        for row in sorted {
            let name = self.name(&row.declaration)?;
            let tag = match row.status {
                ReducibilityStatus::Reducible => layout::REDUCIBILITY_REDUCIBLE,
                ReducibilityStatus::Semireducible => layout::REDUCIBILITY_SEMIREDUCIBLE,
                ReducibilityStatus::Irreducible => layout::REDUCIBILITY_IRREDUCIBLE,
                ReducibilityStatus::ImplicitReducible => layout::REDUCIBILITY_IMPLICIT_REDUCIBLE,
            };
            let mut fields = (0..layout::PROD_POINTERS)
                .map(|_| Obj::mk_nat(0))
                .collect::<Vec<_>>();
            fields[layout::PROD_FST] = name;
            fields[layout::PROD_SND] = Obj::mk_nat(tag);
            entries.push(self.ctor(0, fields, &[])?);
        }
        let entries = self.array(entries)?;
        let name = self.name(&Name::from_components(
            layout::REDUCIBILITY_EXTENSION.split('.'),
        ))?;
        self.ctor(0, vec![name, entries], &[])
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::source_extensions::{self, DecodeLimits};

    fn input() -> ModuleWriteInput<'static> {
        ModuleWriteInput {
            is_module: false,
            imports: &[],
            constants: &[],
            extra_const_names: &[],
        }
    }

    fn header(version: u8) -> OleanWriteHeader<'static> {
        OleanWriteHeader {
            version,
            flags: 1,
            lean_version: crate::format::PIN_TAG.strip_prefix('v').unwrap(),
            githash: crate::format::PIN_COMMIT,
            base_addr: 2 * crate::format::REGION_ALIGN as u64,
        }
    }

    fn metadata() -> SourceMetadata {
        SourceMetadata {
            reducibility: [
                ("Foo.bar", ReducibilityStatus::Reducible),
                ("Foo.baz", ReducibilityStatus::Semireducible),
                ("A.B.c", ReducibilityStatus::Irreducible),
                ("Nat.add", ReducibilityStatus::ImplicitReducible),
            ]
            .into_iter()
            .map(|(name, status)| ReducibilityEntry {
                declaration: Name::from_components(name.split('.')),
                status,
            })
            .collect(),
            ..SourceMetadata::default()
        }
    }

    #[test]
    fn all_statuses_roundtrip_in_quick_lt_order_under_exact_writer_limits() {
        let metadata = metadata();
        let mut expected = metadata.reducibility.clone();
        expected.sort_by(|left, right| left.declaration.quick_cmp(&right.declaration));
        assert_ne!(metadata.reducibility, expected);
        for version in [2, 3] {
            let encoded = encode_module_with_source_metadata(
                input(),
                &metadata,
                header(version),
                WriteBudget::default(),
            )
            .unwrap();
            let view = crate::region::OleanView::parse(&encoded.bytes).unwrap();
            let blocks = view
                .extension_payloads(crate::region::WalkBudget::default(), 1024 * 1024)
                .unwrap();
            let decoded = source_extensions::decode(&blocks, DecodeLimits::default()).unwrap();
            assert_eq!(decoded.reducibility, expected);
            assert!(decoded.uninterpreted.is_empty());
            let exact = WriteBudget {
                max_bytes: encoded.report.file_bytes,
                max_objects: encoded.report.runtime_objects,
            };
            assert_eq!(
                encode_module_with_source_metadata(input(), &metadata, header(version), exact)
                    .unwrap()
                    .bytes,
                encoded.bytes
            );
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
                    encode_module_with_source_metadata(input(), &metadata, header(version), budget),
                    Err(WriteError::Budget { .. })
                ));
            }
        }
    }

    #[test]
    fn duplicate_and_anonymous_status_entries_are_refused() {
        let mut repeated = metadata();
        repeated.reducibility.push(repeated.reducibility[0].clone());
        let mut anonymous = metadata();
        anonymous.reducibility[0].declaration = Name::anonymous();
        for bad in [repeated, anonymous] {
            assert!(matches!(
                encode_module_with_source_metadata(
                    input(),
                    &bad,
                    header(3),
                    WriteBudget::default()
                ),
                Err(WriteError::Contract { .. })
            ));
        }
    }
}
