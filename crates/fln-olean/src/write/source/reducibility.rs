//! The pin's sorted local core map and chronological scoped extra updates.
use super::*;
use crate::source_extensions::{ReducibilityEntry, ReducibilityExtraEntry, ReducibilityStatus};

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
            entries.push(self.reducibility_entry(&row.declaration, row.status)?);
        }
        let entries = self.array(entries)?;
        let name = self.name(&Name::from_components(
            layout::REDUCIBILITY_EXTENSION.split('.'),
        ))?;
        self.ctor(0, vec![name, entries], &[])
    }

    pub(super) fn reducibility_extra_block(
        &mut self,
        rows: &[ReducibilityExtraEntry],
    ) -> WResult<Obj> {
        self.source_array_bound(rows.len())?;
        let mut entries = Vec::with_capacity(rows.len());
        for row in rows {
            if row.declaration.is_anonymous() || row.scope.as_ref().is_some_and(Name::is_anonymous)
            {
                return Err(WriteError::Contract {
                    what: "anonymous reducibility extra declaration or scope",
                });
            }
            let entry = self.reducibility_entry(&row.declaration, row.status)?;
            let entry = match &row.scope {
                None => self.ctor(layout::SCOPE_GLOBAL, vec![entry], &[])?,
                Some(scope) => {
                    let scope = self.name(scope)?;
                    self.ctor(layout::SCOPE_SCOPED, vec![scope, entry], &[])?
                }
            };
            entries.push(entry);
        }
        let entries = self.array(entries)?;
        let name = self.name(&Name::from_components(
            layout::REDUCIBILITY_EXTRA_EXTENSION.split('.'),
        ))?;
        self.ctor(0, vec![name, entries], &[])
    }

    fn reducibility_entry(
        &mut self,
        declaration: &Name,
        status: ReducibilityStatus,
    ) -> WResult<Obj> {
        let name = self.name(declaration)?;
        let tag = match status {
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
        self.ctor(0, fields, &[])
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

    #[test]
    fn extra_updates_preserve_scopes_duplicates_and_order_with_exact_budgets() {
        let mut metadata = metadata();
        for (scope, status) in [
            (None, ReducibilityStatus::Irreducible),
            (Some("Visible"), ReducibilityStatus::ImplicitReducible),
            (None, ReducibilityStatus::Reducible),
            (None, ReducibilityStatus::Semireducible),
        ] {
            metadata.reducibility_extra.push(ReducibilityExtraEntry {
                scope: scope.map(|value| Name::from_components([value])),
                declaration: Name::from_components(["Imported", "identity"]),
                status,
            });
        }
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
            assert_eq!(decoded.reducibility_extra, metadata.reducibility_extra);
            assert_eq!(decoded.reducibility.len(), metadata.reducibility.len());
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
            assert!(
                source_extensions::decode(
                    &blocks,
                    DecodeLimits {
                        max_entries: metadata.reducibility.len()
                            + metadata.reducibility_extra.len()
                            - 1,
                        ..DecodeLimits::default()
                    },
                )
                .unwrap_err()
                .is_resource()
            );
        }
    }

    #[test]
    fn extra_only_modules_preserve_their_serialized_extension_block() {
        let metadata = SourceMetadata {
            reducibility_extra: [
                ReducibilityStatus::Irreducible,
                ReducibilityStatus::Reducible,
            ]
            .into_iter()
            .map(|status| ReducibilityExtraEntry {
                scope: None,
                declaration: Name::from_components(["Imported", "identity"]),
                status,
            })
            .collect(),
            ..SourceMetadata::default()
        };
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
            assert_eq!(
                blocks.len(),
                1,
                "an override-only module still has metadata"
            );
            assert_eq!(
                blocks[0].name,
                Name::from_components([source_extensions::REDUCIBILITY_EXTRA_EXTENSION]),
            );
            assert_eq!(blocks[0].entries.len(), 2);
            let decoded = source_extensions::decode(&blocks, DecodeLimits::default()).unwrap();
            assert_eq!(decoded.reducibility_extra, metadata.reducibility_extra);
            assert!(decoded.reducibility.is_empty());
            assert!(decoded.uninterpreted.is_empty());
        }
    }
}
