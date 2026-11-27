//! The pin's chronological global/scoped symmetry-lemma registrations.
use super::*;

impl Encoder {
    pub(super) fn symm_block(&mut self, rows: &[SymmEntry]) -> WResult<Obj> {
        self.source_array_bound(rows.len())?;
        let mut entries = Vec::with_capacity(rows.len());
        for row in rows {
            if row.declaration.is_anonymous() || row.scope.as_ref().is_some_and(Name::is_anonymous)
            {
                return Err(WriteError::Contract {
                    what: "anonymous symmetry declaration or scope",
                });
            }
            let declaration = self.name(&row.declaration)?;
            let keys = self.discr_tree_keys(&row.keys)?;
            let mut fields = (0..layout::PROD_POINTERS)
                .map(|_| Obj::mk_nat(0))
                .collect::<Vec<_>>();
            fields[layout::PROD_FST] = declaration;
            fields[layout::PROD_SND] = keys;
            let entry = self.ctor(0, fields, &[])?;
            entries.push(match &row.scope {
                None => self.ctor(layout::SCOPE_GLOBAL, vec![entry], &[])?,
                Some(scope) => {
                    let scope = self.name(scope)?;
                    self.ctor(layout::SCOPE_SCOPED, vec![scope, entry], &[])?
                }
            });
        }
        let entries = self.array(entries)?;
        let name = self.name(&Name::from_components(layout::SYMM_EXTENSION.split('.')))?;
        self.ctor(0, vec![name, entries], &[])
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::region::{OleanView, WalkBudget};
    use crate::source_extensions::{self, DecodeLimits};

    fn n(text: &str) -> Name {
        Name::from_components(text.split('.'))
    }
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

    #[test]
    fn symmetry_rows_keep_scopes_paths_and_duplicates_under_exact_shared_budgets() {
        let first = SymmEntry {
            declaration: n("reverse"),
            keys: vec![DiscrTreeKey::Const(n("Eq"), 1), DiscrTreeKey::Star],
            scope: None,
        };
        let metadata = SourceMetadata {
            symms: vec![
                first.clone(),
                SymmEntry {
                    declaration: n("generic"),
                    keys: vec![DiscrTreeKey::Star],
                    scope: Some(n("Mode.Choice")),
                },
                first,
            ],
            ..SourceMetadata::default()
        };
        for version in crate::format::OLEAN_ACCEPTED_VERSIONS {
            let encoded = encode_module_with_source_metadata(
                input(),
                &metadata,
                header(*version),
                WriteBudget::default(),
            )
            .unwrap();
            let exact = WriteBudget {
                max_bytes: encoded.report.file_bytes,
                max_objects: encoded.report.runtime_objects,
            };
            assert_eq!(
                encode_module_with_source_metadata(input(), &metadata, header(*version), exact)
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
                    encode_module_with_source_metadata(
                        input(),
                        &metadata,
                        header(*version),
                        budget
                    ),
                    Err(WriteError::Budget { .. })
                ));
            }
            let blocks = OleanView::parse(&encoded.bytes)
                .unwrap()
                .extension_payloads(WalkBudget::default(), 4 << 20)
                .unwrap();
            let decoded = source_extensions::decode(&blocks, DecodeLimits::default()).unwrap();
            assert_eq!(decoded.symms, metadata.symms);
            let mut namespaces = vec![n("Mode"), n("Mode.Choice")];
            namespaces.sort_by(Name::quick_cmp);
            assert_eq!(decoded.namespaces, namespaces);
            assert!(decoded.uninterpreted.is_empty());
            let payloads: Vec<_> = blocks.iter().flat_map(|block| &block.entries).collect();
            let exact = DecodeLimits {
                max_bytes: payloads.iter().map(|bytes| bytes.len()).sum(),
                max_objects: payloads
                    .iter()
                    .map(|bytes| fln_rt::region::audit(bytes, 0).unwrap().objects)
                    .sum(),
                max_entries: payloads.len(),
                max_indices: 0,
                max_keys: 5,
            };
            assert_eq!(
                source_extensions::decode(&blocks, exact).unwrap().symms,
                metadata.symms
            );
            for limits in [
                DecodeLimits {
                    max_bytes: exact.max_bytes - 1,
                    ..exact
                },
                DecodeLimits {
                    max_objects: exact.max_objects - 1,
                    ..exact
                },
                DecodeLimits {
                    max_entries: exact.max_entries - 1,
                    ..exact
                },
                DecodeLimits {
                    max_keys: exact.max_keys - 1,
                    ..exact
                },
            ] {
                assert!(
                    source_extensions::decode(&blocks, limits)
                        .unwrap_err()
                        .is_resource()
                );
            }
        }
    }

    #[test]
    fn symmetry_only_metadata_is_retained_and_invalid_names_or_paths_refuse() {
        let row = SymmEntry {
            declaration: n("reverse"),
            keys: vec![DiscrTreeKey::Star],
            scope: None,
        };
        let encode = |row| {
            encode_module_with_source_metadata(
                input(),
                &SourceMetadata {
                    symms: vec![row],
                    ..SourceMetadata::default()
                },
                header(crate::format::OLEAN_ACCEPTED_VERSIONS[0]),
                WriteBudget::default(),
            )
        };
        let encoded = encode(row.clone()).unwrap();
        let blocks = OleanView::parse(&encoded.bytes)
            .unwrap()
            .extension_payloads(WalkBudget::default(), 4 << 20)
            .unwrap();
        assert_eq!(blocks.len(), 1);
        assert_eq!(
            source_extensions::decode(&blocks, DecodeLimits::default())
                .unwrap()
                .symms
                .as_slice(),
            std::slice::from_ref(&row)
        );
        for invalid in [
            SymmEntry {
                declaration: Name::anonymous(),
                ..row.clone()
            },
            SymmEntry {
                scope: Some(Name::anonymous()),
                ..row.clone()
            },
            SymmEntry {
                keys: vec![],
                ..row.clone()
            },
            SymmEntry {
                keys: vec![DiscrTreeKey::Const(n("Eq"), 1)],
                ..row.clone()
            },
            SymmEntry {
                keys: vec![DiscrTreeKey::Star, DiscrTreeKey::Star],
                ..row
            },
        ] {
            assert!(matches!(encode(invalid), Err(WriteError::Contract { .. })));
        }
    }
}
