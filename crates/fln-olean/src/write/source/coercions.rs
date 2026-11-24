//! The pin's chronological global coercion-delaboration registrations.
use super::*;
use crate::source_extensions::CoeFnKind;

impl Encoder {
    pub(super) fn coercion_block(&mut self, rows: &[CoeEntry]) -> WResult<Obj> {
        self.source_array_bound(rows.len())?;
        let mut entries = Vec::with_capacity(rows.len());
        for row in rows {
            if row.declaration.is_anonymous() || row.coercee >= row.num_args {
                return Err(WriteError::Contract {
                    what: "anonymous coercion declaration or invalid argument index",
                });
            }
            let mut fields = (0..layout::COE_FN_POINTERS)
                .map(|_| Obj::mk_nat(0))
                .collect::<Vec<_>>();
            fields[layout::COE_FN_NUM_ARGS] = self.nat_u64(u64::from(row.num_args))?;
            fields[layout::COE_FN_COERCEE] = self.nat_u64(u64::from(row.coercee))?;
            let mut scalars = [0; layout::COE_FN_SCALAR_BYTES];
            scalars[layout::COE_FN_TYPE_SCALAR] = match row.kind {
                CoeFnKind::Coe => layout::COE_FN_COE,
                CoeFnKind::CoeFun => layout::COE_FN_COE_FUN,
                CoeFnKind::CoeSort => layout::COE_FN_COE_SORT,
            };
            let info = self.ctor(0, fields, &scalars)?;
            let mut pair = (0..layout::PROD_POINTERS)
                .map(|_| Obj::mk_nat(0))
                .collect::<Vec<_>>();
            pair[layout::PROD_FST] = self.name(&row.declaration)?;
            pair[layout::PROD_SND] = info;
            let entry = self.ctor(0, pair, &[])?;
            entries.push(self.ctor(layout::SCOPE_GLOBAL, vec![entry], &[])?);
        }
        let entries = self.array(entries)?;
        let extension = self.name(&Name::from_components(layout::COE_EXTENSION.split('.')))?;
        self.ctor(0, vec![extension, entries], &[])
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::region::{OleanView, OpaqueExtensionBlock, WalkBudget};
    use crate::source_extensions::{self, DecodeError, DecodeLimits};
    use fln_rt::convert::inject_name;
    use fln_rt::region::compact;

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
    fn coercion_only_metadata_keeps_kinds_and_update_order_under_exact_budgets() {
        let metadata = SourceMetadata {
            coercions: vec![
                CoeEntry {
                    declaration: n("wrap"),
                    num_args: 1,
                    coercee: 0,
                    kind: CoeFnKind::Coe,
                },
                CoeEntry {
                    declaration: n("toFunction"),
                    num_args: 2,
                    coercee: 1,
                    kind: CoeFnKind::CoeFun,
                },
                CoeEntry {
                    declaration: n("wrap"),
                    num_args: 4,
                    coercee: 2,
                    kind: CoeFnKind::CoeSort,
                },
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
            let blocks = OleanView::parse(&encoded.bytes)
                .unwrap()
                .extension_payloads(WalkBudget::default(), 4 << 20)
                .unwrap();
            assert_eq!(
                blocks.len(),
                1,
                "coercion-only modules retain their journal"
            );
            let decoded = source_extensions::decode(&blocks, DecodeLimits::default()).unwrap();
            assert_eq!(decoded.coercions, metadata.coercions);
            assert!(decoded.namespaces.is_empty());
            assert!(decoded.uninterpreted.is_empty());
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
            let payloads: Vec<_> = blocks.iter().flat_map(|block| &block.entries).collect();
            let exact = DecodeLimits {
                max_bytes: payloads.iter().map(|bytes| bytes.len()).sum(),
                max_objects: payloads
                    .iter()
                    .map(|bytes| fln_rt::region::audit(bytes, 0).unwrap().objects)
                    .sum(),
                max_entries: payloads.len(),
                max_indices: 0,
                max_keys: 0,
            };
            assert_eq!(
                source_extensions::decode(&blocks, exact).unwrap().coercions,
                metadata.coercions
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
    fn coercion_writer_refuses_anonymous_targets_and_out_of_range_indices() {
        for (declaration, num_args, coercee) in [
            (Name::anonymous(), 1, 0),
            (n("wrap"), 0, 0),
            (n("wrap"), 2, 2),
        ] {
            let metadata = SourceMetadata {
                coercions: vec![CoeEntry {
                    declaration,
                    num_args,
                    coercee,
                    kind: CoeFnKind::Coe,
                }],
                ..SourceMetadata::default()
            };
            assert!(matches!(
                encode_module_with_source_metadata(
                    input(),
                    &metadata,
                    header(crate::format::OLEAN_ACCEPTED_VERSIONS[0]),
                    WriteBudget::default()
                ),
                Err(WriteError::Contract { .. })
            ));
        }
    }

    // Build the source-verified wire shape independently of the typed writer:
    // global (Prod declaration (CoeFnInfo numArgs coercee type)), with the
    // CoeFnType tag in scalar storage after the two Nat object slots.
    fn wire_row(declaration: &Name, num_args: usize, coercee: usize, kind: &[u8]) -> Obj {
        let info = Obj::mk_ctor(0, vec![Obj::mk_nat(num_args), Obj::mk_nat(coercee)], kind);
        let pair = Obj::mk_ctor(0, vec![inject_name(declaration), info], &[]);
        Obj::mk_ctor(0, vec![pair], &[])
    }

    #[test]
    fn malformed_coercion_payloads_expose_no_valid_prefix() {
        let valid = compact(&wire_row(&n("wrap"), 2, 1, &[1]), 0).unwrap();
        let scoped = Obj::mk_ctor(1, vec![inject_name(&n("Mode")), Obj::mk_nat(0)], &[]);
        let invalid = [
            wire_row(&Name::anonymous(), 1, 0, &[0]),
            wire_row(&n("wrap"), 0, 0, &[0]),
            wire_row(&n("wrap"), 2, 2, &[0]),
            wire_row(&n("wrap"), 1, 0, &[3]),
            wire_row(&n("wrap"), 1, 0, &[]),
            scoped,
        ];
        for row in invalid {
            let blocks = [OpaqueExtensionBlock {
                name: n(source_extensions::COE_EXTENSION),
                entries: vec![valid.clone(), compact(&row, 0).unwrap()],
            }];
            assert!(matches!(
                source_extensions::decode(&blocks, DecodeLimits::default()),
                Err(DecodeError::Shape { .. })
            ));
        }
        let blocks = [OpaqueExtensionBlock {
            name: n(source_extensions::COE_EXTENSION),
            entries: vec![valid],
        }];
        assert_eq!(
            source_extensions::decode(&blocks, DecodeLimits::default())
                .unwrap()
                .coercions,
            [CoeEntry {
                declaration: n("wrap"),
                num_args: 2,
                coercee: 1,
                kind: CoeFnKind::CoeFun,
            }]
        );
    }
}
