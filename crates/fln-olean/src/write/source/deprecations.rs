//! The pin's deprecatedAttr is a module-owned, Name.quickLt-sorted parameter map.
use super::*;

impl Encoder {
    fn deprecation_option(&mut self, value: Option<Obj>) -> WResult<Obj> {
        let Some(value) = value else {
            return Ok(Obj::mk_nat(layout::OPTION_NONE));
        };
        let mut fields: Vec<_> = std::iter::repeat_with(|| Obj::mk_nat(0))
            .take(layout::OPTION_SOME_POINTERS)
            .collect();
        fields[layout::OPTION_SOME_VAL] = value;
        self.ctor(layout::OPTION_SOME, fields, &[])
    }

    pub(super) fn deprecation_block(&mut self, rows: &[DeprecationEntry]) -> WResult<Obj> {
        self.source_array_bound(rows.len())?;
        let mut sorted: Vec<_> = rows.iter().collect();
        sorted.sort_by(|left, right| left.declaration.quick_cmp(&right.declaration));
        if sorted.iter().any(|row| {
            row.declaration.is_anonymous() || row.new_name.as_ref().is_some_and(Name::is_anonymous)
        }) || sorted
            .windows(2)
            .any(|pair| pair[0].declaration == pair[1].declaration)
        {
            return Err(WriteError::Contract {
                what: "anonymous or duplicate deprecated declaration",
            });
        }
        let mut entries = Vec::with_capacity(sorted.len());
        for row in sorted {
            let mut fields: Vec<_> = std::iter::repeat_with(|| Obj::mk_nat(0))
                .take(layout::DEPRECATION_POINTERS)
                .collect();
            let new_name = row
                .new_name
                .as_ref()
                .map(|name| self.name(name))
                .transpose()?;
            fields[layout::DEPRECATION_NEW_NAME_OPTION] = self.deprecation_option(new_name)?;
            let text = row
                .text
                .as_ref()
                .map(|text| self.string(text))
                .transpose()?;
            fields[layout::DEPRECATION_TEXT_OPTION] = self.deprecation_option(text)?;
            let since = row
                .since
                .as_ref()
                .map(|text| self.string(text))
                .transpose()?;
            fields[layout::DEPRECATION_SINCE_OPTION] = self.deprecation_option(since)?;
            let entry = self.ctor(0, fields, &[])?;
            let mut pair: Vec<_> = std::iter::repeat_with(|| Obj::mk_nat(0))
                .take(layout::PROD_POINTERS)
                .collect();
            pair[layout::PROD_FST] = self.name(&row.declaration)?;
            pair[layout::PROD_SND] = entry;
            entries.push(self.ctor(0, pair, &[])?);
        }
        let entries = self.array(entries)?;
        let extension = self.name(&Name::from_components(
            layout::DEPRECATED_EXTENSION.split('.'),
        ))?;
        self.ctor(0, vec![extension, entries], &[])
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::region::{OleanView, WalkBudget};
    use crate::source_extensions::{self, DecodeLimits};

    #[test]
    fn deprecation_parameters_roundtrip_without_constants_and_share_writer_budgets() {
        let n = |text: &str| Name::from_components(text.split('.'));
        let rows = vec![
            DeprecationEntry {
                declaration: n("Enum.toCtorIdx"),
                new_name: Some(n("Enum.ctorIdx")),
                text: None,
                since: Some("2025-08-25".into()),
            },
            DeprecationEntry {
                declaration: n("old"),
                new_name: None,
                text: Some("use the new API λ\0".into()),
                since: None,
            },
        ];
        for version in crate::format::OLEAN_ACCEPTED_VERSIONS {
            let mut header = super::super::tests::header();
            header.version = *version;
            let input = || super::super::tests::input();
            let metadata = SourceMetadata {
                deprecations: rows.clone(),
                ..SourceMetadata::default()
            };
            let encoded = encode_module_with_source_metadata(
                input(),
                &metadata,
                header,
                WriteBudget::default(),
            )
            .unwrap();
            let blocks = OleanView::parse(&encoded.bytes)
                .unwrap()
                .extension_payloads(WalkBudget::default(), 1 << 20)
                .unwrap();
            let decoded = source_extensions::decode(&blocks, DecodeLimits::default()).unwrap();
            let mut expected = rows.clone();
            expected.sort_by(|a, b| a.declaration.quick_cmp(&b.declaration));
            assert_eq!(decoded.deprecations, expected);
            assert_eq!(
                blocks.len(),
                1,
                "deprecation-only modules must retain metadata"
            );
            let exact = WriteBudget {
                max_bytes: encoded.report.file_bytes,
                max_objects: encoded.report.runtime_objects,
            };
            assert_eq!(
                encode_module_with_source_metadata(input(), &metadata, header, exact)
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
                    encode_module_with_source_metadata(input(), &metadata, header, budget),
                    Err(WriteError::Budget { .. })
                ));
            }
            for invalid in [
                vec![rows[0].clone(), rows[0].clone()],
                vec![DeprecationEntry {
                    declaration: Name::anonymous(),
                    ..rows[0].clone()
                }],
                vec![DeprecationEntry {
                    new_name: Some(Name::anonymous()),
                    ..rows[0].clone()
                }],
            ] {
                let metadata = SourceMetadata {
                    deprecations: invalid,
                    ..SourceMetadata::default()
                };
                assert!(matches!(
                    encode_module_with_source_metadata(
                        input(),
                        &metadata,
                        header,
                        WriteBudget::default()
                    ),
                    Err(WriteError::Contract { .. })
                ));
            }
        }
    }
}
