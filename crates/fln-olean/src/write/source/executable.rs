//! The pin's parametric attributes export final, module-owned maps sorted by
//! `Name.quickLt`. Attribute values are data, never permission to execute a symbol.
use super::*;
use crate::ir_format as entry_layout;

impl Encoder {
    fn executable_attribute_block(&mut self, extension: &str, rows: Vec<Obj>) -> WResult<Obj> {
        let entries = self.array(rows)?;
        let name = self.name(&Name::from_components(extension.split('.')))?;
        self.ctor(0, vec![name, entries], &[])
    }

    fn executable_attribute_entry(&mut self, name: &Name, value: Obj) -> WResult<Obj> {
        let name = self.name(name)?;
        let mut fields = (0..layout::PROD_POINTERS)
            .map(|_| Obj::mk_nat(0))
            .collect::<Vec<_>>();
        fields[layout::PROD_FST] = name;
        fields[layout::PROD_SND] = value;
        self.ctor(0, fields, &[])
    }

    pub(super) fn implemented_by_block(&mut self, rows: &[ImplementedByEntry]) -> WResult<Obj> {
        self.source_array_bound(rows.len())?;
        let mut sorted: Vec<_> = rows.iter().collect();
        sorted.sort_by(|left, right| left.declaration.quick_cmp(&right.declaration));
        if sorted.iter().any(|row| {
            row.declaration.is_anonymous()
                || row.implementation.is_anonymous()
                || row.declaration == row.implementation
        }) || sorted
            .windows(2)
            .any(|pair| pair[0].declaration == pair[1].declaration)
        {
            return Err(WriteError::Contract {
                what: "invalid or duplicate implemented_by declaration",
            });
        }
        let mut entries = Vec::with_capacity(sorted.len());
        for row in sorted {
            let implementation = self.name(&row.implementation)?;
            entries.push(self.executable_attribute_entry(&row.declaration, implementation)?);
        }
        self.executable_attribute_block(layout::IMPLEMENTED_BY_EXTENSION, entries)
    }

    fn extern_entry(&mut self, entry: &ExternEntry) -> WResult<Obj> {
        let (tag, fields) = match entry {
            ExternEntry::Adhoc { backend } => {
                let mut fields = (0..entry_layout::EXTERN_ENTRY_ADHOC_POINTERS)
                    .map(|_| Obj::mk_nat(0))
                    .collect::<Vec<_>>();
                fields[entry_layout::EXTERN_ENTRY_ADHOC_BACKEND] = self.name(backend)?;
                (entry_layout::EXTERN_ENTRY_ADHOC, fields)
            }
            ExternEntry::Inline { backend, pattern } => {
                let mut fields = (0..entry_layout::EXTERN_ENTRY_INLINE_POINTERS)
                    .map(|_| Obj::mk_nat(0))
                    .collect::<Vec<_>>();
                fields[entry_layout::EXTERN_ENTRY_INLINE_BACKEND] = self.name(backend)?;
                fields[entry_layout::EXTERN_ENTRY_INLINE_PATTERN] = self.string(pattern)?;
                (entry_layout::EXTERN_ENTRY_INLINE, fields)
            }
            ExternEntry::Standard { backend, symbol } => {
                let mut fields = (0..entry_layout::EXTERN_ENTRY_STANDARD_POINTERS)
                    .map(|_| Obj::mk_nat(0))
                    .collect::<Vec<_>>();
                fields[entry_layout::EXTERN_ENTRY_STANDARD_BACKEND] = self.name(backend)?;
                fields[entry_layout::EXTERN_ENTRY_STANDARD_FN] = self.string(symbol)?;
                (entry_layout::EXTERN_ENTRY_STANDARD, fields)
            }
            ExternEntry::Opaque => {
                return Ok(Obj::mk_nat(usize::from(entry_layout::EXTERN_ENTRY_OPAQUE)));
            }
        };
        self.ctor(tag, fields, &[])
    }

    pub(super) fn extern_block(&mut self, rows: &[ExternAttribute]) -> WResult<Obj> {
        self.source_array_bound(rows.len())?;
        let mut sorted: Vec<_> = rows.iter().collect();
        sorted.sort_by(|left, right| left.declaration.quick_cmp(&right.declaration));
        if sorted.iter().any(|row| row.declaration.is_anonymous())
            || sorted
                .windows(2)
                .any(|pair| pair[0].declaration == pair[1].declaration)
        {
            return Err(WriteError::Contract {
                what: "anonymous or duplicate extern declaration",
            });
        }
        let mut entries = Vec::with_capacity(sorted.len());
        for row in sorted {
            // ExternAttrData's single field is representation-erased. The value
            // is the List itself, including scalar nil for an explicit empty list.
            let mut list = Obj::mk_nat(usize::from(layout::LIST_NIL));
            for entry in row.entries.iter().rev() {
                let head = self.extern_entry(entry)?;
                let mut fields = (0..layout::LIST_CONS_POINTERS)
                    .map(|_| Obj::mk_nat(0))
                    .collect::<Vec<_>>();
                fields[layout::LIST_CONS_HEAD] = head;
                fields[layout::LIST_CONS_TAIL] = list;
                list = self.ctor(layout::LIST_CONS, fields, &[])?;
            }
            entries.push(self.executable_attribute_entry(&row.declaration, list)?);
        }
        self.executable_attribute_block(layout::EXTERN_EXTENSION, entries)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::source_extensions::{self, DecodeLimits};

    fn n(text: &str) -> Name {
        Name::from_components(text.split('.'))
    }

    fn metadata() -> SourceMetadata {
        SourceMetadata {
            implemented_by: vec![
                ImplementedByEntry {
                    declaration: n("Foo.bar"),
                    implementation: n("Impl.bar"),
                },
                ImplementedByEntry {
                    declaration: n("A.b"),
                    implementation: Name::str(Name::num(n("_private.M"), 7), "b"),
                },
            ],
            externs: vec![
                ExternAttribute {
                    declaration: n("Foo.bar"),
                    entries: vec![
                        ExternEntry::Adhoc {
                            backend: Name::anonymous(),
                        },
                        ExternEntry::Inline {
                            backend: n("c"),
                            pattern: "λ\0 $1".into(),
                        },
                        ExternEntry::Standard {
                            backend: n("all"),
                            symbol: "native_symbol".into(),
                        },
                        ExternEntry::Opaque,
                    ],
                },
                ExternAttribute {
                    declaration: n("A.b"),
                    entries: Vec::new(),
                },
            ],
            ..SourceMetadata::default()
        }
    }

    #[test]
    fn executable_attributes_roundtrip_every_value_in_pin_order_and_exact_budgets() {
        let metadata = metadata();
        let mut replacements = metadata.implemented_by.clone();
        replacements.sort_by(|a, b| a.declaration.quick_cmp(&b.declaration));
        let mut externs = metadata.externs.clone();
        externs.sort_by(|a, b| a.declaration.quick_cmp(&b.declaration));
        for version in [2, 3] {
            let encode = |budget| {
                let mut header = super::super::tests::header();
                header.version = version;
                encode_module_with_source_metadata(
                    super::super::tests::input(),
                    &metadata,
                    header,
                    budget,
                )
            };
            let encoded = encode(WriteBudget::default()).unwrap();
            let view = crate::region::OleanView::parse(&encoded.bytes).unwrap();
            let blocks = view
                .extension_payloads(crate::region::WalkBudget::default(), 1024 * 1024)
                .unwrap();
            let decoded = source_extensions::decode(&blocks, DecodeLimits::default()).unwrap();
            assert_eq!(decoded.implemented_by, replacements);
            assert_eq!(decoded.externs, externs);
            assert!(decoded.uninterpreted.is_empty());
            let exact = WriteBudget {
                max_bytes: encoded.report.file_bytes,
                max_objects: encoded.report.runtime_objects,
            };
            assert_eq!(encode(exact).unwrap().bytes, encoded.bytes);
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
                assert!(matches!(encode(budget), Err(WriteError::Budget { .. })));
            }
        }
    }

    #[test]
    fn ambiguous_or_nameless_executable_entries_are_refused() {
        let mut duplicate = metadata();
        duplicate
            .implemented_by
            .push(duplicate.implemented_by[0].clone());
        let mut duplicate_extern = metadata();
        duplicate_extern
            .externs
            .push(duplicate_extern.externs[0].clone());
        let mut self_replacement = metadata();
        self_replacement.implemented_by[0].implementation =
            self_replacement.implemented_by[0].declaration.clone();
        let mut anonymous = metadata();
        anonymous.externs[0].declaration = Name::anonymous();
        for bad in [duplicate, duplicate_extern, self_replacement, anonymous] {
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
