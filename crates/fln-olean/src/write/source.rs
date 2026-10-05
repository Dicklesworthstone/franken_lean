//! Typed persistent source metadata, encoded by the ordinary metered writer.
//!
//! This is data construction, not admission. Consumers must still recheck the
//! declarations before activating these registrations. All supporting names,
//! arrays and records share the module's object and byte budgets.
use super::*;
use crate::source_extension_format as layout;
use crate::source_extensions::ClassEntry;
use std::collections::HashSet;

#[derive(Debug, Clone, Default)]
pub struct SourceMetadata {
    pub classes: Vec<ClassEntry>,
    /// The module's own `protected` declarations: the pin's `protectedExt`
    /// entries, one `Name` each. They are written sorted by `Name.quickLt`, the
    /// order the pin's `isTagged` binary-searches, so the pinned Reference
    /// reading this module answers `isProtected` correctly.
    pub protected: Vec<Name>,
}

/// Encode the supported source journals in the pinned physical layout. Empty
/// metadata takes the original path and produces byte-identical basic modules.
pub fn encode_module_with_source_metadata(
    input: ModuleWriteInput<'_>,
    metadata: &SourceMetadata,
    header: OleanWriteHeader<'_>,
    budget: WriteBudget,
) -> WResult<EncodedModule> {
    if metadata.classes.is_empty() && metadata.protected.is_empty() {
        return encode_module(input, header, budget);
    }
    encode_module_metadata(input, Some(metadata), header, budget)
}

impl Encoder {
    fn source_indices(&mut self, values: &[u32]) -> WResult<Obj> {
        // Check the array's storage before allocating the temporary field list.
        self.source_array_bound(values.len())?;
        let mut seen = HashSet::new();
        let mut fields = Vec::new();
        for &value in values {
            if !seen.insert(value) {
                return Err(WriteError::Contract {
                    what: "duplicate source metadata index",
                });
            }
            fields.push(self.nat_u64(u64::from(value))?);
        }
        self.array(fields)
    }

    fn source_array_bound(&self, count: usize) -> WResult<()> {
        let bytes = u64::try_from(count)
            .ok()
            .and_then(|count| count.checked_mul(8))
            .and_then(|bytes| bytes.checked_add(24))
            .and_then(|bytes| bytes.checked_add(self.bytes))
            .ok_or(WriteError::Contract {
                what: "source metadata array size overflows",
            })?;
        if bytes > self.budget.max_bytes {
            return Err(WriteError::Budget {
                resource: WriteResource::Bytes,
                limit: self.budget.max_bytes,
                attempted: bytes,
            });
        }
        Ok(())
    }

    /// The module's extension blocks: one per non-empty supported journal.
    pub(super) fn source_entries(&mut self, metadata: &SourceMetadata) -> WResult<Obj> {
        let mut blocks = Vec::new();
        if !metadata.classes.is_empty() {
            blocks.push(self.class_block(&metadata.classes)?);
        }
        if !metadata.protected.is_empty() {
            blocks.push(self.protected_block(&metadata.protected)?);
        }
        self.array(blocks)
    }

    fn class_block(&mut self, classes: &[ClassEntry]) -> WResult<Obj> {
        self.source_array_bound(classes.len())?;
        let mut names = HashSet::new();
        let mut entries = Vec::new();
        for class in classes {
            if class.name.is_anonymous() || !names.insert(class.name.clone()) {
                return Err(WriteError::Contract {
                    what: "anonymous or duplicate exported class",
                });
            }
            let name = self.name(&class.name)?;
            let out_params = self.source_indices(&class.out_params)?;
            let out_levels = self.source_indices(&class.out_level_params)?;
            let mut fields: Vec<_> = (0..layout::CLASS_POINTERS)
                .map(|_| Obj::mk_nat(0))
                .collect();
            fields[layout::CLASS_NAME] = name;
            fields[layout::CLASS_OUT_PARAMS] = out_params;
            fields[layout::CLASS_OUT_LEVEL_PARAMS] = out_levels;
            entries.push(self.ctor(0, fields, &[])?);
        }
        let entries = self.array(entries)?;
        let name = self.name(&Name::from_components(layout::CLASS_EXTENSION.split('.')))?;
        self.ctor(0, vec![name, entries], &[])
    }

    /// `protectedExt`'s entries: each a `Name`, in `Name.quickLt` order, as
    /// `mkTagDeclarationExtension`'s `toArrayFn` writes them.
    fn protected_block(&mut self, protected: &[Name]) -> WResult<Obj> {
        self.source_array_bound(protected.len())?;
        let mut sorted: Vec<&Name> = protected.iter().collect();
        sorted.sort_by(|left, right| left.quick_cmp(right));
        if sorted.iter().any(|name| name.is_anonymous())
            || sorted
                .windows(2)
                .any(|pair| pair[0].quick_cmp(pair[1]) == std::cmp::Ordering::Equal)
        {
            return Err(WriteError::Contract {
                what: "anonymous or duplicate protected declaration",
            });
        }
        let mut entries = Vec::with_capacity(sorted.len());
        for name in sorted {
            entries.push(self.name(name)?);
        }
        let entries = self.array(entries)?;
        let name = self.name(&Name::from_components(
            layout::PROTECTED_EXTENSION.split('.'),
        ))?;
        self.ctor(0, vec![name, entries], &[])
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::source_extensions::{self, DecodeLimits};
    fn header() -> OleanWriteHeader<'static> {
        OleanWriteHeader {
            version: crate::format::OLEAN_ACCEPTED_VERSIONS[0],
            flags: 1,
            lean_version: crate::format::PIN_TAG.strip_prefix('v').unwrap(),
            githash: crate::format::PIN_COMMIT,
            base_addr: 2 * crate::format::REGION_ALIGN as u64,
        }
    }
    fn input() -> ModuleWriteInput<'static> {
        ModuleWriteInput {
            is_module: false,
            imports: &[],
            constants: &[],
            extra_const_names: &[],
        }
    }
    fn metadata() -> SourceMetadata {
        SourceMetadata {
            classes: vec![ClassEntry {
                name: Name::from_components(["Library", "Class"]),
                out_params: vec![1, 3],
                out_level_params: vec![2],
            }],
            protected: Vec::new(),
        }
    }
    /// Protected names round-trip, alone and beside classes, in `Name.quickLt`
    /// order whatever order they were supplied in; a repeat or an anonymous name
    /// is refused, never written.
    #[test]
    fn protected_names_roundtrip_in_quick_lt_order() {
        let names: Vec<Name> = ["Foo.bar", "Foo.baz", "A.B.c", "Nat.add", "Foo.qux"]
            .iter()
            .map(|text| Name::from_components(text.split('.')))
            .collect();
        let mut sorted = names.clone();
        sorted.sort_by(|left, right| left.quick_cmp(right));
        assert_ne!(sorted, names, "the fixture order is not already the pin's");
        for classes in [Vec::new(), metadata().classes] {
            let metadata = SourceMetadata {
                classes: classes.clone(),
                protected: names.clone(),
            };
            let encoded = encode_module_with_source_metadata(
                input(),
                &metadata,
                header(),
                WriteBudget::default(),
            )
            .unwrap();
            let view = crate::region::OleanView::parse(&encoded.bytes).unwrap();
            let blocks = view
                .extension_payloads(crate::region::WalkBudget::default(), 1024 * 1024)
                .unwrap();
            let decoded = source_extensions::decode(&blocks, DecodeLimits::default()).unwrap();
            assert_eq!(decoded.protected, sorted);
            assert_eq!(decoded.classes, classes);
            assert!(decoded.uninterpreted.is_empty());
        }
        let mut repeated = names.clone();
        repeated.push(names[2].clone());
        for bad in [repeated, vec![Name::anonymous()]] {
            let metadata = SourceMetadata {
                classes: Vec::new(),
                protected: bad,
            };
            assert!(matches!(
                encode_module_with_source_metadata(
                    input(),
                    &metadata,
                    header(),
                    WriteBudget::default()
                ),
                Err(WriteError::Contract { .. })
            ));
        }
    }
    #[test]
    fn empty_metadata_preserves_the_original_module_bytes() {
        let original = encode_module(input(), header(), WriteBudget::default()).unwrap();
        let typed = encode_module_with_source_metadata(
            input(),
            &SourceMetadata::default(),
            header(),
            WriteBudget::default(),
        )
        .unwrap();
        assert_eq!(original.bytes, typed.bytes);
        assert_eq!(
            original.report.runtime_objects,
            typed.report.runtime_objects
        );
    }
    #[test]
    fn class_records_roundtrip_under_exact_shared_writer_limits() {
        let metadata = metadata();
        let encoded = encode_module_with_source_metadata(
            input(),
            &metadata,
            header(),
            WriteBudget::default(),
        )
        .unwrap();
        let view = crate::region::OleanView::parse(&encoded.bytes).unwrap();
        let blocks = view
            .extension_payloads(crate::region::WalkBudget::default(), 1024 * 1024)
            .unwrap();
        let decoded = source_extensions::decode(&blocks, DecodeLimits::default()).unwrap();
        assert_eq!(decoded.classes, metadata.classes);
        assert!(decoded.instances.is_empty() && decoded.uninterpreted.is_empty());
        let exact = WriteBudget {
            max_bytes: encoded.report.file_bytes,
            max_objects: encoded.report.runtime_objects,
        };
        assert_eq!(
            encode_module_with_source_metadata(input(), &metadata, header(), exact)
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
                encode_module_with_source_metadata(input(), &metadata, header(), budget),
                Err(WriteError::Budget { .. })
            ));
        }
    }
    #[test]
    fn ambiguous_class_names_and_repeated_indices_are_refused() {
        let good = metadata();
        let mut duplicate = good.clone();
        duplicate.classes.push(duplicate.classes[0].clone());
        let mut bad_index = good.clone();
        bad_index.classes[0].out_params.push(1);
        let mut anonymous = good;
        anonymous.classes[0].name = Name::anonymous();
        for bad in [duplicate, bad_index, anonymous] {
            assert!(matches!(
                encode_module_with_source_metadata(input(), &bad, header(), WriteBudget::default()),
                Err(WriteError::Contract { .. })
            ));
        }
    }
}
