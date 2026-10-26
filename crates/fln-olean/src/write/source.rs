//! Typed persistent source metadata, encoded by the ordinary metered writer.
//!
//! This is data construction, not admission. Consumers must still recheck the
//! declarations before activating these registrations. All supporting names,
//! arrays and records share the module's object and byte budgets.
use super::*;
use crate::source_extension_format as layout;
use crate::source_extensions::{
    AliasEntry, ClassEntry, DefaultEntry, DiscrTreeKey, ExternAttribute, ExternEntry,
    ImplementedByEntry, InlineEntry, InstanceEntry, ReducibilityEntry, SimpEntry, SimpKind,
    SimpTheorem, StructureEntry, StructureField, StructureParent,
};
use std::collections::HashSet;

mod aliases;
mod defaults;
mod executable;
mod inlining;
mod instances;
mod namespaces;
mod reducibility;
mod simp;
mod structures;

#[derive(Debug, Clone, Default)]
pub struct SourceMetadata {
    /// Explicit module-owned namespace registrations, independent of aliases.
    pub namespaces: Vec<Name>,
    pub classes: Vec<ClassEntry>,
    /// Chronological global/scoped entries, retaining repeated priority updates.
    pub instances: Vec<InstanceEntry>,
    /// Chronological module-owned defaults, preserving repeated registrations
    /// and rows for candidates whose declarations belong to imported modules.
    pub defaults: Vec<DefaultEntry>,
    /// Chronological default simp registrations, retaining proof orientation,
    /// scopes, priorities and the pin's discrimination-tree paths.
    pub simp: Vec<SimpEntry>,
    /// Chronological module-owned `export` aliases, including imported targets.
    pub aliases: Vec<AliasEntry>,
    /// The module's own `protected` declarations: the pin's `protectedExt`
    /// entries, one `Name` each. They are written sorted by `Name.quickLt`, the
    /// order the pin's `isTagged` binary-searches, so the pinned Reference
    /// reading this module answers `isProtected` correctly.
    pub protected: Vec<Name>,
    /// This module's own internally generated auxiliary recursors, written as
    /// the pin's `auxRecExt` tag array in `Name.quickLt` order.
    pub aux_recursors: Vec<Name>,
    /// Module-owned `Lean.noncomputableExt` tags, sorted by `Name.quickLt`.
    pub noncomputable: Vec<Name>,
    /// Owned definitional-equality tags. The pin's defeq attribute also records
    /// backward_defeq; emit both sorted tag arrays, never just the subset.
    /// These flags are metadata, not a certificate of equality.
    pub defeq: Vec<Name>,
    /// This module's final status for each owned declaration. The writer sorts
    /// these by Name.quickLt for the pin's per-module binary search.
    pub reducibility: Vec<ReducibilityEntry>,
    /// Final inlining kind for each module-owned declaration, written as the
    /// pin's `inlineAttrs` enum map in `Name.quickLt` order.
    pub inline: Vec<InlineEntry>,
    /// Final executable replacement for each owned declaration, sorted by
    /// `Name.quickLt` for the pin's parametric-attribute lookup.
    pub implemented_by: Vec<ImplementedByEntry>,
    /// Final extern attribute per owned declaration. Preserve backend order,
    /// entry kinds and an explicitly empty list; these convey no ABI authority.
    pub externs: Vec<ExternAttribute>,
    /// Module-owned structure interfaces, including physical parent subobjects.
    /// The writer preserves field/parent order and sorts only the pin's indexes.
    pub structures: Vec<StructureEntry>,
}

/// Encode source journals and the namespaces implied by local declarations.
/// Empty journals with no qualified local declarations retain the original
/// basic-module bytes. Explicit empty namespaces need a source namespace journal
/// and are not inferred here; imported declarations are not re-exported.
pub fn encode_module_with_source_metadata(
    input: ModuleWriteInput<'_>,
    metadata: &SourceMetadata,
    header: OleanWriteHeader<'_>,
    budget: WriteBudget,
) -> WResult<EncodedModule> {
    namespaces::encode(input, metadata, header, budget)
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
        let blocks = self.source_blocks(metadata)?;
        self.array(blocks)
    }

    fn source_blocks(&mut self, metadata: &SourceMetadata) -> WResult<Vec<Obj>> {
        let mut blocks = Vec::new();
        if !metadata.classes.is_empty() {
            blocks.push(self.class_block(&metadata.classes)?);
        }
        if !metadata.instances.is_empty() {
            blocks.push(self.instance_block(&metadata.instances)?);
        }
        if !metadata.defaults.is_empty() {
            blocks.push(self.default_block(&metadata.defaults)?);
        }
        if !metadata.simp.is_empty() {
            blocks.push(self.simp_block(&metadata.simp)?);
        }
        if !metadata.aliases.is_empty() {
            blocks.push(self.alias_block(&metadata.aliases)?);
        }
        if !metadata.structures.is_empty() {
            blocks.push(self.structure_block(&metadata.structures)?);
        }
        if !metadata.protected.is_empty() {
            blocks.push(self.tagged_names_block(
                layout::PROTECTED_EXTENSION,
                &metadata.protected,
                "anonymous or duplicate protected declaration",
            )?);
        }
        if !metadata.aux_recursors.is_empty() {
            blocks.push(self.tagged_names_block(
                layout::AUX_RECURSOR_EXTENSION,
                &metadata.aux_recursors,
                "anonymous or duplicate auxiliary recursor",
            )?);
        }
        if !metadata.reducibility.is_empty() {
            blocks.push(self.reducibility_block(&metadata.reducibility)?);
        }
        if !metadata.inline.is_empty() {
            blocks.push(self.inline_block(&metadata.inline)?);
        }
        if !metadata.implemented_by.is_empty() {
            blocks.push(self.implemented_by_block(&metadata.implemented_by)?);
        }
        if !metadata.externs.is_empty() {
            blocks.push(self.extern_block(&metadata.externs)?);
        }
        if !metadata.noncomputable.is_empty() {
            blocks.push(self.tagged_names_block(
                layout::NONCOMPUTABLE_EXTENSION,
                &metadata.noncomputable,
                "anonymous or duplicate noncomputable declaration",
            )?);
        }
        if !metadata.defeq.is_empty() {
            for extension in [layout::DEFEQ_EXTENSION, layout::BACKWARD_DEFEQ_EXTENSION] {
                blocks.push(self.tagged_names_block(
                    extension,
                    &metadata.defeq,
                    "anonymous or duplicate definitional-equality declaration",
                )?);
            }
        }
        Ok(blocks)
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

    /// `TagDeclarationExtension` entries: each a `Name`, in `Name.quickLt`
    /// order, as `mkTagDeclarationExtension`'s `toArrayFn` writes them.
    fn tagged_names_block(
        &mut self,
        extension: &str,
        tagged: &[Name],
        invalid: &'static str,
    ) -> WResult<Obj> {
        self.source_array_bound(tagged.len())?;
        let mut sorted: Vec<&Name> = tagged.iter().collect();
        sorted.sort_by(|left, right| left.quick_cmp(right));
        if sorted.iter().any(|name| name.is_anonymous())
            || sorted
                .windows(2)
                .any(|pair| pair[0].quick_cmp(pair[1]) == std::cmp::Ordering::Equal)
        {
            return Err(WriteError::Contract { what: invalid });
        }
        let mut entries = Vec::with_capacity(sorted.len());
        for name in sorted {
            entries.push(self.name(name)?);
        }
        let entries = self.array(entries)?;
        let name = self.name(&Name::from_components(extension.split('.')))?;
        self.ctor(0, vec![name, entries], &[])
    }
}

#[cfg(test)]
mod defeq_tests;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::source_extensions::{self, DecodeLimits};
    pub(super) fn header() -> OleanWriteHeader<'static> {
        OleanWriteHeader {
            version: crate::format::OLEAN_ACCEPTED_VERSIONS[0],
            flags: 1,
            lean_version: crate::format::PIN_TAG.strip_prefix('v').unwrap(),
            githash: crate::format::PIN_COMMIT,
            base_addr: 2 * crate::format::REGION_ALIGN as u64,
        }
    }
    pub(super) fn input() -> ModuleWriteInput<'static> {
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
            ..SourceMetadata::default()
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
                ..SourceMetadata::default()
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
                ..SourceMetadata::default()
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
    fn noncomputable_tags_roundtrip_without_namespace_or_other_metadata() {
        let names = vec![
            Name::from_components(["simple"]),
            Name::from_components(["A", "f"]),
            Name::from_components(["A.f"]),
            Name::str(
                Name::num(Name::from_components(["_private", "Lib"]), 0),
                "value",
            ),
        ];
        let metadata = SourceMetadata {
            noncomputable: names.clone(),
            ..SourceMetadata::default()
        };
        let encoded = encode_module_with_source_metadata(
            input(),
            &metadata,
            header(),
            WriteBudget::default(),
        )
        .unwrap();
        let blocks = crate::region::OleanView::parse(&encoded.bytes)
            .unwrap()
            .extension_payloads(crate::region::WalkBudget::default(), 1024 * 1024)
            .unwrap();
        assert_eq!(blocks.len(), 1, "no namespace was inferred from tag names");
        assert_eq!(
            blocks[0].name,
            Name::from_components(layout::NONCOMPUTABLE_EXTENSION.split('.'))
        );
        let mut sorted = names;
        sorted.sort_by(Name::quick_cmp);
        let decoded = source_extensions::decode(&blocks, DecodeLimits::default()).unwrap();
        assert_eq!(decoded.noncomputable, sorted);
        assert!(decoded.uninterpreted.is_empty());
        assert!(decoded.aux_recursors.is_empty() && decoded.protected.is_empty());
        let mut repeated = blocks.clone();
        let duplicate = repeated[0].entries[0].clone();
        repeated[0].entries.push(duplicate);
        assert!(source_extensions::decode(&repeated, DecodeLimits::default()).is_err());
    }

    #[test]
    fn noncomputable_metadata_spends_shared_writer_and_decoder_budgets() {
        let metadata = SourceMetadata {
            noncomputable: vec![Name::from_components(["x"])],
            ..SourceMetadata::default()
        };
        let encoded = encode_module_with_source_metadata(
            input(),
            &metadata,
            header(),
            WriteBudget::default(),
        )
        .unwrap();
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
        let blocks = crate::region::OleanView::parse(&encoded.bytes)
            .unwrap()
            .extension_payloads(crate::region::WalkBudget::default(), 1024 * 1024)
            .unwrap();
        for limits in [
            DecodeLimits {
                max_entries: 0,
                ..DecodeLimits::default()
            },
            DecodeLimits {
                max_bytes: 0,
                ..DecodeLimits::default()
            },
            DecodeLimits {
                max_objects: 0,
                ..DecodeLimits::default()
            },
        ] {
            assert!(source_extensions::decode(&blocks, limits).is_err());
        }
        assert_eq!(
            source_extensions::decode(&blocks, DecodeLimits::default())
                .unwrap()
                .noncomputable,
            metadata.noncomputable
        );
    }

    #[test]
    fn noncomputable_writer_refuses_anonymous_and_repeated_tags() {
        let name = Name::from_components(["x"]);
        for names in [vec![Name::anonymous()], vec![name.clone(), name]] {
            assert!(matches!(
                encode_module_with_source_metadata(
                    input(),
                    &SourceMetadata {
                        noncomputable: names,
                        ..SourceMetadata::default()
                    },
                    header(),
                    WriteBudget::default()
                ),
                Err(WriteError::Contract { .. })
            ));
        }
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
