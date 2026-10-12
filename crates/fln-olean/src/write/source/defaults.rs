//! The pinned default-instance extension is an ordered array of registrations.
//! Repeated names remain entries: changing priority does not erase an old row.
use super::*;

impl Encoder {
    pub(super) fn default_block(&mut self, defaults: &[DefaultEntry]) -> WResult<Obj> {
        self.source_array_bound(defaults.len())?;
        let mut entries = Vec::with_capacity(defaults.len());
        for row in defaults {
            if row.class.is_anonymous() || row.declaration.is_anonymous() {
                return Err(WriteError::Contract {
                    what: "anonymous default class or candidate",
                });
            }
            let class = self.name(&row.class)?;
            let declaration = self.name(&row.declaration)?;
            let priority = self.nat_u64(u64::from(row.priority))?;
            let mut fields: Vec<_> = (0..layout::DEFAULT_POINTERS)
                .map(|_| Obj::mk_nat(0))
                .collect();
            fields[layout::DEFAULT_CLASS_NAME] = class;
            fields[layout::DEFAULT_INSTANCE_NAME] = declaration;
            fields[layout::DEFAULT_PRIORITY] = priority;
            entries.push(self.ctor(0, fields, &[0; layout::DEFAULT_SCALAR_BYTES])?);
        }
        let entries = self.array(entries)?;
        let name = self.name(&Name::from_components(layout::DEFAULT_EXTENSION.split('.')))?;
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

    fn metadata() -> SourceMetadata {
        SourceMetadata {
            defaults: [
                ("Imported.choice", 2000),
                ("Local.choice", 1000),
                ("Imported.choice", 100),
                ("Local.choice", 1000),
            ]
            .into_iter()
            .map(|(declaration, priority)| DefaultEntry {
                class: n("Imported.Choice"),
                declaration: n(declaration),
                priority,
            })
            .collect(),
            ..SourceMetadata::default()
        }
    }

    fn encode(metadata: &SourceMetadata, budget: WriteBudget) -> WResult<EncodedModule> {
        encode_module_with_source_metadata(
            ModuleWriteInput {
                is_module: false,
                imports: &[],
                constants: &[],
                extra_const_names: &[],
            },
            metadata,
            OleanWriteHeader {
                version: format::OLEAN_ACCEPTED_VERSIONS[0],
                flags: 1,
                lean_version: format::PIN_TAG.strip_prefix('v').unwrap(),
                githash: format::PIN_COMMIT,
                base_addr: 2 * format::REGION_ALIGN as u64,
            },
            budget,
        )
    }

    #[test]
    fn default_registrations_roundtrip_in_chronological_order_under_exact_limits() {
        // There are no local constants or namespaces. A defaults-only module
        // must still encode its extension rather than take the empty fast path.
        let metadata = metadata();
        let encoded = encode(&metadata, WriteBudget::default()).unwrap();
        let view = OleanView::parse(&encoded.bytes).unwrap();
        let blocks = view
            .extension_payloads(WalkBudget::default(), 1024 * 1024)
            .unwrap();
        let decoded = source_extensions::decode(&blocks, DecodeLimits::default()).unwrap();
        assert_eq!(decoded.defaults, metadata.defaults);
        assert!(decoded.classes.is_empty());
        assert!(decoded.instances.is_empty());
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

    #[test]
    fn anonymous_default_class_or_candidate_is_refused() {
        let mut class = metadata();
        class.defaults[0].class = Name::anonymous();
        let mut candidate = metadata();
        candidate.defaults[0].declaration = Name::anonymous();
        for bad in [class, candidate] {
            assert!(matches!(
                encode(&bad, WriteBudget::default()),
                Err(WriteError::Contract { .. })
            ));
        }
    }
}
