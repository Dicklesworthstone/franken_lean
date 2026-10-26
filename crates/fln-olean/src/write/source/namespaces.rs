//! Namespace entries for modules written by the source pipeline.
//!
//! The pin's Lean.Namespace exports an Array Name, sorted by Name.quickLt.
//! Qualified declarations register their proper prefixes. Alias names and
//! targets do not register namespaces.
//! Merely writing the constants does not perform this registration on import.
//!
//! Empty and re-export-only namespaces come from explicit registrations, never
//! inferred from aliases, referenced constants or extra runtime constant names.
//! A scoped registration also names its exact namespace, even when its
//! declaration lives elsewhere and the namespace has no constants of its own.
use super::*;

/// `namespacesExt` is PRIVATE at the pin. Its key is not `Lean.namespacesExt`,
/// nor a dotted string with a string-valued "0" component. The descriptor's
/// name is constructed in vendored stage0/stdlib/Lean/Namespace.c, initFn's
/// closed__13, from closed__3/5/7/10/11 (closed__10 is Name.num 0).
pub(super) fn extension_name() -> Name {
    crate::source_extensions::namespace_extension_name()
}

impl Encoder {
    fn retain_namespace(&self, names: &mut HashSet<Name>, namespace: &Name) -> WResult<bool> {
        if names.contains(namespace) {
            return Ok(false);
        }
        let count = names.len().checked_add(1).ok_or(WriteError::Contract {
            what: "namespace entry count overflows",
        })?;
        self.source_array_bound(count)?;
        let nonanonymous =
            count - usize::from(namespace.is_anonymous() || names.contains(&Name::anonymous()));
        let attempted = u64::try_from(nonanonymous).map_err(|_| WriteError::Contract {
            what: "namespace object count overflows",
        })?;
        // Each distinct nonanonymous Name needs at least one object. The
        // shared encoder charges the actual name and supporting objects.
        if attempted > self.budget.max_objects {
            return Err(WriteError::Budget {
                resource: WriteResource::Objects,
                limit: self.budget.max_objects,
                attempted,
            });
        }
        names.insert(namespace.clone());
        Ok(true)
    }

    fn declaration_namespaces(
        &self,
        constants: &[ConstantInfo],
        namespaces: &[Name],
        instances: &[InstanceEntry],
        simp: &[SimpEntry],
    ) -> WResult<Vec<Name>> {
        let mut names = HashSet::new();
        for mut namespace in constants
            .iter()
            .map(|constant| constant.constant_val().name.parent())
            .chain(
                instances
                    .iter()
                    .filter_map(|instance| instance.scope.clone()),
            )
            .chain(simp.iter().filter_map(|entry| entry.scope.clone()))
        {
            while !namespace.is_anonymous() {
                // Every previous walk finished its ancestor chain. A shared
                // prefix therefore lets us stop, not repeatedly walk to root.
                if !self.retain_namespace(&mut names, &namespace)? {
                    break;
                }
                namespace = namespace.parent();
            }
        }
        // `Environment.registerNamespace` registers exactly its argument, not
        // its ancestors. Source namespace commands supply their entered
        // prefixes themselves; metadata must not invent additional entries.
        for namespace in namespaces {
            self.retain_namespace(&mut names, namespace)?;
        }
        let mut names: Vec<_> = names.into_iter().collect();
        names.sort_by(Name::quick_cmp);
        Ok(names)
    }

    fn namespace_block(&mut self, namespaces: &[Name]) -> WResult<Obj> {
        self.source_array_bound(namespaces.len())?;
        let mut entries = Vec::with_capacity(namespaces.len());
        for namespace in namespaces {
            entries.push(self.name(namespace)?);
        }
        let entries = self.array(entries)?;
        let name = self.name(&extension_name())?;
        self.ctor(0, vec![name, entries], &[])
    }
}

pub(super) fn encode(
    input: ModuleWriteInput<'_>,
    metadata: &SourceMetadata,
    header: OleanWriteHeader<'_>,
    budget: WriteBudget,
) -> WResult<EncodedModule> {
    let header_bytes = build_header(header)?;
    let mut encoder = Encoder::new(budget, header.version)?;
    let namespaces = encoder.declaration_namespaces(
        input.constants,
        &metadata.namespaces,
        &metadata.instances,
        &metadata.simp,
    )?;
    if namespaces.is_empty() {
        return if metadata.classes.is_empty()
            && metadata.instances.is_empty()
            && metadata.defaults.is_empty()
            && metadata.simp.is_empty()
            && metadata.aliases.is_empty()
            && metadata.protected.is_empty()
            && metadata.aux_recursors.is_empty()
            && metadata.noncomputable.is_empty()
            && metadata.defeq.is_empty()
            && metadata.backward_defeq.is_empty()
            && metadata.reducibility.is_empty()
            && metadata.inline.is_empty()
            && metadata.implemented_by.is_empty()
            && metadata.externs.is_empty()
            && metadata.structures.is_empty()
        {
            encode_module(input, header, budget)
        } else {
            encode_module_metadata(input, Some(metadata), header, budget)
        };
    }
    // The private extension identity is pin-specific. A repin needs a fresh
    // audit of Namespace.lean and its compiled descriptor, not a guessed key.
    if format::PIN_COMMIT != "8c9756b28d64dab099da31a4c09229a9e6a2ef35" {
        return Err(WriteError::Unsupported {
            what: "namespace extension identity has not been audited for this pin",
        });
    }
    let mut blocks = encoder.source_blocks(metadata)?;
    blocks.push(encoder.namespace_block(&namespaces)?);
    let entries = encoder.array(blocks)?;
    let root = encoder.module_root_with_entries(input, Some(entries))?;
    let finished = finish_region(
        encoder,
        root,
        header_bytes,
        header.version,
        header.base_addr,
    )?;
    let expr_nodes =
        u64::try_from(finished.encoder.exprs.len()).map_err(|_| WriteError::Contract {
            what: "expression node count overflows",
        })?;
    let imports = u64::try_from(input.imports.len()).map_err(|_| WriteError::Contract {
        what: "import count overflows",
    })?;
    let constants = u64::try_from(input.constants.len()).map_err(|_| WriteError::Contract {
        what: "constant count overflows",
    })?;
    let extra_const_names =
        u64::try_from(input.extra_const_names.len()).map_err(|_| WriteError::Contract {
            what: "extra constant-name count overflows",
        })?;
    let file_bytes = u64::try_from(finished.bytes.len()).map_err(|_| WriteError::Contract {
        what: "final file size overflows",
    })?;
    Ok(EncodedModule {
        bytes: finished.bytes,
        root: finished.root,
        report: ModuleWriteReport {
            imports,
            constants,
            extra_const_names,
            expr_nodes,
            expr_presentations: finished.encoder.expr_presentations,
            shared_expr_presentations: finished
                .encoder
                .expr_presentations
                .saturating_sub(expr_nodes),
            runtime_objects: finished.region.objects,
            file_bytes,
        },
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::region::{OleanView, WalkBudget};
    use crate::source_extensions::{self, DecodeLimits};
    use fln_env::constants::AxiomVal;
    use fln_rt::convert::Conversion;

    fn name(text: &str) -> Name {
        Name::from_components(text.split('.'))
    }
    fn constant(name: Name) -> ConstantInfo {
        ConstantInfo::Axiom(AxiomVal {
            base: ConstantVal {
                name,
                level_params: vec![],
                type_: Expr::sort(Level::zero()),
            },
            is_unsafe: false,
        })
    }
    fn header(version: u8) -> OleanWriteHeader<'static> {
        OleanWriteHeader {
            version,
            flags: 1,
            lean_version: format::PIN_TAG.strip_prefix('v').unwrap(),
            githash: format::PIN_COMMIT,
            base_addr: 2 * format::REGION_ALIGN as u64,
        }
    }
    fn input(constants: &[ConstantInfo]) -> ModuleWriteInput<'_> {
        ModuleWriteInput {
            is_module: false,
            imports: &[],
            constants,
            extra_const_names: &[],
        }
    }

    #[test]
    fn private_extension_identity_matches_the_pinned_compiler_descriptor() {
        // Namespace.c initFn closed__13's LEAN_SCALAR_PTR_LITERAL hash.
        assert_eq!(
            extension_name().hash(),
            u64::from_le_bytes([210, 169, 133, 77, 254, 44, 181, 250])
        );
        assert!(matches!(
            extension_name().parent().parent().leaf_view(),
            LeafView::Num(0)
        ));
    }

    #[test]
    fn scoped_namespaces_include_the_scope_itself_without_using_the_target_parent() {
        let escaped = Name::str(
            Name::num(Name::from_components(["Feature.with.dot"]), 7),
            "Inner",
        );
        let row = |scope| InstanceEntry {
            declaration: name("Unrelated.candidate"),
            value: Expr::const_(name("Unrelated.candidate"), vec![]),
            priority: 1000,
            synth_order: vec![],
            keys: vec![DiscrTreeKey::Const(name("Class"), 0)],
            scope,
        };
        let encoder = Encoder::new(WriteBudget::default(), 2).unwrap();
        let rows = [
            row(Some(name("Feature.Inner"))),
            row(Some(escaped.clone())),
            row(None),
        ];
        let actual = encoder
            .declaration_namespaces(&[], &[], &rows, &[])
            .unwrap();
        let mut expected = vec![
            name("Feature"),
            name("Feature.Inner"),
            escaped.clone(),
            escaped.parent(),
            escaped.parent().parent(),
        ];
        expected.sort_by(Name::quick_cmp);
        assert_eq!(actual, expected);
        assert!(!actual.contains(&name("Unrelated")));
        assert!(!actual.contains(&name("Class")));
        let limited = Encoder::new(
            WriteBudget {
                max_objects: 1,
                ..WriteBudget::default()
            },
            2,
        )
        .unwrap();
        assert!(matches!(
            limited.declaration_namespaces(&[], &[], &rows, &[]),
            Err(WriteError::Budget {
                resource: WriteResource::Objects,
                ..
            })
        ));
    }

    #[test]
    fn proper_prefixes_are_unique_and_sorted_without_registering_the_leaf() {
        let constants: Vec<_> = ["Lib.Inner.one", "Lib.Inner.two", "Lib.Other.three", "root"]
            .into_iter()
            .map(|text| constant(name(text)))
            .collect();
        let encoder = Encoder::new(WriteBudget::default(), 2).unwrap();
        let mut expected = vec![name("Lib"), name("Lib.Inner"), name("Lib.Other")];
        expected.sort_by(Name::quick_cmp);
        assert_eq!(
            encoder
                .declaration_namespaces(&constants, &[], &[], &[])
                .unwrap(),
            expected
        );
        let mut reversed = constants;
        reversed.reverse();
        assert_eq!(
            encoder
                .declaration_namespaces(&reversed, &[], &[], &[])
                .unwrap(),
            expected
        );
    }

    #[test]
    fn numeric_and_escaped_components_survive_the_physical_name_payload() {
        let parent = Name::num(Name::str(Name::anonymous(), "A.B"), 7);
        let constants = [constant(Name::str(parent.clone(), "value"))];
        let mut encoder = Encoder::new(WriteBudget::default(), 2).unwrap();
        let namespaces = encoder
            .declaration_namespaces(&constants, &[], &[], &[])
            .unwrap();
        assert!(namespaces.contains(&parent));
        assert!(namespaces.contains(&Name::str(Name::anonymous(), "A.B")));
        assert!(!namespaces.contains(&name("A")));
        let block = encoder.namespace_block(&namespaces).unwrap();
        let mut conversion = Conversion::new();
        assert_eq!(
            conversion
                .project_name(&block.try_ctor_child(0).unwrap())
                .unwrap(),
            extension_name()
        );
        assert_ne!(
            extension_name(),
            name("_private.Lean.Namespace.0.Lean.namespacesExt")
        );
        let entries = block.try_ctor_child(1).unwrap();
        assert_eq!(entries.try_array_view().unwrap().0, namespaces.len());
        for (index, expected) in namespaces.iter().enumerate() {
            assert_eq!(
                conversion
                    .project_name(&entries.array_child(index))
                    .unwrap(),
                *expected
            );
        }
    }

    #[test]
    fn complete_modules_include_namespaces_beside_existing_metadata_in_both_formats() {
        let constants = [constant(name("Lib.Class")), constant(name("Lib.protected"))];
        let metadata = SourceMetadata {
            classes: vec![ClassEntry {
                name: name("Lib.Class"),
                out_params: vec![],
                out_level_params: vec![],
            }],
            protected: vec![name("Lib.protected")],
            ..SourceMetadata::default()
        };
        for version in [2, 3] {
            let encoded = encode_module_with_source_metadata(
                input(&constants),
                &metadata,
                header(version),
                WriteBudget::default(),
            )
            .unwrap();
            let view = OleanView::parse(&encoded.bytes).unwrap();
            assert_eq!(
                view.shared_audit().unwrap().objects,
                encoded.report.runtime_objects
            );
            view.walk(WalkBudget::default()).unwrap();
            let blocks = view
                .extension_payloads(WalkBudget::default(), 1024 * 1024)
                .unwrap();
            let decoded = source_extensions::decode(&blocks, DecodeLimits::default()).unwrap();
            assert_eq!(decoded.classes, metadata.classes);
            assert_eq!(decoded.protected, metadata.protected);
            assert_eq!(decoded.namespaces, vec![name("Lib")]);
            assert!(decoded.uninterpreted.is_empty());
            assert_eq!(encoded.report.constants, 2);
            assert_eq!(encoded.bytes.len() as u64, encoded.report.file_bytes);
            let exact = WriteBudget {
                max_objects: encoded.report.runtime_objects,
                max_bytes: encoded.report.file_bytes,
            };
            assert_eq!(
                encode_module_with_source_metadata(
                    input(&constants),
                    &metadata,
                    header(version),
                    exact,
                )
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
                        input(&constants),
                        &metadata,
                        header(version),
                        budget,
                    ),
                    Err(WriteError::Budget { .. })
                ));
            }
        }
    }

    #[test]
    fn unqualified_modules_keep_basic_bytes_and_extra_names_do_not_create_namespaces() {
        let constants = [constant(name("plain"))];
        let extras = [name("Foreign.Internal.onlyExtra")];
        let input = ModuleWriteInput {
            extra_const_names: &extras,
            ..input(&constants)
        };
        for version in [2, 3] {
            let baseline = encode_module(input, header(version), WriteBudget::default()).unwrap();
            let actual = encode_module_with_source_metadata(
                input,
                &SourceMetadata::default(),
                header(version),
                WriteBudget::default(),
            )
            .unwrap();
            assert_eq!(actual, baseline);
        }
    }

    #[test]
    fn explicit_root_namespace_round_trips_in_both_formats() {
        let metadata = SourceMetadata {
            namespaces: vec![name("Only.Exact"), Name::anonymous()],
            ..SourceMetadata::default()
        };
        for version in [2, 3] {
            let encoded = encode_module_with_source_metadata(
                input(&[]),
                &metadata,
                header(version),
                WriteBudget::default(),
            )
            .unwrap();
            let view = OleanView::parse(&encoded.bytes).unwrap();
            view.walk(WalkBudget::default()).unwrap();
            let blocks = view
                .extension_payloads(WalkBudget::default(), 1024 * 1024)
                .unwrap();
            let decoded = source_extensions::decode(&blocks, DecodeLimits::default()).unwrap();
            let mut expected = metadata.namespaces.clone();
            expected.sort_by(Name::quick_cmp);
            assert_eq!(decoded.namespaces, expected);
            assert!(!decoded.namespaces.contains(&name("Only")));
            assert_eq!(encoded.report.constants, 0);
            assert!(decoded.classes.is_empty());
        }
        // The root name is an immediate scalar, not a heap name object.
        let encoder = Encoder::new(
            WriteBudget {
                max_objects: 0,
                ..WriteBudget::default()
            },
            2,
        )
        .unwrap();
        assert_eq!(
            encoder
                .declaration_namespaces(&[], &[Name::anonymous()], &[], &[])
                .unwrap(),
            vec![Name::anonymous()]
        );
        assert!(
            encoder
                .declaration_namespaces(&[], &[name("A")], &[], &[])
                .is_err()
        );
    }

    #[test]
    fn namespace_planning_is_bounded_and_failure_does_not_poison_a_retry() {
        let constants = [constant(name("A.B.C.D.value"))];
        let limited = Encoder::new(
            WriteBudget {
                max_objects: 2,
                ..WriteBudget::default()
            },
            2,
        )
        .unwrap();
        assert!(matches!(
            limited.declaration_namespaces(&constants, &[], &[], &[]),
            Err(WriteError::Budget {
                resource: WriteResource::Objects,
                ..
            })
        ));
        let fresh = Encoder::new(WriteBudget::default(), 2).unwrap();
        assert_eq!(
            fresh
                .declaration_namespaces(&constants, &[], &[], &[])
                .unwrap()
                .len(),
            4
        );
    }

    #[test]
    fn explicit_empty_namespaces_survive_but_dotted_aliases_create_none() {
        let metadata = SourceMetadata {
            namespaces: vec![
                name("Empty"),
                name("Empty.ReexportOnly"),
                name("Only.Exact"),
            ],
            aliases: vec![AliasEntry {
                alias: name("Invented.Inner.x"),
                declaration: name("Original.x"),
            }],
            ..SourceMetadata::default()
        };
        for version in [2, 3] {
            let encoded = encode_module_with_source_metadata(
                input(&[]),
                &metadata,
                header(version),
                WriteBudget::default(),
            )
            .unwrap();
            let view = OleanView::parse(&encoded.bytes).unwrap();
            let blocks = view
                .extension_payloads(WalkBudget::default(), 1024 * 1024)
                .unwrap();
            let decoded = source_extensions::decode(&blocks, DecodeLimits::default()).unwrap();
            let mut expected = vec![
                name("Empty"),
                name("Empty.ReexportOnly"),
                name("Only.Exact"),
            ];
            expected.sort_by(Name::quick_cmp);
            assert_eq!(decoded.namespaces, expected);
            assert!(!decoded.namespaces.contains(&name("Only")));
            assert_eq!(decoded.aliases, metadata.aliases);
            assert!(decoded.uninterpreted.is_empty());
        }
    }
}
