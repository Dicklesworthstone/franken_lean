//! TagAttribute's Name journal for tactic candidate fallback policy.
//!
//! registerTagAttribute uses the declaration ref as its persistent extension
//! name (Lean/Attributes.lean). Its entries are ordinary serialized Names, not
//! another executable attribute or an initializer.

use super::*;

pub const NO_FALLBACK_EXTENSION: &str = "Lean.Elab.Tactic.noFallbackAttr";

impl Decoder {
    /// Shares this import sequence's byte, object, entry and Name budgets with
    /// the macro registrations. A malformed tag poisons the decoder as usual.
    pub fn decode_no_fallback(
        &mut self,
        blocks: &[OpaqueExtensionBlock],
    ) -> Result<BTreeSet<Name>, DecodeError> {
        if let Some(refusal) = self.refusal {
            return Err(match refusal {
                Refusal::Resource => limit("macro policy decoder after resource exhaustion"),
                Refusal::Malformed => shape("macro policy decoder reused after refusal"),
            });
        }
        let result = self.decode_no_fallback_batch(blocks);
        if let Err(error) = &result {
            self.refusal = Some(if error.is_resource() {
                Refusal::Resource
            } else {
                Refusal::Malformed
            });
        }
        result
    }

    fn decode_no_fallback_batch(
        &mut self,
        blocks: &[OpaqueExtensionBlock],
    ) -> Result<BTreeSet<Name>, DecodeError> {
        let wanted = Name::from_components(NO_FALLBACK_EXTENSION.split('.'));
        let mut seen = BTreeSet::new();
        let mut tagged = BTreeSet::new();
        for block in blocks {
            if !seen.insert(&block.name) {
                return Err(shape("duplicate tactic macro policy extension block"));
            }
            if block.name != wanted {
                continue;
            }
            self.remaining.max_entries = self
                .remaining
                .max_entries
                .checked_sub(block.entries.len())
                .ok_or_else(|| limit("tactic no_fallback entries"))?;
            for payload in &block.entries {
                self.remaining.max_bytes = self
                    .remaining
                    .max_bytes
                    .checked_sub(payload.len())
                    .ok_or_else(|| limit("tactic no_fallback payload bytes"))?;
                let audited = audit(payload, 0).map_err(DecodeError::Region)?;
                self.remaining.max_objects = self
                    .remaining
                    .max_objects
                    .checked_sub(audited.objects)
                    .ok_or_else(|| limit("tactic no_fallback objects"))?;
                let object = materialize(payload, 0).map_err(DecodeError::Region)?;
                let name = self.reader.name(&object)?;
                if !tagged.insert(name) {
                    return Err(shape("duplicate tactic no_fallback declaration"));
                }
            }
        }
        Ok(tagged)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use fln_rt::convert::inject_name;
    use fln_rt::obj::Obj;
    use fln_rt::region::compact;

    fn name(text: &str) -> Name {
        Name::from_components(text.split('.'))
    }

    fn block(extension: &str, objects: &[Obj]) -> OpaqueExtensionBlock {
        OpaqueExtensionBlock {
            name: name(extension),
            entries: objects
                .iter()
                .map(|object| compact(object, 0).unwrap())
                .collect(),
        }
    }

    fn tags(names: &[Name]) -> OpaqueExtensionBlock {
        block(
            NO_FALLBACK_EXTENSION,
            &names.iter().map(inject_name).collect::<Vec<_>>(),
        )
    }

    fn registration() -> OpaqueExtensionBlock {
        let row = Obj::mk_ctor(
            0,
            vec![inject_name(&name("kind")), inject_name(&name("User.rule"))],
            &[],
        );
        block(
            MACRO_EXTENSION,
            &[Obj::mk_ctor(
                crate::source_extensions::format::SCOPE_GLOBAL,
                vec![row],
                &[],
            )],
        )
    }

    #[test]
    fn no_fallback_tags_keep_structural_names_and_ignore_unrelated_extensions() {
        let expected = BTreeSet::from([
            Name::str(Name::anonymous(), "a.b"),
            name("a.b"),
            Name::num(name("_private.User"), 7),
        ]);
        let decoded = Decoder::new(DecodeLimits::default())
            .decode_no_fallback(&[tags(&expected.iter().cloned().collect::<Vec<_>>())])
            .unwrap();
        assert_eq!(decoded, expected);

        // A printable spelling alone cannot confer the extension's identity,
        // and the macro journal is not a policy journal.
        let unrelated = [
            OpaqueExtensionBlock {
                name: Name::str(Name::anonymous(), NO_FALLBACK_EXTENSION),
                entries: vec![vec![0xff]],
            },
            OpaqueExtensionBlock {
                name: name(MACRO_EXTENSION),
                entries: vec![vec![0xff]],
            },
        ];
        let limits = DecodeLimits {
            max_bytes: 0,
            max_objects: 0,
            max_entries: 0,
            ..DecodeLimits::default()
        };
        assert!(
            Decoder::new(limits)
                .decode_no_fallback(&unrelated)
                .unwrap()
                .is_empty()
        );
    }

    #[test]
    fn policy_and_macro_entries_share_exact_budgets_in_both_orders() {
        let policy = tags(&[name("User.rule")]);
        let macros = registration();
        let payloads: Vec<_> = policy.entries.iter().chain(&macros.entries).collect();
        let bytes = payloads.iter().map(|payload| payload.len()).sum();
        let objects = payloads
            .iter()
            .map(|payload| audit(payload, 0).unwrap().objects)
            .sum();
        let exact = DecodeLimits {
            max_bytes: bytes,
            max_objects: objects,
            max_entries: 2,
            ..DecodeLimits::default()
        };
        for policy_first in [false, true] {
            let first = |decoder: &mut Decoder| {
                if policy_first {
                    decoder
                        .decode_no_fallback(std::slice::from_ref(&policy))
                        .map(|_| ())
                } else {
                    decoder.decode(std::slice::from_ref(&macros)).map(|_| ())
                }
            };
            let second = |decoder: &mut Decoder| {
                if policy_first {
                    decoder.decode(std::slice::from_ref(&macros)).map(|_| ())
                } else {
                    decoder
                        .decode_no_fallback(std::slice::from_ref(&policy))
                        .map(|_| ())
                }
            };
            let mut decoder = Decoder::new(exact);
            first(&mut decoder).unwrap();
            second(&mut decoder).unwrap();
            let remaining = decoder.remaining_limits();
            assert_eq!(remaining.max_bytes, 0);
            assert_eq!(remaining.max_objects, 0);
            assert_eq!(remaining.max_entries, 0);
            for (limits, suffix) in [
                (
                    DecodeLimits {
                        max_bytes: bytes - 1,
                        ..exact
                    },
                    "payload bytes",
                ),
                (
                    DecodeLimits {
                        max_objects: objects - 1,
                        ..exact
                    },
                    "objects",
                ),
                (
                    DecodeLimits {
                        max_entries: 1,
                        ..exact
                    },
                    "entries",
                ),
            ] {
                let mut decoder = Decoder::new(limits);
                first(&mut decoder).unwrap();
                let prefix = if policy_first {
                    "macro"
                } else {
                    "tactic no_fallback"
                };
                assert!(matches!(
                    second(&mut decoder),
                    Err(DecodeError::Limit { resource })
                        if resource == format!("{prefix} {suffix}")
                ));
                assert!(decoder.decode(&[]).unwrap_err().is_resource());
                assert!(decoder.decode_no_fallback(&[]).unwrap_err().is_resource());
            }
        }
    }

    #[test]
    fn duplicate_policy_blocks_and_tags_refuse_the_whole_batch() {
        let one = tags(&[name("User.rule")]);
        for (blocks, expected) in [
            (
                vec![one.clone(), one],
                "duplicate tactic macro policy extension block",
            ),
            (
                vec![tags(&[name("User.rule"), name("User.rule")])],
                "duplicate tactic no_fallback declaration",
            ),
        ] {
            let mut decoder = Decoder::new(DecodeLimits::default());
            assert!(matches!(
                decoder.decode_no_fallback(&blocks),
                Err(DecodeError::Shape { detail }) if detail == expected
            ));
            assert!(matches!(
                decoder.decode(&[]),
                Err(DecodeError::Shape { .. })
            ));
            assert!(matches!(
                decoder.decode_no_fallback(&[]),
                Err(DecodeError::Shape { .. })
            ));
        }
    }

    #[test]
    fn malformed_policy_suffixes_poison_both_decoder_entry_points() {
        let malformed_name = Obj::mk_ctor(
            1,
            vec![inject_name(&Name::anonymous()), Obj::mk_string("forged")],
            &0u64.to_le_bytes(),
        );
        for payload in [
            compact(&inject_name(&Name::anonymous()), 0).unwrap(),
            compact(&Obj::mk_nat(2), 0).unwrap(),
            compact(&Obj::mk_string("not a Name"), 0).unwrap(),
            compact(&malformed_name, 0).unwrap(),
            vec![0xff],
        ] {
            let mut input = tags(&[name("User.validPrefix")]);
            input.entries.push(payload);
            let mut decoder = Decoder::new(DecodeLimits::default());
            let error = decoder.decode_no_fallback(&[input]).unwrap_err();
            assert!(!error.is_resource(), "{error:?}");
            assert!(matches!(
                decoder.decode(&[]),
                Err(DecodeError::Shape { .. })
            ));
            assert!(matches!(
                decoder.decode_no_fallback(&[]),
                Err(DecodeError::Shape { .. })
            ));
        }
        let mut decoder = Decoder::new(DecodeLimits::default());
        assert!(
            decoder
                .decode(&[block(MACRO_EXTENSION, &[Obj::mk_nat(0)])])
                .is_err()
        );
        assert!(matches!(
            decoder.decode_no_fallback(&[tags(&[name("User.rule")])]),
            Err(DecodeError::Shape { .. })
        ));
    }

    #[test]
    fn live_pinned_no_fallback_journal_separates_tags_from_macro_registration() {
        use crate::region::{OleanView, WalkBudget};
        use fln_core::name::LeafView;
        use std::path::PathBuf;
        use std::process::Command;

        let Some(reference) = std::env::var_os("FLN_REFERENCE_LEAN").map(PathBuf::from) else {
            assert!(
                std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
                "pinned Reference required for the no_fallback journal"
            );
            eprintln!("SKIP: no_fallback journal requires FLN_REFERENCE_LEAN");
            return;
        };
        let version = Command::new(&reference)
            .args(["-j1", "--githash"])
            .output()
            .unwrap();
        assert!(version.status.success());
        assert_eq!(
            String::from_utf8(version.stdout).unwrap().trim(),
            crate::format::PIN_COMMIT
        );
        let root = std::env::var_os("FLN_IR_REFERENCE_ARTIFACTS")
            .map(PathBuf::from)
            .unwrap_or_else(std::env::temp_dir);
        let unique = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let dir = root.join(format!("tactic-policy-{}-{unique}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(
            dir.join("NativeTacticPolicyJournal.lean"),
            include_str!("../../../fixtures/NativeTacticPolicyJournal.lean"),
        )
        .unwrap();
        let result = Command::new(&reference)
            .current_dir(&dir)
            .args([
                "-j1",
                "-o",
                "NativeTacticPolicyJournal.olean",
                "NativeTacticPolicyJournal.lean",
            ])
            .output()
            .unwrap();
        std::fs::write(dir.join("compile.stdout"), &result.stdout).unwrap();
        std::fs::write(dir.join("compile.stderr"), &result.stderr).unwrap();
        assert!(
            result.status.success(),
            "{dir:?}: {}{}",
            String::from_utf8_lossy(&result.stdout),
            String::from_utf8_lossy(&result.stderr)
        );
        let public = std::fs::read(dir.join("NativeTacticPolicyJournal.olean")).unwrap();
        let server = std::fs::read(dir.join("NativeTacticPolicyJournal.olean.server")).unwrap();
        let private = std::fs::read(dir.join("NativeTacticPolicyJournal.olean.private")).unwrap();
        let public_blocks = OleanView::parse(&public)
            .unwrap()
            .extension_payloads(WalkBudget::default(), 8 << 20)
            .unwrap();
        let private_blocks = OleanView::parse_with_dependencies(&private, &[&public, &server])
            .unwrap()
            .extension_payloads(WalkBudget::default(), 8 << 20)
            .unwrap();
        let exported = Decoder::new(DecodeLimits::default())
            .decode_no_fallback(&public_blocks)
            .unwrap();
        assert_eq!(exported, BTreeSet::from([name("stopFallback")]));
        let mut decoder = Decoder::new(DecodeLimits::default());
        let rows = decoder.decode(&private_blocks).unwrap();
        let tagged = decoder.decode_no_fallback(&private_blocks).unwrap();
        assert_eq!(tagged.len(), 2, "{tagged:?}; {dir:?}");
        assert!(tagged.contains(&name("stopFallback")));
        assert!(!tagged.contains(&name("allowFallback")));
        let private_name = tagged
            .iter()
            .find(|declaration| **declaration != name("stopFallback"))
            .unwrap();
        assert_eq!(private_name.leaf_view(), LeafView::Str("privateTagged"));
        let counter = private_name.parent();
        assert!(matches!(counter.leaf_view(), LeafView::Num(_)));
        assert_eq!(counter.parent(), name("_private.NativeTacticPolicyJournal"));
        assert_eq!(rows.len(), 2, "{rows:?}");
        assert!(
            rows.iter()
                .all(|row| row.key == name("journalTactic") && row.scope.is_none())
        );
        assert_eq!(
            rows.into_iter()
                .map(|row| row.declaration)
                .collect::<BTreeSet<_>>(),
            BTreeSet::from([name("stopFallback"), name("allowFallback")]),
            "tagging a private declaration alone does not register a macro"
        );
        eprintln!(
            "pinned tactic policy: one public tag, two complete tags, two macro registrations"
        );
    }
}
