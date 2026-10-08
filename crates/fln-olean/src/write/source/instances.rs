//! The pin's InstanceEntry and SimpleScopedEnvExtension.Entry payloads.
//! All objects use the ordinary writer's cumulative byte/object budgets.
use super::*;

impl Encoder {
    fn instance_keys(&mut self, keys: &[InstanceKey]) -> WResult<Obj> {
        self.source_array_bound(keys.len())?;
        // One complete prefix-encoded tree, never an unindexed empty fallback.
        let mut pending = 1usize;
        let mut values = Vec::with_capacity(keys.len());
        for key in keys {
            if pending == 0 {
                return Err(WriteError::Contract {
                    what: "trailing instance discrimination keys",
                });
            }
            let arity = match key {
                InstanceKey::Const(_, arity) | InstanceKey::FVar(_, arity) => *arity as usize,
                InstanceKey::Arrow => 1,
                InstanceKey::Proj(_, _, arity) => {
                    (*arity as usize)
                        .checked_add(1)
                        .ok_or(WriteError::Contract {
                            what: "instance key arity overflows",
                        })?
                }
                _ => 0,
            };
            pending = (pending - 1)
                .checked_add(arity)
                .ok_or(WriteError::Contract {
                    what: "instance key arity overflows",
                })?;
            values.push(self.instance_key(key)?);
        }
        if pending != 0 {
            return Err(WriteError::Contract {
                what: "empty or incomplete instance discrimination path",
            });
        }
        self.array(values)
    }

    fn instance_key(&mut self, key: &InstanceKey) -> WResult<Obj> {
        match key {
            InstanceKey::Star => Ok(Obj::mk_nat(usize::from(layout::KEY_STAR))),
            InstanceKey::Other => Ok(Obj::mk_nat(usize::from(layout::KEY_OTHER))),
            InstanceKey::Arrow => Ok(Obj::mk_nat(usize::from(layout::KEY_ARROW))),
            InstanceKey::Lit(value) => {
                let value = self.literal(value)?;
                self.ctor(layout::KEY_LIT, vec![value], &[])
            }
            InstanceKey::Const(name, arity) | InstanceKey::FVar(name, arity) => {
                if name.is_anonymous() {
                    return Err(WriteError::Contract {
                        what: "anonymous instance key name",
                    });
                }
                let tag = if matches!(key, InstanceKey::Const(..)) {
                    layout::KEY_CONST
                } else {
                    layout::KEY_FVAR
                };
                let name = self.name(name)?;
                let arity = self.nat_u64(u64::from(*arity))?;
                self.ctor(tag, vec![name, arity], &[])
            }
            InstanceKey::Proj(name, index, arity) => {
                if name.is_anonymous() {
                    return Err(WriteError::Contract {
                        what: "anonymous instance projection name",
                    });
                }
                let name = self.name(name)?;
                let index = self.nat_u64(u64::from(*index))?;
                let arity = self.nat_u64(u64::from(*arity))?;
                self.ctor(layout::KEY_PROJ, vec![name, index, arity], &[])
            }
        }
    }

    pub(super) fn instance_block(&mut self, instances: &[InstanceEntry]) -> WResult<Obj> {
        self.source_array_bound(instances.len())?;
        let mut entries = Vec::with_capacity(instances.len());
        for instance in instances {
            if instance.declaration.is_anonymous()
                || instance.scope.as_ref().is_some_and(Name::is_anonymous)
                || !matches!(instance.value.node(), ExprNode::Const { name, .. }
                    if name == &instance.declaration)
                || instance.value.has_level_mvar()
            {
                return Err(WriteError::Contract {
                    what: "invalid global instance declaration or scope",
                });
            }
            let keys = self.instance_keys(&instance.keys)?;
            let value = self.expression(&instance.value)?;
            let priority = self.nat_u64(u64::from(instance.priority))?;
            let name = self.name(&instance.declaration)?;
            // Option.some, matching the decoder's required globalName? shape.
            let global = self.ctor(1, vec![name], &[])?;
            let synth_order = self.source_indices(&instance.synth_order)?;
            let mut fields: Vec<_> = (0..layout::INSTANCE_POINTERS)
                .map(|_| Obj::mk_nat(0))
                .collect();
            fields[layout::INSTANCE_KEYS] = keys;
            fields[layout::INSTANCE_VAL] = value;
            fields[layout::INSTANCE_PRIORITY] = priority;
            fields[layout::INSTANCE_GLOBAL_NAME_OPTION] = global;
            fields[layout::INSTANCE_SYNTH_ORDER] = synth_order;
            let mut scalars = [0; layout::INSTANCE_SCALAR_BYTES];
            scalars[layout::INSTANCE_ATTR_KIND_SCALAR] = if instance.scope.is_some() {
                layout::ATTRIBUTE_SCOPED
            } else {
                layout::ATTRIBUTE_GLOBAL
            };
            let entry = self.ctor(0, fields, &scalars)?;
            entries.push(match &instance.scope {
                Some(scope) => {
                    let scope = self.name(scope)?;
                    self.ctor(layout::SCOPE_SCOPED, vec![scope, entry], &[])?
                }
                None => self.ctor(layout::SCOPE_GLOBAL, vec![entry], &[])?,
            });
        }
        let entries = self.array(entries)?;
        let name = self.name(&Name::from_components(
            layout::INSTANCE_EXTENSION.split('.'),
        ))?;
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
    fn row(
        name: &str,
        priority: u32,
        scope: Option<Name>,
        keys: Vec<InstanceKey>,
    ) -> InstanceEntry {
        InstanceEntry {
            declaration: n(name),
            value: Expr::const_(n(name), vec![]),
            priority,
            synth_order: vec![3, 1],
            scope,
            keys,
        }
    }
    fn rows() -> Vec<InstanceEntry> {
        use InstanceKey::*;
        vec![
            row(
                "zFirst",
                2000,
                None,
                vec![
                    Const(n("C"), 6),
                    Star,
                    Other,
                    Lit(Literal::Str("λ".into())),
                    FVar(n("x"), 0),
                    Arrow,
                    Const(n("T"), 0),
                    Proj(n("S"), 2, 0),
                    Lit(Literal::Nat(NatLit::from_u64(7))),
                ],
            ),
            row("aSecond", 1000, Some(n("Scope")), vec![Const(n("C"), 0)]),
            row("zFirst", 1000, None, vec![Const(n("C"), 0)]),
        ]
    }
    fn encode(
        rows: Vec<InstanceEntry>,
        version: u8,
        budget: WriteBudget,
    ) -> WResult<EncodedModule> {
        encode_module_with_source_metadata(
            ModuleWriteInput {
                is_module: false,
                imports: &[],
                constants: &[],
                extra_const_names: &[],
            },
            &SourceMetadata {
                instances: rows,
                ..SourceMetadata::default()
            },
            OleanWriteHeader {
                version,
                flags: 1,
                lean_version: format::PIN_TAG.strip_prefix('v').unwrap(),
                githash: format::PIN_COMMIT,
                base_addr: 2 * format::REGION_ALIGN as u64,
            },
            budget,
        )
    }

    #[test]
    fn every_pinned_key_scope_priority_and_chronological_update_round_trips() {
        for &version in format::OLEAN_ACCEPTED_VERSIONS {
            let rows = rows();
            let encoded = encode(rows.clone(), version, WriteBudget::default()).unwrap();
            let view = OleanView::parse(&encoded.bytes).unwrap();
            let blocks = view
                .extension_payloads(WalkBudget::default(), 1 << 20)
                .unwrap();
            let decoded = source_extensions::decode(&blocks, DecodeLimits::default()).unwrap();
            assert_eq!(decoded.instances, rows);
            assert!(decoded.uninterpreted.is_empty());
        }
    }

    #[test]
    fn malformed_paths_values_scopes_and_orders_are_refused() {
        let good = row("instance", 1000, None, vec![InstanceKey::Const(n("C"), 0)]);
        for keys in [
            vec![],
            vec![InstanceKey::Const(n("C"), 1)],
            vec![InstanceKey::Star, InstanceKey::Other],
            vec![InstanceKey::FVar(Name::anonymous(), 0)],
        ] {
            let mut bad = good.clone();
            bad.keys = keys;
            assert!(matches!(
                encode(vec![bad], 2, WriteBudget::default()),
                Err(WriteError::Contract { .. })
            ));
        }
        for which in 0..4 {
            let mut bad = good.clone();
            match which {
                0 => bad.declaration = Name::anonymous(),
                1 => bad.value = Expr::const_(n("different"), vec![]),
                2 => bad.scope = Some(Name::anonymous()),
                _ => bad.synth_order = vec![1, 1],
            }
            assert!(matches!(
                encode(vec![bad], 2, WriteBudget::default()),
                Err(WriteError::Contract { .. })
            ));
        }
    }

    #[test]
    fn instance_payloads_share_exact_module_byte_and_object_limits() {
        for &version in format::OLEAN_ACCEPTED_VERSIONS {
            let output = encode(rows(), version, WriteBudget::default()).unwrap();
            let exact = WriteBudget {
                max_bytes: output.report.file_bytes,
                max_objects: output.report.runtime_objects,
            };
            assert_eq!(encode(rows(), version, exact).unwrap().bytes, output.bytes);
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
                    encode(rows(), version, budget),
                    Err(WriteError::Budget { .. })
                ));
            }
        }
    }
}
