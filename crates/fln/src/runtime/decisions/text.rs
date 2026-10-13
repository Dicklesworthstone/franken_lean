//! Post-admission execution of the pin's constructive String/Char equality.
//!
//! Only `Decidable.decide` applied to these exact standard decisions selects
//! this adapter. The kernel expressions, propositions and proof fields are
//! untouched. The inventories bind the full type/body/structural dependency
//! closure, extracted by `cargo run -p fln --example extract_text_equality`.
use super::*;

const STRING: &str = include_str!("string_dependencies.txt");
const CHARACTER: &str = include_str!("char_dependencies.txt");
const PRIMITIVE: &str = "_fln_runtime_text_equality_abi";

#[derive(Default)]
pub(in crate::runtime) struct Store {
    string_checked: bool,
    char_checked: bool,
    string_primitive: Option<IntrinsicBinding>,
}

fn dependency(encoded: &str) -> Name {
    encoded.split('/').fold(Name::anonymous(), |prefix, part| {
        if let Some(text) = part.strip_prefix("s:") {
            Name::str(prefix, text)
        } else {
            Name::num(
                prefix,
                part.strip_prefix("n:")
                    .expect("fixed text equality name")
                    .parse()
                    .expect("fixed numeric component"),
            )
        }
    })
}

impl Preparation<'_> {
    pub(crate) fn text_equality_intrinsic_binding(
        &self,
        requested: &Name,
    ) -> Option<IntrinsicBinding> {
        self.text_decisions
            .string_primitive
            .as_ref()
            .filter(|binding| &binding.name == requested)
            .cloned()
    }

    pub(in crate::runtime) fn text_equality_intrinsic_type(
        &self,
        requested: &Name,
    ) -> Option<Expr> {
        self.text_equality_intrinsic_binding(requested).map(|_| {
            let string = Expr::const_(name("String"), vec![]);
            Expr::forall_e(
                Name::anonymous(),
                string.clone(),
                Expr::forall_e(
                    Name::anonymous(),
                    string,
                    Expr::const_(name("Bool"), vec![]),
                    BinderInfo::Default,
                ),
                BinderInfo::Default,
            )
        })
    }

    fn text_equality_model(&mut self, character: bool) -> Result<bool, IngressError> {
        if if character {
            self.text_decisions.char_checked
        } else {
            self.text_decisions.string_checked
        } {
            self.tick()?;
            return Ok(true);
        }
        let inventory = if character { CHARACTER } else { STRING };
        if inventory.trim().is_empty() {
            return Err(unsupported(
                "text equality requires its complete pinned model",
            ));
        }
        for line in inventory.lines() {
            self.tick()?;
            let (encoded, digest) = line
                .split_once('\t')
                .expect("fixed text equality inventory row");
            for _ in encoded.split('/') {
                self.tick()?;
            }
            let label = dependency(encoded);
            if self
                .environment
                .entry(&label)
                .is_none_or(|entry| entry.digest().to_hex() != digest)
            {
                return Err(unsupported(
                    "text equality dependency differs from the complete pinned model",
                ));
            }
            // Logical identities do not bind execution journals. Do not bypass
            // a user-selected implementation or an initialized runtime value.
            if self
                .runtime_initializers
                .is_some_and(|names| names.contains(&label))
                || self.implementation_target(&label)?.is_some()
            {
                return Ok(false);
            }
            source_intrinsics::check_selected_extern_attribute(
                self.environment,
                &label,
                &mut self.externs,
                &mut self.visited,
                self.limits,
            )?;
        }
        // Cache only after every body, rule, metadata entry and budget check.
        if character {
            self.text_decisions.char_checked = true;
        } else {
            self.text_decisions.string_checked = true;
        }
        Ok(true)
    }

    pub(super) fn text_equality_decision(
        &mut self,
        callee: &Name,
        operands: &[Expr],
    ) -> Result<Option<Expr>, IngressError> {
        let character = if callee == &name("instDecidableEqChar") {
            true
        } else if callee == &name("instDecidableEqString") || callee == &name("String.decEq") {
            false
        } else {
            return Ok(None);
        };
        if operands.len() != 2 || !self.text_equality_model(character)? {
            return Ok(None);
        }
        if character {
            // Preserve the logical Char/UInt32/BitVec/Fin records. Read each
            // operand exactly once through their checked projection layout.
            let projections = self.native_character_projections()?;
            let mut values = Vec::with_capacity(2);
            for operand in operands {
                let mut value = operand.clone();
                for projection in &projections {
                    self.tick()?;
                    value = Expr::proj(projection.clone(), 0, value);
                }
                values.push(value);
            }
            return Ok(Some(
                values
                    .into_iter()
                    .fold(Expr::const_(name("Nat.beq"), vec![]), Expr::app),
            ));
        }
        if self.text_decisions.string_primitive.is_none() {
            let primitive = name(PRIMITIVE);
            if self.environment.contains(&primitive) {
                return Err(unsupported("text equality primitive name collision"));
            }
            let mut binding = generated_source_intrinsic_binding(&name("String.decEq"))
                .ok_or_else(|| unsupported("text equality generated native row"))?;
            if binding.arguments != [ValueType::String, ValueType::String]
                || binding.result != ValueType::Bool
                || binding.universe_arity != 0
            {
                return Err(unsupported("text equality generated native signature"));
            }
            binding.name = primitive;
            self.text_decisions.string_primitive = Some(binding);
        }
        Ok(Some(
            operands
                .iter()
                .cloned()
                .fold(Expr::const_(name(PRIMITIVE), vec![]), Expr::app),
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::source_check::modules::imported::SourceOleanImportLimits;
    use fln_comp::fir::EffectClass;
    use fln_comp::flbc::{ArgumentOwnership, ResultOwnership};
    use std::sync::OnceLock;

    const STACK: usize = 128 << 20;

    fn string(value: &str) -> Expr {
        Expr::lit(fln_core::expr::Literal::Str(value.to_owned()))
    }

    fn natural(value: u64) -> Expr {
        Expr::lit(fln_core::expr::Literal::Nat(
            fln_core::expr::NatLit::from_u64(value),
        ))
    }

    fn on_stack(test: impl FnOnce() + Send + 'static) {
        std::thread::Builder::new()
            .stack_size(STACK)
            .spawn(test)
            .unwrap()
            .join()
            .unwrap();
    }

    fn environment() -> &'static Environment {
        static PIN: OnceLock<Environment> = OnceLock::new();
        PIN.get_or_init(|| {
            let module = name("Init.Prelude");
            Engine::builder()
                .build_empty()
                .import_olean_modules_for_source(
                    &[OleanModuleInput {
                        name: &module,
                        artifact: include_bytes!(concat!(
                            env!("CARGO_MANIFEST_DIR"),
                            "/../fln-conformance/fixtures/tag_attributes/prelude.olean"
                        )),
                        server_artifact: Some(include_bytes!(concat!(
                            env!("CARGO_MANIFEST_DIR"),
                            "/../fln-conformance/fixtures/tag_attributes/prelude.olean.server"
                        ))),
                        private_artifact: Some(include_bytes!(concat!(
                            env!("CARGO_MANIFEST_DIR"),
                            "/../fln-conformance/fixtures/tag_attributes/prelude.olean.private"
                        ))),
                    }],
                    std::slice::from_ref(&module),
                    &KVMap::new(),
                    SourceOleanImportLimits::new(OleanCheckLimits::new(
                        16 << 20,
                        Budget::for_stack_bytes(STACK),
                    )),
                )
                .unwrap()
                .into_complete()
                .expect("both checking seats admit the mandatory retained Prelude")
                .engine
                .environment()
                .clone()
        })
    }

    /// Hostile comparison data only: altered constants are not admitted by a
    /// checker or installed in an executable engine. All other entries and
    /// execution journals retain the authentic predecessor's exact bytes.
    fn altered(
        target: &str,
        change: impl FnOnce(ConstantInfo) -> Option<ConstantInfo>,
    ) -> Environment {
        let original = environment();
        let target = name(target);
        let changed = change(original.find(&target).unwrap().clone());
        let mut result = Environment::new();
        for (label, _) in original.constants() {
            if label != &target {
                result = result.with_entry(original.entry(label).unwrap()).unwrap();
            }
        }
        if let Some(changed) = changed {
            result = result.add_decl(changed).unwrap();
        }
        for (label, state) in original.extensions() {
            result = result.register_extension(state.descriptor.clone()).unwrap();
            for entry in state.entries() {
                result = result
                    .push_extension_entry(label, entry.payload.clone())
                    .unwrap();
            }
        }
        result
    }

    #[test]
    fn pinned_text_decisions_bind_complete_models_and_borrowed_native_arguments() {
        on_stack(|| {
            let mut prep = Preparation::new(environment(), IngressLimits::default());
            let operands = [string("λ"), string("λ")];
            assert!(
                prep.text_equality_decision(&name("instDecidableEqString"), &operands)
                    .unwrap()
                    .is_some()
            );
            assert!(prep.text_equality_model(true).unwrap());
            let binding = prep
                .text_equality_intrinsic_binding(&name(PRIMITIVE))
                .unwrap();
            assert_eq!(binding.row, "extern:String.decEq");
            assert_eq!(binding.arguments, [ValueType::String, ValueType::String]);
            assert_eq!(binding.result, ValueType::Bool);
            assert_eq!(binding.effect, EffectClass::Pure);
            assert_eq!(
                binding.argument_ownership,
                [ArgumentOwnership::Borrowed, ArgumentOwnership::Borrowed]
            );
            assert_eq!(binding.result_ownership, ResultOwnership::Scalar);
            assert!(
                prep.text_equality_intrinsic_binding(&name("String.decEq"))
                    .is_none()
            );
        });
    }

    #[test]
    fn missing_or_changed_text_dependencies_never_fill_success_caches() {
        on_stack(|| {
            for (target, character) in [
                ("String.decEq", false),
                ("instDecidableEqString", false),
                ("Decidable.decide", false),
                ("instDecidableEqChar", true),
                ("Nat.beq", true),
                ("Char", true),
                ("Char.mk", true),
                ("Decidable.rec", true),
            ] {
                for omit in [false, true] {
                    let changed = altered(target, |mut info| {
                        if omit {
                            return None;
                        }
                        match &mut info {
                            ConstantInfo::Defn(value) => value.value = natural(13),
                            ConstantInfo::Induct(value) => value.num_indices += 1,
                            ConstantInfo::Ctor(value) => value.num_fields += 1,
                            ConstantInfo::Rec(value) => value.rules[0].rhs = natural(13),
                            _ => panic!("unexpected comparison mutant"),
                        }
                        Some(info)
                    });
                    let mut prep = Preparation::new(&changed, IngressLimits::default());
                    assert!(
                        prep.text_equality_model(character).is_err(),
                        "{target}; omit={omit}"
                    );
                    assert!(!prep.text_decisions.string_checked);
                    assert!(!prep.text_decisions.char_checked);
                    assert!(prep.text_decisions.string_primitive.is_none());
                }
            }
        });
    }

    #[test]
    fn text_decision_budgets_charge_checks_and_cached_uses_without_partial_publication() {
        on_stack(|| {
            for character in [false, true] {
                let mut complete = Preparation::new(environment(), IngressLimits::default());
                assert!(complete.text_equality_model(character).unwrap());
                let cost = complete.visited;
                assert!(cost > 1);
                let mut stopped = Preparation::new(
                    environment(),
                    IngressLimits {
                        max_nodes: cost - 1,
                        ..IngressLimits::default()
                    },
                );
                assert!(matches!(
                    stopped.text_equality_model(character),
                    Err(IngressError::ResourceLimit { .. })
                ));
                assert!(!stopped.text_decisions.string_checked);
                assert!(!stopped.text_decisions.char_checked);
                assert!(stopped.text_decisions.string_primitive.is_none());
                complete.limits.max_nodes = cost;
                assert!(matches!(
                    complete.text_equality_model(character),
                    Err(IngressError::ResourceLimit { .. })
                ));
            }
        });
    }

    #[test]
    fn conflicting_externs_and_initialized_helpers_cannot_be_bypassed() {
        on_stack(|| {
            for (target, character) in [("String.decEq", false), ("Nat.beq", true)] {
                let changed = fln_elab::externs::register(
                    environment(),
                    &name(target),
                    vec![fln_elab::externs::ExternEntry::Standard {
                        backend: name("all"),
                        symbol: "foreign_text_equality".to_owned(),
                    }],
                )
                .unwrap();
                let mut prep = Preparation::new(&changed, IngressLimits::default());
                assert!(prep.text_equality_model(character).is_err());
                assert!(prep.text_decisions.string_primitive.is_none());

                let initialized = [name(target)].into_iter().collect();
                let mut prep = Preparation::new(environment(), IngressLimits::default())
                    .with_runtime_initializers(&initialized);
                assert!(!prep.text_equality_model(character).unwrap());
                assert!(!prep.text_decisions.string_checked);
                assert!(!prep.text_decisions.char_checked);
            }
        });
    }

    #[test]
    fn explicit_implementations_and_private_name_collisions_are_not_overridden() {
        on_stack(|| {
            let ConstantInfo::Defn(mut replacement) =
                environment().find(&name("String.decEq")).unwrap().clone()
            else {
                panic!("pinned String.decEq definition");
            };
            replacement.base.name = name("replacementTextDecision");
            replacement.all.clear();
            let changed = environment()
                .add_decl(ConstantInfo::Defn(replacement))
                .unwrap();
            let changed = fln_elab::implemented_by::register(
                &changed,
                &name("String.decEq"),
                &name("replacementTextDecision"),
            )
            .unwrap();
            let mut prep = Preparation::new(&changed, IngressLimits::default());
            assert!(!prep.text_equality_model(false).unwrap());
            assert!(!prep.text_decisions.string_checked);
            assert!(prep.text_decisions.string_primitive.is_none());

            let ConstantInfo::Defn(mut collision) =
                environment().find(&name("String.decEq")).unwrap().clone()
            else {
                unreachable!();
            };
            collision.base.name = name(PRIMITIVE);
            collision.all.clear();
            let changed = environment()
                .add_decl(ConstantInfo::Defn(collision))
                .unwrap();
            let mut prep = Preparation::new(&changed, IngressLimits::default());
            assert!(
                prep.text_equality_decision(&name("String.decEq"), &[string("a"), string("b")])
                    .is_err()
            );
            assert!(prep.text_decisions.string_primitive.is_none());
        });
    }
}
