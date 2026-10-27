//! Post-admission contracts for the pin's constructive equality decisions.
//!
//! For String/Char, `Decidable.decide` applied to the exact standard decision
//! selects the adapter. The kernel expressions, propositions and proof fields are
//! untouched. The inventories bind the full type/body/structural dependency
//! closure, extracted by `cargo run -p fln --example extract_text_equality`.
//! The raw Nat decision bindings share these checks and keep their constructor
//! representation rather than applying `Decidable.decide`.
use super::*;

const STRING: &str = include_str!("string_dependencies.txt");
const CHARACTER: &str = include_str!("char_dependencies.txt");
const NATURAL: &str = include_str!("nat_dependencies.txt");
const PRIMITIVE: &str = "_fln_runtime_text_equality_abi";
/// The checked `String.decEq` as a first-class decision, over [`PRIMITIVE`].
const STRING_DECISION: &str = "_fln_runtime_string_decEq";

#[derive(Default)]
pub(in crate::runtime) struct Store {
    string_checked: bool,
    char_checked: bool,
    string_primitive: Option<IntrinsicBinding>,
    string_decision: bool,
    pub(super) natural_primitives: [Option<IntrinsicBinding>; 3],
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
        if !self.checked_equality_inventory(inventory)? {
            return Ok(false);
        }
        // Cache only after every body, rule, metadata entry and budget check.
        if character {
            self.text_decisions.char_checked = true;
        } else {
            self.text_decisions.string_checked = true;
        }
        Ok(true)
    }

    pub(super) fn native_natural_decision_model(
        &mut self,
        requested: &Name,
    ) -> Result<bool, IngressError> {
        let header = format!("@{}", requested.to_display_string());
        let mut inventory = None;
        for section in NATURAL.trim_end().split("\n\n") {
            self.tick()?;
            let (label, rows) = section
                .split_once('\n')
                .ok_or_else(|| unsupported("malformed natural decision contract section"))?;
            if !label.starts_with('@') {
                return Err(unsupported("malformed natural decision contract header"));
            }
            if label == header && inventory.replace(rows).is_some() {
                return Err(unsupported("duplicate natural decision contract section"));
            }
        }
        let inventory =
            inventory.ok_or_else(|| unsupported("missing natural decision contract section"))?;
        // This contract refuses every selected replacement in its dependency
        // closure. Inspect those edges before resolving targets so a refused
        // candidate cannot invoke another native recognizer during selection.
        for line in inventory.lines() {
            self.tick()?;
            let (encoded, _) = line.split_once('\t').expect("fixed natural equality row");
            for _ in encoded.split('/') {
                self.tick()?;
            }
            if self.implementations()?.get(&dependency(encoded)).is_some() {
                return Ok(false);
            }
        }
        self.checked_equality_inventory(inventory)
    }

    fn checked_equality_inventory(&mut self, inventory: &str) -> Result<bool, IngressError> {
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
        self.text_string_primitive()?;
        Ok(Some(
            operands
                .iter()
                .cloned()
                .fold(Expr::const_(name(PRIMITIVE), vec![]), Expr::app),
        ))
    }

    /// One native row per program: the applied decision and the first-class
    /// one call the same private primitive.
    fn text_string_primitive(&mut self) -> Result<(), IngressError> {
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
        Ok(())
    }

    /// `String.decEq` passed as a value (an instance argument, a `BEq` built
    /// by `instBEqOfDecidableEq`) has no `decide` around it to select the
    /// applied adapter. Under the same complete pinned model and extern check,
    /// rebuild its `Decidable` from the native Boolean, as `Nat.decEq` does;
    /// otherwise its body would match on the String structure itself.
    pub(super) fn native_string_decision_target(
        &mut self,
        requested: &Name,
    ) -> Result<Option<Name>, IngressError> {
        let target = name(STRING_DECISION);
        if self.text_decisions.string_decision {
            self.tick()?;
            return Ok(Some(target));
        }
        source_intrinsics::read_extern_attributes(
            self.environment,
            &mut self.externs,
            &mut self.visited,
            self.limits,
        )?;
        if !self
            .externs
            .as_ref()
            .is_some_and(|table| table.get(requested).is_some())
        {
            return Ok(None);
        }
        source_intrinsics::check_selected_extern_attribute(
            self.environment,
            requested,
            &mut self.externs,
            &mut self.visited,
            self.limits,
        )?;
        // Callable-type and companion lookups consult this target for any
        // String.decEq they meet, including in an environment holding only
        // part of the pinned model. A model that is absent or different grants
        // no native authority and leaves the ordinary path in force; only a
        // budget stop is an answer here.
        match self.text_equality_model(false) {
            Ok(true) => {}
            Ok(false) | Err(IngressError::UnsupportedNode { .. }) => return Ok(None),
            Err(error) => return Err(error),
        }
        let decision = Expr::app(
            Expr::const_(name("Decidable"), vec![]),
            Expr::const_(name("True"), vec![]),
        );
        if self.value_type(&decision)? != Some(ValueType::Constructor) {
            return Err(unsupported("native decision constructor representation"));
        }
        self.text_string_primitive()?;
        let mut branches = Vec::new();
        for constructor in ["Decidable.isFalse", "Decidable.isTrue"] {
            let value = self
                .specialize_constructor(
                    &Expr::const_(name(constructor), vec![]),
                    &[Expr::const_(name("True"), vec![]), proofs::erased_value()],
                )?
                .ok_or_else(|| unsupported("native decision constructor adapter"))?;
            branches.push(value);
        }
        let string = Expr::const_(name("String"), vec![]);
        let mut value = Expr::const_(name(PRIMITIVE), vec![]);
        for index in [1, 0] {
            value = Expr::app(
                value,
                Expr::bvar(index).expect("fixed native decision argument"),
            );
        }
        let motive = Expr::lam(
            Name::anonymous(),
            Expr::const_(name("Bool"), vec![]),
            decision.clone(),
            BinderInfo::Default,
        );
        value = [motive, branches.remove(0), branches.remove(0), value]
            .into_iter()
            .fold(
                Expr::const_(name("Bool.rec"), vec![Level::one()]),
                Expr::app,
            );
        let mut type_ = decision;
        for _ in 0..2 {
            value = Expr::lam(
                Name::anonymous(),
                string.clone(),
                value,
                BinderInfo::Default,
            );
            type_ = Expr::forall_e(
                Name::anonymous(),
                string.clone(),
                type_,
                BinderInfo::Default,
            );
        }
        self.remember_native_scalar_adapter_definition(DefinitionVal {
            base: fln_env::constants::ConstantVal {
                name: target.clone(),
                level_params: Vec::new(),
                type_,
            },
            value,
            hints: fln_env::constants::ReducibilityHints::Abbrev,
            safety: fln_env::constants::DefinitionSafety::Safe,
            all: Vec::new(),
        })?;
        self.text_decisions.string_decision = true;
        Ok(Some(target))
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
        engine().environment()
    }

    fn engine() -> &'static Engine {
        static PIN: OnceLock<Engine> = OnceLock::new();
        PIN.get_or_init(|| {
            let module = name("Init.Prelude");
            Engine::builder()
                .build_empty()
                .import_olean_modules_for_source(
                    &[OleanModuleInput {
                        name: &module,
                        // File-relative, as fln-olean's source_extensions test includes the
                        // same fixture: compile-time bytes need no compile-time tree root.
                        artifact: include_bytes!(
                            "../../../../fln-conformance/fixtures/tag_attributes/prelude.olean"
                        ),
                        server_artifact: Some(include_bytes!(
                            "../../../../fln-conformance/fixtures/tag_attributes/prelude.olean.server"
                        )),
                        private_artifact: Some(include_bytes!(
                            "../../../../fln-conformance/fixtures/tag_attributes/prelude.olean.private"
                        )),
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
        })
    }

    #[test]
    fn pinned_natural_decisions_execute_dynamic_constructor_branches() {
        on_stack(|| {
            let definitions = r"
def chooseEq (n m : Nat) : Bool := if _h : n = m then true else false
def chooseLe (n m : Nat) : Bool := if _h : n ≤ m then true else false
def chooseLt (n m : Nat) : Bool := if _h : n < m then true else false
def choosePartial (n m : Nat) : Bool :=
  let f := Nat.decEq n
  match f m with
  | .isFalse _ => false
  | .isTrue _ => true
structure NatDecision where
  run : (n m : Nat) → Decidable (n = m)
def chooseStored (n m : Nat) : Bool :=
  let box : NatDecision := ⟨Nat.decEq⟩
  match box.run n m with
  | .isFalse _ => false
  | .isTrue _ => true
";
            let checked = engine()
                .check_source_files(
                    &[definitions.as_bytes()],
                    &KVMap::new(),
                    crate::SourceCheckLimits::new(crate::EngineAdmissionLimits::new(
                        Budget::for_stack_bytes(STACK),
                    )),
                )
                .unwrap()
                .into_complete()
                .expect("the actual source definitions pass both checkers");
            let source = "#eval chooseEq 0 0\n\
                #eval chooseEq 0 7\n\
                #eval chooseEq 18446744073709551616 18446744073709551616\n\
                #eval chooseEq 18446744073709551617 18446744073709551616\n\
                #eval chooseLe 0 0\n\
                #eval chooseLe 0 7\n\
                #eval chooseLe 18446744073709551617 18446744073709551616\n\
                #eval chooseLe 18446744073709551616 18446744073709551617\n\
                #eval chooseLt 0 0\n\
                #eval chooseLt 0 7\n\
                #eval chooseLt 18446744073709551617 18446744073709551616\n\
                #eval chooseLt 18446744073709551616 18446744073709551617\n\
                #eval choosePartial 0 0\n\
                #eval choosePartial 0 7\n\
                #eval choosePartial 18446744073709551616 18446744073709551616\n\
                #eval choosePartial 18446744073709551617 18446744073709551616\n\
                #eval chooseStored 0 0\n\
                #eval chooseStored 0 7\n";
            let result = checked
                .engine
                .execute_source_definitions(
                    &[source.as_bytes()],
                    &KVMap::new(),
                    crate::EngineExecutionLimits::new(Budget::for_stack_bytes(STACK)),
                )
                .unwrap()
                .into_complete()
                .expect("the checked source evaluation completes");
            assert_eq!(result.executions.len(), 18);
            let values: Vec<_> = result
                .executions
                .iter()
                .map(|execution| {
                    crate::closed_vm_value(&execution.exit)
                        .unwrap_or_else(|error| {
                            panic!("{error:?}; actual VM exit: {:?}", execution.exit)
                        })
                        .unwrap_or_else(|| {
                            panic!(
                                "each query returns a closed Bool; actual VM exit: {:?}",
                                execution.exit
                            )
                        })
                })
                .collect();
            assert_eq!(
                values,
                [1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0]
                    .map(crate::ClosedVmValue::Scalar)
            );
        });
    }

    /// `String.decEq` used as a value — a partial application, a stored field,
    /// a `BEq` built from the instance — has no `decide` around it. It still
    /// runs the native row through the same model, and shares one intrinsic
    /// declaration with the applied decision in the same program.
    #[test]
    fn pinned_string_decisions_execute_as_values_and_share_one_native_row() {
        on_stack(|| {
            let definitions = r#"
def chooseString (a b : String) : Bool := if _h : a = b then true else false
def stringPartial (a b : String) : Bool :=
  let f := String.decEq a
  match f b with
  | .isFalse _ => false
  | .isTrue _ => true
structure StringDecision where
  run : (a b : String) → Decidable (a = b)
def stringStored (a b : String) : Bool :=
  let box : StringDecision := ⟨String.decEq⟩
  match box.run a b with
  | .isFalse _ => false
  | .isTrue _ => true
def stringBoth (a b : String) : Bool :=
  let f := String.decEq a
  match f b with
  | .isFalse _ => decide (a = b)
  | .isTrue _ => decide (b = a)
"#;
            let checked = engine()
                .check_source_files(
                    &[definitions.as_bytes()],
                    &KVMap::new(),
                    crate::SourceCheckLimits::new(crate::EngineAdmissionLimits::new(
                        Budget::for_stack_bytes(STACK),
                    )),
                )
                .unwrap()
                .into_complete()
                .expect("the actual source definitions pass both checkers");
            let source = "#eval chooseString \"λ😀\" \"λ😀\"\n\
                #eval chooseString \"λ😀\" \"λ\"\n\
                #eval stringPartial \"λ😀\" \"λ😀\"\n\
                #eval stringPartial \"\" \"x\"\n\
                #eval stringStored \"abc\" \"abc\"\n\
                #eval stringStored \"abc\" \"abd\"\n\
                #eval stringBoth \"abc\" \"abc\"\n\
                #eval stringBoth \"abc\" \"ab\"\n";
            let result = checked
                .engine
                .execute_source_definitions(
                    &[source.as_bytes()],
                    &KVMap::new(),
                    crate::EngineExecutionLimits::new(Budget::for_stack_bytes(STACK)),
                )
                .unwrap()
                .into_complete()
                .expect("the checked source evaluation completes");
            let values: Vec<_> = result
                .executions
                .iter()
                .map(|execution| crate::closed_vm_value(&execution.exit).unwrap().unwrap())
                .collect();
            assert_eq!(
                values,
                [1, 0, 1, 0, 1, 0, 1, 0].map(crate::ClosedVmValue::Scalar)
            );

            let mut prep = Preparation::new(environment(), IngressLimits::default());
            let target = prep
                .native_natural_decision_target(&name("String.decEq"))
                .unwrap()
                .expect("the pinned String decision binds as a value");
            assert_eq!(target, name(STRING_DECISION));
            let binding = prep
                .text_equality_intrinsic_binding(&name(PRIMITIVE))
                .expect("the shared native row");
            assert_eq!(binding.row, "extern:String.decEq");
            assert_eq!(
                binding.argument_ownership,
                [ArgumentOwnership::Borrowed, ArgumentOwnership::Borrowed]
            );
            assert_eq!(binding.result_ownership, ResultOwnership::Scalar);

            // A foreign extern is refused, a selected replacement is never
            // bypassed, and an altered model never fills the success cache.
            let foreign = fln_elab::externs::register(
                environment(),
                &name("String.decEq"),
                vec![fln_elab::externs::ExternEntry::Standard {
                    backend: name("all"),
                    symbol: "foreign_text_equality".to_owned(),
                }],
            )
            .unwrap();
            let mut prep = Preparation::new(&foreign, IngressLimits::default());
            assert!(
                prep.native_natural_decision_target(&name("String.decEq"))
                    .is_err()
            );
            let ConstantInfo::Defn(mut replacement) =
                environment().find(&name("String.decEq")).unwrap().clone()
            else {
                unreachable!();
            };
            replacement.base.name = name("replacementStringDecision");
            replacement.all = vec![name("replacementStringDecision")];
            let replaced = environment()
                .add_decl(ConstantInfo::Defn(replacement))
                .unwrap();
            let replaced = fln_elab::implemented_by::register(
                &replaced,
                &name("String.decEq"),
                &name("replacementStringDecision"),
            )
            .unwrap();
            let mut prep = Preparation::new(&replaced, IngressLimits::default());
            assert!(
                prep.native_natural_decision_target(&name("String.decEq"))
                    .unwrap()
                    .is_none()
            );
            assert!(!prep.text_decisions.string_decision);
            let changed = altered("String.decEq", |mut info| {
                let ConstantInfo::Defn(value) = &mut info else {
                    unreachable!()
                };
                value.value = natural(13);
                Some(info)
            });
            let mut prep = Preparation::new(&changed, IngressLimits::default());
            assert!(
                prep.native_natural_decision_target(&name("String.decEq"))
                    .unwrap()
                    .is_none(),
                "an altered model grants no native authority"
            );
            assert!(!prep.text_decisions.string_decision);
            assert!(prep.text_decisions.string_primitive.is_none());
            // So does a model the environment holds only part of.
            let partial = altered("String.decEq.match_1", |_| None);
            let mut prep = Preparation::new(&partial, IngressLimits::default());
            assert!(
                prep.native_natural_decision_target(&name("String.decEq"))
                    .unwrap()
                    .is_none()
            );
            assert!(!prep.text_decisions.string_decision);
            // A budget stop is still an answer, never a silent fallback.
            let mut complete = Preparation::new(environment(), IngressLimits::default());
            assert!(
                complete
                    .native_natural_decision_target(&name("String.decEq"))
                    .unwrap()
                    .is_some()
            );
            let mut stopped = Preparation::new(
                environment(),
                IngressLimits {
                    max_nodes: complete.visited - 1,
                    ..IngressLimits::default()
                },
            );
            assert!(matches!(
                stopped.native_natural_decision_target(&name("String.decEq")),
                Err(IngressError::ResourceLimit { .. })
            ));
            assert!(!stopped.text_decisions.string_decision);
        });
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
    fn pinned_raw_natural_decisions_keep_constructor_and_native_ownership_contracts() {
        on_stack(|| {
            for operation in ["Nat.decEq", "Nat.decLe", "Nat.decLt"] {
                let mut prep = Preparation::new(environment(), IngressLimits::default());
                let target = prep
                    .native_natural_decision_target(&name(operation))
                    .unwrap()
                    .expect("the actual pinned native decision has a compiler adapter");
                assert!(prep.specialized_definition(&target).is_some());
                assert!(
                    prep.native_decision_intrinsic_binding(&name(operation))
                        .is_none()
                );
                let binding = prep
                    .text_decisions
                    .natural_primitives
                    .iter()
                    .flatten()
                    .next()
                    .unwrap();
                assert_eq!(binding.row, format!("extern:{operation}"));
                assert_eq!(binding.arguments, [ValueType::Nat, ValueType::Nat]);
                assert_eq!(binding.result, ValueType::Bool);
                assert_eq!(binding.effect, EffectClass::Pure);
                assert_eq!(
                    binding.argument_ownership,
                    [ArgumentOwnership::Borrowed, ArgumentOwnership::Borrowed]
                );
                assert_eq!(binding.result_ownership, ResultOwnership::Scalar);
                let cost = prep.visited;
                assert!(cost > 1);
                let mut stopped = Preparation::new(
                    environment(),
                    IngressLimits {
                        max_nodes: cost - 1,
                        ..IngressLimits::default()
                    },
                );
                assert!(matches!(
                    stopped.native_natural_decision_target(&name(operation)),
                    Err(IngressError::ResourceLimit { .. })
                ));
            }
        });
    }

    #[test]
    fn changed_natural_decision_dependencies_and_externs_never_receive_native_bindings() {
        on_stack(|| {
            for (target, operation) in [
                ("Nat.decEq", "Nat.decEq"),
                ("Nat.decEq.match_1", "Nat.decEq"),
                ("Nat", "Nat.decEq"),
                ("Nat.zero", "Nat.decEq"),
                ("Nat.rec", "Nat.decEq"),
                ("Decidable", "Nat.decEq"),
                ("Decidable.isTrue", "Nat.decEq"),
                ("Decidable.rec", "Nat.decEq"),
                ("Nat.decLe", "Nat.decLe"),
                ("Nat.decLt", "Nat.decLt"),
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
                        prep.native_natural_decision_target(&name(operation))
                            .is_err(),
                        "{target}; omit={omit}"
                    );
                }
            }
            for operation in ["Nat.decEq", "Nat.decLe", "Nat.decLt"] {
                let foreign = fln_elab::externs::register(
                    environment(),
                    &name(operation),
                    vec![fln_elab::externs::ExternEntry::Standard {
                        backend: name("all"),
                        symbol: "foreign_natural_equality".to_owned(),
                    }],
                )
                .unwrap();
                let mut prep = Preparation::new(&foreign, IngressLimits::default());
                assert!(
                    prep.native_natural_decision_target(&name(operation))
                        .is_err()
                );
            }
            let changed_ordering = altered("Nat.decLt", |mut info| {
                let ConstantInfo::Defn(value) = &mut info else {
                    panic!("the pinned ordering decision is a definition");
                };
                value.value = natural(13);
                Some(info)
            });
            let mut prep = Preparation::new(&changed_ordering, IngressLimits::default());
            assert!(
                prep.native_natural_decision_target(&name("Nat.decEq"))
                    .unwrap()
                    .is_some()
            );
            let ConstantInfo::Defn(mut replacement) =
                environment().find(&name("Nat.decEq")).unwrap().clone()
            else {
                unreachable!();
            };
            let replacement_name = name("replacementNaturalDecision");
            replacement.base.name = replacement_name.clone();
            replacement.all = vec![replacement_name.clone()];
            let replaced = environment()
                .add_decl(ConstantInfo::Defn(replacement))
                .unwrap();
            let replaced = fln_elab::implemented_by::register(
                &replaced,
                &name("Nat.decEq"),
                &replacement_name,
            )
            .unwrap();
            let mut prep = Preparation::new(&replaced, IngressLimits::default());
            assert!(
                prep.native_natural_decision_target(&name("Nat.decEq"))
                    .unwrap()
                    .is_none(),
                "a selected replacement must refuse the closed native adapter"
            );
        });
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
