//! Source recursion reaches the IR exporter only through an admitted logical
//! interface and its exact checked executable companion. These tests use the
//! ordinary source checker; the installed Lake suite exercises physical `.ir`
//! consumers against the pinned Lean toolchain.
use super::*;
use crate::{Engine, EngineAdmissionLimits, EngineExecutionLimits, SourceCheckLimits};
use fln_comp::ingress::{IngressError, IngressResource};
use fln_core::{options::KVMap, outcome::Outcome};
use fln_env::constants::{ConstantInfo, DefinitionSafety};

const COUNT: &str = "partial def count (n : Nat) : Nat := \
    if n == 0 then 7 else count (n - 1)\n";

const ENUM_RECURSION: &str = r#"inductive Choice where | first | second | third
inductive Single where | only
partial def carryChoice (n : Nat) (value : Choice) : Choice :=
  if n == 0 then value else carryChoice (n - 1) value
partial def resetChoice (n : Nat) (value : Choice) : Choice :=
  if n == 0 then value else resetChoice (n - 1) Choice.third
partial def dropChoice (n : Nat) (ignored : Choice) : Nat :=
  if n == 0 then 7 else dropChoice (n - 1) ignored
partial def dropSingle (n : Nat) (ignored : Single) : Nat :=
  if n == 0 then 7 else dropSingle (n - 1) ignored
"#;

fn name(text: &str) -> Name {
    Name::from_components(text.split('.'))
}

fn execution_limits() -> EngineExecutionLimits {
    let mut limits = EngineExecutionLimits::new(crate::Budget::for_stack_bytes(2 * 1024 * 1024));
    // Compilation must work without evaluating even one instruction. In
    // particular, a nonterminating partial body cannot be sampled for a value.
    limits.vm.max_steps = 0;
    limits
}

fn checked(source: &str) -> Engine {
    let admission = EngineAdmissionLimits::new(execution_limits().kernel);
    Engine::with_source_seed(admission)
        .unwrap()
        .into_complete()
        .unwrap()
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(admission),
        )
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .unwrap()
        .engine
}

fn export(
    engine: &Engine,
    entry: &str,
) -> std::result::Result<Outcome<IrModule>, DefinitionCompileError> {
    compile_checked_source_definition(
        engine,
        &name(entry),
        &KVMap::new(),
        execution_limits(),
        CompileLimits::default(),
    )
}

fn assert_unsupported(engine: &Engine, entry: &str) {
    let error = export(engine, entry).unwrap_err();
    assert!(
        matches!(
            error,
            DefinitionCompileError::Ir(CompileError::Unsupported { .. })
                | DefinitionCompileError::Engine(crate::EngineExecutionError::Ingress(
                    IngressError::UnsupportedNode { .. }
                ))
        ),
        "expected an explicit unsupported refusal for {entry}, got {error:?}"
    );
}

#[test]
fn source_recursion_exports_logical_unary_entries_without_evaluation() {
    let engine = checked(&format!(
        r#"def structural : Nat -> Nat
  | .zero => 7
  | .succ n => structural n
def accumulating : Nat -> Nat
  | .zero => 0
  | .succ n => accumulating n + 2
{COUNT}
partial def spin (n : Nat) : Nat := spin (n + 1)
"#
    ));
    let before = engine.environment().clone();
    for label in ["count", "spin", "structural", "accumulating"] {
        let entry = name(label);
        let companion = Name::str(entry.clone(), "_unsafe_rec");
        if matches!(label, "count" | "spin") || engine.environment().contains(&companion) {
            assert!(matches!(
                engine.environment().find(&companion),
                Some(ConstantInfo::Defn(value)) if value.safety == DefinitionSafety::Partial
            ));
            assert!(
                is_checked_recursive_companion(
                    &engine,
                    &companion,
                    execution_limits(),
                    CompileLimits::default(),
                )
                .unwrap()
            );
        }
        let module = export(&engine, label)
            .unwrap_or_else(|error| panic!("{label}: {error:?}"))
            .into_complete()
            .unwrap();
        let Some(IrDecl::Function { params, result, .. }) =
            module.decls.iter().find(|decl| decl.name() == &entry)
        else {
            panic!("missing logical exported function {label}")
        };
        assert_eq!(params.len(), 1);
        assert_eq!(params[0].ty, IrType::TObject);
        assert_eq!(*result, IrType::TObject);
        assert!(module.decls.iter().all(|decl| {
            !decl.name().to_display_string().contains("_unsafe_rec")
                && decl.name() != &Name::str(entry.clone(), "_redArg")
        }));
        assert_eq!(engine.environment(), &before);
    }
    assert!(matches!(
        engine.environment().find(&name("count")),
        Some(ConstantInfo::Opaque(value)) if !value.is_unsafe
    ));
    for source in [
        "theorem leakedComputation : count 0 = 7 := by rfl",
        "def leakedBody : Nat := count._unsafe_rec 0",
    ] {
        assert!(
            engine
                .check_source_files(
                    &[source.as_bytes()],
                    &KVMap::new(),
                    SourceCheckLimits::new(EngineAdmissionLimits::new(execution_limits().kernel)),
                )
                .is_err(),
            "compilation changed logical opacity: {source}"
        );
    }
    assert_eq!(engine.environment(), &before);
}

#[test]
fn source_recursion_exports_closed_primitive_signatures_without_evaluation() {
    let engine = checked(
        r#"partial def textCount (n : Nat) : String :=
  if n == 0 then "done" else textCount (n - 1)
partial def truthCount (n : Nat) : Bool :=
  if n == 0 then true else truthCount (n - 1)
partial def flagNat (b : Bool) : Nat :=
  if b then flagNat false else 23
partial def flagText (b : Bool) : String :=
  if b then flagText false else "flag"
partial def flagBool (b : Bool) : Bool :=
  if b then flagBool false else true
partial def stringNat (s : String) : Nat := stringNat s
partial def stringText (s : String) : String := stringText s
partial def stringBool (s : String) : Bool := stringBool s
"#,
    );
    let before = engine.environment().clone();
    for (label, parameter, returned) in [
        ("textCount", IrType::TObject, IrType::Object),
        ("truthCount", IrType::TObject, IrType::UInt8),
        ("flagNat", IrType::UInt8, IrType::TObject),
        ("flagText", IrType::UInt8, IrType::Object),
        ("flagBool", IrType::UInt8, IrType::UInt8),
        ("stringNat", IrType::Object, IrType::TObject),
        ("stringText", IrType::Object, IrType::Object),
        ("stringBool", IrType::Object, IrType::UInt8),
    ] {
        let entry = name(label);
        let module = export(&engine, label)
            .unwrap_or_else(|error| panic!("{label}: {error:?}"))
            .into_complete()
            .unwrap();
        let Some(IrDecl::Function { params, result, .. }) =
            module.decls.iter().find(|decl| decl.name() == &entry)
        else {
            panic!("missing primitive recursive export {label}")
        };
        assert_eq!(params.len(), 1);
        assert_eq!(params[0].ty, parameter, "{label}");
        assert_eq!(*result, returned, "{label}");
        assert!(module.decls.iter().all(|decl| {
            !decl.name().to_display_string().contains("_unsafe_rec")
                && decl.name() != &Name::str(entry.clone(), "_redArg")
        }));
        assert_eq!(engine.environment(), &before);
    }
    // String-parameter examples deliberately do not terminate. Successful
    // compilation with zero VM fuel must never sample their runtime values.
    assert!(matches!(
        engine.environment().find(&name("textCount")),
        Some(ConstantInfo::Opaque(value)) if !value.is_unsafe
    ));
    let source = "theorem leakedText : textCount 0 = \"done\" := by rfl";
    assert!(
        engine
            .check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(EngineAdmissionLimits::new(execution_limits().kernel)),
            )
            .is_err(),
        "compilation exposed a partial implementation"
    );
    assert_eq!(engine.environment(), &before);
}

#[test]
fn recursive_source_uses_keep_checked_hidden_operator_models_and_metadata_guards() {
    use fln_env::constants::AxiomVal;
    let private = checked(
        r#"partial def hiddenAdd (n total : Nat) : Nat :=
  if n == 0 then total else hiddenAdd (n - 1) (total + 2)
partial def hiddenDrop (n ignored : Nat) : Nat :=
  if n == 0 then 7 else hiddenDrop (n - 1) (ignored + 0)
"#,
    );
    let hidden = name("Nat.add");
    let mut public = crate::Environment::new();
    for (label, declaration) in private.environment().constants() {
        public = if label == &hidden {
            assert!(matches!(declaration, ConstantInfo::Defn(_)));
            public
                .add_decl(ConstantInfo::Axiom(AxiomVal {
                    base: declaration.constant_val().clone(),
                    is_unsafe: false,
                }))
                .unwrap()
        } else {
            public
                .with_entry(private.environment().entry(label).unwrap())
                .unwrap()
        };
    }
    for (journal, state) in private.environment().extensions() {
        public = public.register_extension(state.descriptor.clone()).unwrap();
        for entry in state.entries() {
            public = public
                .push_extension_entry(journal, std::sync::Arc::clone(&entry.payload))
                .unwrap();
        }
    }
    public = public.with_imported_metadata_validation(private.environment());
    let engine = Engine::from_environment(public.clone())
        .with_checked_runtime_imports(public.clone(), &private);
    let options = KVMap::new();
    let original = engine.logical_root(&options);
    for (label, reduced) in [("hiddenAdd", false), ("hiddenDrop", true)] {
        let module = export(&engine, label)
            .unwrap_or_else(|error| panic!("{label}: {error:?}"))
            .into_complete()
            .unwrap();
        assert_eq!(
            module
                .decls
                .iter()
                .any(|decl| decl.name() == &Name::str(name(label), "_redArg")),
            reduced
        );
        assert_eq!(engine.logical_root(&options), original);
    }
    assert!(matches!(
        engine.environment().find(&hidden),
        Some(ConstantInfo::Axiom(_))
    ));
    // A header alone never grants the complete operator contract, and a local
    // executable replacement must remain visible through the checked overlay.
    assert_unsupported(&Engine::from_environment(public.clone()), "hiddenAdd");
    let replaced = fln_elab::implemented_by::register(&public, &hidden, &name("Nat.sub")).unwrap();
    let replaced =
        Engine::from_environment(replaced).with_checked_runtime_imports(public.clone(), &private);
    assert_unsupported(&replaced, "hiddenAdd");
    let mut bounded = execution_limits();
    bounded.ingress.max_nodes = 0;
    assert!(matches!(
        compile_checked_source_definition(
            &engine,
            &name("hiddenAdd"),
            &options,
            bounded,
            CompileLimits::default(),
        ),
        Err(DefinitionCompileError::Engine(
            crate::EngineExecutionError::Ingress(IngressError::ResourceLimit { .. })
        ))
    ));
    assert_eq!(engine.logical_root(&options), original);
}

#[test]
fn source_recursion_exports_checked_enum_carriers_and_reduced_entries() {
    let engine = checked(ENUM_RECURSION);
    let before = engine.environment().clone();
    for (label, argument, returned, reduced) in [
        ("carryChoice", IrType::UInt8, IrType::UInt8, false),
        ("resetChoice", IrType::UInt8, IrType::UInt8, false),
        ("dropChoice", IrType::UInt8, IrType::TObject, true),
        ("dropSingle", IrType::Tagged, IrType::TObject, true),
    ] {
        let module = export(&engine, label)
            .unwrap_or_else(|error| panic!("{label}: {error:?}"))
            .into_complete()
            .unwrap();
        let entry = name(label);
        let Some(IrDecl::Function { params, result, .. }) =
            module.decls.iter().find(|decl| decl.name() == &entry)
        else {
            panic!("missing recursive enum export {label}")
        };
        assert_eq!(
            params
                .iter()
                .map(|param| param.ty.clone())
                .collect::<Vec<_>>(),
            [IrType::TObject, argument],
            "{label}"
        );
        assert_eq!(*result, returned, "{label}");
        assert!(params.iter().all(|param| !param.borrow), "{label}");
        assert_eq!(
            module
                .decls
                .iter()
                .any(|decl| decl.name() == &Name::str(entry.clone(), "_boxed")),
            label != "dropSingle",
            "source boxing for {label}"
        );
        let helper = Name::str(entry, "_redArg");
        let actual = module.decls.iter().find_map(|decl| match decl {
            IrDecl::Function {
                name,
                params,
                result,
                ..
            } if name == &helper => Some((
                params
                    .iter()
                    .map(|param| param.ty.clone())
                    .collect::<Vec<_>>(),
                result.clone(),
            )),
            _ => None,
        });
        assert_eq!(
            actual,
            reduced.then(|| (vec![IrType::TObject], IrType::TObject)),
            "{label}"
        );
        assert!(
            module
                .decls
                .iter()
                .all(|decl| { decl.name() != &Name::str(helper.clone(), "_boxed") })
        );
        assert!(
            module
                .decls
                .iter()
                .all(|decl| { !decl.name().to_display_string().contains("_unsafe_rec") })
        );
        assert_eq!(engine.environment(), &before);
    }
}

#[test]
fn recursive_enum_exports_refuse_payloads_and_constructor_replacements() {
    use fln_elab::externs::ExternEntry;
    let engine = checked(&format!(
        "{ENUM_RECURSION}\
         inductive Payload where | wrap (n : Nat)\n\
         partial def carryPayload (n : Nat) (value : Payload) : Payload :=\n\
           if n == 0 then value else carryPayload (n - 1) value\n\
         inductive BoxedPayload where | empty | value (n : Nat)\n\
         def identityBoxed (value : BoxedPayload) : BoxedPayload := value\n\
         partial def carryBoxed (n : Nat) (value : BoxedPayload) : BoxedPayload :=\n\
           if n == 0 then value else carryBoxed (n - 1) value\n\
         def replacement : Choice := Choice.first\n"
    ));
    let before = engine.environment().clone();
    assert_unsupported(&engine, "carryPayload");
    // This layout is supported by ordinary exports. It must not enter through
    // the recursive enum path just because both use the shared data projection.
    assert!(
        export(&engine, "identityBoxed")
            .unwrap()
            .into_complete()
            .is_ok()
    );
    assert_unsupported(&engine, "carryBoxed");
    let constructor = name("Choice.third");
    let external = fln_elab::externs::register(
        engine.environment(),
        &constructor,
        vec![ExternEntry::Standard {
            backend: Name::anonymous(),
            symbol: "unbound_enum_constructor".into(),
        }],
    )
    .unwrap();
    assert_unsupported(&Engine::from_environment(external), "resetChoice");
    let replacement = fln_elab::implemented_by::register(
        engine.environment(),
        &constructor,
        &name("replacement"),
    )
    .unwrap();
    assert_unsupported(&Engine::from_environment(replacement), "resetChoice");
    assert_eq!(engine.environment(), &before);
    assert!(
        export(&engine, "resetChoice")
            .unwrap()
            .into_complete()
            .is_ok()
    );
}

#[test]
fn source_recursion_refuses_unsafe_entries_and_unverified_companions() {
    let engine = checked(&format!(
        "{COUNT}\
         unsafe def unsafeEntry (n : Nat) : Nat := n\n\
         def counterfeit (n : Nat) : Nat := n\n\
         def counterfeit._unsafe_rec (n : Nat) : Nat := n\n\
         opaque opaqueCounterfeit : Nat -> Nat := fun n => n\n\
         def opaqueCounterfeit._unsafe_rec (n : Nat) : Nat := n\n"
    ));
    for entry in [
        "count._unsafe_rec",
        "unsafeEntry",
        "counterfeit",
        "opaqueCounterfeit",
    ] {
        assert_unsupported(&engine, entry);
    }
    assert!(
        is_checked_recursive_companion(
            &engine,
            &name("counterfeit._unsafe_rec"),
            execution_limits(),
            CompileLimits::default(),
        )
        .is_err()
    );
}

#[test]
fn source_recursion_preserves_multiargument_and_reduced_abis_without_evaluation() {
    let engine = checked(
        r#"partial def accumulator (n total : Nat) : Nat :=
  if n == 0 then total else accumulator (n - 1) (total + 2)
partial def dropSecond (n ignored : Nat) : Nat :=
  if n == 0 then 7 else dropSecond (n - 1) ignored
partial def swap (n left right : Nat) : Nat :=
  if n == 0 then left else swap (n - 1) right left
partial def flags (n : Nat) (value ignored : Bool) : Bool :=
  if n == 0 then value else flags (n - 1) value ignored
partial def identityArg (n ignored : Nat) : Nat :=
  if n == 0 then 7 else identityArg (n - 1) (ignored + 0)
partial def changedArg (n ignored : Nat) : Nat :=
  if n == 0 then 7 else changedArg (n - 1) (ignored + 2)
partial def erasedProduct (n ignored : Nat) : Nat :=
  if n == 0 then 7 else erasedProduct (n - 1) (ignored * 0)
partial def subSelf (n ignored : Nat) : Nat :=
  if n == 0 then 7 else subSelf (n - 1) (ignored - ignored)
partial def eqSelf (n ignored : Nat) : Nat :=
  if ignored == ignored then n else eqSelf n ignored
partial def leSelf (n ignored : Nat) : Nat :=
  if Nat.ble ignored ignored then n else leSelf n ignored
partial def branchFact (n : Nat) (b : Bool) : Nat :=
  if (if b then b else true) then n else branchFact n b
partial def identityBool (n : Nat) (b : Bool) : Nat :=
  if n == 0 then 7 else identityBool (n - 1) (if b then true else b)
partial def spinBoth (a b : Nat) : Nat := spinBoth a b
"#,
    );
    let before = engine.environment().clone();
    // These masks match the pinned compiler's reduceArity pass. In particular,
    // changed/permuted recursive arguments count, unchanged same-slot arguments
    // do not, and the pin preserves the telescope when no parameters are used.
    for (label, arity, reduced, borrowed, boxed, reduced_boxed) in [
        ("accumulator", 2, None, &[][..], false, false),
        ("dropSecond", 2, Some(1), &[1][..], true, false),
        ("swap", 3, None, &[1, 2][..], true, false),
        ("flags", 3, Some(2), &[][..], true, true),
        ("identityArg", 2, Some(1), &[1][..], true, false),
        ("changedArg", 2, None, &[][..], false, false),
        ("erasedProduct", 2, Some(1), &[1][..], true, false),
        ("subSelf", 2, None, &[][..], false, false),
        ("eqSelf", 2, None, &[0, 1][..], true, false),
        ("leSelf", 2, None, &[0, 1][..], true, false),
        ("branchFact", 2, Some(1), &[0][..], true, true),
        ("identityBool", 2, Some(1), &[][..], true, false),
        ("spinBoth", 2, None, &[0, 1][..], true, false),
    ] {
        let entry = name(label);
        let module = export(&engine, label)
            .unwrap_or_else(|error| panic!("{label}: {error:?}"))
            .into_complete()
            .unwrap();
        let Some(IrDecl::Function {
            params,
            result,
            body,
            ..
        }) = module.decls.iter().find(|decl| decl.name() == &entry)
        else {
            panic!("missing recursive exported function {label}")
        };
        assert_eq!(params.len(), arity, "{label}");
        assert_eq!(
            params
                .iter()
                .enumerate()
                .filter_map(|(index, param)| param.borrow.then_some(index))
                .collect::<Vec<_>>(),
            borrowed,
            "borrowed source ABI for {label}"
        );
        for &index in borrowed {
            assert!(
                body.stmts.iter().any(|statement| matches!(
                    statement,
                    IrStmt::Inc { x, n: 1, checked: true, persistent: false }
                        if *x == params[index].x
                )),
                "borrowed closure operand needs an owned donation: {label}"
            );
        }
        let boxed_entry = Name::str(entry.clone(), "_boxed");
        assert_eq!(
            module.decls.iter().any(|decl| decl.name() == &boxed_entry),
            boxed,
            "boxed source ABI for {label}"
        );
        if boxed {
            let Some(IrDecl::Function { body, .. }) =
                module.decls.iter().find(|decl| decl.name() == &boxed_entry)
            else {
                panic!("missing boxed source entry")
            };
            for &index in borrowed {
                assert!(
                    body.stmts.iter().any(|statement| matches!(
                        statement,
                        IrStmt::Dec { x, n: 1, checked: true, persistent: false }
                            if *x == params[index].x
                    )),
                    "boxed entry must release the owner's borrow: {label}"
                );
            }
        }
        assert_eq!(
            *result,
            if label == "flags" {
                IrType::UInt8
            } else {
                IrType::TObject
            },
            "{label}"
        );
        let helper = Name::str(entry.clone(), "_redArg");
        let actual = module.decls.iter().find_map(|decl| match decl {
            IrDecl::Function { name, params, .. } if name == &helper => Some(params.len()),
            _ => None,
        });
        assert_eq!(actual, reduced, "{label}");
        assert_eq!(
            module
                .decls
                .iter()
                .any(|decl| decl.name() == &Name::str(helper.clone(), "_boxed")),
            reduced_boxed,
            "boxed reduced ABI for {label}"
        );
        assert!(
            module
                .decls
                .iter()
                .all(|decl| { !decl.name().to_display_string().contains("_unsafe_rec") })
        );
        assert!(matches!(
            engine.environment().find(&entry),
            Some(ConstantInfo::Opaque(value)) if !value.is_unsafe
        ));
        assert_eq!(engine.environment(), &before);
    }
}

#[test]
fn recursive_ownership_distinguishes_tail_calls_and_reaches_a_fixed_point() {
    let engine = checked(
        r#"partial def spreadOwnership (n left right : Nat) : Nat :=
  if n == 0 then left else spreadOwnership (n - 1) right (left + 2)
partial def nestedCall (n value : Nat) : Nat :=
  if n == 0 then value else nestedCall (n - 1) value + 2
partial def consumingText (n : Nat) (left right : String) : String :=
  if n == 0 then left else consumingText (n - 1) (left ++ right) right
partial def persistentText (n : Nat) (text : String) : String :=
  if n == 0 then text else persistentText (n - 1) ("prefix" ++ text)
"#,
    );
    let before = engine.environment().clone();
    for (label, borrowed, boxed) in [
        ("spreadOwnership", &[][..], false),
        ("nestedCall", &[0, 1][..], true),
        ("consumingText", &[2][..], true),
        // The normalized DAG cannot prove whether a consumed literal shares
        // its binding with another occurrence. Keep the prior owned adapter.
        ("persistentText", &[][..], true),
    ] {
        let module = export(&engine, label)
            .unwrap_or_else(|error| panic!("{label}: {error:?}"))
            .into_complete()
            .unwrap();
        let entry = name(label);
        let Some(IrDecl::Function { params, .. }) =
            module.decls.iter().find(|decl| decl.name() == &entry)
        else {
            panic!("missing recursive ownership entry")
        };
        assert_eq!(
            params
                .iter()
                .enumerate()
                .filter_map(|(index, param)| param.borrow.then_some(index))
                .collect::<Vec<_>>(),
            borrowed,
            "{label}"
        );
        assert_eq!(
            module
                .decls
                .iter()
                .any(|decl| decl.name() == &Name::str(entry.clone(), "_boxed")),
            boxed,
            "{label}"
        );
        assert_eq!(engine.environment(), &before);
    }
}

#[test]
fn source_recursion_refuses_unproved_public_signatures_and_mutual_groups() {
    let engine = checked(
        r#"partial def higherOrder (f : Nat -> Nat) (n : Nat) : Nat :=
  higherOrder f n
partial def generic (A : Type) (a : A) : A := generic A a
partial def unknownOperation (n ignored : Nat) : Nat :=
  if n == 0 then 7 else unknownOperation (n - 1) (ignored % 2)
partial def recursiveInitializer (n ignored : Nat) : Nat :=
  let x := recursiveInitializer n ignored
  n
partial def conditionalArgument (n : Nat) (b : Bool) : Nat :=
  conditionalArgument n (if b then false else true)
partial def conditionalRecursion (n : Nat) (b : Bool) : Nat :=
  if b then conditionalRecursion n false else n
partial def sharedDiscriminator (n ignored : Nat) : Nat :=
  if n == 0 then (if n == 0 then ignored else 7) else sharedDiscriminator n ignored
partial def literalBeq (n x : Nat) : Nat :=
  if Nat.beq 0 0 then n else literalBeq x n
partial def literalBle (n x : Nat) : Nat :=
  if Nat.ble 0 0 then n else literalBle x n
partial def literalDictionary (n x : Nat) : Nat :=
  if 0 == 0 then n else literalDictionary x n
mutual
  partial def first (n : Nat) : Nat := second n
  partial def second (n : Nat) : Nat := first n
end
"#,
    );
    for entry in [
        "higherOrder",
        "generic",
        "unknownOperation",
        "recursiveInitializer",
        "conditionalArgument",
        "conditionalRecursion",
        "sharedDiscriminator",
        "literalBeq",
        "literalBle",
        "literalDictionary",
        "first",
        "second",
    ] {
        assert_unsupported(&engine, entry);
    }
}

#[test]
fn source_recursion_refuses_executable_metadata_on_either_half() {
    use fln_elab::externs::ExternEntry;
    let engine = checked(&format!("{COUNT}def replacement (n : Nat) : Nat := n\n"));
    for target in [name("count"), name("count._unsafe_rec")] {
        let extern_environment = fln_elab::externs::register(
            engine.environment(),
            &target,
            vec![ExternEntry::Standard {
                backend: Name::anonymous(),
                symbol: "unbound_recursive_export".into(),
            }],
        )
        .unwrap();
        assert_unsupported(&Engine::from_environment(extern_environment), "count");

        let replacement_environment =
            fln_elab::implemented_by::register(engine.environment(), &target, &name("replacement"))
                .unwrap();
        assert_unsupported(&Engine::from_environment(replacement_environment), "count");

        let noncomputable_environment =
            fln_elab::noncomputable::register(engine.environment(), &target).unwrap();
        assert_unsupported(
            &Engine::from_environment(noncomputable_environment),
            "count",
        );
    }
}

#[test]
fn source_recursion_refuses_initialized_globals_before_any_stored_body() {
    let engine = checked(&format!("{COUNT}opaque initialized : Nat := 42\n"));
    for target in [
        name("count"),
        name("count._unsafe_rec"),
        name("initialized"),
    ] {
        let mut changed = engine.clone();
        std::sync::Arc::make_mut(&mut changed.runtime_initializers).insert(target.clone());
        let entry = if target == name("initialized") {
            "initialized"
        } else {
            "count"
        };
        assert_unsupported(&changed, entry);
    }
}

#[test]
fn source_recursion_linkage_exhaustion_remains_a_resource_nonanswer() {
    let engine = checked(COUNT);
    let before = engine.environment().clone();
    let mut execution = execution_limits();
    execution.ingress.fir.max_functions = 0;
    let error = compile_checked_source_definition(
        &engine,
        &name("count"),
        &KVMap::new(),
        execution,
        CompileLimits::default(),
    )
    .unwrap_err();
    assert!(
        matches!(
            error,
            DefinitionCompileError::Engine(crate::EngineExecutionError::Ingress(
                IngressError::ResourceLimit {
                    resource: IngressResource::ProgramTables,
                    limit: 0,
                    observed: 1,
                }
            ))
        ),
        "{error:?}"
    );
    assert_eq!(engine.environment(), &before);
}
