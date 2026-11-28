//! Omitted opaque values use the pin's ordered, checked inhabitant search.
//! Runtime replacements never expose the logical body or authorize a witness.
#![forbid(unsafe_code)]

use fln::{
    Budget, ConstantInfo, Engine, EngineAdmissionLimits, EngineExecutionLimits, Expr, KVMap, Name,
    SourceCheckLimits, VmExit,
};
use fln_core::expr::ExprNode;
use std::collections::BTreeSet;

// These are the actual logical declarations from Init/Prelude. The source seed
// supplies Inhabited, but deliberately does not preinstall classical choice.
const FOUNDATION: &str = r#"universe u
class inductive Nonempty (A : Sort u) : Prop where
  | intro (value : A) : Nonempty A
axiom Classical.choice {A : Sort u} : Nonempty A -> A
noncomputable def Classical.ofNonempty {A : Sort u} [witness : Nonempty A] : A :=
  Classical.choice witness
"#;

const TOKEN: &str = r#"structure WitnessToken where
  value : Nat
instance tokenNonempty : Nonempty WitnessToken := Nonempty.intro (WitnessToken.mk 7)
"#;

fn n(text: &str) -> Name {
    Name::from_components(text.split('.'))
}

fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 << 20))
}

fn checked(base: &Engine, source: &str) -> Engine {
    base.check_source_files(
        &[source.as_bytes()],
        &KVMap::new(),
        SourceCheckLimits::new(limits()),
    )
    .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
    .into_complete()
    .unwrap()
    .engine
}

fn seed() -> Engine {
    let base = Engine::with_source_seed(limits())
        .unwrap()
        .into_complete()
        .unwrap();
    assert!(!base.environment().contains(&n("Nonempty")));
    checked(&checked(&base, FOUNDATION), TOKEN)
}

fn on_stack(body: impl FnOnce() + Send) {
    std::thread::scope(|scope| {
        std::thread::Builder::new()
            .stack_size(16 << 20)
            .spawn_scoped(scope, body)
            .unwrap()
            .join()
            .unwrap();
    });
}

fn constants(expression: &Expr) -> BTreeSet<Name> {
    let mut pending = vec![expression];
    let mut result = BTreeSet::new();
    while let Some(expression) = pending.pop() {
        match expression.node() {
            ExprNode::Const { name, .. } => {
                result.insert(name.clone());
            }
            ExprNode::App { f, a } => pending.extend([f, a]),
            ExprNode::Lam {
                binder_type, body, ..
            }
            | ExprNode::ForallE {
                binder_type, body, ..
            } => pending.extend([binder_type, body]),
            ExprNode::LetE {
                type_, value, body, ..
            } => pending.extend([type_, value, body]),
            ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => pending.push(expr),
            _ => {}
        }
    }
    result
}

fn opaque_body<'a>(engine: &'a Engine, declaration: &str) -> &'a Expr {
    let Some(ConstantInfo::Opaque(value)) = engine.environment().find(&n(declaration)) else {
        panic!("missing opaque {declaration}");
    };
    assert!(!value.is_unsafe);
    &value.value
}

fn execute(engine: &Engine, source: &str, expected: &[&str]) {
    let before = engine.logical_root(&KVMap::new());
    let executed = engine
        .execute_source_definitions(
            &[source.as_bytes()],
            &KVMap::new(),
            EngineExecutionLimits::new(limits().kernel),
        )
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .unwrap();
    let values: Vec<_> = executed
        .executions
        .iter()
        .map(|execution| {
            let VmExit::Returned(value) = &execution.exit else {
                panic!("unexpected opaque execution: {:?}", execution.exit);
            };
            fln::nat_decimal(&value.value).unwrap()
        })
        .collect();
    assert_eq!(values, expected);
    assert_eq!(engine.logical_root(&KVMap::new()), before);
}

fn refused(base: &Engine, source: &str) -> String {
    let before = base.logical_root(&KVMap::new());
    let error = base
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        )
        .expect_err(source);
    assert_ne!(
        error.disposition().0,
        "internal-fault",
        "{source}\n{error:?}"
    );
    assert_eq!(base.logical_root(&KVMap::new()), before);
    format!("{error:?}")
}

#[test]
fn nonempty_opaque_executes_its_checked_replacement_without_exposing_its_body() {
    on_stack(|| {
        let base = seed();
        let before = base.logical_root(&KVMap::new());
        let engine = checked(
            &base,
            "unsafe def makeImp (_ : Nat) : WitnessToken := WitnessToken.mk 9\n\
             @[implemented_by makeImp] opaque make (_ : Nat) : WitnessToken\n",
        );
        let body = constants(opaque_body(&engine, "make"));
        assert!(body.contains(&n("Classical.ofNonempty")));
        assert!(body.contains(&n("tokenNonempty")));
        assert!(!body.contains(&n("Inhabited.default")));
        assert!(!body.contains(&n("makeImp")));
        assert_eq!(
            fln_elab::implemented_by::ImplementedByTable::read(engine.environment())
                .unwrap()
                .get(&n("make")),
            Some(&n("makeImp"))
        );
        execute(&engine, "#eval (make 0).value\n", &["9"]);
        refused(
            &engine,
            "theorem revealOpaque : (make 0).value = 9 := by rfl\n",
        );
        assert_eq!(base.logical_root(&KVMap::new()), before);
        assert!(!base.environment().contains(&n("make")));
    });
}

#[test]
fn inhabited_precedes_nonempty_and_lexical_default_names_cannot_redirect_it() {
    on_stack(|| {
        let engine = checked(
            &seed(),
            "instance tokenInhabited : Inhabited WitnessToken where\n  default := WitnessToken.mk 11\n\
             opaque preferred : WitnessToken\n\
             namespace Shadow\n\
             def default : Nat := 77\n\
             opaque selected : Nat\n\
             opaque localDefault (default : Nat) : Nat\n\
             end Shadow\n",
        );
        for declaration in ["preferred", "Shadow.selected", "Shadow.localDefault"] {
            let body = constants(opaque_body(&engine, declaration));
            assert!(body.contains(&n("Inhabited.default")), "{declaration}");
            assert!(!body.contains(&n("Classical.ofNonempty")), "{declaration}");
            assert!(!body.contains(&n("Shadow.default")), "{declaration}");
        }
        execute(
            &engine,
            "#eval preferred.value\n#eval Shadow.selected\n#eval Shadow.localDefault 99\n",
            &["11", "0", "0"],
        );
    });
}

#[test]
fn nonempty_witnesses_preserve_polymorphic_headers_and_whole_function_results() {
    on_stack(|| {
        let engine = checked(
            &seed(),
            "noncomputable opaque logical : WitnessToken\n\
             noncomputable opaque generic.{u} {A : Sort u} [Nonempty A] : A\n\
             noncomputable opaque inferred {A} [Nonempty A] : A\n\
             abbrev Callback := Nat -> WitnessToken\n\
             instance callbackNonempty : Nonempty Callback := Nonempty.intro (fun _ => WitnessToken.mk 13)\n\
             noncomputable opaque callback : Callback\n\
             namespace Shadow\n\
             def Classical.ofNonempty : Nat := 23\n\
             noncomputable opaque logical : WitnessToken\n\
             end Shadow\n\
             @[extern \"franken_lean_opaque_witness_test\"] opaque external : WitnessToken\n\
             inductive Claim : Prop where | intro\n\
             instance claimNonempty : Nonempty Claim := Nonempty.intro Claim.intro\n\
             opaque proof : Claim\n",
        );
        for declaration in [
            "logical",
            "generic",
            "inferred",
            "callback",
            "Shadow.logical",
            "external",
            "proof",
        ] {
            let body = constants(opaque_body(&engine, declaration));
            assert!(body.contains(&n("Classical.ofNonempty")), "{declaration}");
            assert!(!body.contains(&n("Shadow.Classical.ofNonempty")));
        }
        assert!(constants(opaque_body(&engine, "callback")).contains(&n("callbackNonempty")));
        let generic = engine.environment().find(&n("generic")).unwrap();
        assert_eq!(generic.constant_val().level_params, [n("u")]);
        assert_eq!(
            engine
                .environment()
                .find(&n("inferred"))
                .unwrap()
                .constant_val()
                .level_params
                .len(),
            1
        );
        let tags = fln_elab::noncomputable::read(engine.environment()).unwrap();
        for declaration in [
            "logical",
            "generic",
            "inferred",
            "callback",
            "Shadow.logical",
        ] {
            assert!(tags.contains(&n(declaration)), "{declaration}");
        }
        assert!(!tags.contains(&n("external")));
        assert!(!tags.contains(&n("proof")));
        refused(&engine, "def forbiddenRuntime : WitnessToken := logical\n");
    });
}

#[test]
fn missing_witnesses_and_invalid_replacements_refuse_without_publishing() {
    on_stack(|| {
        let base = seed();
        for declaration in [
            "opaque denied : WitnessToken",
            "unsafe opaque denied : WitnessToken",
        ] {
            let error = refused(&base, &format!("{declaration}\n"));
            assert!(error.contains("NoncomputableDependency"), "{error}");
            assert!(error.contains("ofNonempty"), "{error}");
        }
        for source in [
            // An ordinary parameter is not a partial-definition-style provider.
            "noncomputable opaque denied {A : Type} (value : A) : A\n",
            "inductive Witnessless where\n@[extern \"franken_lean_missing_witness\"] opaque denied : Witnessless\n",
            "unsafe def wrong (_ : Nat) : Nat := 0\n@[implemented_by wrong] opaque denied (_ : Nat) : WitnessToken\n",
            // The pin's unsafe no-witness sorry fallback is a separate, unsupported profile.
            "inductive Witnessless where\nunsafe opaque denied : Witnessless\n",
        ] {
            refused(&base, source);
            for declaration in ["denied", "wrong", "Witnessless"] {
                assert!(!base.environment().contains(&n(declaration)), "{source}");
            }
        }
        // A refused search must not alter the next independent declaration.
        let recovered = checked(&base, "opaque retry : Nat\n");
        execute(&recovered, "#eval retry\n", &["0"]);
    });
}
