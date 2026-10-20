//! Real source programs exercise the semantic effects of successful lowering
//! through every public admission/execution door and cached module replay.
#![forbid(unsafe_code)]
use fln::source_check::modules::{
    SourceModuleCacheLimits, SourceModuleCheckLimits, SourceModuleSession,
};
use fln::{
    ClosedVmValue, Engine, EngineExecutionLimits, KVMap, SourceCheckLimits, SourceModuleInput,
};
use fln_elab::reducibility::{Reducibility, table};

use super::{limits, n};

fn countdown(name: &str) -> String {
    format!(
        "def {name} (n : Nat) : Nat :=\n  if h : 0 < n then {name} (n - 1) + 1 else 0\ntermination_by n\ndecreasing_by exact @Nat.sub_lt n 1 h (Nat.succ_pos 0)"
    )
}

fn assert_computes_but_does_not_unfold(engine: &Engine, name: &str) {
    assert_eq!(
        table(engine.environment()).unwrap().status(&n(name)),
        Reducibility::Irreducible,
        "successful well-founded lowering marks {name} irreducible"
    );
    let source = format!("def opacityAnswer : Nat := {name} 42");
    let result = engine
        .execute_source_definition(
            source.as_bytes(),
            &KVMap::new(),
            EngineExecutionLimits::new(limits().kernel),
        )
        .expect("irreducibility does not block native execution")
        .into_complete()
        .expect("native execution finishes");
    assert_eq!(
        fln::closed_vm_value(&result.exit).unwrap(),
        Some(ClosedVmValue::Scalar(42))
    );
    let root = engine.logical_root(&KVMap::new());
    let proof = format!("theorem forbiddenUnfold : {name} 42 = 42 := by rfl");
    assert!(
        engine
            .admit_source_declaration(proof.as_bytes(), &KVMap::new(), limits())
            .is_err(),
        "ordinary source conversion must respect {name}'s opacity"
    );
    assert_eq!(engine.logical_root(&KVMap::new()), root);
}

pub fn assert_source_opacity_routes(base: &Engine) {
    let options = KVMap::new();
    let base_root = base.logical_root(&options);
    let admitted = base
        .admit_source_declaration(
            countdown("admittedCountdown").as_bytes(),
            &options,
            limits(),
        )
        .expect("standalone source admission lowers well-founded recursion")
        .into_complete()
        .expect("standalone admission finishes");
    assert_eq!(admitted.base_logical_root, base_root);
    assert_eq!(
        admitted.result_logical_root,
        admitted.engine.logical_root(&options)
    );
    assert_computes_but_does_not_unfold(&admitted.engine, "admittedCountdown");

    let source = format!("namespace Scoped\n{}\nend Scoped", countdown("countdown"));
    let checked = base
        .check_source_files(
            &[source.as_bytes()],
            &options,
            SourceCheckLimits::new(limits()),
        )
        .expect("scoped source checking carries the lowering effect")
        .into_complete()
        .expect("scoped checking finishes");
    assert_eq!(
        checked.result_logical_root,
        checked.engine.logical_root(&options)
    );
    assert_computes_but_does_not_unfold(&checked.engine, "Scoped.countdown");

    let streamed = base
        .execute_source_definitions(
            &[countdown("streamedCountdown").as_bytes()],
            &options,
            EngineExecutionLimits::new(limits().kernel),
        )
        .expect("the command stream publishes the checked function template")
        .into_complete()
        .expect("the stream finishes");
    assert_eq!(
        streamed.result_logical_root,
        streamed.engine.logical_root(&options)
    );
    assert_computes_but_does_not_unfold(&streamed.engine, "streamedCountdown");

    let executed = base
        .execute_source_definition(
            countdown("executedCountdown").as_bytes(),
            &options,
            EngineExecutionLimits::new(limits().kernel),
        )
        .expect("the standalone execution door retains the effect on its closure")
        .into_complete()
        .expect("the function value executes");
    assert_eq!(
        executed.result_logical_root,
        executed.engine.logical_root(&options)
    );
    assert_computes_but_does_not_unfold(&executed.engine, "executedCountdown");

    // A body mentioning the fixed-point operator is not evidence that the
    // source elaborator performed recursive-definition lowering.
    let ordinary = base
        .check_source_files(
            &[b"def explicitFix (n : Nat) : Nat := @WellFounded.Nat.fix Nat (fun _ => Nat) (fun x : Nat => x) (fun k _ => k) n"],
            &options,
            SourceCheckLimits::new(limits()),
        )
        .expect("an explicit checked fix application is an ordinary definition")
        .into_complete()
        .expect("ordinary checking finishes");
    assert_eq!(
        table(ordinary.engine.environment())
            .unwrap()
            .status(&n("explicitFix")),
        Reducibility::Semireducible
    );

    // Inferring the implicit subtrahend from the result used to unfold
    // Nat.sub too early, leaving `by decide` with the unsolved goal 0 < ?m.
    base.admit_source_declaration(
        b"theorem inferDecrease (n : Nat) (h : 0 < n) : n - 1 < n := Nat.sub_lt h (by decide)",
        &options,
        limits(),
    )
    .expect("same-definition argument congruence determines the implicit measure")
    .into_complete()
    .expect("the inferred proof passes both checkers");

    let module_name = n("CountdownLibrary");
    let entry = n("CountdownClient");
    let library = format!(
        "prelude\nimport Init.WFTactics\n{}",
        countdown("libraryCountdown")
    );
    let modules = [
        SourceModuleInput {
            name: &module_name,
            source: library.as_bytes(),
        },
        SourceModuleInput {
            name: &entry,
            source:
                b"prelude\nimport CountdownLibrary\ndef libraryAnswer : Nat := libraryCountdown 42",
        },
    ];
    let mut session = SourceModuleSession::new(
        base.clone(),
        options.clone(),
        SourceModuleCheckLimits::new(SourceCheckLimits::new(limits())),
        SourceModuleCacheLimits::default(),
    );
    let cold = session
        .check(&modules, &entry)
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!((cold.reused_modules, cold.elaborated_modules), (0, 2));
    assert!(cold.checked.replayed_declarations > 0);
    assert_computes_but_does_not_unfold(&cold.checked.checked.engine, "libraryCountdown");
    let warm = session
        .check(&modules, &entry)
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!((warm.reused_modules, warm.elaborated_modules), (2, 0));
    assert_eq!(
        warm.checked.checked.result_logical_root,
        cold.checked.checked.result_logical_root
    );
    assert_computes_but_does_not_unfold(&warm.checked.checked.engine, "libraryCountdown");
    assert_eq!(base.logical_root(&options), base_root);
}
