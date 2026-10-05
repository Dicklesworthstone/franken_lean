//! The pin's discrimination tree narrows instance candidates (bead `fln-52qv`),
//! over pinned closures admitted by the council with their instance journals
//! activated.
//!
//! Two claims. The narrowed list for a goal is the pin's own: the expected
//! lists come from the pinned `lean` with `prelude`, the same import, and
//! `set_option trace.Meta.synthInstance.instances true`. And the filter loses no
//! candidate: with every imported instance's own type as a goal, each global
//! candidate the search's selection step applies is one the tree admits, apart
//! from an exact, pin-traced set the pin's own tree never offers.
#![forbid(unsafe_code)]
use fln::source_check::modules::imported::SourceOleanImportLimits;
use fln::{
    BinderInfo, Budget, Engine, EngineAdmissionLimits, Environment, Expr, KVMap, Level, Literal,
    Name, NatLit, OleanCheckLimits, OleanDecodeLimits, OleanModuleInput, Outcome,
    SourceCheckLimits, olean_module_imports,
};
use fln_elab::source::inspect::{Selection, audit_instance_goal};
use std::collections::BTreeSet;
use std::path::{Path, PathBuf};

const STACK: usize = 256 * 1024 * 1024;

fn n(text: &str) -> Name {
    Name::from_components(text.split('.'))
}

fn pinned_lib() -> Option<PathBuf> {
    let lib = std::env::var_os("FLN_REFERENCE_LIB")
        .map(PathBuf::from)
        .or_else(|| {
            std::env::var_os("HOME").map(|home| {
                PathBuf::from(home).join(".elan/toolchains/leanprover--lean4---v4.32.0/lib/lean")
            })
        })
        .filter(|lib| lib.is_dir());
    assert!(
        lib.is_some() || std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
        "FLN_REQUIRE_REFERENCE is set but the pinned Reference lib/lean is absent"
    );
    lib
}

/// `root` and its import closure, admitted through the council with their
/// instance journals activated.
fn import_closure(lib: &Path, root: &str) -> Engine {
    let mut pending = vec![n(root)];
    let mut seen = BTreeSet::new();
    let mut names = Vec::new();
    let mut parts = Vec::new();
    while let Some(module) = pending.pop() {
        if !seen.insert(module.clone()) {
            continue;
        }
        let base = module
            .to_display_string()
            .split('.')
            .fold(lib.to_path_buf(), |path, part| path.join(part))
            .with_extension("olean");
        let read = |path: PathBuf| std::fs::read(&path).expect("pinned olean part");
        let exported = read(base.clone());
        pending.extend(
            olean_module_imports(&exported, OleanDecodeLimits::new(exported.len()))
                .expect("pinned imports"),
        );
        parts.push([
            exported,
            read(base.with_extension("olean.server")),
            read(base.with_extension("olean.private")),
        ]);
        names.push(module);
    }
    let inputs: Vec<OleanModuleInput<'_>> = names
        .iter()
        .zip(&parts)
        .map(|(name, [exported, server, private])| OleanModuleInput {
            name,
            artifact: exported,
            server_artifact: Some(server),
            private_artifact: Some(private),
        })
        .collect();
    let limits = SourceOleanImportLimits::new(OleanCheckLimits::new(
        256 * 1024 * 1024,
        Budget::for_stack_bytes(STACK),
    ));
    match Engine::from_environment(Environment::new()).import_olean_modules_for_source(
        &inputs,
        &[n(root)],
        &KVMap::new(),
        limits,
    ) {
        Ok(Outcome::Complete(imported)) => imported.engine,
        other => panic!("the pinned closure passes the council: {other:?}"),
    }
}

fn on_stack(body: impl FnOnce() + Send + 'static) {
    std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(body)
        .expect("spawn the checking thread")
        .join()
        .expect("the checking thread completes");
}

fn constant(name: &str, levels: usize) -> Expr {
    Expr::const_(n(name), vec![Level::zero(); levels])
}

/// `∀ n : Nat, Decidable (op n 5)` for `op` one of `LT.lt` and `GT.gt`.
fn comparison_goal(op: &str) -> Expr {
    let five = Expr::lit(Literal::Nat(NatLit::from_u64(5)));
    let numeral = [
        constant("Nat", 0),
        five.clone(),
        Expr::app(constant("instOfNatNat", 0), five),
    ]
    .into_iter()
    .fold(constant("OfNat.ofNat", 1), Expr::app);
    let comparison = [
        constant("Nat", 0),
        constant("instLTNat", 0),
        Expr::bvar(0).unwrap(),
        numeral,
    ]
    .into_iter()
    .fold(constant(op, 1), Expr::app);
    Expr::forall_e(
        n("n"),
        constant("Nat", 0),
        Expr::app(constant("Decidable", 0), comparison),
        BinderInfo::Default,
    )
}

/// The admitted global candidates for `goal`, and how many there were.
fn admitted(env: &Environment, goal: &Expr) -> (BTreeSet<String>, usize) {
    let audit = audit_instance_goal(env, goal, Budget::for_stack_bytes(STACK))
        .expect("the goal is audited")
        .expect("the search starts on the goal");
    let names = audit
        .candidates
        .iter()
        .filter(|row| row.admitted)
        .map(|row| row.declaration.to_display_string())
        .collect();
    (names, audit.candidates.len())
}

/// Against `Init.Core`, the pin returns `Nat.decLt` alone for both `n < 5` and
/// `n > 5` (`GT.gt` is reducible, so the pin keys `5 < n`), out of every
/// `Decidable` instance in the closure. And `if n < 5` asks for that decision as
/// written: normalizing the condition first turned it into
/// `Nat.le (Nat.succ n) 5`, which no stored path matches, so the narrowed search
/// had nothing to try. The pin, with `prelude` and `import Init.Core`, accepts
/// the declaration. (`>` is not in the native grammar under this closure, so
/// only the `GT.gt` goal, not its source, is checked here.)
#[test]
fn decidable_comparisons_on_nat_narrow_to_the_pins_list_under_init_core() {
    let Some(lib) = pinned_lib() else {
        eprintln!("SKIP: pinned Reference lib/lean absent (set FLN_REQUIRE_REFERENCE=1 to fail)");
        return;
    };
    on_stack(move || {
        let engine = import_closure(&lib, "Init.Core");
        for op in ["LT.lt", "GT.gt"] {
            let (names, total) = admitted(engine.environment(), &comparison_goal(op));
            eprintln!(
                "Decidable ({op} n 5) under Init.Core: {total} candidates, admitted {names:?}"
            );
            assert_eq!(names, BTreeSet::from(["Nat.decLt".to_owned()]), "{op}");
            assert!(
                total > 30,
                "the class has its whole closure's instances: {total}"
            );
        }
        let limits =
            SourceCheckLimits::new(EngineAdmissionLimits::new(Budget::for_stack_bytes(STACK)));
        let source = "def f (n : Nat) : Nat := if n < 5 then n else 5";
        let checked = engine.check_source_files(&[source.as_bytes()], &KVMap::new(), limits);
        assert!(
            matches!(checked, Ok(Outcome::Complete(_))),
            "{source} must be admitted within the default budget: {checked:?}"
        );
    });
}

/// Goals whose applicable candidates the pin's own index never offers (bead
/// `fln-gkhu`). Selection runs at the `instances` transparency, where a `Nat` or
/// `BitVec` decision procedure unifies with an order goal on a wrapper type by
/// unfolding that type's `LE`/`LT` instance; the pin's tree keys the goal by the
/// wrapper type and never tries it.
///
/// Each row is the pin's own answer, measured on 2026-10-05 with the pinned
/// `lean`, `set_option trace.Meta.synthInstance true`, on `Decidable (a ≤ b)` or
/// `Decidable (a < b)` over `Fin 5`, `UInt32` and `BitVec 8`: `offers` is the
/// instance list that trace printed, and `never_offered` the candidates this
/// selection applies that the list leaves out. Both halves are checked: each
/// offered instance the closure holds must be kept, and the loss set must equal
/// the `never_offered` union exactly, so any other loss fails and so does one of
/// these becoming kept. A pin-extracted `getUnify` fixture for every goal is the
/// lasting form of this check; when it lands this table goes stale and leaves.
struct PinTracedGoal {
    goal: &'static str,
    offers: [&'static str; 3],
    never_offered: &'static [&'static str],
}

const PIN_TRACED_GOALS: [PinTracedGoal; 6] = [
    PinTracedGoal {
        goal: "Fin.decLe",
        offers: ["instDecidableRelLe", "Std.instDecidableLE", "Fin.decLe"],
        never_offered: &["Nat.decLe"],
    },
    PinTracedGoal {
        goal: "Fin.decLt",
        offers: ["instDecidableRelLt", "Std.instDecidableLT", "Fin.decLt"],
        never_offered: &["Nat.decLt"],
    },
    PinTracedGoal {
        goal: "UInt32.decLe",
        offers: ["instDecidableRelLe", "Std.instDecidableLE", "UInt32.decLe"],
        never_offered: &["Nat.decLe", "instDecidableLeBitVec"],
    },
    PinTracedGoal {
        goal: "UInt32.decLt",
        offers: ["instDecidableRelLt", "Std.instDecidableLT", "UInt32.decLt"],
        never_offered: &["Nat.decLt", "instDecidableLtBitVec"],
    },
    PinTracedGoal {
        goal: "instDecidableLeBitVec",
        offers: [
            "instDecidableRelLe",
            "Std.instDecidableLE",
            "instDecidableLeBitVec",
        ],
        never_offered: &["Nat.decLe"],
    },
    PinTracedGoal {
        goal: "instDecidableLtBitVec",
        offers: [
            "instDecidableRelLt",
            "Std.instDecidableLT",
            "instDecidableLtBitVec",
        ],
        never_offered: &["Nat.decLt"],
    },
];

/// Every imported instance of `Init.Core`'s closure, its own type as the goal:
/// no candidate that the selection step applies is filtered out unless the pin's
/// own index never offers it (`PIN_TRACED_GOALS`), and each instance that is a
/// candidate of its own goal is admitted for it.
#[test]
fn the_filter_keeps_every_candidate_the_selection_step_applies_under_init_core() {
    let Some(lib) = pinned_lib() else {
        eprintln!("SKIP: pinned Reference lib/lean absent (set FLN_REQUIRE_REFERENCE=1 to fail)");
        return;
    };
    on_stack(move || {
        let engine = import_closure(&lib, "Init.Core");
        let env = engine.environment();
        let registry =
            fln_elab::instances::InstanceRegistry::read(env).expect("the registry reads");
        let mut instances: Vec<Name> = env
            .constants()
            .map(|(name, _)| name)
            .filter(|name| registry.imported_instance_parameters(name).is_some())
            .cloned()
            .collect();
        instances.sort_by_key(Name::to_display_string);
        let (mut goals, mut skipped, mut candidates, mut kept, mut applies, mut open) =
            (0, 0, 0, 0, 0, 0);
        let mut lost = Vec::new();
        let (mut traced_goals, mut offered_kept) = (0, 0);
        for instance in &instances {
            let type_ = env
                .find(instance)
                .expect("an admitted instance")
                .constant_val()
                .type_
                .clone();
            let Some(audit) = audit_instance_goal(env, &type_, Budget::for_stack_bytes(STACK))
                .unwrap_or_else(|error| panic!("{instance:?}: {error:?}"))
            else {
                skipped += 1;
                continue;
            };
            goals += 1;
            candidates += audit.candidates.len();
            for row in &audit.candidates {
                kept += usize::from(row.admitted);
                match row.selection {
                    Selection::Applies => {
                        applies += 1;
                        if !row.admitted {
                            lost.push((instance.clone(), row.declaration.clone()));
                        }
                    }
                    Selection::Inconclusive => open += 1,
                    Selection::Fails => {}
                }
                if &row.declaration == instance && !row.admitted {
                    lost.push((instance.clone(), row.declaration.clone()));
                }
            }
            // The pin's own list for this goal: every offered instance the
            // closure holds is a candidate, and the filter keeps it.
            let display = instance.to_display_string();
            if let Some(traced) = PIN_TRACED_GOALS
                .iter()
                .find(|traced| traced.goal == display)
            {
                traced_goals += 1;
                for offered in traced.offers {
                    let offered = n(offered);
                    if env.find(&offered).is_none() {
                        continue;
                    }
                    let row = audit
                        .candidates
                        .iter()
                        .find(|row| row.declaration == offered)
                        .unwrap_or_else(|| {
                            panic!("{display}: the pin offers {offered:?}, absent here")
                        });
                    assert!(
                        row.admitted,
                        "{display}: the pin offers {offered:?}, filtered out"
                    );
                    offered_kept += 1;
                }
            }
        }
        eprintln!(
            "Init.Core: {} instances, {goals} goals audited, {skipped} not started; \
             {candidates} candidates before the filter, {kept} after; \
             {applies} applied, {open} inconclusive; {traced_goals} pin-traced goals, \
             {offered_kept} pin-offered instances kept",
            instances.len()
        );
        let lost: BTreeSet<(String, String)> = lost
            .iter()
            .map(|(goal, candidate)| (goal.to_display_string(), candidate.to_display_string()))
            .collect();
        let never_offered: BTreeSet<(String, String)> = PIN_TRACED_GOALS
            .iter()
            .flat_map(|traced| {
                traced
                    .never_offered
                    .iter()
                    .map(|candidate| (traced.goal.to_owned(), (*candidate).to_owned()))
            })
            .collect();
        assert_eq!(
            traced_goals,
            PIN_TRACED_GOALS.len(),
            "every pin-traced goal is audited"
        );
        assert!(
            offered_kept >= PIN_TRACED_GOALS.len(),
            "{offered_kept} pin-offered instances checked: at least each goal's own"
        );
        assert_eq!(
            lost, never_offered,
            "filtered out but applicable, beyond what the pin's own index never offers"
        );
        assert!(
            goals > 100 && kept < candidates,
            "{goals} goals, {kept} of {candidates}"
        );
    });
}
