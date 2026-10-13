//! Auxiliary simp evidence is selected through the ordinary proof/checker path.
#![forbid(unsafe_code)]
use fln::*;
use fln_elab::source::scope::simp::{self, ImportedSimpRule};

fn n(name: &str) -> Name {
    Name::from_components(name.split('.'))
}
fn c(name: &str) -> Expr {
    Expr::const_(n(name), vec![])
}
fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 << 20))
}
fn admit(base: Engine, name: Name, type_: Expr) -> Engine {
    base.admit_declaration(
        Declaration::Axiom(AxiomVal {
            base: ConstantVal {
                name,
                level_params: vec![],
                type_,
            },
            is_unsafe: false,
        }),
        &KVMap::new(),
        limits(),
    )
    .unwrap()
    .into_complete()
    .unwrap()
    .engine
}
fn law(function: &str) -> Expr {
    let x = Expr::bvar(0).unwrap();
    let eq = Expr::app(
        Expr::app(
            Expr::app(Expr::const_(n("Eq"), vec![Level::one()]), c("Nat")),
            Expr::app(c(function), x.clone()),
        ),
        x,
    );
    Expr::forall_e(n("x"), c("Nat"), eq, BinderInfo::Default)
}
fn engine() -> Engine {
    let mut base = Engine::with_source_seed(limits())
        .unwrap()
        .into_complete()
        .unwrap();
    for f in ["f", "g"] {
        base = admit(
            base,
            n(f),
            Expr::forall_e(n("x"), c("Nat"), c("Nat"), BinderInfo::Default),
        );
        base = admit(base, n(&format!("law_{f}")), law(f));
    }
    base
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
fn refused(base: &Engine, source: &str) {
    let root = base.logical_root(&KVMap::new());
    assert!(
        base.check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits())
        )
        .is_err(),
        "{source}"
    );
    assert_eq!(base.logical_root(&KVMap::new()), root);
}
fn register(base: &Engine, origin: Name, proof: Name) -> Engine {
    Engine::from_environment(
        simp::register_imported_proof(base.environment(), &origin, &proof, 1000).unwrap(),
    )
}

#[test]
fn origin_is_not_borrowed_as_proof_and_erasure_removes_all_auxiliaries() {
    let base = engine();
    let source = "theorem result (x : Nat) : f (g x) = x := by simp";
    refused(&base, source);
    let first = register(&base, n("f"), n("law_f"));
    refused(&first, source);
    let both = register(&first, n("f"), n("law_g"));
    checked(&both, source);
    for tactic in ["simp [-f]", "simp only []", "simp only [law_f]"] {
        refused(
            &both,
            &format!("theorem absent (x : Nat) : f (g x) = x := by {tactic}"),
        );
    }
    let erased = checked(&both, "attribute [-simp] f");
    refused(&erased, source);
    checked(&both, source);
}

#[test]
fn safe_definition_valued_evidence_is_not_an_unfolding_request() {
    let base = checked(&engine(), "def evidence (x : Nat) : f x = x := law_f x");
    let selected = register(&base, n("f"), n("evidence"));
    checked(&selected, "theorem use (x : Nat) : f (f x) = x := by simp");
    refused(
        &selected,
        "theorem falseResult (x : Nat) : f x = 0 := by simp",
    );
    assert!(simp::register_imported_proof(base.environment(), &n("f"), &n("f"), 1000).is_err());
}

#[test]
fn numeric_private_proofs_cannot_alias_source_string_components() {
    let numeric = Name::str(Name::num(n("_private.Aux"), 7), "proof");
    let textual = Name::from_components(["_private", "Aux", "7", "proof"]);
    let base = admit(
        admit(engine(), numeric.clone(), law("f")),
        textual.clone(),
        law("g"),
    );
    let selected = register(&base, n("f"), numeric.clone());
    checked(&selected, "theorem use (x : Nat) : f x = x := by simp");
    refused(
        &selected,
        "theorem notSelected (x : Nat) : g x = x := by simp",
    );
    let different = register(&base, n("f"), textual);
    checked(&different, "theorem use (x : Nat) : g x = x := by simp");
    refused(
        &different,
        "theorem notSelected (x : Nat) : f x = x := by simp",
    );
    assert_eq!(
        simp::read(selected.environment()).unwrap()[0].proof,
        Some(numeric)
    );
}

#[test]
fn imported_repetition_reinstates_a_rule_after_a_local_erasure() {
    let base = engine();
    let selected = register(&base, n("f"), n("law_f"));
    let repeated = register(&selected, n("f"), n("law_f"));
    let extension = n("FrankenLean.sourceSimp.v1");
    let event = repeated
        .environment()
        .extension(&extension)
        .unwrap()
        .entries()
        .last()
        .unwrap()
        .payload
        .clone();
    let erased = checked(&selected, "attribute [-simp] f");
    let replayed = Engine::from_environment(
        erased
            .environment()
            .push_extension_entry(&extension, event.to_vec())
            .unwrap(),
    );
    checked(&replayed, "theorem use (x : Nat) : f x = x := by simp");
    refused(&erased, "theorem absent (x : Nat) : f x = x := by simp");
}

#[test]
fn explicit_rules_and_mixed_batches_preserve_their_own_selection() {
    let base = engine();
    let updated = simp::import_rules(
        base.environment(),
        &[
            ImportedSimpRule::Proof {
                origin: n("f"),
                proof: n("law_f"),
                priority: 500,
            },
            ImportedSimpRule::Proof {
                origin: n("f"),
                proof: n("law_g"),
                priority: 1000,
            },
            ImportedSimpRule::Erase {
                declaration: n("f"),
            },
            ImportedSimpRule::Proof {
                origin: n("g"),
                proof: n("law_g"),
                priority: 1000,
            },
        ],
    )
    .unwrap();
    let selected = Engine::from_environment(updated);
    checked(
        &selected,
        "theorem explicit (x : Nat) : f (g x) = x := by simp [law_f]",
    );
    refused(
        &selected,
        "theorem absent (x : Nat) : f (g x) = x := by simp",
    );
    assert!(simp::read(base.environment()).unwrap().is_empty());
}
