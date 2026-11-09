//! Deferred ordinary source typing may unfold safe definitions; selection
//! queries and the final dual-checker admission retain their own policies.
#![forbid(unsafe_code)]
use fln::{Engine, EngineAdmissionLimits, SourceCheckLimits};
use fln_core::{name::Name, options::KVMap, outcome::Outcome};
use fln_elab::{
    NatDefinitionElabError, elaborate_definition_in_scope_with_budget,
    source::{SourceInferenceError, scope::SourceScope},
    tactic_macros::{
        TacticMacroError, TacticMacroExpander, TacticMacroExpansion, TacticMacroProvider,
    },
};
use fln_env::environment::Environment;
use fln_kernel::verdict::Budget;
use fln_syntax::tree::{Preresolved, Syntax};
use std::sync::Arc;

fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}
fn engine() -> Engine {
    Engine::with_source_seed(limits())
        .unwrap()
        .into_complete()
        .unwrap()
}
fn check(base: &Engine, source: &str) -> fln::SourceFileCheck {
    base.check_source_files(
        &[source.as_bytes()],
        &KVMap::new(),
        SourceCheckLimits::new(limits()),
    )
    .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
    .into_complete()
    .expect("both checkers must answer")
}
const WRAP: &str = "def wrap (n : Nat) : Nat := n\n";

/// The bounded source seed omits the library declarations conversion mode uses
/// to transport its result. Admit their ordinary proofs here so these checks run
/// without a Reference installation; the CLI's conv suite covers real imports.
fn conv_environment() -> Engine {
    check(
        &engine(),
        r#"def id.{u} {α : Sort u} (a : α) : α := a
def Eq.mp.{u} {α β : Sort u} (h : α = β) (a : α) : β := by
  cases h
  exact a
def Eq.mpr.{u} {α β : Sort u} (h : α = β) (b : β) : α := by
  cases h
  exact b
def wrap.{u} {α : Sort u} (a : α) : α := a
def alias.{u} {α : Sort u} (a : α) : α := wrap a
"#,
    )
    .engine
}

struct DeltaMacro(Syntax);

impl TacticMacroExpander for DeltaMacro {
    fn contains(&self, kind: &Name) -> bool {
        *kind == Name::from_components(["Test", "convDelta"])
    }

    fn enter_tactic(&self, _: usize) -> Result<u64, TacticMacroError> {
        Ok(0)
    }

    fn expand_tactic(
        &self,
        _: &Syntax,
        candidate: usize,
        _: u64,
        _: usize,
        _: &Environment,
        _: &SourceScope,
    ) -> Result<TacticMacroExpansion, TacticMacroError> {
        Ok(if candidate == 0 {
            TacticMacroExpansion::Expanded {
                syntax: self.0.clone(),
                no_fallback: false,
            }
        } else {
            TacticMacroExpansion::Exhausted
        })
    }

    fn expand_term(
        &self,
        _: &Syntax,
        _: usize,
        _: &Environment,
        _: &SourceScope,
    ) -> Result<Option<Syntax>, TacticMacroError> {
        Ok(None)
    }
}

/// Exercise metadata introduced at the deferred macro boundary, after the
/// initial declaration scan. The provider supplies Syntax, never declarations.
fn generated_delta(
    base: &Engine,
    goal: &str,
    spelling: &str,
    metadata: Vec<Preresolved>,
) -> Result<fln_kernel::Declaration, NatDefinitionElabError> {
    let template = format!("theorem unused : True := by conv => delta {spelling}");
    let template = fln_parse::parse_definition(template.as_bytes()).unwrap();
    let mut pending = vec![template.syntax()];
    let mut expansion = loop {
        let syntax = pending.pop().expect("parsed conv block");
        if syntax.kind()
            == Some(&Name::from_components([
                "Lean", "Parser", "Tactic", "Conv", "conv",
            ]))
        {
            break syntax.clone();
        }
        if let Syntax::Node { args, .. } = syntax {
            pending.extend(args);
        }
    };
    let mut pending = vec![&mut expansion];
    while let Some(syntax) = pending.pop() {
        match syntax {
            Syntax::Ident {
                val, preresolved, ..
            } if *val == Name::from_components([spelling]) => {
                *preresolved = metadata.clone();
            }
            Syntax::Node { args, .. } => pending.extend(args),
            _ => {}
        }
    }
    let source = format!("theorem generated (n : Nat) : {goal} := by skip");
    let mut syntax = fln_parse::parse_definition(source.as_bytes())
        .unwrap()
        .syntax()
        .clone();
    let mut pending = vec![&mut syntax];
    while let Some(syntax) = pending.pop() {
        if let Syntax::Node { kind, args, .. } = syntax {
            if *kind == Name::from_components(["Lean", "Parser", "Tactic", "skip"]) {
                *kind = Name::from_components(["Test", "convDelta"]);
            }
            pending.extend(args);
        }
    }
    let scope = SourceScope {
        tactic_macros: Some(TacticMacroProvider(Arc::new(DeltaMacro(expansion)))),
        ..SourceScope::default()
    };
    elaborate_definition_in_scope_with_budget(&syntax, base.environment(), limits().kernel, &scope)
}

#[test]
fn conv_delta_preserves_global_identifier_metadata_from_macro_expansion() {
    let base = conv_environment();
    let wrap = Preresolved::Decl {
        name: Name::from_components(["wrap"]),
        fields: vec![],
    };
    for (goal, spelling, metadata) in [
        (
            "wrap n = n",
            "unresolvableCapturedSpelling",
            vec![wrap.clone()],
        ),
        (
            "alias n = wrap n",
            "alias",
            vec![
                Preresolved::Namespace {
                    ns: Name::from_components(["UnknownNamespace"]),
                },
                Preresolved::Decl {
                    name: Name::from_components(["wrap"]),
                    fields: vec!["ignoredField".into()],
                },
            ],
        ),
    ] {
        let declaration = generated_delta(&base, goal, spelling, metadata).unwrap();
        base.admit_declaration(declaration, &KVMap::new(), limits())
            .unwrap()
            .into_complete()
            .expect("the generated proof must pass both checkers");
    }
    assert!(matches!(
        generated_delta(&base, "wrap n = n", "alias", vec![wrap.clone(), wrap]),
        Err(NatDefinitionElabError::Inference(SourceInferenceError::NameScope(
            fln_elab::source::scope::ScopeError::Ambiguous(_, candidates)
        ))) if candidates == vec![Name::from_components(["wrap"]); 2]
    ));
    assert!(matches!(
        generated_delta(&base, "alias n = wrap n", "alias", vec![Preresolved::Decl {
            name: Name::from_components(["missingCapturedDefinition"]),
            fields: vec![],
        }]),
        Err(NatDefinitionElabError::Inference(SourceInferenceError::UnknownConstant(name)))
            if name == Name::from_components(["missingCapturedDefinition"])
    ));
}

#[test]
fn conv_delta_expands_selected_definitions_beneath_binders_and_at_each_universe() {
    let base = conv_environment();
    for source in [
        "theorem converted (n : Nat) : alias (wrap n) = n := by\n  conv => delta wrap alias",
        "theorem quantified : ∀ n : Nat, wrap (wrap n) = n := by\n  conv => delta wrap\n  intro n\n  rfl",
        "theorem functions : (fun n : Nat => wrap (wrap n)) = (fun n : Nat => n) := by\n  conv => delta wrap",
        "theorem polymorphic.{u} {α : Sort u} (a : α) : alias a = a := by\n  conv => delta wrap alias",
        "theorem typeArgument (α : Type) : wrap α = α := by\n  conv => delta wrap",
        "theorem propArgument (p : Prop) : wrap p = p := by\n  conv => delta wrap",
    ] {
        check(&base, source);
    }
}

#[test]
fn conv_delta_transports_hypotheses_and_resolves_global_names() {
    let base = conv_environment();
    check(
        &base,
        r#"theorem transported (n m : Nat) (h : alias n = m) : n = m := by
  conv at h => delta wrap alias
  exact h
namespace DeltaNames
def localWrap (n : Nat) : Nat := n
theorem names (n : Nat) : localWrap n = n := by
  conv => delta localWrap
theorem localShadow (localWrap : Nat) : DeltaNames.localWrap localWrap = localWrap := by
  conv => delta localWrap
end DeltaNames
open DeltaNames
theorem opened (n : Nat) : localWrap n = n := by
  conv => delta localWrap
theorem openedShadow (localWrap : Nat) : DeltaNames.localWrap localWrap = localWrap := by
  conv => delta localWrap
theorem shadowed (wrap : Nat) : _root_.wrap wrap = wrap := by
  conv => delta _root_.wrap
"#,
    );
}

#[test]
fn conv_delta_succeeds_unchanged_without_exposing_opaque_bodies() {
    let base = check(
        &conv_environment(),
        "opaque sealed : Nat := 7\ntheorem witness : True := True.intro\n",
    )
    .engine;
    for source in [
        "theorem untouched (n : Nat) : n = n := by\n  conv => delta wrap Nat Nat.succ",
        "theorem opaqueUnchanged : sealed = sealed := by\n  conv => delta sealed",
        "theorem theoremUnchanged : witness = witness := by\n  conv => delta witness",
    ] {
        check(&base, source);
    }
    for source in [
        "theorem bad : sealed = 7 := by\n  conv => delta sealed",
        "theorem bad (n : Nat) : alias n = Nat.succ n := by\n  conv => delta wrap alias",
        "theorem bad (n : Nat) : alias n = n := by\n  conv => delta alias missingDefinition",
    ] {
        let root = base.logical_root(&KVMap::new());
        let error = base
            .check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits()),
            )
            .expect_err("conversion cannot erase an invalid proof or an unknown name");
        assert_eq!(
            error.disposition(),
            ("elaboration", false, 1),
            "{source}: {error:?}"
        );
        assert_eq!(base.logical_root(&KVMap::new()), root);
        assert!(!base.environment().contains(&Name::from_components(["bad"])));
    }
}

#[test]
fn ordinary_rfl_infers_shared_arguments_through_safe_delta_conversion() {
    let base = check(&engine(), WRAP).engine;
    for source in [
        "theorem left (n : Nat) : wrap n = n := rfl",
        "theorem right (n : Nat) : n = wrap n := rfl",
        "theorem nested (n : Nat) : wrap (wrap n) = n := rfl",
        "theorem beta (n : Nat) : wrap ((fun x => x) n) = n := rfl",
        "theorem proofLambda : forall n : Nat, wrap n = n := fun n => rfl",
    ] {
        check(&base, source);
    }
}

#[test]
fn ordinary_implicit_calls_not_only_rfl_use_the_delta_retry() {
    check(
        &engine(),
        "def wrap (n : Nat) : Nat := n\ndef reflAlias {n : Nat} : wrap n = n := by rfl\ntheorem use (n : Nat) : n = n := reflAlias\ndef takeProof (n : Nat) (h : wrap n = n) : Nat := n\ndef answer : Nat := takeProof 7 rfl\ntheorem result : answer = 7 := by rfl",
    );
}

#[test]
fn polymorphic_definitions_are_instantiated_before_delta_matching() {
    check(
        &engine(),
        "def identity {A : Sort u} (x : A) : A := x\ntheorem term {A : Sort u} (x : A) : identity x = x := rfl\ntheorem type (A : Type) : identity A = A := rfl\ntheorem prop (P : Prop) : identity P = P := rfl",
    );
}

#[test]
fn failed_speculative_conversion_falls_back_without_publishing_assignments() {
    let base = check(&engine(), WRAP).engine;
    check(
        &base,
        "theorem fallback (x y : Nat) (h : x = y) : wrap x = y := by first | exact rfl | exact h",
    );
    check(
        &base,
        "theorem direct (x : Nat) : wrap x = x := by first | exact rfl | fail",
    );
    for source in [
        "theorem bad (n : Nat) : wrap n = Nat.succ n := rfl",
        "theorem bad : wrap 0 = 1 := by first | exact rfl | rfl",
        "theorem bad (rfl : Nat) (n : Nat) : wrap n = n := rfl",
    ] {
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
        assert!(!base.environment().contains(&Name::from_components(["bad"])));
    }
}

#[test]
fn resource_nonanswers_do_not_trigger_conversion_success() {
    let base = check(&engine(), WRAP).engine;
    let root = base.logical_root(&KVMap::new());
    let mut low = SourceCheckLimits::new(limits());
    low.admission.kernel = low.admission.kernel.narrowed(0, 32);
    let result = base.check_source_files(
        &[b"theorem low (n : Nat) : wrap n = n := rfl"],
        &KVMap::new(),
        low,
    );
    match result {
        Ok(Outcome::Inconclusive(_)) => {}
        Err(error) => assert!(
            matches!(error.disposition(), ("resource" | "inconclusive", false, 3)),
            "{error:?}"
        ),
        other => panic!("resource stop changed into a verdict: {other:?}"),
    }
    assert_eq!(base.logical_root(&KVMap::new()), root);
    assert!(!base.environment().contains(&Name::from_components(["low"])));
}

const HIDDEN_NUMBER: &str = "def hiddenNumber : Nat := 4\n";
const IRREDUCIBLE_NUMBER: &str =
    "def hiddenNumber : Nat := 4\nattribute [irreducible] hiddenNumber\n";
const HIDDEN_VALUE_PROOF: &str = "theorem t : hiddenNumber = 4 := rfl";
const HIDDEN_OPERAND_PROOF: &str = "theorem t : Nat.add hiddenNumber 2 = 6 := rfl";

fn refuses_source_conversion(base: &Engine, source: &str, declaration: &str) {
    let options = KVMap::new();
    let root = base.logical_root(&options);
    let result = base.check_source_files(
        &[source.as_bytes()],
        &options,
        SourceCheckLimits::new(limits()),
    );
    let Err(error) = result else {
        panic!("irreducible value was exposed while elaborating {source}");
    };
    assert_eq!(
        error.disposition(),
        ("elaboration", false, 1),
        "{source} must fail during term conversion, not parsing or kernel checking: {error:?}",
    );
    assert_eq!(base.logical_root(&options), root);
    assert!(
        !base
            .environment()
            .contains(&Name::from_components([declaration]))
    );
}

fn refuses_default_reflexivity(base: &Engine, source: &str) {
    refuses_source_conversion(base, source, "t");
    check(
        base,
        "theorem opaqueReflexivity : hiddenNumber = hiddenNumber := rfl",
    );
}

fn source_reflexivity_preserves_irreducibility(base: &Engine) {
    let regular = check(base, HIDDEN_NUMBER).engine;
    // These exact terms are accepted before the status changes. Provisioning
    // the journal directly also covers metadata activated by an artifact import.
    for source in [HIDDEN_VALUE_PROOF, HIDDEN_OPERAND_PROOF] {
        check(&regular, source);
    }
    let environment = fln_elab::reducibility::register(
        regular.environment(),
        &Name::from_components(["hiddenNumber"]),
        fln_elab::reducibility::Reducibility::Irreducible,
    )
    .unwrap();
    let opaque = Engine::from_environment(environment);
    for source in [HIDDEN_VALUE_PROOF, HIDDEN_OPERAND_PROOF] {
        refuses_default_reflexivity(&opaque, source);
    }
}

#[test]
fn source_term_reflexivity_preserves_imported_irreducibility_metadata() {
    source_reflexivity_preserves_irreducibility(&engine());
}

#[test]
fn source_term_reflexivity_preserves_irreducibility_with_coercions_enabled() {
    let base = Engine::with_coercion_seed(limits())
        .unwrap()
        .into_complete()
        .unwrap();
    source_reflexivity_preserves_irreducibility(&base);
}

#[test]
fn source_irreducible_attribute_blocks_term_reflexivity_of_a_definition() {
    // Exact Reference 4.32.0 (8c9756b) observation: the full three-command
    // program is refused with a type mismatch at `rfl`. Check the prefix on
    // its own so a parser refusal of the attribute cannot satisfy this test.
    let regular = check(&engine(), HIDDEN_NUMBER).engine;
    check(&regular, HIDDEN_VALUE_PROOF);
    let opaque = check(&engine(), IRREDUCIBLE_NUMBER).engine;
    refuses_default_reflexivity(&opaque, HIDDEN_VALUE_PROOF);
}

#[test]
fn source_irreducible_attribute_blocks_computation_of_a_nat_operand() {
    let regular = check(&engine(), HIDDEN_NUMBER).engine;
    check(&regular, HIDDEN_OPERAND_PROOF);
    let opaque = check(&engine(), IRREDUCIBLE_NUMBER).engine;
    refuses_default_reflexivity(&opaque, HIDDEN_OPERAND_PROOF);
}

fn conversion_engines() -> [Engine; 2] {
    [
        engine(),
        Engine::with_coercion_seed(limits())
            .unwrap()
            .into_complete()
            .unwrap(),
    ]
}

#[test]
fn source_irreducible_attribute_blocks_explicit_closed_reflexivity() {
    // Explicit parameters leave no inference hole to force a solver check.
    // Reference rejects both closed proof types at ordinary transparency.
    for base in conversion_engines() {
        let regular = check(&base, HIDDEN_NUMBER).engine;
        let opaque = check(&base, IRREDUCIBLE_NUMBER).engine;
        for source in [
            "theorem t : hiddenNumber = 4 := @Eq.refl Nat hiddenNumber",
            "theorem t : 4 = hiddenNumber := @Eq.refl Nat 4",
        ] {
            check(&regular, source);
            refuses_default_reflexivity(&opaque, source);
        }
    }
}

fn refuses_hidden_carrier_conversion(source: &str) {
    for base in conversion_engines() {
        let regular = check(&base, "def HiddenCarrier : Type := Nat").engine;
        check(&regular, source);
        let opaque = check(
            &base,
            "def HiddenCarrier : Type := Nat\nattribute [irreducible] HiddenCarrier",
        )
        .engine;
        let options = KVMap::new();
        let root = opaque.logical_root(&options);
        let result = opaque.check_source_files(
            &[source.as_bytes()],
            &options,
            SourceCheckLimits::new(limits()),
        );
        let Err(error) = result else {
            panic!("irreducible carrier was exposed while elaborating {source}");
        };
        assert_eq!(
            error.disposition(),
            ("elaboration", false, 1),
            "{source} must fail in elaboration: {error:?}",
        );
        assert_eq!(opaque.logical_root(&options), root);
        assert!(
            !opaque
                .environment()
                .contains(&Name::from_components(["value"]))
        );
        check(
            &opaque,
            "def sameCarrier (x : HiddenCarrier) : HiddenCarrier := x",
        );
    }
}

#[test]
fn source_irreducible_attribute_preserves_a_closed_expected_carrier() {
    refuses_hidden_carrier_conversion("def value : HiddenCarrier := (4 : Nat)");
}

#[test]
fn source_irreducible_attribute_preserves_a_closed_actual_carrier() {
    refuses_hidden_carrier_conversion("def value (x : HiddenCarrier) : Nat := x");
}

#[test]
fn source_irreducibility_preserves_symbolic_nat_computation() {
    for base in conversion_engines() {
        let opaque = check(&base, IRREDUCIBLE_NUMBER).engine;
        for source in [
            "theorem zeroRight (n : Nat) : Nat.add n 0 = n := rfl",
            "theorem offset (n : Nat) : Nat.add (Nat.add n 2) 3 = Nat.add n 5 := rfl",
            "theorem namedZero : Nat.add hiddenNumber 0 = hiddenNumber := rfl",
            "theorem namedOffset : Nat.add hiddenNumber 2 = Nat.succ (Nat.succ hiddenNumber) := rfl",
        ] {
            check(&opaque, source);
        }
    }
}

#[test]
fn source_projection_reducibility_overrides_abbreviation_hints() {
    let class = "class Choice where\n  value : Nat\n";
    let proofs = [
        "theorem t : @Choice.value (Choice.mk 4) = 4 := rfl",
        "theorem t : @Choice.value (Choice.mk 4) = 4 := @Eq.refl Nat (@Choice.value (Choice.mk 4))",
    ];
    for base in conversion_engines() {
        for prefix in [
            class.to_owned(),
            format!("{class}attribute [reducible] Choice.value"),
        ] {
            let regular = check(&base, &prefix).engine;
            for source in proofs {
                check(&regular, source);
            }
        }
        let opaque = check(
            &base,
            &format!("{class}attribute [irreducible] Choice.value"),
        )
        .engine;
        for source in proofs {
            refuses_source_conversion(&opaque, source, "t");
        }
        check(
            &opaque,
            "theorem sameProjection : @Choice.value (Choice.mk 4) = @Choice.value (Choice.mk 4) := rfl",
        );
    }
}

#[test]
fn source_irreducible_function_types_do_not_expose_their_arrow() {
    let definition = "def HiddenArrow : Type := Nat -> Nat\n";
    let source = "def invoke (f : HiddenArrow) : Nat := f 4";
    for base in conversion_engines() {
        let regular = check(&base, definition).engine;
        check(&regular, source);
        let opaque = check(
            &base,
            &format!("{definition}attribute [irreducible] HiddenArrow"),
        )
        .engine;
        refuses_source_conversion(&opaque, source, "invoke");
        check(
            &opaque,
            "def keepFunction (f : HiddenArrow) : HiddenArrow := f",
        );
    }
}

#[test]
fn source_default_conversion_preserves_opacity_through_definition_wrappers() {
    let prefix = "def hiddenNumber : Nat := 4\ndef wrapNumber : Nat := hiddenNumber\nattribute [irreducible] hiddenNumber";
    for base in conversion_engines() {
        let opaque = check(&base, prefix).engine;
        refuses_default_reflexivity(
            &opaque,
            "theorem t : wrapNumber = 4 := @Eq.refl Nat wrapNumber",
        );
        for source in [
            "theorem sameOpaque : wrapNumber = hiddenNumber := rfl",
            "theorem sameOpaque : wrapNumber = hiddenNumber := @Eq.refl Nat hiddenNumber",
        ] {
            check(&opaque, source);
        }
    }
}

#[test]
fn source_implicit_assignments_preserve_their_closed_opaque_type() {
    let prefix = "def HiddenCarrier : Type := Nat\ndef reveal (n : HiddenCarrier) : Nat := n\ntheorem reflHidden {n : HiddenCarrier} : reveal n = reveal n := rfl\n";
    let source = "theorem assignmentLeak (n : Nat) : n = n := reflHidden";
    for base in conversion_engines() {
        let regular = check(&base, prefix).engine;
        check(&regular, source);
        let opaque = check(
            &base,
            &format!("{prefix}attribute [irreducible] HiddenCarrier"),
        )
        .engine;
        refuses_source_conversion(&opaque, source, "assignmentLeak");
        check(
            &opaque,
            "theorem sameCarrier (n : HiddenCarrier) : reveal n = reveal n := reflHidden",
        );
    }
}
