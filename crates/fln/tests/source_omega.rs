//! Native arithmetic proofs cross the same two checker seats as written proofs.
//! The Reference supplies checked library declarations, never a runtime solver.
#![forbid(unsafe_code)]

use fln::source_check::modules::imported::SourceOleanImportLimits;
use fln::source_check::modules::{
    SourceModuleCacheLimits, SourceModuleCheckLimits, SourceModuleSession,
};
use fln::{
    Budget, ClosedVmValue, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap, Name,
    OleanCheckLimits, OleanDecodeLimits, OleanModuleInput, OleanWriteBudget, SourceCheckLimits,
    SourceModuleInput, olean_module_imports,
};
use fln_core::outcome::InconclusiveCause;
use fln_elab::NatDefinitionElabError;
use fln_elab::arithmetic::{
    ArithmeticProvider, LinearConstraint, OmegaCertificate, OmegaInconclusive, OmegaLimits,
    OmegaOutcome, OmegaResource, OmegaStep,
};
use fln_elab::source::SourceInferenceError;
use fln_elab::source::scope::SourceScope;
use std::collections::BTreeSet;
use std::path::{Path, PathBuf};

const STACK: usize = 256 * 1024 * 1024;

fn n(text: &str) -> Name {
    Name::from_components(text.split('.'))
}

fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(STACK))
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

fn import_closure(lib: &Path) -> Engine {
    let root = n("Init.Omega");
    let mut pending = vec![root.clone()];
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
        let exported = std::fs::read(&base).expect("pinned exported artifact");
        pending.extend(
            olean_module_imports(&exported, OleanDecodeLimits::new(exported.len()))
                .expect("pinned module imports"),
        );
        parts.push([
            exported,
            std::fs::read(base.with_extension("olean.server")).expect("pinned server artifact"),
            std::fs::read(base.with_extension("olean.private")).expect("pinned private artifact"),
        ]);
        names.push(module);
    }
    let inputs: Vec<_> = names
        .iter()
        .zip(&parts)
        .map(|(name, [exported, server, private])| OleanModuleInput {
            name,
            artifact: exported,
            server_artifact: Some(server),
            private_artifact: Some(private),
        })
        .collect();
    Engine::builder()
        .build_empty()
        .import_olean_modules_for_source(
            &inputs,
            &[root],
            &KVMap::new(),
            SourceOleanImportLimits::new(OleanCheckLimits::new(256 * 1024 * 1024, limits().kernel)),
        )
        .expect("the imported arithmetic library passes both checker seats")
        .into_complete()
        .expect("the arithmetic library import finishes")
        .engine
}

// These proof statements are also checked against the live v4.32.0 Reference.
// They exercise independent atoms, integer (not rational) rounding, and branches.
const PROOFS: &[(&str, &str)] = &[
    (
        "natChain",
        "theorem natChain (i j k : Nat) (h₁ : i + 3 ≤ j) (h₂ : j + 4 ≤ k) : i + 7 ≤ k := by omega",
    ),
    (
        "natStrict",
        "theorem natStrict (n : Nat) : n < n + 1 := by omega",
    ),
    (
        "integerRound",
        "theorem integerRound (x : Int) (h₁ : 2 * x ≤ 3) (h₂ : 2 ≤ x) : False := by omega",
    ),
    (
        "negativeRound",
        "theorem negativeRound (x : Int) (h : 2 * x ≤ -1) : x ≤ -1 := by omega",
    ),
    (
        "cancelledCoefficient",
        "theorem cancelledCoefficient (x y : Int) (h : (x - x + 2) * y ≤ 7) (hy : 4 ≤ y) : False := by omega",
    ),
    (
        "mixedDomains",
        "theorem mixedDomains (n : Nat) (z : Int) (h : (n : Int) + 2 ≤ z) (hz : z < 0) : False := by omega",
    ),
    (
        "lateAtom",
        "theorem lateAtom (a b : Nat) (h : (a : Int) + 1 ≤ (b : Int)) (h₂ : b ≤ a) : False := by omega",
    ),
    (
        "truncatedSubtraction",
        "theorem truncatedSubtraction (n : Nat) (h : 0 < n) : n - 1 < n := by omega",
    ),
    (
        "subtractionZero",
        "theorem subtractionZero (m n : Nat) (h : m ≤ n) : m - n = 0 := by omega",
    ),
    (
        "integerEquality",
        "theorem integerEquality (x y : Int) (h : x + 4 = y) : x < y := by omega",
    ),
    (
        "integerDisequality",
        "theorem integerDisequality (x y : Int) (h : x ≠ y) (h₁ : x ≤ y) : x < y := by omega",
    ),
    (
        "naturalDisequality",
        "theorem naturalDisequality (x y : Nat) (h : x ≠ y) (h₁ : x ≤ y) : x < y := by omega",
    ),
    (
        "eitherBound",
        "theorem eitherBound (x : Int) (h : x ≤ 3 ∨ x ≤ 7) : x ≤ 7 := by omega",
    ),
    (
        "bothBounds",
        "theorem bothBounds (x y : Nat) (h : x + 2 ≤ y ∧ y ≤ x) : False := by omega",
    ),
    (
        "implication",
        "theorem implication (n : Nat) (h : n ≤ 3 → n ≤ 2) (hn : n ≤ 3) : n ≤ 2 := by omega",
    ),
    (
        "forallGoal",
        "theorem forallGoal : ∀ n : Nat, n + 1 > n := by omega",
    ),
    (
        "localLet",
        "theorem localLet (x : Int) (h : x ≤ 3) : let y := x + 2; y ≤ 5 := by omega",
    ),
    (
        "opaqueAtoms",
        "theorem opaqueAtoms (f : Nat → Int) (n : Nat) (h : f n ≤ 3) : f n < 4 := by omega",
    ),
    (
        "wideCoefficient",
        "theorem wideCoefficient (x : Int) (h : 340282366920938463463374607431768211457 * x ≤ 340282366920938463463374607431768211456) (hx : 1 ≤ x) : False := by omega",
    ),
    (
        "logicalContradiction",
        "theorem logicalContradiction (n : Nat) (h : n ≤ 2) (hn : ¬(n ≤ 2)) : False := by omega",
    ),
    (
        "negatedConjunction",
        "theorem negatedConjunction (n m : Nat) (h : ¬(n < 3 ∧ m < 4)) (hn : n < 3) : ¬(m < 4) := by omega",
    ),
    (
        "doubleNegation",
        "theorem doubleNegation (n : Nat) (h : ¬¬(n ≤ 3)) : n ≤ 3 := by omega",
    ),
    (
        "quotientRemainderIdentity",
        "theorem quotientRemainderIdentity (n : Nat) : 7 * (n / 7) + n % 7 = n := by omega",
    ),
    (
        "quotientLowerBound",
        "theorem quotientLowerBound (n : Nat) : 7 * (n / 7) ≤ n := by omega",
    ),
    (
        "quotientUpperBound",
        "theorem quotientUpperBound (n : Nat) : n < 7 * (n / 7) + 7 := by omega",
    ),
    (
        "quotientHypBound",
        "theorem quotientHypBound (n : Nat) (h : n < 14) : n / 7 ≤ 1 := by omega",
    ),
    (
        "quotientZeroIff",
        "theorem quotientZeroIff (n : Nat) : n / 7 = 0 ↔ n < 7 := by omega",
    ),
    (
        "uniqueQuotientRemainder",
        "theorem uniqueQuotientRemainder (n q r : Nat) (h : n = 7 * q + r) (hr : r < 7) : n / 7 = q ∧ n % 7 = r := by omega",
    ),
    (
        "quotientZeroDivisor",
        "theorem quotientZeroDivisor (n : Nat) : n / 0 = 0 := by omega",
    ),
    (
        "quotientOneDivisor",
        "theorem quotientOneDivisor (n : Nat) : n / 1 = n := by omega",
    ),
    (
        "quotientCombinedDivisors",
        "theorem quotientCombinedDivisors (n : Nat) : n / 3 + n / 4 ≤ n := by omega",
    ),
    (
        "quotientNestedRemainder",
        "theorem quotientNestedRemainder (n : Nat) : (n / 3) % 2 = (n % 6) / 3 := by omega",
    ),
    (
        "remainderShift",
        "theorem remainderShift (n : Nat) : (n + 7) % 7 = n % 7 := by omega",
    ),
    (
        "remainderParity",
        "theorem remainderParity (n : Nat) (h : n % 2 = 0) : (n + 1) % 2 = 1 := by omega",
    ),
    (
        "remainderBound",
        "theorem remainderBound (n : Nat) : n % 7 < 7 := by omega",
    ),
    (
        "remainderZero",
        "theorem remainderZero (n : Nat) : n % 0 = n := by omega",
    ),
    (
        "remainderOne",
        "theorem remainderOne (n : Nat) : n % 1 = 0 := by omega",
    ),
    (
        "goalLetDivisor",
        "theorem goalLetDivisor (n : Nat) : let k := 7; n % k < 7 := by omega",
    ),
    (
        "groundArithmeticDivisor",
        "theorem groundArithmeticDivisor (n : Nat) : n % (2 + 5) < 7 := by omega",
    ),
    (
        "groundZeroDivisor",
        "theorem groundZeroDivisor (n : Nat) : n % (2 - 2) = n := by omega",
    ),
    (
        "groundMixedDivisor",
        "theorem groundMixedDivisor (n : Nat) : n % (18 / 3 + 2 * 2) < 10 := by omega",
    ),
    (
        "groundPowerDivisor",
        "theorem groundPowerDivisor (n : Nat) : n % (2 ^ 3) < 8 := by omega",
    ),
    (
        "quotientGroundArithmetic",
        "theorem quotientGroundArithmetic (n : Nat) : n / (2 + 5) = n / 7 := by omega",
    ),
    (
        "quotientGoalLet",
        "theorem quotientGoalLet (n : Nat) : let k := 7; n / k = n / 7 := by omega",
    ),
    (
        "forallThenDivisorLet",
        "theorem forallThenDivisorLet : ∀ n : Nat, let k : Nat := 7; n % k < 7 := by omega",
    ),
    (
        "nestedGoalDivisorLets",
        "theorem nestedGoalDivisorLets (n : Nat) : let k : Nat := 2; let j : Nat := k + 5; n % j < 7 := by omega",
    ),
    (
        "wideDivisor",
        "theorem wideDivisor (n : Nat) : n % 340282366920938463463374607431768211457 < 340282366920938463463374607431768211457 := by omega",
    ),
    (
        "rawNatQuotientNonnegative",
        "theorem rawNatQuotientNonnegative (n k : Nat) : 0 ≤ Nat.div n k := by omega",
    ),
    (
        "rawNatRemainderNonnegative",
        "theorem rawNatRemainderNonnegative (n k : Nat) : 0 ≤ Nat.mod n k := by omega",
    ),
    (
        "intQuotientLower",
        "theorem intQuotientLower (x : Int) : 7 * (x / 7) ≤ x := by omega",
    ),
    (
        "intRemainderBounds",
        "theorem intRemainderBounds (x : Int) : 0 ≤ x % 7 ∧ x % 7 < 7 := by omega",
    ),
    (
        "intDivisionIdentity",
        "theorem intDivisionIdentity (x : Int) : 7 * (x / 7) + x % 7 = x := by omega",
    ),
    (
        "intNegativeQuotient",
        "theorem intNegativeQuotient : (-8 : Int) / 7 = -2 := by omega",
    ),
    (
        "intNegativeRemainder",
        "theorem intNegativeRemainder : (-8 : Int) % 7 = 6 := by omega",
    ),
    (
        "intZeroQuotient",
        "theorem intZeroQuotient (x : Int) : x / 0 = 0 := by omega",
    ),
    (
        "intZeroRemainder",
        "theorem intZeroRemainder (x : Int) : x % 0 = x := by omega",
    ),
];

fn record_case(failures: &mut Vec<String>, label: &str, check: impl FnOnce()) {
    if let Err(payload) = std::panic::catch_unwind(std::panic::AssertUnwindSafe(check)) {
        let detail = payload
            .downcast_ref::<String>()
            .map(String::as_str)
            .or_else(|| payload.downcast_ref::<&str>().copied())
            .unwrap_or("non-string panic");
        failures.push(format!("{label}: {detail}"));
    }
}

fn assert_cases_complete(failures: &[String]) {
    assert!(
        failures.is_empty(),
        "arithmetic cases failed:\n{}",
        failures.join("\n")
    );
}

fn assert_proofs(base: &Engine) {
    let mut failures = Vec::new();
    let before = base.logical_root(&KVMap::new());
    for (name, source) in PROOFS {
        eprintln!("omega proof: {name}");
        record_case(&mut failures, name, || {
            let checked = base
                .check_source_files(
                    &[source.as_bytes()],
                    &KVMap::new(),
                    SourceCheckLimits::new(limits()),
                )
                .unwrap_or_else(|e| panic!("{name}: {e:?}"))
                .into_complete()
                .unwrap_or_else(|reason| panic!("{name}: unfinished proof: {reason:?}"));
            assert_eq!(checked.theorems, 1, "{name}");
            assert!(checked.engine.environment().contains(&n(name)), "{name}");
            assert_eq!(checked.base_logical_root, before);
            assert_eq!(base.logical_root(&KVMap::new()), before);
        });
    }
    assert_cases_complete(&failures);
}

const REFUSALS: &[&str] = &[
    "theorem embeddedBeta (x : Int) (h : x ≤ 3) : (fun y : Int => y + 2) x ≤ 5 := by omega",
    "theorem universalIdentity : ∀ p : Prop, p → p := by omega",
    "theorem bareTrue : True := by omega",
    "theorem falseConjunct (p : Prop) (h : False ∧ p) : False := by omega",
    "theorem primitiveNatSub (n : Nat) (h : 0 < n) : Nat.sub n 1 < n := by omega",
    "theorem primitiveIntSub (x : Int) (h : x ≤ 3) : Int.sub x 1 ≤ 2 := by omega",
    // Live pin refusals: omega does not use arbitrary logical atoms or unfold
    // embedded let expressions. Keep these separate from arithmetic logic and
    // the initial goal's let binders, both of which the pin does process.
    "theorem arbitraryAtom (p : Prop) (h : p) (hn : ¬p) : False := by omega",
    "theorem arbitraryNegation (p : Prop) (h : ¬¬p) : p := by omega",
    "theorem arbitraryConjunction (p q : Prop) (h : ¬(p ∧ q)) (hp : p) : ¬q := by omega",
    "theorem arbitraryImplication (p : Prop) (n : Nat) (h : p → n < 4) (hp : p) : n < 4 := by omega",
    "theorem embeddedLet (x : Int) (h : x ≤ 3) : (let y := x + 2; y) ≤ 5 := by omega",
    "theorem impossible (n : Nat) : n + 1 ≤ n := by omega",
    "theorem strictGap (x y : Int) (h : x ≤ y) : x + 1 ≤ y := by omega",
    "theorem nonlinear (x : Int) : 0 ≤ x * x := by omega",
    "theorem missingHypothesis (p : Prop) : p := by omega",
    "def hiddenSuccessor (n : Nat) : Nat := n + 1\ntheorem hiddenBody (n : Nat) : n < hiddenSuccessor n := by omega",
    "def customOrder : LE Nat := ⟨fun _ _ => True⟩\ntheorem customDictionary (n : Nat) (h : @LE.le Nat customOrder (n + 1) n) : False := by omega",
    "theorem extraTactic (n : Nat) : n = n := by\n  try omega\n  rfl",
    "theorem divisionRawConstant (n : Nat) : Nat.div n 7 ≤ n := by omega",
    "theorem divisionRawZero (n : Nat) : Nat.div n 0 = 0 := by omega",
    "theorem divisionVariable (n k : Nat) (h : 0 < k) : n / k ≤ n := by omega",
    "theorem divisionIdentityVariable (n k : Nat) : k * (n / k) + n % k = n := by omega",
    "theorem falseQuotientBound (n : Nat) : n / 7 < n := by omega",
    "theorem falseRemainderValue (n : Nat) : n % 7 = 0 := by omega",
    "theorem remainderVariable (n k : Nat) (h : 0 < k) : n % k < k := by omega",
    "theorem remainderRawConstant (n : Nat) : Nat.mod n 7 < 7 := by omega",
    "theorem remainderVariableZero (n k : Nat) (h : k = 0) : n % k = n := by omega",
    "theorem remainderRawZero (n : Nat) : Nat.mod n 0 = n := by omega",
    "theorem divisorAlgebraicCancellation (n k : Nat) : n % (k - k + 7) < 7 := by omega",
    "theorem divisorZeroMultiple (n k : Nat) : n % (k * 0 + 7) < 7 := by omega",
    "theorem divisorRawSuccessor (n : Nat) : n % (Nat.succ 6) < 7 := by omega",
    "theorem divisorRawAddition (n : Nat) : n % (Nat.add 2 5) < 7 := by omega",
    "def divisorSeven : Nat := 7\ntheorem divisorNamedDefinition (n : Nat) : n % divisorSeven < 7 := by omega",
    "theorem divisorBeta (n : Nat) : n % ((fun k : Nat => k + 5) 2) < 7 := by omega",
    "theorem nestedRemainderDivisor (n : Nat) : n % (10 % 7) < 3 := by omega",
    "theorem rawZeroDivisor (n : Nat) : n % Nat.zero = n := by omega",
    "theorem tacticLetDivisor (n : Nat) : n % 7 < 7 := by\n  let k : Nat := 7\n  have bound : n % k < 7 := by omega\n  exact bound",
    "theorem tacticHaveDivisor (n : Nat) : n % 7 < 7 := by\n  have k : Nat := 7\n  have bound : n % k < 7 := by omega\n  exact bound",
    "theorem tacticLetArithmeticDivisor (n : Nat) : n % 7 < 7 := by\n  let k : Nat := 2\n  have bound : n % (k + 5) < 7 := by omega\n  exact bound",
    "theorem divisorLetBeforeForall : let k : Nat := 7; ∀ n : Nat, n % k < 7 := by omega",
    "theorem divisorLetBeforeImplication (n : Nat) : let k : Nat := 7; n < 20 → n % k < 7 := by omega",
    "theorem divisorLetBeforeNot (n : Nat) : let k : Nat := 7; ¬ (n % k ≥ 7) := by omega",
    "theorem divisorLetBeforeNe (n : Nat) : let k : Nat := 7; n % k ≠ 7 := by omega",
    "theorem intRawQuotient (x : Int) : 7 * Int.ediv x 7 ≤ x := by omega",
    "theorem intRawRemainder (x : Int) : Int.emod x 7 < 7 := by omega",
    "def customMod : Mod Nat := ⟨fun _ _ => 100⟩\ntheorem customModDictionary (n : Nat) : @HMod.hMod Nat Nat Nat (@instHMod Nat customMod) n 7 < 7 := by omega",
    "def customDiv : Div Nat := ⟨fun _ _ => 100⟩\ntheorem customDivDictionary (n : Nat) : 7 * @HDiv.hDiv Nat Nat Nat (@instHDiv Nat customDiv) n 7 ≤ n := by omega",
];

fn assert_refusals(base: &Engine) {
    let mut failures = Vec::new();
    for source in [
        "def customMod : Mod Nat := ⟨fun _ _ => 100⟩\ntheorem customModControl (n : Nat) : @HMod.hMod Nat Nat Nat (@instHMod Nat customMod) n 7 = 100 := rfl",
        "def customDiv : Div Nat := ⟨fun _ _ => 100⟩\ntheorem customDivControl (n : Nat) : @HDiv.hDiv Nat Nat Nat (@instHDiv Nat customDiv) n 7 = 100 := rfl",
        "theorem tacticLetDivisorControl (n : Nat) : n % 7 < 7 := by\n  let k : Nat := 7\n  have bound : n % k < 7 := Nat.mod_lt n (Nat.succ_pos 6)\n  exact bound",
    ] {
        record_case(&mut failures, source.lines().next().unwrap(), || {
            base.check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits()),
            )
            .expect("the divisor control is valid ordinary source")
            .into_complete()
            .expect("the written control proof passes both checker seats");
        });
    }
    record_case(&mut failures, "custom dictionary control", || {
        base.check_source_files(
        &["def customOrder : LE Nat := ⟨fun _ _ => True⟩\ntheorem customOrderControl (n : Nat) : @LE.le Nat customOrder (n + 1) n := True.intro".as_bytes()],
        &KVMap::new(), SourceCheckLimits::new(limits()),
    ).expect("the custom dictionary is valid source and really makes the order proposition true")
        .into_complete().expect("custom dictionary control passes both seats");
    });
    let before = base.logical_root(&KVMap::new());
    for source in REFUSALS {
        eprintln!("omega refusal: {}", source.lines().next().unwrap());
        record_case(&mut failures, source.lines().next().unwrap(), || {
            let refusal = base
                .check_source_files(
                    &[source.as_bytes()],
                    &KVMap::new(),
                    SourceCheckLimits::new(limits()),
                )
                .expect_err("the pin-refused tactic must fail with an ordinary source diagnostic");
            assert!(
                !matches!(
                    refusal.disposition().0,
                    "resource" | "inconclusive" | "internal-fault"
                ),
                "a nonanswer is not evidence of the intended refusal: {source}: {refusal:?}"
            );
            assert_eq!(base.logical_root(&KVMap::new()), before);
        });
    }
    assert_cases_complete(&failures);
}

fn cancelled(_: &[LinearConstraint], _: OmegaLimits) -> OmegaOutcome {
    OmegaOutcome::Inconclusive {
        reason: OmegaInconclusive::Cancelled,
        steps_used: 1,
    }
}

fn exhausted(_: &[LinearConstraint], _: OmegaLimits) -> OmegaOutcome {
    OmegaOutcome::Inconclusive {
        reason: OmegaInconclusive::ResourceLimit {
            resource: OmegaResource::Rows,
            limit: 1,
            observed: 2,
        },
        steps_used: 1,
    }
}

fn malformed(inputs: &[LinearConstraint], _: OmegaLimits) -> OmegaOutcome {
    OmegaOutcome::Unsat {
        certificate: OmegaCertificate {
            version: 1,
            inputs: inputs.to_vec(),
            steps: vec![],
            conclusion: 0,
        },
        steps_used: 1,
    }
}

fn no_contradiction(_: &[LinearConstraint], _: OmegaLimits) -> OmegaOutcome {
    OmegaOutcome::Sat {
        witness: vec![],
        steps_used: 1,
    }
}

fn expanded_proof(inputs: &[LinearConstraint], limits: OmegaLimits) -> OmegaOutcome {
    let OmegaOutcome::Unsat {
        mut certificate,
        steps_used,
    } = fln_anvil::omega::solve(inputs, limits)
    else {
        panic!("the proof-budget fixture must have a native contradiction");
    };
    let one = inputs
        .iter()
        .flat_map(|row| &row.coeffs)
        .map(|coefficient| coefficient.magnitude())
        .find(|magnitude| magnitude.limbs_le() == [1])
        .expect("the proof-budget fixture contains a unit coefficient")
        .clone();
    // Each combination reserves at least 64 + 32 * 5 = 224 proof nodes, even
    // with an empty coefficient vector. Scale the expansion to the actual
    // remaining source budget so numeric replay still has ample work headroom.
    let extra_steps = usize::try_from(limits.max_steps.div_ceil(224))
        .unwrap_or(usize::MAX)
        .saturating_add(32);
    assert!(certificate.steps.len() + extra_steps <= limits.max_rows);
    for _ in 0..extra_steps {
        let parent = certificate.conclusion;
        certificate.steps.push(OmegaStep::Combine {
            left: parent,
            right: parent,
            left_scale: one.clone(),
            right_scale: one.clone(),
        });
        certificate.conclusion = u32::try_from(certificate.steps.len() - 1).unwrap();
    }
    let checked = fln_anvil::omega::check_certificate(inputs, &certificate, limits)
        .expect("expanded certificate is valid and within all numeric checker limits");
    assert!(
        checked
            .last()
            .unwrap()
            .coeffs
            .iter()
            .all(|value| value.is_zero())
    );
    assert!(checked.last().unwrap().bound.is_negative());
    eprintln!(
        "omega proof budget: {} valid certificate steps",
        certificate.steps.len()
    );
    OmegaOutcome::Unsat {
        certificate,
        // Keep the small solver's reported cost: the resource stop must come
        // from the source proof builder's own accounting, not provider fuel.
        steps_used,
    }
}

fn assert_provider_boundary(base: &Engine) {
    // These deliberately faulty accelerators exercise the real source tactic:
    // `try` must not turn cancellation, exhaustion or certificate corruption
    // into a successful rfl fallback. They confer no admission authority.
    let parsed = fln_parse::parse_definition(
        b"theorem boundary (n : Nat) : n = n := by\n  try omega\n  rfl",
    )
    .expect("source parser");
    let mut failures = Vec::new();
    for (provider, cause) in [
        (
            cancelled as fn(&[LinearConstraint], OmegaLimits) -> OmegaOutcome,
            "cancelled",
        ),
        (exhausted, "resource"),
        (malformed, "certificate"),
        (expanded_proof, "proof_resource"),
    ] {
        eprintln!("omega provider boundary: {cause}");
        record_case(&mut failures, cause, || {
            let scope = SourceScope {
                arithmetic: Some(ArithmeticProvider(provider)),
                ..SourceScope::default()
            };
            let result = fln_elab::elaborate_definition_in_scope_with_budget(
                parsed.syntax(),
                base.environment(),
                limits().kernel,
                &scope,
            );
            match (cause, result) {
                (
                    "cancelled",
                    Err(NatDefinitionElabError::Inference(
                        SourceInferenceError::ArithmeticInconclusive(reason),
                    )),
                ) => assert!(matches!(reason.cause, InconclusiveCause::Cancelled { .. })),
                (
                    "resource",
                    Err(NatDefinitionElabError::Inference(
                        SourceInferenceError::ArithmeticInconclusive(reason),
                    )),
                ) => assert!(matches!(
                    reason.cause,
                    InconclusiveCause::ResourceExhausted { .. }
                )),
                (
                    "certificate",
                    Err(NatDefinitionElabError::Inference(SourceInferenceError::Tactic(reason))),
                ) => assert_eq!(
                    reason.to_string(),
                    "native arithmetic returned an invalid certificate"
                ),
                (
                    "proof_resource",
                    Err(NatDefinitionElabError::Inference(SourceInferenceError::ResourceLimit)),
                ) => {}
                (
                    "proof_resource",
                    Err(NatDefinitionElabError::Inference(
                        SourceInferenceError::ArithmeticInconclusive(reason),
                    )),
                ) => assert!(matches!(
                    reason.cause,
                    InconclusiveCause::ResourceExhausted { .. }
                )),
                (_, result) => panic!("{cause} must escape tactic backtracking: {result:?}"),
            }
        });
    }
    record_case(&mut failures, "recoverable unsuccessful search", || {
        let scope = SourceScope {
            arithmetic: Some(ArithmeticProvider(no_contradiction)),
            ..SourceScope::default()
        };
        let fallback = fln_elab::elaborate_definition_in_scope_with_budget(
            parsed.syntax(),
            base.environment(),
            limits().kernel,
            &scope,
        )
        .expect("an ordinary unsuccessful search remains recoverable by try");
        base.admit_declaration(fallback, &KVMap::new(), limits())
            .expect("the written rfl fallback passes both checker seats")
            .into_complete()
            .expect("the fallback is a complete checked proof");
    });
    assert_cases_complete(&failures);
}

const SCOPED_SOURCES: &[&str] = &[
    "namespace OmegaScope\nsection\ntheorem scopedStep (n : Nat) : n < n + 1 := by omega\nend\nend OmegaScope\ntheorem afterScope (n : Nat) : n < n + 2 := by omega",
    "theorem nextFile (n : Nat) : n < n + 3 := by omega",
];

fn assert_scoped_proofs(base: &Engine) {
    let files: Vec<_> = SCOPED_SOURCES
        .iter()
        .map(|source| source.as_bytes())
        .collect();
    let checked = base
        .check_source_files(&files, &KVMap::new(), SourceCheckLimits::new(limits()))
        .expect("arithmetic capability survives namespace, section, and file boundaries")
        .into_complete()
        .expect("scoped arithmetic proofs pass both checker seats");
    assert_eq!(checked.theorems, 3);
    for name in ["OmegaScope.scopedStep", "afterScope", "nextFile"] {
        assert!(checked.engine.environment().contains(&n(name)), "{name}");
    }
    assert!(checked.scope.arithmetic.is_some());
    assert!(matches!(
        base.check_source_files(&[], &KVMap::new(), SourceCheckLimits::new(limits())),
        Err(fln::SourceCheckError::EmptyInput)
    ));
    let empty = base
        .check_source_files(&[b""], &KVMap::new(), SourceCheckLimits::new(limits()))
        .expect("an empty source file preserves runtime capabilities")
        .into_complete()
        .expect("an empty source file completes");
    assert!(empty.scope.arithmetic.is_some());
}

fn assert_module_replay(base: &Engine) {
    let public_files = [
        (
            n("OmegaLibrary"),
            "module\nprelude\npublic import Init.Omega\npublic theorem arithmeticStep (n : Nat) : n < n + 1 := by omega",
        ),
        (
            n("OmegaClient"),
            "module\nprelude\npublic import OmegaLibrary\npublic theorem twiceStep (n : Nat) : n < n + 2 := by omega",
        ),
    ];
    let public_inputs: Vec<_> = public_files
        .iter()
        .map(|(name, source)| SourceModuleInput {
            name,
            source: source.as_bytes(),
        })
        .collect();
    let new_session = || {
        SourceModuleSession::new(
            base.clone(),
            KVMap::new(),
            SourceModuleCheckLimits::new(SourceCheckLimits::new(limits())),
            SourceModuleCacheLimits::default(),
        )
    };
    let mut public_session = new_session();
    let public = public_session
        .check(&public_inputs, &n("OmegaClient"))
        .expect("public module source checking retains native arithmetic")
        .into_complete()
        .expect("public arithmetic proofs pass both checker seats");
    assert_eq!((public.reused_modules, public.elaborated_modules), (0, 2));
    assert!(public.checked.checked.scope.arithmetic.is_some());
    assert!(
        public
            .checked
            .checked
            .engine
            .environment()
            .contains(&n("twiceStep"))
    );
    // Public/private split artifact emission is an existing explicit frontier.
    // Keep its refusal while checking replay through the supported legacy
    // artifact writer; neither route may silently discard module visibility.
    assert!(matches!(
        public_session.compile(
            &public_inputs,
            &n("OmegaClient"),
            OleanWriteBudget::default()
        ),
        Err(fln::source_check::modules::SourceModuleBuildError::Check(
            fln::source_check::modules::SourceModuleCheckError::ImportContext {
                reason: "module-system .olean emission requires public/private split artifacts",
                ..
            }
        ))
    ));
    let files = [
        (
            n("OmegaLibrary"),
            "prelude\nimport Init.Omega\ntheorem arithmeticStep (n : Nat) : n < n + 1 := by omega",
        ),
        (
            n("OmegaClient"),
            "prelude\nimport OmegaLibrary\ntheorem twiceStep (n : Nat) : n < n + 2 := by omega",
        ),
    ];
    let inputs: Vec<_> = files
        .iter()
        .map(|(name, source)| SourceModuleInput {
            name,
            source: source.as_bytes(),
        })
        .collect();
    let mut session = new_session();
    let cold = session
        .compile(&inputs, &n("OmegaClient"), OleanWriteBudget::default())
        .expect("source modules retain their native arithmetic provider")
        .into_complete()
        .expect("cold arithmetic module compilation completes");
    assert_eq!((cold.reused_modules, cold.elaborated_modules), (0, 2));
    assert!(cold.checked.checked.scope.arithmetic.is_some());
    let warm = session
        .compile(&inputs, &n("OmegaClient"), OleanWriteBudget::default())
        .expect("arithmetic proof artifacts replay through both seats")
        .into_complete()
        .expect("warm arithmetic module replay completes");
    assert_eq!((warm.reused_modules, warm.elaborated_modules), (2, 0));
    assert!(warm.checked.checked.scope.arithmetic.is_some());
    assert_eq!(
        cold.checked.checked.engine.logical_root(&KVMap::new()),
        warm.checked.checked.engine.logical_root(&KVMap::new())
    );
}

fn assert_decreasing_proof(base: &Engine) {
    let source = b"def arithmeticCountdown (n : Nat) : Nat :=\n  if h : 0 < n then arithmeticCountdown (n - 1) + 1 else 0\ntermination_by n\ndecreasing_by omega\ndef arithmeticAnswer : Nat := arithmeticCountdown 42";
    let result = base
        .execute_source_definitions(
            &[source],
            &KVMap::new(),
            EngineExecutionLimits::new(limits().kernel),
        )
        .expect("omega discharges checked recursive obligations")
        .into_complete()
        .expect("native recursive computation finishes");
    let values: Vec<_> = result
        .executions
        .iter()
        .filter_map(|execution| fln::closed_vm_value(&execution.exit).expect("normal VM exit"))
        .collect();
    assert_eq!(values, vec![ClosedVmValue::Scalar(42)]);
}

fn assert_ground_divisor_limits(base: &Engine) {
    let before = base.logical_root(&KVMap::new());
    let mut failures = Vec::new();
    for source in [
        "theorem oversizedGroundDivisor (n : Nat) : n % (2 ^ 20000) < 2 ^ 20000 := by\n  try omega",
        "theorem oversizedGroundExponent (n : Nat) : n % (2 ^ (2 ^ 100)) < 2 ^ (2 ^ 100) := by\n  try omega",
    ] {
        record_case(&mut failures, source.lines().next().unwrap(), || {
            let outcome = base
                .check_source_files(
                    &[source.as_bytes()],
                    &KVMap::new(),
                    SourceCheckLimits::new(limits()),
                )
                .expect("oversized ground arithmetic returns a typed nonanswer");
            let fln::Outcome::Inconclusive(reason) = outcome else {
                panic!("try must not swallow the ground divisor resource stop: {outcome:?}");
            };
            let InconclusiveCause::ResourceExhausted { usage } = reason.cause else {
                panic!("the divisor width must stop before exponentiation: {reason:?}");
            };
            assert_eq!(
                usage.allowed,
                OmegaLimits::default().max_coefficient_limbs as u64
            );
            assert!(usage.is_genuine_exhaustion());
            assert_eq!(base.logical_root(&KVMap::new()), before);
        });
    }
    record_case(&mut failures, "ground divisor recovery", || {
        base.check_source_files(
            &[b"theorem divisorRecovery (n : Nat) : n % 7 < 7 := by omega"],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        )
        .expect("a later constant-divisor proof remains usable")
        .into_complete()
        .expect("the recovery proof passes both checker seats");
        assert_eq!(base.logical_root(&KVMap::new()), before);
    });
    assert_cases_complete(&failures);
}

#[test]
fn native_omega_reifies_and_replays_checked_integer_proofs() {
    let Some(lib) = pinned_lib() else {
        eprintln!("SKIP: pinned Reference absent (set FLN_REQUIRE_REFERENCE=1 to fail)");
        return;
    };
    std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(move || {
            let base = import_closure(&lib);
            // Reuse the expensive checked import while reporting independent
            // failures. Every case still contributes to the final hard gate.
            let mut failures = Vec::new();
            for (label, check) in [
                ("proofs", assert_proofs as fn(&Engine)),
                ("scoped proofs", assert_scoped_proofs),
                ("refusals", assert_refusals),
                ("provider boundary", assert_provider_boundary),
                ("ground divisor limits", assert_ground_divisor_limits),
                ("decreasing proof", assert_decreasing_proof),
                ("module replay", assert_module_replay),
            ] {
                eprintln!("omega phase: {label}");
                record_case(&mut failures, label, || check(&base));
            }
            assert_cases_complete(&failures);
        })
        .expect("spawn native arithmetic checking thread")
        .join()
        .expect("native omega gate finishes");
}
