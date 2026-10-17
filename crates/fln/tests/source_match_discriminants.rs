//! A `match` on a local, in the seed world: as the pin's match elaborator (vendored
//! `Lean/Elab/Match.lean`, `generalize` and the motive), the discriminant stays in scope in the
//! branches, a `let` before the match may read it, and an expected type that mentions it refines
//! it. A guard for those shapes without imports, so it also runs where the pin is absent. The
//! refinement rule itself (refine only what the motive or a later local mentions) is measured
//! against the pinned `lean` v4.32.0 in `fln-cli`'s `source_match_discriminants`. This seed world
//! accepts these programs either way.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, SourceCheckLimits};

const OPT: &str = "inductive Opt where\n  | some (n : Nat)\n  | none\n\
                   def Opt.getD : Opt → Nat → Nat\n  | Opt.some n, _ => n\n  | Opt.none, d => d\n";

fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}
fn check(program: &str) -> Result<(), String> {
    let engine = Engine::with_source_seed(limits())
        .unwrap()
        .into_complete()
        .unwrap();
    let source = format!("{OPT}{program}");
    match engine.check_source_files(
        &[source.as_bytes()],
        &KVMap::new(),
        SourceCheckLimits::new(limits()),
    ) {
        Ok(outcome) => {
            outcome.into_complete().unwrap();
            Ok(())
        }
        Err(error) => Err(error.to_string()),
    }
}

#[test]
fn the_discriminant_stays_in_scope() {
    for program in [
        "def g (o : Opt) : Nat := match o with\n  | Opt.some n => n + o.getD 0\n  | Opt.none => 0\n\
         theorem t : g (Opt.some 2) = 4 := rfl\ntheorem u : g Opt.none = 0 := rfl\n",
        "def g (o : Opt) : Nat :=\n  let k := o.getD 5\n  match o with\n  | Opt.some n => n + k\n  | Opt.none => k\n\
         theorem t : g Opt.none = 5 := rfl\ntheorem u : g (Opt.some 1) = 2 := rfl\n",
        "def g (o : Opt) : o = o := match o with\n  | Opt.some _ => rfl\n  | Opt.none => rfl\n",
    ] {
        check(program).unwrap_or_else(|error| panic!("{program}: {error}"));
    }
    let wrong = "def g (o : Opt) : Nat := match o with\n  | Opt.some n => n + o.getD 0\n  | Opt.none => 0\n\
                 theorem t : g (Opt.some 2) = 2 := rfl\n";
    assert!(check(wrong).is_err(), "accepted {wrong}");
}
