//! `| p₁ | p₂ => rhs`, one alternative with two pattern groups, in the seed world: as the pin's
//! `expandMatchAlt` (vendored `Lean/Elab/BindersUtil.lean`), it is `| p₁ => rhs` and
//! `| p₂ => rhs`, in a term `match`, in equations and over two columns. A name one group binds
//! and another does not is unbound in that copy. These are the shapes of `fln-cli`'s
//! `source_match_alternative_groups`, which runs each program through the pinned `lean` v4.32.0
//! first, here without imports so they also run where the pin is absent.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, SourceCheckLimits};

fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}
fn check(source: &str) -> Result<(), String> {
    let engine = Engine::with_source_seed(limits())
        .unwrap()
        .into_complete()
        .unwrap();
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

const MATCH: &str = "def g (n : Nat) : Nat := match n with\n  | 0 | 1 => 1\n  | _ => 2\n";
const EQUATIONS: &str = "def h : Nat → Bool\n  | 0 | 2 => true\n  | _ => false\n";
const COLUMNS: &str = "inductive Opt where\n  | some (n : Nat)\n  | none\n\
                       def leaf (o : Opt) (b : Bool) : Bool := match o, b with\n  \
                       | Opt.none, _ | _, true => true\n  | Opt.some _, false => false\n";

#[test]
fn each_group_is_an_alternative_with_the_same_right_hand_side() {
    for source in [
        format!(
            "{MATCH}theorem t : g 0 = 1 := rfl\ntheorem u : g 1 = 1 := rfl\ntheorem v : g 5 = 2 := rfl\n"
        ),
        format!(
            "{EQUATIONS}theorem t : h 2 = true := rfl\ntheorem u : h 0 = true := rfl\ntheorem v : h 1 = false := rfl\n"
        ),
        format!(
            "{COLUMNS}theorem t : leaf Opt.none false = true := rfl\n\
                 theorem u : leaf (Opt.some 1) true = true := rfl\n\
                 theorem v : leaf (Opt.some 1) false = false := rfl\n"
        ),
    ] {
        check(&source).unwrap_or_else(|error| panic!("{source}: {error}"));
    }
    for source in [
        format!("{MATCH}theorem t : g 1 = 2 := rfl\n"),
        format!("{EQUATIONS}theorem t : h 1 = true := rfl\n"),
        format!("{COLUMNS}theorem t : leaf (Opt.some 1) true = false := rfl\n"),
        // `x` is bound by the first group only.
        "inductive Opt where\n  | some (n : Nat)\n  | none\n\
         def g (o : Opt) : Nat := match o with\n  | Opt.some x | Opt.none => x\n"
            .to_owned(),
    ] {
        assert!(check(&source).is_err(), "accepted {source}");
    }
}
