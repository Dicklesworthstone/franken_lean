//! Reserved declaration names, as the pin refuses them: `checkNotAlreadyDeclared`
//! (Lean/Elab/DeclModifiers.lean:29-55) over the ported `registerReservedNamePredicate`
//! predicates, and `ensureEqnReservedNamesAvailable` (Lean/Meta/Eqns.lean:89-92). Every program
//! here was run through the pinned `lean` v4.32.0 first (2026-10-11); a refusal quotes its message.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, SourceCheckLimits};

fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}
fn engine() -> Engine {
    Engine::with_source_seed(limits())
        .unwrap()
        .into_complete()
        .unwrap()
}
fn check(source: &str) -> Result<(), String> {
    match engine().check_source_files(
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

const TOWER: &str = "def Tower : Nat → Type\n  | 0 => Nat\n  | n + 1 => Tower n → Tower n\n";

#[test]
fn a_reserved_name_is_refused_with_the_pins_message() {
    for (source, message) in [
        // Meta/Eqns.lean: equation names of a safe definition, abbreviation, instance or
        // projection, whatever the declaration that takes them.
        (
            "def f : Nat := 1\ndef f.eq_1 : Nat := 1\n",
            "`f.eq_1` is a reserved name",
        ),
        (
            "def f : Nat := 1\ndef f.eq_0 : Nat := 1\n",
            "`f.eq_0` is a reserved name",
        ),
        (
            "def f : Nat := 1\ndef f.eq_1_0 : Nat := 1\n",
            "`f.eq_1_0` is a reserved name",
        ),
        (
            "def f : Nat := 1\ndef f.eq_def : Nat := 1\n",
            "`f.eq_def` is a reserved name",
        ),
        (
            "def f : Nat := 1\ndef f.eq_unfold : Nat := 1\n",
            "`f.eq_unfold` is a reserved name",
        ),
        (
            "abbrev a : Nat := 1\ndef a.eq_1 : Nat := 1\n",
            "`a.eq_1` is a reserved name",
        ),
        (
            "instance i : Inhabited Nat := ⟨1⟩\ndef i.eq_1 : Nat := 1\n",
            "`i.eq_1` is a reserved name",
        ),
        (
            "structure S where\n  x : Nat\ndef S.x.eq_1 : Nat := 1\n",
            "`S.x.eq_1` is a reserved name",
        ),
        (
            "def f : Nat := 1\naxiom f.eq_1 : Nat\n",
            "`f.eq_1` is a reserved name",
        ),
        (
            "def f : Nat := 1\ninductive f.eq_1 where | a\n",
            "`f.eq_1` is a reserved name",
        ),
        (
            "def f : Nat := 1\nstructure f.eq_1 where\n  x : Nat\n",
            "`f.eq_1` is a reserved name",
        ),
        (
            "def f : Nat := 1\nnamespace f\ndef eq_1 : Nat := 1\nend f\n",
            "`f.eq_1` is a reserved name",
        ),
        // Meta/Tactic/FunInd.lean: `fun_cases` of any safe definition, `induct` of a
        // structurally recursive one.
        (
            "def f : Nat := 1\ndef f.fun_cases : Nat := 1\n",
            "`f.fun_cases` is a reserved name",
        ),
        (
            "def f : Nat := 1\ndef f.fun_cases_unfolding : Nat := 1\n",
            "`f.fun_cases_unfolding` is a reserved name",
        ),
        (
            &format!("{TOWER}def Tower.induct : Nat := 1\n"),
            "`Tower.induct` is a reserved name",
        ),
        (
            &format!("{TOWER}def Tower.induct_unfolding : Nat := 1\n"),
            "`Tower.induct_unfolding` is a reserved name",
        ),
        // Meta/Injective.lean: `hinj` of a constructor.
        (
            "inductive T where | a\ndef T.a.hinj : Nat := 1\n",
            "`T.a.hinj` is a reserved name",
        ),
        // Meta/CongrTheorems.lean: `hcongr_<n>` and `congr_simp` of any constant.
        (
            "def Nat.congr_simp : Nat := 1\n",
            "`Nat.congr_simp` is a reserved name",
        ),
        (
            "def f : Nat := 1\ndef f.hcongr_1 : Nat := 1\n",
            "`f.hcongr_1` is a reserved name",
        ),
        (
            "theorem t : 1 = 1 := rfl\ndef t.congr_simp : Nat := 1\n",
            "`t.congr_simp` is a reserved name",
        ),
        (
            "inductive T where | a\ndef T.rec.congr_simp : Nat := 1\n",
            "`T.rec.congr_simp` is a reserved name",
        ),
    ] {
        let error = check(source).expect_err(source);
        assert!(error.contains(message), "{source}\n{error}");
    }
}

#[test]
fn a_structural_definitions_auxiliaries_are_already_declared() {
    // The pin declares `_f`, `_sunfold` and `_unsafe_rec` beside every structurally recursive
    // definition, a `Prop`-valued one included.
    let equations = "def eqns : Nat → Nat\n  | 0 => 0\n  | n + 1 => eqns n\n";
    let predicate = "def P : Nat → Prop\n  | 0 => True\n  | n + 1 => P n\n";
    for (source, message) in [
        (
            format!("{TOWER}def Tower._sunfold : Nat := 1\n"),
            "`Tower._sunfold` has already been declared",
        ),
        (
            format!("{TOWER}def Tower._f : Nat := 1\n"),
            "`Tower._f` has already been declared",
        ),
        (
            format!("{TOWER}def Tower._unsafe_rec : Nat := 1\n"),
            "`Tower._unsafe_rec` has already been declared",
        ),
        (
            format!("{TOWER}namespace Tower\ndef _sunfold : Nat := 1\nend Tower\n"),
            "`Tower._sunfold` has already been declared",
        ),
        (
            format!("{equations}def eqns._f : Nat := 1\n"),
            "`eqns._f` has already been declared",
        ),
        (
            format!("{predicate}def P._sunfold : Nat := 1\n"),
            "`P._sunfold` has already been declared",
        ),
    ] {
        let error = check(&source).expect_err(&source);
        assert!(error.contains(message), "{source}\n{error}");
    }
    // A nonrecursive definition and a structurally recursive theorem have none of them.
    for source in [
        "def plain (n : Nat) : Nat := match n with | 0 => 1 | k + 1 => k\n\
         def plain._sunfold : Nat := 1\ndef plain._f : Nat := 1\ndef plain._unsafe_rec : Nat := 1\n"
            .to_owned(),
        "theorem t : ∀ n : Nat, n + 0 = n\n  | 0 => rfl\n  | n + 1 => rfl\ndef t._sunfold : Nat := 1\n"
            .to_owned(),
        format!("{TOWER}def Tower._g : Nat := 1\ndef Tower.sunfold : Nat := 1\n"),
    ] {
        check(&source).unwrap_or_else(|error| panic!("{source}\n{error}"));
    }
}

#[test]
fn a_definition_whose_equation_name_is_taken_is_refused() {
    for (source, message) in [
        (
            "def f.eq_1 : Nat := 1\ndef f : Nat := 1\n",
            "failed to declare `f` because `f.eq_1` has already been declared",
        ),
        (
            "def f.eq_def : Nat := 1\ndef f : Nat := 1\n",
            "failed to declare `f` because `f.eq_def` has already been declared",
        ),
        (
            "def a.eq_unfold : Nat := 1\nabbrev a : Nat := 1\n",
            "failed to declare `a` because `a.eq_unfold` has already been declared",
        ),
        (
            "def t.eq_1 : Nat := 1\ntheorem t : 1 = 1 := rfl\n",
            "failed to declare `t` because `t.eq_1` has already been declared",
        ),
        (
            "def i.eq_def : Nat := 1\ninstance i : Inhabited Nat := ⟨1⟩\n",
            "failed to declare `i` because `i.eq_def` has already been declared",
        ),
        (
            "def o.eq_1 : Nat := 1\nopaque o : Nat\n",
            "failed to declare `o` because `o.eq_1` has already been declared",
        ),
    ] {
        let error = check(source).expect_err(source);
        assert!(error.contains(message), "{source}\n{error}");
    }
}

#[test]
fn names_no_predicate_claims_stay_free() {
    for source in [
        // A theorem or an opaque constant has no equation or `fun_cases` names.
        "theorem t : 1 = 1 := rfl\ndef t.eq_1 : Nat := 1\n",
        "theorem t : 1 = 1 := rfl\ndef t.fun_cases : Nat := 1\n",
        "opaque o : Nat\ndef o.eq_1 : Nat := 1\n",
        // An inductive type is not a definition, and only a constructor has `hinj`.
        "inductive T where | a\ndef T.eq_1 : Nat := 1\n",
        "inductive T where | a\ndef T.a.eq_1 : Nat := 1\n",
        "inductive T where | a\ndef T.hinj : Nat := 1\n",
        // `induct` needs recursion; `congr_simp` needs an existing constant.
        "def f : Nat := 1\ndef f.induct : Nat := 1\n",
        "def g.congr_simp : Nat := 1\n",
        // Suffixes that are not `eq_`/`hcongr_` followed by `String.isNat` digits.
        "def f : Nat := 1\ndef f.eq_x : Nat := 1\ndef f.eq_ : Nat := 1\ndef f.eq_1_ : Nat := 1\ndef f.hcongr_ : Nat := 1\n",
        // Only `eq_1` of the indexed names is checked before a definition, and never before an
        // axiom or an inductive type.
        "def f.eq_2 : Nat := 1\ndef f : Nat := 1\n",
        "def x.eq_1 : Nat := 1\naxiom x : Nat\n",
        "def T.eq_1 : Nat := 1\ninductive T where | a\n",
        "def S.eq_1 : Nat := 1\nstructure S where\n  x : Nat\n",
        // A structure field named like a reserved suffix is not checked as a declaration.
        "structure S where\n  congr_simp : Nat\n",
    ] {
        check(source).unwrap_or_else(|error| panic!("{source}\n{error}"));
    }
}
