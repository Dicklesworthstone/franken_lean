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
const MUT_STRUCT: &str = "mutual\n  def meven : Nat → Bool\n    | 0 => true\n    | n + 1 => modd n\n  def modd : Nat → Bool\n    | 0 => false\n    | n + 1 => meven n\nend\n";

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

#[test]
fn mutual_structural_reserved_and_auxiliary_names_match_the_pin() {
    // Verified against pinned `lean` v4.32.0 (2026-11-22):
    // Meta/Tactic/FunInd.lean:1500-1520 (`induct`, `induct_unfolding`, `mutual_induct`,
    // `mutual_induct_unfolding`) and structural auxiliary declarations (`_f`, `_sunfold`,
    // `_unsafe_rec`). Well-founded and mutual well-founded end-to-end pin differentials live in
    // `source_mutual_well_founded.rs` where `Init.WFTactics` is imported.
    for (source, message) in [
        (
            format!("{MUT_STRUCT}def meven.mutual_induct : Nat := 1\n"),
            "`meven.mutual_induct` is a reserved name",
        ),
        (
            format!("{MUT_STRUCT}def meven.mutual_induct_unfolding : Nat := 1\n"),
            "`meven.mutual_induct_unfolding` is a reserved name",
        ),
        (
            format!("{MUT_STRUCT}def meven.induct : Nat := 1\n"),
            "`meven.induct` is a reserved name",
        ),
        (
            format!("{MUT_STRUCT}def modd.induct : Nat := 1\n"),
            "`modd.induct` is a reserved name",
        ),
        (
            format!("{MUT_STRUCT}def modd.induct_unfolding : Nat := 1\n"),
            "`modd.induct_unfolding` is a reserved name",
        ),
        (
            format!("{MUT_STRUCT}def meven._sunfold : Nat := 1\n"),
            "`meven._sunfold` has already been declared",
        ),
        (
            format!("{MUT_STRUCT}def meven._f : Nat := 1\n"),
            "`meven._f` has already been declared",
        ),
        (
            format!("{MUT_STRUCT}def meven._unsafe_rec : Nat := 1\n"),
            "`meven._unsafe_rec` has already been declared",
        ),
        (
            format!("{MUT_STRUCT}def modd._sunfold : Nat := 1\n"),
            "`modd._sunfold` has already been declared",
        ),
        (
            format!("{MUT_STRUCT}def modd._f : Nat := 1\n"),
            "`modd._f` has already been declared",
        ),
        (
            format!("{MUT_STRUCT}def modd._unsafe_rec : Nat := 1\n"),
            "`modd._unsafe_rec` has already been declared",
        ),
    ] {
        let error = check(&source).expect_err(&source);
        assert!(error.contains(message), "{source}\n{error}");
    }
    // Pin-verified negative control: only the first member of a mutual block reserves
    // `mutual_induct` / `mutual_induct_unfolding`.
    for source in [
        format!("{MUT_STRUCT}def modd.mutual_induct : Nat := 1\n"),
        format!("{MUT_STRUCT}def modd.mutual_induct_unfolding : Nat := 1\n"),
    ] {
        check(&source).unwrap_or_else(|error| panic!("{source}\n{error}"));
    }
}

#[test]
fn structural_definitions_admit_first_class_sunfold_declarations() {
    use fln_core::expr::ExprNode;
    use fln_core::name::Name;
    use fln_env::constants::{ConstantInfo, DefinitionSafety, ReducibilityHints};

    fn n(path: &str) -> Name {
        Name::from_components(path.split('.'))
    }
    fn has_tag(expr: &fln_core::expr::Expr, tag: &str) -> bool {
        let mut stack = vec![expr];
        while let Some(cur) = stack.pop() {
            match cur.node() {
                ExprNode::MData { data, expr } => {
                    if data.get_bool(&n(tag), false) {
                        return true;
                    }
                    stack.push(expr);
                }
                ExprNode::App { f, a } => {
                    stack.push(a);
                    stack.push(f);
                }
                ExprNode::Lam {
                    binder_type, body, ..
                }
                | ExprNode::ForallE {
                    binder_type, body, ..
                } => {
                    stack.push(body);
                    stack.push(binder_type);
                }
                ExprNode::LetE {
                    type_, value, body, ..
                } => {
                    stack.push(body);
                    stack.push(value);
                    stack.push(type_);
                }
                ExprNode::Proj { expr, .. } => stack.push(expr),
                _ => {}
            }
        }
        false
    }

    let source = format!(
        "{TOWER}\
         def P : Nat → Prop\n  | 0 => True\n  | n + 1 => P n\n\
         def myAdd (x : Nat) : Nat → Nat\n  | 0 => x\n  | n + 1 => Nat.succ (myAdd x n)\n\
         def plain (n : Nat) : Nat := match n with | 0 => 1 | k + 1 => k\n\
         theorem t : ∀ n : Nat, n + 0 = n\n  | 0 => rfl\n  | _ + 1 => rfl\n\
         def propDef : ∀ n : Nat, n = n\n  | 0 => rfl\n  | _ + 1 => rfl\n\
         {MUT_STRUCT}\
         theorem tower_sunfold_0 : Tower._sunfold 0 = Nat := rfl\n\
         theorem p_sunfold_0 : P._sunfold 0 = True := rfl\n\
         theorem add_sunfold_ok : myAdd._sunfold 2 3 = 5 := rfl\n\
         theorem meven_sunfold_ok : meven._sunfold 4 = true := rfl\n\
         theorem modd_sunfold_ok : modd._sunfold 3 = true := rfl\n"
    );
    let checked = engine()
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        )
        .unwrap_or_else(|error| panic!("{source}\n{error}"))
        .into_complete()
        .unwrap();
    let check_cmd = checked
        .engine
        .execute_source_commands_with_checks(
            b"#check @Tower._sunfold\n#check @P._sunfold\n#check @myAdd._sunfold\n#check @meven._sunfold\n#check @modd._sunfold\n",
            &KVMap::new(),
            fln::EngineExecutionLimits::new(limits().kernel),
        )
        .unwrap_or_else(|error| panic!("#check _sunfold failed: {error}"))
        .into_complete()
        .unwrap();
    assert_eq!(check_cmd.checks.len(), 5);
    let env = checked.engine.environment();
    for (owner, sunfold) in [
        ("Tower", "Tower._sunfold"),
        ("P", "P._sunfold"),
        ("myAdd", "myAdd._sunfold"),
        ("meven", "meven._sunfold"),
        ("modd", "modd._sunfold"),
    ] {
        let Some(ConstantInfo::Defn(owner_def)) = env.find(&n(owner)) else {
            panic!("missing owner {owner}");
        };
        let Some(ConstantInfo::Defn(sunfold_def)) = env.find(&n(sunfold)) else {
            panic!("missing admitted {sunfold}");
        };
        assert_eq!(sunfold_def.safety, DefinitionSafety::Safe, "{sunfold}");
        assert!(
            matches!(sunfold_def.hints, ReducibilityHints::Regular(_)),
            "{sunfold}: {:?}",
            sunfold_def.hints
        );
        assert_eq!(
            sunfold_def.base.type_, owner_def.base.type_,
            "{sunfold} type must match owner"
        );
        assert_eq!(sunfold_def.all, vec![n(sunfold)], "{sunfold}");
        assert!(
            has_tag(&sunfold_def.value, "sunfoldMatch"),
            "{sunfold} must carry sunfoldMatch annotation"
        );
        assert!(
            has_tag(&sunfold_def.value, "sunfoldMatchAlt"),
            "{sunfold} must carry sunfoldMatchAlt annotation"
        );
    }
    // Pin `SmartUnfolding.lean:69` negative controls: non-recursive, theorem,
    // and Prop-typed definitions do not admit `_sunfold`.
    for absent in ["plain._sunfold", "t._sunfold", "propDef._sunfold"] {
        assert!(!env.contains(&n(absent)), "{absent} must not be admitted");
    }
}
