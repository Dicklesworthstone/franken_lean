//! KR-312 structure eta at typed conversion sites, with independently authored
//! wire fixtures. A full application of a structure's constructor converts with
//! a term that is not one when their types do and every field converts with the
//! matching projection (the pin's `try_eta_struct_core`). Found by the
//! whole-Init council frontier: `PostconditionT.operation_bind_eq_operation_bind_mk`
//! (`x ≟ Subtype.mk P x.val x.property`) and `Nat.decidableExistsFin._proof_1`
//! (`x ≟ Fin.mk n x.val h`) were K1-accepted and checker-deferred.
#![forbid(unsafe_code)]
use super::*;

fn c(label: &str) -> Expr {
    Expr::const_(primary_name(label), vec![])
}
fn app(f: Expr, args: impl IntoIterator<Item = Expr>) -> Expr {
    args.into_iter().fold(f, Expr::app)
}
fn pi(domain: Expr, body: Expr) -> Expr {
    Expr::forall_e(primary_name("x"), domain, body, BinderInfo::Default)
}
fn axiom(label: &str, ty: Expr) -> ConstantEntry {
    ConstantEntry::new(
        checker_name(label),
        header(
            vec![],
            decoded(&ty),
            ConstantKind::Axiom,
            ConstantSafety::Safe,
        ),
    )
}
fn ty() -> Expr {
    Expr::sort(Level::one())
}
fn mk() -> Expr {
    Expr::const_(Name::str(Name::str(Name::anonymous(), "S"), "mk"), vec![])
}
/// `x.1`, the data field of `x : S`.
fn val_of_x() -> Expr {
    Expr::proj(primary_name("S"), 0, c("x"))
}
/// `S`, a non-recursive structure with a data field and a proof field:
/// `S.mk : A → Pp → S`.
fn environment() -> ConstantEnvironment {
    environment_of(vec![
        axiom("A", ty()),
        axiom("Pp", Expr::sort(Level::zero())),
        axiom("p", c("Pp")),
        axiom("a0", c("A")),
        ConstantEntry::new(
            checker_name("S"),
            ConstantDeclaration::inductive(
                vec![],
                decoded(&ty()),
                ConstantSafety::Safe,
                InductiveDeclaration::new(
                    0,
                    0,
                    vec![checker_name("S")],
                    vec![checker_qualified(&["S", "mk"])],
                    0,
                    false,
                    false,
                ),
            ),
        ),
        ConstantEntry::new(
            checker_qualified(&["S", "mk"]),
            ConstantDeclaration::constructor(
                vec![],
                decoded(&pi(c("A"), pi(c("Pp"), c("S")))),
                ConstantSafety::Safe,
                ConstructorDeclaration::new(checker_name("S"), 0, 0, 2),
            ),
        ),
        // `PS α`, the same shape behind one parameter, as `Subtype` and `Fin`
        // are: `PS.mk : (α : Type) → α → Pp → PS α`. A field index that forgot
        // to skip the parameters would compare the wrong argument.
        ConstantEntry::new(
            checker_name("PS"),
            ConstantDeclaration::inductive(
                vec![],
                decoded(&pi(ty(), ty())),
                ConstantSafety::Safe,
                InductiveDeclaration::new(
                    1,
                    0,
                    vec![checker_name("PS")],
                    vec![checker_qualified(&["PS", "mk"])],
                    0,
                    false,
                    false,
                ),
            ),
        ),
        ConstantEntry::new(
            checker_qualified(&["PS", "mk"]),
            ConstantDeclaration::constructor(
                vec![],
                decoded(&pi(
                    ty(),
                    pi(
                        Expr::bvar(0).expect("parameter"),
                        pi(c("Pp"), app(c("PS"), [Expr::bvar(2).expect("parameter")])),
                    ),
                )),
                ConstantSafety::Safe,
                ConstructorDeclaration::new(checker_name("PS"), 0, 1, 2),
            ),
        ),
        axiom("y", app(c("PS"), [c("A")])),
        axiom("TP", pi(app(c("PS"), [c("A")]), ty())),
        axiom("wp", app(c("TP"), [c("y")])),
        axiom("x", c("S")),
        axiom("T", pi(c("S"), ty())),
        axiom("w", app(c("T"), [c("x")])),
        axiom("w_mk", app(c("T"), [app(mk(), [val_of_x(), c("p")])])),
    ])
}

/// `x ≟ S.mk x.1 p`: the data field converts by projection, and the proof
/// field `x.2 ≟ p` only by proof irrelevance, which needs typing, so the
/// untyped converter cannot close it.
#[test]
fn a_value_converts_with_its_constructor_rebuild_in_both_orientations() {
    let env = environment();
    let rebuilt = app(mk(), [val_of_x(), c("p")]);
    let ps_mk = Expr::const_(Name::str(Name::str(Name::anonymous(), "PS"), "mk"), vec![]);
    let rebuilt_y = app(
        ps_mk,
        [c("A"), Expr::proj(primary_name("PS"), 0, c("y")), c("p")],
    );
    for (label, declared, value) in [
        ("rebuild_declared", app(c("T"), [rebuilt]), c("w")),
        ("rebuild_value", app(c("T"), [c("x")]), c("w_mk")),
        ("parameterized", app(c("TP"), [rebuilt_y]), c("wp")),
    ] {
        let candidate = definition(label, decoded(&declared), decoded(&value));
        let outcome = admit(&env, &candidate, AdmissionBudget::unlimited());
        assert!(
            matches!(outcome, Verdict::Admitted(_)),
            "{label}: {outcome:?}"
        );
    }
}

/// `x ≟ S.mk a0 p` with an unrelated `a0`: structure eta must still compare
/// the data field, so it must not convert.
#[test]
fn structure_eta_compares_every_field() {
    let env = environment();
    let candidate = definition(
        "wrong_field",
        decoded(&app(c("T"), [app(mk(), [c("a0"), c("p")])])),
        decoded(&c("w")),
    );
    let outcome = admit(&env, &candidate, AdmissionBudget::unlimited());
    assert!(
        !matches!(outcome, Verdict::Admitted(_)),
        "a constructor whose data field differs must not convert: {outcome:?}"
    );
}
