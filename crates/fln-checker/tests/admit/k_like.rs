//! KR-317 at typed conversion sites, with independently authored wire fixtures.
//! A K recursor stuck on a major premise that is not a constructor application
//! reduces as if the major were the nullary constructor, when the major's type
//! is definitionally equal to that constructor's (the pin's `to_cnstr_when_K`).
//! whnf applies the rule behind a structural gate with no typing, so a type pair
//! that only structure eta and proof irrelevance close stays stuck there. Found
//! by the whole-Init council frontier: `Fin.addCases_left` was K1-accepted and
//! checker-deferred, on `castLT (castAdd n i) h ≟ i` inside the gate.
#![forbid(unsafe_code)]
use super::*;

fn c(label: &str) -> Expr {
    Expr::const_(primary_name(label), vec![])
}
fn qualified(namespace: &str, leaf: &str) -> Expr {
    Expr::const_(Name::from_components([namespace, leaf]), vec![])
}
fn app(f: Expr, args: impl IntoIterator<Item = Expr>) -> Expr {
    args.into_iter().fold(f, Expr::app)
}
fn bv(index: u32) -> Expr {
    Expr::bvar(index).expect("small bound index")
}
fn pi(domain: Expr, body: Expr) -> Expr {
    Expr::forall_e(primary_name("x"), domain, body, BinderInfo::Default)
}
fn lam(domain: Expr, body: Expr) -> Expr {
    Expr::lam(primary_name("x"), domain, body, BinderInfo::Default)
}
fn ty() -> Expr {
    Expr::sort(Level::one())
}
fn prop() -> Expr {
    Expr::sort(Level::zero())
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
fn keq(alpha: Expr, a: Expr, b: Expr) -> Expr {
    app(c("KEq"), [alpha, a, b])
}
/// `KEq : (α : Type) → α → α → Prop`, a K-like equality: one constructor
/// with no fields, `KEq.refl : (α : Type) → (a : α) → KEq α a a`, and
/// `KEq.rec.{v} : (α : Type) → (a : α) → (motive : (b : α) → KEq α a b →
/// Sort v) → motive a (KEq.refl α a) → (b : α) → (h : KEq α a b) → motive b h`.
fn keq_entries() -> Vec<ConstantEntry> {
    let v = Level::param(primary_name("v"));
    // scope [α, a]: `(b : α) → KEq α a b → Sort v`
    let motive_type = || pi(bv(1), pi(keq(bv(2), bv(1), bv(0)), Expr::sort(v.clone())));
    // scope [α, a, motive]: `motive a (KEq.refl α a)`
    let minor_type = || {
        app(
            bv(0),
            [bv(1), app(qualified("KEq", "refl"), [bv(2), bv(1)])],
        )
    };
    let recursor_type = pi(
        ty(),
        pi(
            bv(0),
            pi(
                motive_type(),
                pi(
                    minor_type(),
                    // scope [α, a, motive, minor]: `(b : α) → (h : KEq α a b) → motive b h`
                    pi(
                        bv(3),
                        pi(keq(bv(4), bv(3), bv(0)), app(bv(3), [bv(1), bv(0)])),
                    ),
                ),
            ),
        ),
    );
    let rule = lam(
        ty(),
        lam(bv(0), lam(motive_type(), lam(minor_type(), bv(0)))),
    );
    vec![
        ConstantEntry::new(
            checker_name("KEq"),
            ConstantDeclaration::inductive(
                vec![],
                decoded(&pi(ty(), pi(bv(0), pi(bv(1), prop())))),
                ConstantSafety::Safe,
                InductiveDeclaration::new(
                    2,
                    1,
                    vec![checker_name("KEq")],
                    vec![checker_qualified(&["KEq", "refl"])],
                    0,
                    false,
                    false,
                ),
            ),
        ),
        ConstantEntry::new(
            checker_qualified(&["KEq", "refl"]),
            ConstantDeclaration::constructor(
                vec![],
                decoded(&pi(ty(), pi(bv(0), keq(bv(1), bv(0), bv(0))))),
                ConstantSafety::Safe,
                ConstructorDeclaration::new(checker_name("KEq"), 0, 2, 0),
            ),
        ),
        ConstantEntry::new(
            checker_qualified(&["KEq", "rec"]),
            ConstantDeclaration::recursor(
                vec![checker_name("v")],
                decoded(&recursor_type),
                ConstantSafety::Safe,
                RecursorDeclaration::new(
                    vec![checker_name("KEq")],
                    2,
                    1,
                    1,
                    1,
                    vec![RecursorRule::new(
                        checker_qualified(&["KEq", "refl"]),
                        0,
                        decoded(&rule),
                    )],
                    true,
                ),
            ),
        ),
    ]
}
/// `S.mk : A → Pp → S`, a structure with a data field and a proof field.
fn structure_entries() -> Vec<ConstantEntry> {
    vec![
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
    ]
}
/// `S.mk first proof`.
fn rebuilt_with(first: Expr, proof: &str) -> Expr {
    app(qualified("S", "mk"), [first, c(proof)])
}
/// `S.mk first p`.
fn rebuilt(first: Expr) -> Expr {
    rebuilt_with(first, "p")
}
/// `x.1`, the data field of `x : S`.
fn first_of_x() -> Expr {
    Expr::proj(primary_name("S"), 0, c("x"))
}
/// `KEq.rec (motive := fun b _ => C) w x major` with `a := S.mk first proof`:
/// of type `C`, and reducing to `w` only by K.
fn cast_with(first: Expr, proof: &str, major: &str) -> Expr {
    let a = rebuilt_with(first, proof);
    app(
        Expr::const_(Name::from_components(["KEq", "rec"]), vec![Level::one()]),
        [
            c("S"),
            a.clone(),
            lam(c("S"), lam(keq(c("S"), a, bv(0)), c("C"))),
            c("w"),
            c("x"),
            c(major),
        ],
    )
}
fn cast(first: Expr, major: &str) -> Expr {
    cast_with(first, "p", major)
}
fn environment() -> ConstantEnvironment {
    let mut rows = vec![
        axiom("A", ty()),
        axiom("Pp", prop()),
        axiom("p", c("Pp")),
        axiom("q", c("Pp")),
        axiom("a0", c("A")),
        axiom("C", ty()),
        axiom("w", c("C")),
        axiom("F", pi(c("C"), ty())),
        axiom("wF", app(c("F"), [c("w")])),
    ];
    rows.extend(keq_entries());
    rows.extend(structure_entries());
    rows.extend([
        axiom("x", c("S")),
        axiom("h", keq(c("S"), rebuilt(first_of_x()), c("x"))),
        axiom("h_other", keq(c("S"), rebuilt(c("a0")), c("x"))),
        axiom("h_other_q", keq(c("S"), rebuilt_with(c("a0"), "q"), c("x"))),
        axiom("wF_q", app(c("F"), [cast_with(c("a0"), "q", "h_other_q")])),
    ]);
    environment_of(rows)
}

/// `wF : F w` at `F (KEq.rec … w x h)`: the cast reduces to `w` once the
/// major's type `KEq S (S.mk x.1 p) x` converts with the constructor's
/// `KEq S (S.mk x.1 p) (S.mk x.1 p)`, which needs `x ≟ S.mk x.1 p`: structure
/// eta, with the proof field `x.2 ≟ p` closed only by proof irrelevance.
#[test]
fn a_k_recursor_reduces_when_the_major_type_converts_only_with_types() {
    let env = environment();
    let candidate = definition(
        "k_cast",
        decoded(&app(c("F"), [cast(first_of_x(), "h")])),
        decoded(&c("wF")),
    );
    let outcome = admit(&env, &candidate, AdmissionBudget::unlimited());
    assert!(matches!(outcome, Verdict::Admitted(_)), "{outcome:?}");
}

/// With `a := S.mk a0 p` for an unrelated `a0`, the major's type does not
/// convert with the constructor's, so K must not fire and nothing converts.
#[test]
fn a_k_recursor_stays_stuck_when_the_major_type_differs() {
    let env = environment();
    let candidate = definition(
        "k_cast_other",
        decoded(&app(c("F"), [cast(c("a0"), "h_other")])),
        decoded(&c("wF")),
    );
    let outcome = admit(&env, &candidate, AdmissionBudget::unlimited());
    assert!(
        !matches!(outcome, Verdict::Admitted(_)),
        "a cast whose indices differ must not reduce: {outcome:?}"
    );
}

/// Two casts whose K gate fails (`S.mk a0 _ ≢ x`) but which agree by
/// congruence: `S.mk a0 p` against `S.mk a0 q`, and the two major proofs,
/// differ only in proofs of one proposition. The pin fires K only inside whnf
/// once its gate succeeds, so an unmet gate must leave the pair to congruence;
/// a lane that let the failed gate fail the pair missed `Quotient.rec` in
/// Init.Core (found by whole-Init frontier run 10, never committed).
#[test]
fn an_unmet_k_gate_leaves_the_pair_to_congruence() {
    let env = environment();
    let candidate = definition(
        "k_congruence",
        decoded(&app(c("F"), [cast(c("a0"), "h_other")])),
        decoded(&c("wF_q")),
    );
    let outcome = admit(&env, &candidate, AdmissionBudget::unlimited());
    assert!(matches!(outcome, Verdict::Admitted(_)), "{outcome:?}");
}
