//! KR-315 (unit-like eta) at typed conversion sites, with independently authored
//! wire fixtures. Two values of a one-constructor, zero-field, non-recursive,
//! index-free inductive type are convertible exactly when their types are
//! (the pin's `is_def_eq_unit_like`). Found by the whole-Init council frontier:
//! `PUnit.ext_iff` in Init.Ext was K1-accepted and checker-deferred.
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
/// An inductive `label` of type `ty` with `ctors`: each constructor row is
/// (leaf name, type, field count). Parameters and indices as given.
fn inductive(
    label: &str,
    ty: Expr,
    parameters: u32,
    indices: u32,
    ctors: &[(&str, Expr, u32)],
) -> Vec<ConstantEntry> {
    let mut rows = vec![ConstantEntry::new(
        checker_name(label),
        ConstantDeclaration::inductive(
            vec![],
            decoded(&ty),
            ConstantSafety::Safe,
            InductiveDeclaration::new(
                parameters,
                indices,
                vec![checker_name(label)],
                ctors
                    .iter()
                    .map(|(leaf, _, _)| checker_qualified(&[label, leaf]))
                    .collect(),
                0,
                false,
                false,
            ),
        ),
    )];
    for (index, (leaf, ctor_type, fields)) in ctors.iter().enumerate() {
        rows.push(ConstantEntry::new(
            checker_qualified(&[label, leaf]),
            ConstantDeclaration::constructor(
                vec![],
                decoded(ctor_type),
                ConstantSafety::Safe,
                ConstructorDeclaration::new(checker_name(label), index as u32, parameters, *fields),
            ),
        ));
    }
    rows
}
fn ty() -> Expr {
    Expr::sort(Level::one())
}
fn environment() -> ConstantEnvironment {
    let mut rows = vec![axiom("A", ty()), axiom("a0", c("A"))];
    // Unit-like: U, and the parameterized W α.
    rows.extend(inductive("U", ty(), 0, 0, &[("mk", c("U"), 0)]));
    rows.extend(inductive(
        "W",
        pi(ty(), ty()),
        1,
        0,
        &[("mk", pi(ty(), app(c("W"), [Expr::bvar(0).unwrap()])), 0)],
    ));
    // Not unit-like: one field, two constructors, an index.
    rows.extend(inductive("V", ty(), 0, 0, &[("mk", pi(c("A"), c("V")), 1)]));
    rows.extend(inductive(
        "B",
        ty(),
        0,
        0,
        &[("t", c("B"), 0), ("f", c("B"), 0)],
    ));
    rows.extend(inductive(
        "I",
        pi(c("A"), ty()),
        0,
        1,
        &[("mk", app(c("I"), [c("a0")]), 0)],
    ));
    // Two opaque values of each type, a family over it, and a witness at the first.
    for (tag, carrier) in [
        ("U", c("U")),
        ("W", app(c("W"), [c("A")])),
        ("V", c("V")),
        ("B", c("B")),
        ("I", app(c("I"), [c("a0")])),
    ] {
        rows.push(axiom(&format!("{tag}1"), carrier.clone()));
        rows.push(axiom(&format!("{tag}2"), carrier.clone()));
        rows.push(axiom(&format!("T{tag}"), pi(carrier.clone(), ty())));
        rows.push(axiom(
            &format!("w{tag}"),
            app(c(&format!("T{tag}")), [c(&format!("{tag}1"))]),
        ));
        rows.push(axiom(
            &format!("consume{tag}"),
            pi(app(c(&format!("T{tag}")), [c(&format!("{tag}2"))]), c("A")),
        ));
    }
    environment_of(rows)
}
/// `final_<tag> : T<tag> <tag>2 := w<tag>`, where `w<tag> : T<tag> <tag>1`: a
/// body conversion that holds only by KR-315.
fn body_candidate(tag: &str) -> ConstantEntry {
    definition(
        &format!("final_{tag}"),
        decoded(&app(c(&format!("T{tag}")), [c(&format!("{tag}2"))])),
        decoded(&c(&format!("w{tag}"))),
    )
}
/// `apply_<tag> : A := consume<tag> w<tag>`: the same obligation at an
/// application argument, the site `PUnit.ext_iff` reached.
fn application_candidate(tag: &str) -> ConstantEntry {
    definition(
        &format!("apply_{tag}"),
        decoded(&c("A")),
        decoded(&app(c(&format!("consume{tag}")), [c(&format!("w{tag}"))])),
    )
}

#[test]
fn values_of_a_unit_like_type_are_convertible_at_body_and_argument_sites() {
    let env = environment();
    for tag in ["U", "W"] {
        for candidate in [body_candidate(tag), application_candidate(tag)] {
            let outcome = admit(&env, &candidate, AdmissionBudget::unlimited());
            assert!(
                matches!(outcome, Verdict::Admitted(_)),
                "{tag}: {outcome:?}"
            );
        }
    }
}

#[test]
fn a_field_a_second_constructor_or_an_index_keeps_values_distinct() {
    let env = environment();
    for tag in ["V", "B", "I"] {
        let outcome = admit(&env, &body_candidate(tag), AdmissionBudget::unlimited());
        assert!(
            matches!(
                outcome,
                Verdict::Deferred(AdmissionDeferred::BodyConversion { .. })
            ),
            "{tag} is not unit-like, so its two opaque values must stay unproven: {outcome:?}"
        );
    }
}
