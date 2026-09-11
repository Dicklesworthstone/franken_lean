//! Independent fixtures for small/singleton elimination; no primary generator.
#![forbid(unsafe_code)]
use super::*;
use fln_checker::admit::{InductiveRejection, InductiveVerdict};
use fln_core::expr::FVarId;

#[derive(Clone)]
struct B {
    id: FVarId,
    ty: Expr,
}
impl B {
    fn new(label: &str, ty: Expr) -> Self {
        Self {
            id: FVarId(primary_name(label)),
            ty,
        }
    }
    fn e(&self) -> Expr {
        Expr::fvar(self.id.clone())
    }
}
fn close(bs: &[B], mut body: Expr, lambda: bool) -> Expr {
    for b in bs.iter().rev() {
        body = body.abstract_fvar(&b.id, 0).unwrap();
        body = if lambda {
            Expr::lam(b.id.0.clone(), b.ty.clone(), body, BinderInfo::Default)
        } else {
            Expr::forall_e(b.id.0.clone(), b.ty.clone(), body, BinderInfo::Default)
        };
    }
    body
}
fn app(head: Expr, args: impl IntoIterator<Item = Expr>) -> Expr {
    args.into_iter().fold(head, Expr::app)
}
fn constant(name: &str, levels: &[Level]) -> Expr {
    Expr::const_(Name::from_components(name.split('.')), levels.to_vec())
}
#[derive(Clone, Copy)]
enum Kind {
    Empty,
    Unit,
    Both,
    Either,
    Witness,
    IndexedWitness,
    HiddenWitness,
}

type ConstructorFields = (Vec<B>, Vec<Expr>);
type FamilyTelescopes = (Vec<B>, Vec<B>, Vec<ConstructorFields>);

// Every fixture has a visibly independent telescope. Mutations change the
// claimed eliminator, never the family or the constructor being inspected.
fn fixture(kind: Kind, large: bool, k: bool, field_level: Level) -> Vec<ConstantEntry> {
    let prop = Expr::sort(Level::zero());
    let u = primary_name("u");
    let family_levels = vec![Level::param(u.clone())];
    let family_level_names = vec![checker_name("u")];
    let p = B::new("P", prop.clone());
    let q = B::new("Q", prop.clone());
    let a = B::new("A", Expr::sort(field_level));
    let w = B::new("w", a.e());
    let x = B::new("x", a.e());
    let f = B::new("f", close(std::slice::from_ref(&x), a.e(), false));
    let (parameters, indices, ctors): FamilyTelescopes = match kind {
        Kind::Empty => (vec![], vec![], vec![]),
        Kind::Unit => (vec![], vec![], vec![(vec![], vec![])]),
        Kind::Both => (
            vec![p.clone(), q.clone()],
            vec![],
            vec![(vec![B::new("hp", p.e()), B::new("hq", q.e())], vec![])],
        ),
        Kind::Either => (
            vec![p.clone(), q.clone()],
            vec![],
            vec![
                (vec![B::new("hp", p.e())], vec![]),
                (vec![B::new("hq", q.e())], vec![]),
            ],
        ),
        Kind::Witness => (vec![a.clone()], vec![], vec![(vec![w], vec![])]),
        Kind::IndexedWitness => (
            vec![a.clone()],
            vec![x],
            vec![(vec![w.clone()], vec![w.e()])],
        ),
        Kind::HiddenWitness => (
            vec![a.clone(), f.clone()],
            vec![x],
            vec![(vec![w.clone()], vec![Expr::app(f.e(), w.e())])],
        ),
    };
    let family = |ix: &[Expr]| {
        app(
            constant("TestPredicate", &family_levels),
            parameters.iter().map(B::e).chain(ix.iter().cloned()),
        )
    };
    let major = B::new(
        "major",
        family(&indices.iter().map(B::e).collect::<Vec<_>>()),
    );
    let motive_level = if large {
        Level::param(primary_name("elim"))
    } else {
        Level::zero()
    };
    let motive = B::new(
        "motive",
        close(
            &indices,
            close(
                std::slice::from_ref(&major),
                Expr::sort(motive_level.clone()),
                false,
            ),
            false,
        ),
    );
    let apply_motive = |ix: &[Expr], val: Expr| app(motive.e(), ix.iter().cloned().chain([val]));
    let ctor_names: Vec<_> = (0..ctors.len())
        .map(|i| format!("TestPredicate.c{i}"))
        .collect();
    let mut minors = Vec::new();
    let mut rows = vec![ConstantEntry::new(
        checker_name("TestPredicate"),
        ConstantDeclaration::inductive(
            family_level_names.clone(),
            decoded(&close(&parameters, close(&indices, prop, false), false)),
            ConstantSafety::Safe,
            InductiveDeclaration::new(
                parameters.len() as u32,
                indices.len() as u32,
                vec![checker_name("TestPredicate")],
                ctor_names
                    .iter()
                    .map(|s| checker_qualified(&s.split('.').collect::<Vec<_>>()))
                    .collect(),
                0,
                false,
                false,
            ),
        ),
    )];
    for (i, (fields, ix)) in ctors.iter().enumerate() {
        let ctor = app(
            constant(&ctor_names[i], &family_levels),
            parameters.iter().chain(fields).map(B::e),
        );
        minors.push(B::new(
            &format!("minor{i}"),
            close(fields, apply_motive(ix, ctor), false),
        ));
        rows.push(ConstantEntry::new(
            checker_qualified(&ctor_names[i].split('.').collect::<Vec<_>>()),
            ConstantDeclaration::constructor(
                family_level_names.clone(),
                decoded(&close(&parameters, close(fields, family(ix), false), false)),
                ConstantSafety::Safe,
                ConstructorDeclaration::new(
                    checker_name("TestPredicate"),
                    i as u32,
                    parameters.len() as u32,
                    fields.len() as u32,
                ),
            ),
        ));
    }
    let mut prefix = parameters.clone();
    prefix.push(motive.clone());
    prefix.extend(minors.clone());
    let mut rec_binders = prefix.clone();
    rec_binders.extend(indices.iter().cloned());
    rec_binders.push(major.clone());
    let rec_type = close(
        &rec_binders,
        apply_motive(&indices.iter().map(B::e).collect::<Vec<_>>(), major.e()),
        false,
    );
    let rules = ctors
        .iter()
        .enumerate()
        .map(|(i, (fields, _))| {
            let mut binders = prefix.clone();
            binders.extend(fields.iter().cloned());
            RecursorRule::new(
                checker_qualified(&ctor_names[i].split('.').collect::<Vec<_>>()),
                fields.len() as u32,
                decoded(&close(
                    &binders,
                    app(minors[i].e(), fields.iter().map(B::e)),
                    true,
                )),
            )
        })
        .collect();
    let mut rec_levels = if large {
        vec![checker_name("elim")]
    } else {
        vec![]
    };
    rec_levels.extend(family_level_names);
    rows.push(ConstantEntry::new(
        checker_qualified(&["TestPredicate", "rec"]),
        ConstantDeclaration::recursor(
            rec_levels,
            decoded(&rec_type),
            ConstantSafety::Safe,
            RecursorDeclaration::new(
                vec![checker_name("TestPredicate")],
                parameters.len() as u32,
                indices.len() as u32,
                1,
                ctors.len() as u32,
                rules,
                k,
            ),
        ),
    ));
    rows
}
fn verdict(rows: &[ConstantEntry]) -> InductiveVerdict {
    admit_inductive(
        &ConstantEnvironment::empty(),
        rows,
        AdmissionBudget::unlimited(),
        EnvironmentBudget::unlimited(),
    )
}
fn assert_admitted(kind: Kind, large: bool, k: bool, level: Level) {
    let result = verdict(&fixture(kind, large, k, level));
    assert!(result.is_admitted(), "{result:?}");
}
fn assert_bad_recursor(kind: Kind, large: bool, k: bool) {
    let result = verdict(&fixture(kind, large, k, Level::one()));
    assert!(
        matches!(
            result,
            InductiveVerdict::Rejected(InductiveRejection::RecursorShape { .. })
        ),
        "{result:?}"
    );
}
#[test]
fn small_and_singleton_elimination_policies_are_derived_from_constructor_fields() {
    for (kind, large, k) in [
        (Kind::Empty, true, false),
        (Kind::Unit, true, true),
        (Kind::Both, true, false),
        (Kind::Either, false, false),
        (Kind::Witness, false, false),
        (Kind::IndexedWitness, true, false),
        (Kind::HiddenWitness, false, false),
    ] {
        assert_admitted(kind, large, k, Level::one());
    }
}
#[test]
fn existential_and_disjunctive_eliminators_cannot_claim_a_fresh_motive_universe() {
    for kind in [Kind::Either, Kind::Witness, Kind::HiddenWitness] {
        assert_bad_recursor(kind, true, false);
    }
}
#[test]
fn singleton_large_elimination_is_not_silently_restricted() {
    for (kind, k) in [
        (Kind::Empty, false),
        (Kind::Unit, true),
        (Kind::Both, false),
        (Kind::IndexedWitness, false),
    ] {
        assert_bad_recursor(kind, false, k);
    }
}
#[test]
fn k_flag_forgery_is_not_accepted_for_data_bearing_or_multiconstructor_predicates() {
    for (kind, large) in [
        (Kind::Empty, true),
        (Kind::Both, true),
        (Kind::Either, false),
        (Kind::Witness, false),
        (Kind::IndexedWitness, true),
    ] {
        assert_bad_recursor(kind, large, true);
    }
    assert_bad_recursor(Kind::Unit, true, false);
}
#[test]
fn impredicative_witness_fields_may_exceed_the_zero_result_universe() {
    let mut level = Level::zero();
    for _ in 0..6 {
        level = level.succ().unwrap();
        assert_admitted(Kind::Witness, false, false, level.clone());
    }
    assert_admitted(
        Kind::Witness,
        false,
        false,
        Level::param(primary_name("u")).succ().unwrap(),
    );
}
#[test]
fn proof_field_sort_normalization_does_not_restrict_singleton_elimination() {
    // Here A is a proposition, so the witness is itself a proof; imax u 0
    // must be classified by its normalized level rather than node spelling.
    let zero = Level::imax(Level::param(primary_name("u")), Level::zero()).unwrap();
    assert_admitted(Kind::Witness, true, false, zero);
}
#[test]
fn propositional_admission_resource_stops_leave_no_environment_and_can_be_retried() {
    let rows = fixture(Kind::Witness, false, false, Level::one());
    let env = ConstantEnvironment::empty();
    let before = env.clone();
    let stopped = admit_inductive_with(
        &env,
        &rows,
        AdmissionBudget::unlimited(),
        EnvironmentBudget::unlimited(),
        || true,
    );
    assert!(
        matches!(stopped, InductiveVerdict::Inconclusive(_)),
        "{stopped:?}"
    );
    let mut budget = AdmissionBudget::unlimited();
    budget.conversion.quick.max_comparisons = 1;
    let stopped = admit_inductive(&env, &rows, budget, EnvironmentBudget::unlimited());
    assert!(
        matches!(stopped, InductiveVerdict::Inconclusive(_)),
        "{stopped:?}"
    );
    assert_eq!(env, before);
    assert!(verdict(&rows).is_admitted());
}
