//! Families whose indices and result sort are exposed only by reducing the
//! declared type, as the pin reads them (`inductive.cpp:222-245`, `:596-607`):
//! `finiteInterClosure : Set (Set α)` and `ofObj : ObjectProperty C` in
//! Mathlib. Every fixture is written by hand with named locals; the recursor
//! and rules here are the comparison subjects, never derived from the checker.
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
fn qualified(name: &str) -> WireName {
    checker_qualified(&name.split('.').collect::<Vec<_>>())
}
fn param(name: &str) -> Level {
    Level::param(primary_name(name))
}
fn type_at(level: Level) -> Expr {
    Expr::sort(level.succ().unwrap())
}

/// `name.{levels} (x : domain) : Sort codomain := fun x => Π (_ : x), result`:
/// the shape of Mathlib's `Set α := α → Prop` and `ObjectProperty C := C → Prop`.
fn arrow_family_definition(
    name: &str,
    levels: &[&str],
    domain: Expr,
    codomain: Expr,
    result: Expr,
) -> ConstantEntry {
    let x = B::new("x", domain);
    let body = close(
        std::slice::from_ref(&x),
        Expr::forall_e(primary_name("a"), x.e(), result, BinderInfo::Default),
        true,
    );
    ConstantEntry::new(
        checker_name(name),
        ConstantDeclaration::definition(
            levels.iter().map(|l| checker_name(*l)).collect(),
            decoded(&close(std::slice::from_ref(&x), codomain, false)),
            ConstantSafety::Safe,
            DefinitionBody::new(
                decoded(&body),
                ReducibilityHint::Abbrev,
                DefinitionSafety::Safe,
                Vec::new(),
            ),
        ),
    )
}

/// The definitions the fixtures unfold.
fn environment() -> ConstantEnvironment {
    let u = param("u");
    environment_of(vec![
        // TestSet.{u} (α : Type u) : Type u := α → Prop
        arrow_family_definition(
            "TestSet",
            &["u"],
            type_at(u.clone()),
            type_at(u.clone()),
            Expr::sort(Level::zero()),
        ),
        // TestPred.{u} (C : Type u) : Type u := C → Prop
        arrow_family_definition(
            "TestPred",
            &["u"],
            type_at(u.clone()),
            type_at(u.clone()),
            Expr::sort(Level::zero()),
        ),
        // TestFam (α : Type) : Type 1 := α → Type
        arrow_family_definition(
            "TestFam",
            &[],
            type_at(Level::zero()),
            type_at(Level::one()),
            type_at(Level::zero()),
        ),
    ])
}

struct Ctor {
    name: &'static str,
    fields: Vec<B>,
    /// `(field position, child indices)` of every recursive field, in order.
    recursive: Vec<(usize, Vec<Expr>)>,
    result: Vec<Expr>,
}
struct Family {
    name: &'static str,
    levels: Vec<&'static str>,
    parameters: Vec<B>,
    /// The declared type after the parameters, as written (reducible).
    declared: Expr,
    /// The index binders the pin reads after reducing `declared`.
    indices: Vec<B>,
    ctors: Vec<Ctor>,
    /// Whether the hand-written recursor claims an extra motive universe.
    large: bool,
    /// The claimed `num_indices`, normally `indices.len()`.
    claimed_indices: usize,
}

impl Family {
    fn family_levels(&self) -> Vec<Level> {
        self.levels.iter().map(|l| param(l)).collect()
    }
    fn applied(&self, indices: impl IntoIterator<Item = Expr>) -> Expr {
        app(
            constant(self.name, &self.family_levels()),
            self.parameters.iter().map(B::e).chain(indices),
        )
    }
    fn rows(&self) -> Vec<ConstantEntry> {
        let level_names: Vec<_> = self.levels.iter().map(|l| checker_name(*l)).collect();
        let rec_name = format!("{}.rec", self.name);
        let ctor_names: Vec<_> = self
            .ctors
            .iter()
            .map(|c| format!("{}.{}", self.name, c.name))
            .collect();
        let mut rows = vec![ConstantEntry::new(
            checker_name(self.name),
            ConstantDeclaration::inductive(
                level_names.clone(),
                decoded(&close(&self.parameters, self.declared.clone(), false)),
                ConstantSafety::Safe,
                InductiveDeclaration::new(
                    self.parameters.len() as u32,
                    self.claimed_indices as u32,
                    vec![checker_name(self.name)],
                    ctor_names.iter().map(|n| qualified(n)).collect(),
                    0,
                    self.ctors.iter().any(|c| !c.recursive.is_empty()),
                    false,
                ),
            ),
        )];
        for (i, ctor) in self.ctors.iter().enumerate() {
            rows.push(ConstantEntry::new(
                qualified(&ctor_names[i]),
                ConstantDeclaration::constructor(
                    level_names.clone(),
                    decoded(&close(
                        &self.parameters,
                        close(&ctor.fields, self.applied(ctor.result.clone()), false),
                        false,
                    )),
                    ConstantSafety::Safe,
                    ConstructorDeclaration::new(
                        checker_name(self.name),
                        i as u32,
                        self.parameters.len() as u32,
                        ctor.fields.len() as u32,
                    ),
                ),
            ));
        }
        // The eliminator, written as the pin builds it (`mk_rec_infos`,
        // `declare_recursors`, `mk_rec_rules`).
        let motive_level = if self.large {
            param("elim")
        } else {
            Level::zero()
        };
        let major = B::new("major", self.applied(self.indices.iter().map(B::e)));
        let motive = B::new(
            "motive",
            close(
                &self.indices,
                close(
                    std::slice::from_ref(&major),
                    Expr::sort(motive_level),
                    false,
                ),
                false,
            ),
        );
        let apply_motive =
            |ix: &[Expr], value: Expr| app(motive.e(), ix.iter().cloned().chain([value]));
        let mut minors = Vec::new();
        for (i, ctor) in self.ctors.iter().enumerate() {
            let hypotheses: Vec<_> = ctor
                .recursive
                .iter()
                .enumerate()
                .map(|(k, (field, ix))| {
                    B::new(&format!("ih{k}"), apply_motive(ix, ctor.fields[*field].e()))
                })
                .collect();
            let constructed = app(
                constant(&ctor_names[i], &self.family_levels()),
                self.parameters.iter().chain(&ctor.fields).map(B::e),
            );
            minors.push(B::new(
                &format!("minor{i}"),
                close(
                    &ctor.fields,
                    close(&hypotheses, apply_motive(&ctor.result, constructed), false),
                    false,
                ),
            ));
        }
        let mut prefix = self.parameters.clone();
        prefix.push(motive.clone());
        prefix.extend(minors.iter().cloned());
        let mut binders = prefix.clone();
        binders.extend(self.indices.iter().cloned());
        binders.push(major.clone());
        let rec_type = close(
            &binders,
            apply_motive(
                &self.indices.iter().map(B::e).collect::<Vec<_>>(),
                major.e(),
            ),
            false,
        );
        let mut rec_level_names = Vec::new();
        let mut rec_levels = Vec::new();
        if self.large {
            rec_level_names.push(checker_name("elim"));
            rec_levels.push(param("elim"));
        }
        rec_level_names.extend(level_names.iter().cloned());
        rec_levels.extend(self.family_levels());
        let rules = self
            .ctors
            .iter()
            .enumerate()
            .map(|(i, ctor)| {
                let calls = ctor.recursive.iter().map(|(field, ix)| {
                    app(
                        constant(&rec_name, &rec_levels),
                        prefix
                            .iter()
                            .map(B::e)
                            .chain(ix.iter().cloned())
                            .chain([ctor.fields[*field].e()]),
                    )
                });
                let body = app(minors[i].e(), ctor.fields.iter().map(B::e).chain(calls));
                let mut bound = prefix.clone();
                bound.extend(ctor.fields.iter().cloned());
                RecursorRule::new(
                    qualified(&ctor_names[i]),
                    ctor.fields.len() as u32,
                    decoded(&close(&bound, body, true)),
                )
            })
            .collect();
        rows.push(ConstantEntry::new(
            qualified(&rec_name),
            ConstantDeclaration::recursor(
                rec_level_names,
                decoded(&rec_type),
                ConstantSafety::Safe,
                RecursorDeclaration::new(
                    vec![checker_name(self.name)],
                    self.parameters.len() as u32,
                    self.claimed_indices as u32,
                    1,
                    self.ctors.len() as u32,
                    rules,
                    false,
                ),
            ),
        ));
        rows
    }
}

/// `inductive Closure.{u} {α : Type u} (S : TestSet (TestSet α)) : TestSet (TestSet α)`
/// with `basic (s) (h : S s) : Closure S s` and the recursive
/// `mono (s t) (h : Closure S s) (k : S t) : Closure S t` — the minimized
/// shape of Mathlib's `FiniteInter.finiteInterClosure`: one universe
/// parameter, two parameters, one index exposed by unfolding `TestSet`.
fn closure(large: bool) -> Family {
    let u = param("u");
    let set = |x: Expr| app(constant("TestSet", std::slice::from_ref(&u)), [x]);
    let alpha = B::new("α", type_at(u.clone()));
    let s_family = B::new("S", set(set(alpha.e())));
    let s = B::new("s", set(alpha.e()));
    let t = B::new("t", set(alpha.e()));
    let closure_of = |x: Expr| {
        app(
            constant("Closure", std::slice::from_ref(&u)),
            [alpha.e(), s_family.e(), x],
        )
    };
    Family {
        name: "Closure",
        levels: vec!["u"],
        parameters: vec![alpha.clone(), s_family.clone()],
        declared: set(set(alpha.e())),
        indices: vec![B::new("a", set(alpha.e()))],
        ctors: vec![
            Ctor {
                name: "basic",
                fields: vec![s.clone(), B::new("h", app(s_family.e(), [s.e()]))],
                recursive: vec![],
                result: vec![s.e()],
            },
            Ctor {
                name: "mono",
                fields: vec![
                    s.clone(),
                    t.clone(),
                    B::new("h", closure_of(s.e())),
                    B::new("k", app(s_family.e(), [t.e()])),
                ],
                recursive: vec![(2, vec![s.e()])],
                result: vec![t.e()],
            },
        ],
        large,
        claimed_indices: 1,
    }
}

/// `inductive OfObj.{u, w} {C : Type u} {ι : Type w} (X : ι → C) : TestPred C`
/// with one constructor. `hidden` is Mathlib's `ofObj`, `mk (i : ι) : OfObj X (X i)`:
/// the data field does not occur bare among the result's indices, so the pin's
/// `elim_only_at_universe_zero` holds. Otherwise `mk (c : C) : OfObj X c`
/// exposes its field and eliminates into every universe.
fn of_obj(hidden: bool, large: bool) -> Family {
    let u = param("u");
    let w = param("w");
    let c_type = B::new("C", type_at(u.clone()));
    let iota = B::new("ι", type_at(w));
    let x = B::new(
        "X",
        close(
            std::slice::from_ref(&B::new("i", iota.e())),
            c_type.e(),
            false,
        ),
    );
    let (field, result) = if hidden {
        let i = B::new("i", iota.e());
        let result = app(x.e(), [i.e()]);
        (i, result)
    } else {
        let c = B::new("c", c_type.e());
        let result = c.e();
        (c, result)
    };
    Family {
        name: "OfObj",
        levels: vec!["u", "w"],
        parameters: vec![c_type.clone(), iota, x],
        declared: app(constant("TestPred", &[u]), [c_type.e()]),
        indices: vec![B::new("a", c_type.e())],
        ctors: vec![Ctor {
            name: "mk",
            fields: vec![field],
            recursive: vec![],
            result: vec![result],
        }],
        large,
        claimed_indices: 1,
    }
}

/// `inductive Tagged {α : Type} : TestFam α` (`TestFam α := α → Type`), a DATA
/// family whose index and result sort `Type` are exposed by reduction, with
/// `mk (a : α) (x : α) : Tagged a`, or with `oversized` the field `x : Type`.
fn tagged(oversized: bool) -> Family {
    let alpha = B::new("α", type_at(Level::zero()));
    let a = B::new("a", alpha.e());
    let field = if oversized {
        type_at(Level::zero())
    } else {
        alpha.e()
    };
    Family {
        name: "Tagged",
        levels: vec![],
        parameters: vec![alpha.clone()],
        declared: app(constant("TestFam", &[]), [alpha.e()]),
        indices: vec![B::new("i", alpha.e())],
        ctors: vec![Ctor {
            name: "mk",
            fields: vec![a.clone(), B::new("x", field)],
            recursive: vec![],
            result: vec![a.e()],
        }],
        large: true,
        claimed_indices: 1,
    }
}

fn verdict(family: &Family) -> InductiveVerdict {
    admit_inductive(
        &environment(),
        &family.rows(),
        AdmissionBudget::unlimited(),
        EnvironmentBudget::unlimited(),
    )
}
fn assert_admitted(family: &Family) {
    let rows = family.rows();
    let result = verdict(family);
    let InductiveVerdict::Admitted(admitted) = &result else {
        panic!("{} must be admitted: {result:?}", family.name);
    };
    assert_eq!(
        admitted.members(),
        rows.iter().map(|r| r.name().clone()).collect::<Vec<_>>()
    );
}
fn assert_recursor_refused(family: &Family) {
    let result = verdict(family);
    assert!(
        matches!(
            &result,
            InductiveVerdict::Rejected(InductiveRejection::RecursorShape { name })
                if name == &qualified(&format!("{}.rec", family.name))
        ),
        "{result:?}"
    );
}

#[test]
fn a_recursive_predicate_whose_index_is_exposed_by_unfolding_is_reconstructed() {
    assert_admitted(&closure(false));
}

#[test]
fn a_multi_constructor_exposed_predicate_cannot_claim_large_elimination() {
    // `elim_only_at_universe_zero` (inductive.cpp:479-494): more than one
    // constructor and a result sort that can be zero eliminate only into Prop.
    assert_recursor_refused(&closure(true));
}

#[test]
fn a_predicate_whose_result_sort_is_exposed_by_unfolding_is_reconstructed() {
    assert_admitted(&of_obj(true, false));
    // Its field occurs bare in the result, so it eliminates everywhere.
    assert_admitted(&of_obj(false, true));
}

#[test]
fn an_exposed_predicate_hiding_a_data_field_cannot_claim_large_elimination() {
    // inductive.cpp:500-526: `i : ι` is not a proof and does not occur among
    // the result's arguments, so the recursor eliminates only into Prop.
    assert_recursor_refused(&of_obj(true, true));
}

#[test]
fn an_exposed_singleton_predicate_is_not_silently_restricted_to_prop() {
    // The converse: `c : C` occurs bare among the result's arguments, so the
    // pin's recursor carries an extra universe and a Prop-only one is forged.
    assert_recursor_refused(&of_obj(false, false));
}

#[test]
fn a_data_family_whose_result_sort_is_exposed_by_unfolding_is_reconstructed() {
    assert_admitted(&tagged(false));
}

#[test]
fn an_exposed_data_family_refuses_a_field_above_its_result_universe() {
    // inductive.cpp:436-442: a field of type `Type` lives in `Type 1`, above
    // the exposed result sort `Type`, and the family is not a predicate.
    let family = tagged(true);
    let result = verdict(&family);
    assert!(
        matches!(
            &result,
            InductiveVerdict::Rejected(InductiveRejection::ConstructorShape { name })
                if name == &qualified("Tagged.mk")
        ),
        "{result:?}"
    );
}

#[test]
fn a_claimed_index_count_the_reduced_telescope_does_not_have_is_refused() {
    // The pin counts every binder the reduced type exposes
    // (inductive.cpp:223-241); one index cannot be claimed as two.
    let mut family = closure(false);
    family.claimed_indices = 2;
    let result = verdict(&family);
    assert!(
        matches!(
            &result,
            InductiveVerdict::Rejected(InductiveRejection::ConstructorShape { name })
                if name == &checker_name("Closure")
        ),
        "{result:?}"
    );
}

#[test]
fn an_unfinished_reduction_is_a_nonanswer_and_can_be_retried() {
    let family = closure(false);
    let rows = family.rows();
    let env = environment();
    let mut budget = AdmissionBudget::unlimited();
    budget.inference.whnf.max_steps = 0;
    budget.inference.whnf.max_reductions = 0;
    let stopped = admit_inductive(&env, &rows, budget, EnvironmentBudget::unlimited());
    assert!(stopped.is_inconclusive_family(), "{stopped:?}");
    assert!(
        !matches!(stopped, InductiveVerdict::Rejected(_)),
        "{stopped:?}"
    );
    let cancelled = admit_inductive_with(
        &env,
        &rows,
        AdmissionBudget::unlimited(),
        EnvironmentBudget::unlimited(),
        || true,
    );
    assert!(cancelled.is_inconclusive_family(), "{cancelled:?}");
    assert!(verdict(&family).is_admitted());
}
