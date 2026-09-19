//! Native mutual generator through both real admission engines, not mock verdicts.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap};
use fln_core::expr::{BinderInfo, Expr, FVarId};
use fln_core::{level::Level, name::Name};
use fln_elab::{
    inductive::{ConstructorSpec, InductiveError, InductiveSpec, mutual_inductive_declaration},
    lctx::LocalDecl,
    records::RecordBudget,
};
use fln_env::environment::Environment;

fn name(s: &str) -> Name {
    Name::from_components(s.split('.'))
}
fn local(s: &str, ty: Expr) -> LocalDecl {
    LocalDecl {
        id: FVarId(name(s)),
        user_name: name(s),
        type_: ty,
        value: None,
        binder_info: BinderInfo::Default,
        index: 0,
    }
}
fn fv(l: &LocalDecl) -> Expr {
    Expr::fvar(l.id.clone())
}
fn apps(f: Expr, args: impl IntoIterator<Item = Expr>) -> Expr {
    args.into_iter().fold(f, Expr::app)
}
fn family(n: &str, us: &[Level], args: impl IntoIterator<Item = Expr>) -> Expr {
    apps(Expr::const_(name(n), us.to_vec()), args)
}
fn ctor(n: &str, fields: Vec<LocalDecl>, result_indices: Vec<Expr>) -> ConstructorSpec {
    ConstructorSpec {
        name: name(n),
        fields,
        result_indices,
    }
}
fn specs(function: bool, indexed: bool) -> Vec<InductiveSpec> {
    let u = Level::param(name("u"));
    let result = Level::succ(u.clone()).unwrap();
    let params = vec![local("A", Expr::sort(result.clone()))];
    let a = fv(&params[0]);
    let ix = local("i", a.clone());
    let rix = local("j", a.clone());
    let value = local("value", a.clone());
    let fi = if indexed { vec![fv(&value)] } else { vec![] };
    let other = family(
        "Forest",
        std::slice::from_ref(&u),
        std::iter::once(a.clone()).chain(fi.clone()),
    );
    let ty = if function {
        Expr::forall_e(Name::anonymous(), a.clone(), other, BinderInfo::Default)
    } else {
        other
    };
    let child = local("child", ty);
    let tree = family(
        "Tree",
        std::slice::from_ref(&u),
        std::iter::once(a.clone()).chain(fi.clone()),
    );
    let head = local("head", tree);
    let tail = local(
        "tail",
        family(
            "Forest",
            std::slice::from_ref(&u),
            std::iter::once(a).chain(fi.clone()),
        ),
    );
    vec![
        InductiveSpec {
            name: name("Tree"),
            level_params: vec![name("u")],
            parameters: params.clone(),
            indices: if indexed { vec![ix] } else { vec![] },
            constructors: vec![ctor("node", vec![value.clone(), child], fi.clone())],
            result_level: result.clone(),
        },
        InductiveSpec {
            name: name("Forest"),
            level_params: vec![name("u")],
            parameters: params,
            indices: if indexed { vec![rix] } else { vec![] },
            constructors: vec![
                ctor("nil", vec![value.clone()], fi.clone()),
                ctor("cons", vec![value, head, tail], fi),
            ],
            result_level: result,
        },
    ]
}
fn accept(specs: &[InductiveSpec]) -> Engine {
    let declaration = mutual_inductive_declaration(specs, RecordBudget::default()).unwrap();
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    Engine::from_environment(Environment::new())
        .admit_declaration(declaration, &KVMap::new(), limits)
        .unwrap_or_else(|e| panic!("{e:?}"))
        .into_complete()
        .expect("both seats complete")
        .engine
}
#[test]
fn generated_direct_indexed_and_function_children_pass_both_seats() {
    for function in [false, true] {
        for indexed in [false, true] {
            let e = accept(&specs(function, indexed));
            for n in [
                "Tree",
                "Forest",
                "Tree.node",
                "Forest.nil",
                "Forest.cons",
                "Tree.rec",
                "Forest.rec",
            ] {
                assert!(e.environment().contains(&name(n)), "{n}");
            }
        }
    }
}
#[test]
fn three_families_and_empty_siblings_keep_all_ordered_motives() {
    let mut s = specs(false, false);
    let mut empty = s[0].clone();
    empty.name = name("Empty");
    empty.constructors.clear();
    s.push(empty);
    accept(&s);
    for f in &mut s {
        f.constructors.clear();
    }
    accept(&s);
}
#[test]
fn negative_and_nonuniform_cross_family_recursion_never_generate_a_candidate() {
    let mut s = specs(false, false);
    let forest = s[0].constructors[0].fields[1].type_.clone();
    s[0].constructors[0].fields[1].type_ = Expr::forall_e(
        Name::anonymous(),
        forest,
        Expr::sort(Level::one()),
        BinderInfo::Default,
    );
    assert!(mutual_inductive_declaration(&s, RecordBudget::default()).is_err());
    let mut s = specs(false, false);
    s[0].constructors[0].fields[1].type_ = family(
        "Forest",
        &[Level::param(name("u"))],
        [Expr::sort(Level::one())],
    );
    assert!(mutual_inductive_declaration(&s, RecordBudget::default()).is_err());
}
#[test]
fn malformed_blocks_and_work_stops_are_not_partial_results() {
    let s = specs(false, true);
    assert_eq!(
        mutual_inductive_declaration(
            &s,
            RecordBudget {
                max_nodes: 0,
                ..RecordBudget::default()
            }
        )
        .unwrap_err(),
        InductiveError::ResourceLimit
    );
    let mut bad = s.clone();
    bad[1].parameters[0].id = FVarId(name("different"));
    assert!(mutual_inductive_declaration(&bad, RecordBudget::default()).is_err());
    let mut bad = s.clone();
    bad[1].name = bad[0].name.clone();
    assert!(mutual_inductive_declaration(&bad, RecordBudget::default()).is_err());
    let mut bad = s;
    bad[1].result_level = Level::zero();
    assert!(mutual_inductive_declaration(&bad, RecordBudget::default()).is_err());
}
