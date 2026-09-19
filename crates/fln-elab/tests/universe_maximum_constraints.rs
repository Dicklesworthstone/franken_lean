//! Maximum equality must not guess a positional correspondence between atoms.
#![forbid(unsafe_code)]
use fln_core::expr::Expr;
use fln_core::level::{LMVarId, Level};
use fln_core::name::Name;
use fln_core::options::KVMap;
use fln_elab::constraint::unify::{UnificationBudget, UnificationError};
use fln_elab::txn::ElabTxn;
use fln_env::environment::Environment;
use fln_kernel::verdict::Budget;
fn name(text: &str) -> Name {
    Name::from_components([text])
}
fn pair(a: Level, b: Level) -> (Expr, Expr) {
    (Expr::sort(a), Expr::sort(b))
}
fn maximum(a: Level, b: Level) -> Level {
    Level::max(a, b).unwrap()
}
fn budget() -> UnificationBudget {
    UnificationBudget::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}
#[test]
fn later_constraints_determine_either_permutation_of_an_ambiguous_maximum() {
    for swap in [false, true] {
        for maximum_first in [false, true] {
            let mut tx = ElabTxn::new(Environment::new(), KVMap::new(), 1);
            let x = LMVarId(name("x"));
            let y = LMVarId(name("y"));
            let a = Level::param(name("alpha"));
            let b = Level::param(name("beta"));
            let (expected_x, expected_y) = if swap {
                (b.clone(), a.clone())
            } else {
                (a.clone(), b.clone())
            };
            let m = pair(
                maximum(Level::mvar(x.clone()), Level::mvar(y.clone())),
                maximum(a, b),
            );
            let mut pairs = vec![
                pair(Level::mvar(x.clone()), expected_x.clone()),
                pair(Level::mvar(y.clone()), expected_y.clone()),
            ];
            if maximum_first {
                pairs.insert(0, m)
            } else {
                pairs.push(m)
            }
            tx.unify_many_with(&pairs, budget(), &|| false)
                .expect("later equations disambiguate the maximum");
            assert_eq!(
                tx.universes.instantiate(&Level::mvar(x)).unwrap(),
                expected_x
            );
            assert_eq!(
                tx.universes.instantiate(&Level::mvar(y)).unwrap(),
                expected_y
            );
        }
    }
}
#[test]
fn an_ambiguous_maximum_alone_does_not_publish_guessed_assignments() {
    let mut tx = ElabTxn::new(Environment::new(), KVMap::new(), 2);
    let before = tx.clone();
    let (a, b) = pair(
        maximum(
            Level::mvar(LMVarId(name("x"))),
            Level::mvar(LMVarId(name("y"))),
        ),
        maximum(Level::param(name("u")), Level::param(name("v"))),
    );
    assert!(matches!(
        tx.unify(&a, &b, budget()),
        Err(UnificationError::Deferred(_))
    ));
    assert_eq!(tx.universes, before.universes);
    assert_eq!(tx.mvars, before.mvars);
    assert_eq!(tx.constraints, before.constraints);
    assert_eq!(tx.env, before.env);
}
