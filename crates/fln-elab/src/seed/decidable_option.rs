//! Constructive Option equality for the native source seed.
//!
//! The element dictionary supplies the only equality decision. Constructor
//! discrimination, injectivity and congruence are ordinary recursor terms;
//! neither host comparisons nor additional axioms supply proof fields.
//! Publication and instance registration remain the seed consumer's job.
use crate::lctx::LocalDecl;
use fln_core::expr::{BinderInfo, Expr, FVarId};
use fln_core::level::Level;
use fln_core::name::Name;
use fln_env::constants::{ConstantVal, DefinitionSafety, DefinitionVal, ReducibilityHints};
use fln_kernel::Declaration;

fn name(s: &str) -> Name {
    Name::from_components(s.split('.'))
}
fn constant(s: &str, levels: Vec<Level>) -> Expr {
    Expr::const_(name(s), levels)
}
fn app(f: Expr, args: impl IntoIterator<Item = Expr>) -> Expr {
    args.into_iter().fold(f, Expr::app)
}
fn fv(local: &LocalDecl) -> Expr {
    Expr::fvar(local.id.clone())
}
fn close(locals: &[&LocalDecl], mut body: Expr, lambda: bool) -> Expr {
    for local in locals.iter().rev() {
        body = body
            .abstract_fvar(&local.id, 0)
            .expect("fixed Option decision telescope");
        body = if lambda {
            Expr::lam(local.user_name.clone(), local.type_.clone(), body, local.binder_info)
        } else {
            Expr::forall_e(local.user_name.clone(), local.type_.clone(), body, local.binder_info)
        };
    }
    body
}
fn eq(carrier: Expr, level: Level, left: Expr, right: Expr) -> Expr {
    app(constant("Eq", vec![level]), [carrier, left, right])
}
fn refl(carrier: Expr, level: Level, value: Expr) -> Expr {
    app(constant("Eq.refl", vec![level]), [carrier, value])
}
fn decision(proposition: Expr) -> Expr {
    Expr::app(constant("Decidable", vec![]), proposition)
}
fn verdict(proposition: Expr, proof: Expr, positive: bool) -> Expr {
    app(
        constant(if positive { "Decidable.isTrue" } else { "Decidable.isFalse" }, vec![]),
        [proposition, proof],
    )
}
fn definition(label: &str, levels: Vec<Name>, locals: &[&LocalDecl], type_: Expr, value: Expr) -> Declaration {
    Declaration::Defn(DefinitionVal {
        base: ConstantVal { name: name(label), level_params: levels, type_: close(locals, type_, false) },
        value: close(locals, value, true),
        hints: ReducibilityHints::Abbrev,
        safety: DefinitionSafety::Safe,
        all: vec![name(label)],
    })
}

struct Terms {
    next: usize,
    universe: Level,
    sort: Level,
    alpha: Expr,
}
impl Terms {
    fn local(&mut self, label: &str, type_: Expr, binder_info: BinderInfo) -> LocalDecl {
        let id = FVarId(name(&format!("_fln_option_decision.{label}_{}", self.next)));
        self.next += 1;
        LocalDecl { id, user_name: name(label), type_, value: None, binder_info, index: 0 }
    }
    fn explicit(&mut self, label: &str, type_: Expr) -> LocalDecl {
        self.local(label, type_, BinderInfo::Default)
    }
    fn option(&self) -> Expr {
        Expr::app(constant("Option", vec![self.universe.clone()]), self.alpha.clone())
    }
    fn none(&self) -> Expr {
        Expr::app(constant("Option.none", vec![self.universe.clone()]), self.alpha.clone())
    }
    fn some(&self, value: Expr) -> Expr {
        app(constant("Option.some", vec![self.universe.clone()]), [self.alpha.clone(), value])
    }
    fn equality(&self, left: Expr, right: Expr) -> Expr {
        eq(self.option(), self.sort.clone(), left, right)
    }
    fn rec(&self, result_sort: Level, motive: Expr, none: Expr, some: Expr, major: Expr) -> Expr {
        app(
            constant("Option.rec", vec![result_sort, self.universe.clone()]),
            [self.alpha.clone(), motive, none, some, major],
        )
    }
    // The carrier universe is explicit: Option.{u} and its elements live in
    // Sort (u+1), not Sort u. The transported family is proposition-valued.
    #[allow(clippy::too_many_arguments)]
    fn transport(&mut self, endpoint: &LocalDecl, left: Expr, right: Expr, evidence: Expr, proposition: Expr, proof: Expr) -> Expr {
        let equality = self.explicit("transport_equality", eq(endpoint.type_.clone(), self.sort.clone(), left.clone(), fv(endpoint)));
        app(
            constant("Eq.rec", vec![Level::zero(), self.sort.clone()]),
            [endpoint.type_.clone(), left, close(&[endpoint, &equality], proposition, true), proof, right, evidence],
        )
    }
    fn mismatch(&mut self, element: Expr, none_left: bool) -> Expr {
        let (left, right) = if none_left { (self.none(), self.some(element)) } else { (self.some(element), self.none()) };
        let hypothesis = self.explicit("different_constructors", self.equality(left.clone(), right.clone()));
        let endpoint = self.explicit("endpoint", self.option());
        let major = self.explicit("discriminator", self.option());
        let field = self.explicit("field", self.alpha.clone());
        let (no, yes) = if none_left { ("True", "False") } else { ("False", "True") };
        let predicate = self.rec(
            Level::one(),
            close(&[&major], Expr::sort(Level::zero()), true),
            constant(no, vec![]),
            close(&[&field], constant(yes, vec![]), true),
            fv(&endpoint),
        );
        let proof = self.transport(&endpoint, left, right, fv(&hypothesis), predicate, constant("True.intro", vec![]));
        close(&[&hypothesis], proof, true)
    }
    fn congruence(&mut self, left: Expr, right: Expr, evidence: Expr) -> Expr {
        let endpoint = self.explicit("element_endpoint", self.alpha.clone());
        let predicate = self.equality(self.some(left.clone()), self.some(fv(&endpoint)));
        let proof = refl(self.option(), self.sort.clone(), self.some(left.clone()));
        self.transport(&endpoint, left, right, evidence, predicate, proof)
    }
    fn injectivity(&mut self, left: Expr, right: Expr, evidence: Expr) -> Expr {
        let endpoint = self.explicit("option_endpoint", self.option());
        let major = self.explicit("extractor", self.option());
        let field = self.explicit("extracted_field", self.alpha.clone());
        // A known left element supplies the empty branch; no Inhabited
        // instance is required to project the two nonempty endpoints.
        let extracted = self.rec(
            self.sort.clone(),
            close(&[&major], self.alpha.clone(), true),
            left.clone(),
            close(&[&field], fv(&field), true),
            fv(&endpoint),
        );
        let predicate = eq(self.alpha.clone(), self.sort.clone(), left.clone(), extracted);
        let proof = refl(self.alpha.clone(), self.sort.clone(), left.clone());
        self.transport(&endpoint, self.some(left), self.some(right), evidence, predicate, proof)
    }
    fn some_decision(&mut self, dictionary: Expr, left: Expr, right: Expr) -> Expr {
        let small = eq(self.alpha.clone(), self.sort.clone(), left.clone(), right.clone());
        let large = self.equality(self.some(left.clone()), self.some(right.clone()));
        let d = self.explicit("element_decision", decision(small.clone()));
        let yes = self.explicit("element_equality", small.clone());
        let no = self.explicit("element_inequality", Expr::app(constant("Not", vec![]), small.clone()));
        let h = self.explicit("some_equality", large.clone());
        let injection = self.injectivity(left.clone(), right.clone(), fv(&h));
        let negative = close(&[&no], verdict(large.clone(), close(&[&h], Expr::app(fv(&no), injection), true), false), true);
        let congruence = self.congruence(left.clone(), right.clone(), fv(&yes));
        let positive = close(&[&yes], verdict(large.clone(), congruence, true), true);
        app(
            constant("Decidable.rec", vec![Level::one()]),
            [small, close(&[&d], decision(large), true), negative, positive, app(dictionary, [left, right])],
        )
    }
}

/// Construct an untrusted generic instance candidate. Admit after Option, Eq,
/// Decidable, Not, True, False and DecidableEq; register only after admission.
pub fn option_equality_decision_seed_declaration() -> Declaration {
    let universe = Level::param(name("u"));
    let sort = universe.succ().expect("fixed Option universe");
    let mut terms = Terms { next: 0, universe, sort: sort.clone(), alpha: Expr::sort(Level::zero()) };
    let alpha = terms.local("alpha", Expr::sort(sort.clone()), BinderInfo::Implicit);
    terms.alpha = fv(&alpha);
    let dictionary = terms.local("inst", Expr::app(constant("DecidableEq", vec![sort.clone()]), fv(&alpha)), BinderInfo::InstImplicit);
    let a = terms.explicit("a", terms.option());
    let b = terms.explicit("b", terms.option());
    let major = terms.explicit("major", terms.option());
    let x = terms.explicit("x", fv(&alpha));
    let y = terms.explicit("y", fv(&alpha));
    let none_eq = terms.equality(terms.none(), terms.none());
    let none_same = verdict(none_eq, refl(terms.option(), sort.clone(), terms.none()), true);
    let none_some_type = terms.equality(terms.none(), terms.some(fv(&y)));
    let none_some_proof = terms.mismatch(fv(&y), true);
    let none_some = close(&[&y], verdict(none_some_type, none_some_proof, false), true);
    let none_branch = close(&[&b], terms.rec(
        Level::one(),
        close(&[&major], decision(terms.equality(terms.none(), fv(&major))), true),
        none_same, none_some, fv(&b),
    ), true);
    let some_none_type = terms.equality(terms.some(fv(&x)), terms.none());
    let some_none_proof = terms.mismatch(fv(&x), false);
    let some_none = verdict(some_none_type, some_none_proof, false);
    let some_some = terms.some_decision(fv(&dictionary), fv(&x), fv(&y));
    let some_branch = close(&[&x, &b], terms.rec(
        Level::one(),
        close(&[&major], decision(terms.equality(terms.some(fv(&x)), fv(&major))), true),
        some_none, close(&[&y], some_some, true), fv(&b),
    ), true);
    let motive = close(&[&major], close(&[&b], decision(terms.equality(fv(&major), fv(&b))), false), true);
    // The outer result is a function over Option alpha: its universe is u+1,
    // although each individual Decidable result lives in Sort 1.
    let value = Expr::app(terms.rec(sort, motive, none_branch, some_branch, fv(&a)), fv(&b));
    definition("instDecidableEqOption", vec![name("u")], &[&alpha, &dictionary, &a, &b], decision(terms.equality(fv(&a), fv(&b))), value)
}

#[cfg(test)]
mod tests {
    use super::*;
    use fln_core::outcome::Outcome;
    use fln_env::environment::{DeclarationBudget, DeclarationCommitted, Environment};
    use fln_env::pmap::CollisionBudget;
    use fln_kernel::capability::{Published, admit};
    use fln_kernel::council::{Council, CouncilOutcome, convene};
    use fln_kernel::verdict::{Budget, Verdict};

    fn budget() -> Budget { Budget::for_stack_bytes(2 * 1024 * 1024) }
    fn environment() -> Environment {
        let mut env = Environment::new();
        for declaration in crate::seed::source_seed_declarations() {
            let Outcome::Complete(admitted) = admit(&env, declaration, budget()) else { panic!("seed nonanswer") };
            let CouncilOutcome::Agreed(checked) = convene(&Council::nobody_was_asked(), admitted) else { panic!("seed rejection") };
            env = match checked.publish(DeclarationBudget::default(), CollisionBudget::default(), None) {
                Outcome::Complete(Published::Committed(DeclarationCommitted::Published(result))) => result.environment,
                Outcome::Complete(Published::BlockCommitted(result)) => result.environment,
                other => panic!("seed publication {other:?}"),
            };
        }
        env
    }
    fn option(carrier: Expr) -> Expr { Expr::app(constant("Option", vec![Level::zero()]), carrier) }
    fn none(carrier: Expr) -> Expr { Expr::app(constant("Option.none", vec![Level::zero()]), carrier) }
    fn some(carrier: Expr, element: Expr) -> Expr { app(constant("Option.some", vec![Level::zero()]), [carrier, element]) }
    fn dictionary(carrier: Expr, element_dictionary: Expr) -> Expr {
        app(constant("instDecidableEqOption", vec![Level::zero()]), [carrier, element_dictionary])
    }
    fn assert_decision(env: &Environment, carrier: Expr, element_dictionary: Expr, left: Expr, right: Expr, expected: bool) {
        let proposition = eq(option(carrier.clone()), Level::one(), left.clone(), right.clone());
        let evidence = app(dictionary(carrier, element_dictionary), [left, right]);
        let value = app(constant("decide", vec![]), [proposition, evidence]);
        for result in [expected, !expected] {
            let bool_ = constant("Bool", vec![]);
            let type_ = eq(bool_.clone(), Level::one(), value.clone(), constant(if result { "Bool.true" } else { "Bool.false" }, vec![]));
            let proof = refl(bool_, Level::one(), value.clone());
            let candidate = definition("decision_test", vec![], &[], type_, proof);
            let verdict = fln_kernel::check(env, &candidate, budget());
            if result == expected {
                assert!(matches!(verdict, Outcome::Complete(Verdict::Accepted { .. })), "{verdict:?}");
            } else {
                assert!(matches!(verdict, Outcome::Complete(Verdict::Rejected { .. })), "{verdict:?}");
            }
        }
    }
    #[test]
    fn option_decisions_compute_all_constructor_and_element_cases() {
        let env = environment();
        let nat = constant("Nat", vec![]);
        let zero = constant("Nat.zero", vec![]);
        let one = Expr::app(constant("Nat.succ", vec![]), zero.clone());
        let values = [none(nat.clone()), some(nat.clone(), zero), some(nat.clone(), one)];
        for (i, left) in values.iter().enumerate() {
            for (j, right) in values.iter().enumerate() {
                assert_decision(&env, nat.clone(), constant("Nat.decEq", vec![]), left.clone(), right.clone(), i == j);
            }
        }
    }
    #[test]
    fn nested_options_use_the_supplied_generic_dictionary() {
        let env = environment();
        let bool_ = constant("Bool", vec![]);
        let inner = option(bool_.clone());
        let dict = dictionary(bool_.clone(), constant("Bool.decEq", vec![]));
        let values = [none(inner.clone()), some(inner.clone(), none(bool_.clone())), some(inner.clone(), some(bool_.clone(), constant("Bool.false", vec![]))), some(inner.clone(), some(bool_, constant("Bool.true", vec![])))];
        for (i, left) in values.iter().enumerate() {
            for (j, right) in values.iter().enumerate() {
                assert_decision(&env, inner.clone(), dict.clone(), left.clone(), right.clone(), i == j);
            }
        }
    }
    #[test]
    fn generic_candidate_contains_no_unresolved_or_escaping_variables() {
        let Declaration::Defn(candidate) = option_equality_decision_seed_declaration() else { unreachable!() };
        assert_eq!(candidate.safety, DefinitionSafety::Safe);
        for term in [&candidate.base.type_, &candidate.value] {
            assert!(!term.has_fvar());
            assert!(!term.has_expr_mvar());
            assert!(!term.has_level_mvar());
            assert!(!term.has_loose_bvars());
        }
        let env = environment();
        assert!(env.contains(&name("instDecidableEqOption")));
    }
}
