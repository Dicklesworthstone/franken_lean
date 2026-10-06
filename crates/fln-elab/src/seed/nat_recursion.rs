//! The pinned logical model of Nat addition and its recursion dependencies.
//!
//! `Nat.add` is compiled through `Nat.brecOn`, not a direct fold over Nat.
//! Replacing that body by the extensionally equal fold changes conversion on
//! an unknown second operand. These fixed native candidates preserve the pin's
//! product-valued course-of-values recursion, helper telescopes and universes.
//! Every candidate still passes the ordinary admission engines; this module
//! supplies no reduction rule, axiom, or publication authority.
//!
//! Authority: Init/Prelude.lean and Lean/Meta/Constructions/BRecOn.lean at the
//! pinned 4.32.0 epoch, checked against that executable's full declaration prints.

use super::*;
use crate::lctx::LocalDecl;
use crate::records::{Builder, RecordBudget, RecordSpec, app, fresh, fv, record_declarations};
use fln_core::expr::FVarId;
use fln_env::constants::ConstantInfo;
use std::collections::HashSet;

fn name(label: &str) -> Name {
    Name::from_components(label.split('.'))
}

fn level(label: &str) -> Level {
    Level::param(name(label))
}

fn constant(label: &str, levels: Vec<Level>) -> Expr {
    Expr::const_(name(label), levels)
}

fn nat() -> Expr {
    constant("Nat", Vec::new())
}

fn zero() -> Expr {
    constant("Nat.zero", Vec::new())
}

fn succ(value: Expr) -> Expr {
    Expr::app(constant("Nat.succ", Vec::new()), value)
}

fn below(universe: &Level, motive: Expr, value: Expr) -> Expr {
    app(
        constant("Nat.below", vec![universe.clone()]),
        [motive, value],
    )
}

fn product(left_level: &Level, right_level: &Level, left: Expr, right: Expr) -> Expr {
    app(
        constant("PProd", vec![left_level.clone(), right_level.clone()]),
        [left, right],
    )
}

fn pair(
    left_level: &Level,
    right_level: &Level,
    left_type: Expr,
    right_type: Expr,
    left: Expr,
    right: Expr,
) -> Expr {
    app(
        constant("PProd.mk", vec![left_level.clone(), right_level.clone()]),
        [left_type, right_type, left, right],
    )
}

/// Fixed locals and the existing capture-avoiding telescope closer. Its bound
/// covers candidate construction only; source and kernel budgets are separate.
struct Terms {
    used: HashSet<FVarId>,
    builder: Builder,
}

impl Terms {
    fn new() -> Self {
        Self {
            used: HashSet::new(),
            builder: Builder {
                remaining: RecordBudget::default().max_nodes,
            },
        }
    }

    fn local(&mut self, label: &str, type_: Expr, style: BinderInfo) -> LocalDecl {
        fresh(&mut self.used, label, type_, style)
    }

    fn pi(&mut self, locals: &[LocalDecl], body: Expr) -> Expr {
        self.builder
            .close(locals, body, false, false)
            .expect("fixed Nat recursion type telescope")
    }

    fn lam(&mut self, locals: &[LocalDecl], body: Expr) -> Expr {
        self.builder
            .close(locals, body, true, false)
            .expect("fixed Nat recursion value telescope")
    }

    fn arrow(&mut self, domain: Expr, codomain: Expr) -> Expr {
        let argument = self.local("arg", domain, BinderInfo::Default);
        self.pi(&[argument], codomain)
    }

    fn motive(&mut self, universe: &Level) -> LocalDecl {
        let value = self.local("t", nat(), BinderInfo::Default);
        let type_ = self.pi(&[value], Expr::sort(universe.clone()));
        self.local("motive", type_, BinderInfo::Implicit)
    }

    fn functional(&mut self, universe: &Level, motive: &LocalDecl) -> LocalDecl {
        let value = self.local("t", nat(), BinderInfo::Default);
        let history = self.local(
            "f",
            below(universe, fv(motive), fv(&value)),
            BinderInfo::Default,
        );
        let result = Expr::app(fv(motive), fv(&value));
        let type_ = self.pi(&[value, history], result);
        self.local("F_1", type_, BinderInfo::Default)
    }

    fn add_motive(&mut self) -> Expr {
        let value = self.local("x", nat(), BinderInfo::Default);
        let function = self.arrow(nat(), nat());
        self.lam(&[value], function)
    }

    fn definition(
        &mut self,
        label: &str,
        universes: &[&str],
        locals: &[LocalDecl],
        result: Expr,
        body: Expr,
    ) -> Declaration {
        let declaration = name(label);
        Declaration::Defn(DefinitionVal {
            base: ConstantVal {
                name: declaration.clone(),
                level_params: universes.iter().map(|universe| name(universe)).collect(),
                type_: self.pi(locals, result),
            },
            value: self.lam(locals, body),
            hints: ReducibilityHints::Abbrev,
            safety: DefinitionSafety::Safe,
            all: vec![declaration],
        })
    }
}

fn punit() -> Declaration {
    let mut terms = Terms::new();
    let universe = level("u");
    let elimination = level("u_1");
    let family = constant("PUnit", vec![universe.clone()]);
    let constructor = constant("PUnit.unit", vec![universe.clone()]);
    let value = terms.local("t", family.clone(), BinderInfo::Default);
    let motive_type = terms.pi(std::slice::from_ref(&value), Expr::sort(elimination));
    let motive = terms.local("motive", motive_type, BinderInfo::Implicit);
    let minor = terms.local(
        "unit",
        Expr::app(fv(&motive), constructor),
        BinderInfo::Default,
    );
    let result = Expr::app(fv(&motive), fv(&value));
    let recursor_type = terms.pi(&[motive.clone(), minor.clone(), value], result);
    let mut rule_motive = motive;
    rule_motive.binder_info = BinderInfo::Default;
    let rule_body = fv(&minor);
    let rule = terms.lam(&[rule_motive, minor], rule_body);
    // Sort u can be Prop. The general source generator currently requires a
    // decided result universe, so construct this fixed block explicitly. The
    // existing kernel reconstructs large elimination for its nullary singleton;
    // its K flag is false because the declared result level is not literally 0.
    Declaration::Inductive(InductiveBlock {
        types: vec![InductiveVal {
            base: ConstantVal {
                name: name("PUnit"),
                level_params: vec![name("u")],
                type_: Expr::sort(universe),
            },
            num_params: 0,
            num_indices: 0,
            all: vec![name("PUnit")],
            ctors: vec![name("PUnit.unit")],
            num_nested: 0,
            is_rec: false,
            is_unsafe: false,
            is_reflexive: false,
        }],
        ctors: vec![ConstructorVal {
            base: ConstantVal {
                name: name("PUnit.unit"),
                level_params: vec![name("u")],
                type_: family,
            },
            induct: name("PUnit"),
            cidx: 0,
            num_params: 0,
            num_fields: 0,
            is_unsafe: false,
        }],
        recursors: vec![RecursorVal {
            base: ConstantVal {
                name: name("PUnit.rec"),
                level_params: vec![name("u_1"), name("u")],
                type_: recursor_type,
            },
            all: vec![name("PUnit")],
            num_params: 0,
            num_indices: 0,
            num_motives: 1,
            num_minors: 1,
            rules: vec![RecursorRule {
                ctor: name("PUnit.unit"),
                nfields: 0,
                rhs: rule,
            }],
            k: false,
            is_unsafe: false,
        }],
    })
}

fn pprod() -> Declaration {
    let mut terms = Terms::new();
    let alpha = terms.local("α", Expr::sort(level("u")), BinderInfo::Default);
    let beta = terms.local("β", Expr::sort(level("v")), BinderInfo::Default);
    let first = terms.local("fst", fv(&alpha), BinderInfo::Default);
    let second = terms.local("snd", fv(&beta), BinderInfo::Default);
    let result = Level::max(
        Level::max(Level::one(), level("u")).expect("fixed PProd result universe"),
        level("v"),
    )
    .expect("fixed PProd result universe");
    record_declarations(
        &RecordSpec {
            name: name("PProd"),
            level_params: vec![name("u"), name("v")],
            parameters: vec![alpha, beta],
            fields: vec![first, second],
            result_level: result,
            is_class: false,
        },
        RecordBudget::default(),
    )
    .expect("fixed PProd family")
    .into_iter()
    .next()
    .expect("record construction emits its family first")
}

fn nat_cases_on() -> Declaration {
    let mut terms = Terms::new();
    let universe = level("u");
    let motive = terms.motive(&universe);
    let value = terms.local("t", nat(), BinderInfo::Default);
    let first = terms.local("zero", Expr::app(fv(&motive), zero()), BinderInfo::Default);
    let predecessor = terms.local("n", nat(), BinderInfo::Default);
    let next_type = terms.pi(
        std::slice::from_ref(&predecessor),
        Expr::app(fv(&motive), succ(fv(&predecessor))),
    );
    let next = terms.local("succ", next_type, BinderInfo::Default);
    let hypothesis = terms.local(
        "n_ih",
        Expr::app(fv(&motive), fv(&predecessor)),
        BinderInfo::Default,
    );
    let step_body = Expr::app(fv(&next), fv(&predecessor));
    let step = terms.lam(&[predecessor, hypothesis], step_body);
    let body = app(
        constant("Nat.rec", vec![universe]),
        [fv(&motive), fv(&first), step, fv(&value)],
    );
    let result = Expr::app(fv(&motive), fv(&value));
    terms.definition(
        "Nat.casesOn",
        &["u"],
        &[motive, value, first, next],
        result,
        body,
    )
}

fn nat_below() -> Declaration {
    let mut terms = Terms::new();
    let universe = level("u");
    let result_level = Level::max(Level::one(), universe.clone()).expect("fixed below universe");
    let motive = terms.motive(&universe);
    let value = terms.local("t", nat(), BinderInfo::Default);
    let recursor_motive = terms.lam(
        std::slice::from_ref(&value),
        Expr::sort(result_level.clone()),
    );
    let predecessor = terms.local("n", nat(), BinderInfo::Default);
    let history_type = terms.local(
        "n_ih",
        Expr::sort(result_level.clone()),
        BinderInfo::Default,
    );
    let step_body = product(
        &universe,
        &result_level,
        Expr::app(fv(&motive), fv(&predecessor)),
        fv(&history_type),
    );
    let step = terms.lam(&[predecessor, history_type], step_body);
    let body = app(
        constant(
            "Nat.rec",
            vec![
                result_level
                    .clone()
                    .succ()
                    .expect("fixed below sort universe"),
            ],
        ),
        [
            recursor_motive,
            constant("PUnit", vec![result_level.clone()]),
            step,
            fv(&value),
        ],
    );
    terms.definition(
        "Nat.below",
        &["u"],
        &[motive, value],
        Expr::sort(result_level),
        body,
    )
}

fn nat_brec_on_go() -> Declaration {
    let mut terms = Terms::new();
    let universe = level("u");
    let result_level = Level::max(Level::one(), universe.clone()).expect("fixed brecOn universe");
    let motive = terms.motive(&universe);
    let value = terms.local("t", nat(), BinderInfo::Default);
    let functional = terms.functional(&universe, &motive);
    let result = product(
        &universe,
        &result_level,
        Expr::app(fv(&motive), fv(&value)),
        below(&universe, fv(&motive), fv(&value)),
    );
    let recursor_motive = terms.lam(std::slice::from_ref(&value), result.clone());
    let unit = constant("PUnit.unit", vec![result_level.clone()]);
    let first = pair(
        &universe,
        &result_level,
        Expr::app(fv(&motive), zero()),
        constant("PUnit", vec![result_level.clone()]),
        app(fv(&functional), [zero(), unit.clone()]),
        unit,
    );
    let predecessor = terms.local("n", nat(), BinderInfo::Default);
    let predecessor_result = product(
        &universe,
        &result_level,
        Expr::app(fv(&motive), fv(&predecessor)),
        below(&universe, fv(&motive), fv(&predecessor)),
    );
    let history = terms.local("n_ih", predecessor_result.clone(), BinderInfo::Default);
    let step_body = pair(
        &universe,
        &result_level,
        Expr::app(fv(&motive), succ(fv(&predecessor))),
        predecessor_result,
        app(fv(&functional), [succ(fv(&predecessor)), fv(&history)]),
        fv(&history),
    );
    let step = terms.lam(&[predecessor, history], step_body);
    let body = app(
        constant("Nat.rec", vec![result_level]),
        [recursor_motive, first, step, fv(&value)],
    );
    terms.definition(
        "Nat.brecOn.go",
        &["u"],
        &[motive, value, functional],
        result,
        body,
    )
}

fn nat_brec_on() -> Declaration {
    let mut terms = Terms::new();
    let universe = level("u");
    let motive = terms.motive(&universe);
    let value = terms.local("t", nat(), BinderInfo::Default);
    let functional = terms.functional(&universe, &motive);
    let combined = app(
        constant("Nat.brecOn.go", vec![universe]),
        [fv(&motive), fv(&value), fv(&functional)],
    );
    let body = Expr::proj(name("PProd"), 0, combined);
    let result = Expr::app(fv(&motive), fv(&value));
    terms.definition(
        "Nat.brecOn",
        &["u"],
        &[motive, value, functional],
        result,
        body,
    )
}

fn nat_add_match() -> Declaration {
    let mut terms = Terms::new();
    let universe = level("u_1");
    let first_type_argument = terms.local("x", nat(), BinderInfo::Default);
    let second_type_argument = terms.local("x_1", nat(), BinderInfo::Default);
    let motive_type = terms.pi(
        &[first_type_argument, second_type_argument],
        Expr::sort(universe.clone()),
    );
    let motive = terms.local("motive", motive_type, BinderInfo::Default);
    let left = terms.local("x", nat(), BinderInfo::Default);
    let right = terms.local("x_1", nat(), BinderInfo::Default);
    let a = terms.local("a", nat(), BinderInfo::Default);
    let b = terms.local("b", nat(), BinderInfo::Default);
    let first_type = terms.pi(std::slice::from_ref(&a), app(fv(&motive), [fv(&a), zero()]));
    let first = terms.local("h_1", first_type, BinderInfo::Default);
    let next_result = app(fv(&motive), [fv(&a), succ(fv(&b))]);
    let next_type = terms.pi(&[a, b], next_result);
    let next = terms.local("h_2", next_type, BinderInfo::Default);
    let major = terms.local("x_2", nat(), BinderInfo::Default);
    let recursor_motive = terms.lam(
        std::slice::from_ref(&major),
        app(fv(&motive), [fv(&left), fv(&major)]),
    );
    let step_body = app(fv(&next), [fv(&left), fv(&major)]);
    let step = terms.lam(&[major], step_body);
    let body = app(
        constant("Nat.casesOn", vec![universe]),
        [
            recursor_motive,
            fv(&right),
            Expr::app(fv(&first), fv(&left)),
            step,
        ],
    );
    let result = app(fv(&motive), [fv(&left), fv(&right)]);
    terms.definition(
        "Nat.add.match_1",
        &["u_1"],
        &[motive, left, right, first, next],
        result,
        body,
    )
}

fn nat_add_functional() -> Declaration {
    let mut terms = Terms::new();
    let universe = Level::one();
    let motive = terms.add_motive();
    let value = terms.local("x", nat(), BinderInfo::Default);
    let history = terms.local(
        "f",
        below(&universe, motive.clone(), fv(&value)),
        BinderInfo::Default,
    );
    let left = terms.local("x_1", nat(), BinderInfo::Default);
    let a = terms.local("a", nat(), BinderInfo::Default);
    let b = terms.local("b", nat(), BinderInfo::Default);
    let matcher_result = terms.arrow(below(&universe, motive.clone(), fv(&b)), nat());
    let matcher_motive = terms.lam(&[a.clone(), b.clone()], matcher_result);
    let zero_history = terms.local(
        "x",
        below(&universe, motive.clone(), zero()),
        BinderInfo::Default,
    );
    let first_body = fv(&a);
    let first = terms.lam(&[a.clone(), zero_history], first_body);
    let succ_history = terms.local(
        "x",
        below(&universe, motive, succ(fv(&b))),
        BinderInfo::Default,
    );
    let previous_function = Expr::proj(name("PProd"), 0, fv(&succ_history));
    let next_body = succ(Expr::app(previous_function, fv(&a)));
    let next = terms.lam(&[a, b, succ_history], next_body);
    let matched = app(
        constant("Nat.add.match_1", vec![universe]),
        [matcher_motive, fv(&left), fv(&value), first, next],
    );
    let body = Expr::app(matched, fv(&history));
    terms.definition("Nat.add._f", &[], &[value, history, left], nat(), body)
}

/// Minimal logical dependencies, ordered before every use. The product
/// projections in these bodies are primitive Proj nodes, so named projection
/// helpers and the separate brecOn equation theorem are not dependencies.
pub(super) fn nat_add_support_seed_declarations() -> [Declaration; 8] {
    [
        punit(),
        pprod(),
        nat_cases_on(),
        nat_below(),
        nat_brec_on_go(),
        nat_brec_on(),
        nat_add_match(),
        nat_add_functional(),
    ]
}

/// Arithmetic execution may replace the logical body only when that body's
/// complete fixed dependency closure is the seed's. Matching Nat.add itself
/// cannot detect a separately admitted Nat.add._f with different behavior.
/// This checks a bounded list of constants, including all generated family
/// metadata; it neither scans the environment nor consults optional journals.
pub(super) fn has_nat_add_seed_dependencies(environment: &Environment) -> bool {
    let matches =
        |expected: ConstantInfo| environment.find(&expected.constant_val().name) == Some(&expected);
    std::iter::once(super::nat_inductive_seed_declaration())
        .chain(nat_add_support_seed_declarations())
        .all(|declaration| match declaration {
            Declaration::Defn(definition) => matches(ConstantInfo::Defn(definition)),
            Declaration::Inductive(block) => {
                block
                    .types
                    .into_iter()
                    .all(|family| matches(ConstantInfo::Induct(family)))
                    && block
                        .ctors
                        .into_iter()
                        .all(|constructor| matches(ConstantInfo::Ctor(constructor)))
                    && block
                        .recursors
                        .into_iter()
                        .all(|recursor| matches(ConstantInfo::Rec(recursor)))
            }
            _ => false,
        })
}

pub(super) fn nat_add_seed_declaration() -> Declaration {
    let mut terms = Terms::new();
    let left = terms.local("x", nat(), BinderInfo::Default);
    let right = terms.local("x_1", nat(), BinderInfo::Default);
    let motive = terms.add_motive();
    let body = app(
        constant("Nat.brecOn", vec![Level::one()]),
        [
            motive,
            fv(&right),
            constant("Nat.add._f", Vec::new()),
            fv(&left),
        ],
    );
    let Declaration::Defn(mut declaration) =
        terms.definition("Nat.add", &[], &[left, right], nat(), body)
    else {
        unreachable!("fixed Nat.add definition candidate");
    };
    declaration.hints = ReducibilityHints::Regular(1);
    Declaration::Defn(declaration)
}
