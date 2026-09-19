//! Small native collection candidates for the ordinary source seed.
//!
//! These are not trusted primitives. The families and generated recursors use
//! the existing inductive generator; every operation is a safe definition over
//! those recursors. The seed consumer must admit every row through its ordinary
//! kernel and independent-checker policy before publishing an environment.
mod list;

use super::*;
use crate::inductive::{ConstructorSpec, InductiveSpec, inductive_declaration};
use crate::lctx::LocalDecl;
use crate::records::{Builder, RecordBudget, app, fresh, fv};
use fln_core::expr::FVarId;
use std::collections::HashSet;

fn name(label: &str) -> Name {
    Name::from_components(label.split('.'))
}
fn level(label: &str) -> Level {
    Level::param(name(label))
}
fn type_level(label: &str) -> Level {
    level(label)
        .succ()
        .expect("fixed collection universe depth")
}
fn constant(label: &str, levels: Vec<Level>) -> Expr {
    Expr::const_(name(label), levels)
}
fn option(alpha: Expr, universe: Level) -> Expr {
    Expr::app(constant("Option", vec![universe]), alpha)
}

/// Fresh locals plus the existing capture-avoiding telescope closer. The work
/// bound covers only these fixed candidate constructions, not user programs.
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
    fn parameter(&mut self, label: &str, universe: &str) -> LocalDecl {
        self.local(
            label,
            Expr::sort(type_level(universe)),
            BinderInfo::Implicit,
        )
    }
    fn pi(&mut self, locals: &[LocalDecl], body: Expr) -> Expr {
        self.builder
            .close(locals, body, false, false)
            .expect("fixed collection type telescope")
    }
    fn lam(&mut self, locals: &[LocalDecl], body: Expr) -> Expr {
        self.builder
            .close(locals, body, true, false)
            .expect("fixed collection value telescope")
    }
    fn arrow(&mut self, domain: Expr, codomain: Expr) -> Expr {
        let argument = self.local("arg", domain, BinderInfo::Default);
        self.pi(&[argument], codomain)
    }
    fn definition(
        &mut self,
        label: &str,
        universes: &[&str],
        locals: &[LocalDecl],
        result: Expr,
        body: Expr,
    ) -> Declaration {
        let declaration_name = name(label);
        Declaration::Defn(DefinitionVal {
            base: ConstantVal {
                name: declaration_name.clone(),
                level_params: universes.iter().map(|u| name(u)).collect(),
                type_: self.pi(locals, result),
            },
            value: self.lam(locals, body),
            hints: ReducibilityHints::Abbrev,
            safety: DefinitionSafety::Safe,
            all: vec![declaration_name],
        })
    }
}

fn option_family() -> Declaration {
    let mut terms = Terms::new();
    // Family parameters are explicit; the generator makes constructor and
    // recursor parameters implicit, as required by the existing source path.
    let alpha = terms.local("α", Expr::sort(type_level("u")), BinderInfo::Default);
    let value = terms.local("val", fv(&alpha), BinderInfo::Default);
    inductive_declaration(
        &InductiveSpec {
            name: name("Option"),
            level_params: vec![name("u")],
            parameters: vec![alpha],
            indices: Vec::new(),
            constructors: vec![
                ConstructorSpec {
                    name: name("none"),
                    fields: Vec::new(),
                    result_indices: Vec::new(),
                },
                ConstructorSpec {
                    name: name("some"),
                    fields: vec![value],
                    result_indices: Vec::new(),
                },
            ],
            result_level: type_level("u"),
        },
        RecordBudget::default(),
    )
    .expect("fixed positive Option family")
}

fn option_get_d() -> Declaration {
    let mut terms = Terms::new();
    let alpha = terms.parameter("α", "u");
    let option_alpha = option(fv(&alpha), level("u"));
    let value = terms.local("self", option_alpha.clone(), BinderInfo::Default);
    let fallback = terms.local("fallback", fv(&alpha), BinderInfo::Default);
    let major = terms.local("t", option_alpha, BinderInfo::Default);
    let element = terms.local("a", fv(&alpha), BinderInfo::Default);
    let motive = terms.lam(&[major], fv(&alpha));
    let some = terms.lam(std::slice::from_ref(&element), fv(&element));
    let body = app(
        constant("Option.rec", vec![type_level("u"), level("u")]),
        [fv(&alpha), motive, fv(&fallback), some, fv(&value)],
    );
    let result = fv(&alpha);
    terms.definition(
        "Option.getD",
        &["u"],
        &[alpha, value, fallback],
        result,
        body,
    )
}

fn option_map() -> Declaration {
    let mut terms = Terms::new();
    let alpha = terms.parameter("α", "u");
    let beta = terms.parameter("β", "v");
    let function_type = terms.arrow(fv(&alpha), fv(&beta));
    let function = terms.local("f", function_type, BinderInfo::Default);
    let option_alpha = option(fv(&alpha), level("u"));
    let option_beta = option(fv(&beta), level("v"));
    let value = terms.local("self", option_alpha.clone(), BinderInfo::Default);
    let major = terms.local("t", option_alpha, BinderInfo::Default);
    let element = terms.local("a", fv(&alpha), BinderInfo::Default);
    let motive = terms.lam(&[major], option_beta.clone());
    let none = Expr::app(constant("Option.none", vec![level("v")]), fv(&beta));
    let mapped = app(
        constant("Option.some", vec![level("v")]),
        [fv(&beta), Expr::app(fv(&function), fv(&element))],
    );
    let some = terms.lam(&[element], mapped);
    let body = app(
        constant("Option.rec", vec![type_level("v"), level("u")]),
        [fv(&alpha), motive, none, some, fv(&value)],
    );
    terms.definition(
        "Option.map",
        &["u", "v"],
        &[alpha, beta, function, value],
        option_beta,
        body,
    )
}

fn option_bind() -> Declaration {
    let mut terms = Terms::new();
    let alpha = terms.parameter("α", "u");
    let beta = terms.parameter("β", "v");
    let option_alpha = option(fv(&alpha), level("u"));
    let option_beta = option(fv(&beta), level("v"));
    let value = terms.local("self", option_alpha.clone(), BinderInfo::Default);
    let function_type = terms.arrow(fv(&alpha), option_beta.clone());
    let function = terms.local("f", function_type, BinderInfo::Default);
    let major = terms.local("t", option_alpha, BinderInfo::Default);
    let motive = terms.lam(&[major], option_beta.clone());
    let none = Expr::app(constant("Option.none", vec![level("v")]), fv(&beta));
    let body = app(
        constant("Option.rec", vec![type_level("v"), level("u")]),
        [fv(&alpha), motive, none, fv(&function), fv(&value)],
    );
    terms.definition(
        "Option.bind",
        &["u", "v"],
        &[alpha, beta, value, function],
        option_beta,
        body,
    )
}

fn option_predicate(is_some: bool) -> Declaration {
    let mut terms = Terms::new();
    let alpha = terms.parameter("α", "u");
    let option_alpha = option(fv(&alpha), level("u"));
    let value = terms.local("self", option_alpha.clone(), BinderInfo::Default);
    let major = terms.local("t", option_alpha, BinderInfo::Default);
    let element = terms.local("a", fv(&alpha), BinderInfo::Default);
    let bool_type = constant("Bool", Vec::new());
    let motive = terms.lam(&[major], bool_type.clone());
    let (label, none, some) = if is_some {
        ("Option.isSome", "Bool.false", "Bool.true")
    } else {
        ("Option.isNone", "Bool.true", "Bool.false")
    };
    let some = terms.lam(&[element], constant(some, Vec::new()));
    let body = app(
        constant("Option.rec", vec![Level::one(), level("u")]),
        [
            fv(&alpha),
            motive,
            constant(none, Vec::new()),
            some,
            fv(&value),
        ],
    );
    terms.definition(label, &["u"], &[alpha, value], bool_type, body)
}

/// The family precedes every operation. No declaration is admitted here.
pub(super) fn option_seed_declarations() -> [Declaration; 6] {
    [
        option_family(),
        option_get_d(),
        option_map(),
        option_bind(),
        option_predicate(true),
        option_predicate(false),
    ]
}

/// Option must already be available because List.head? returns it.
pub(super) fn list_seed_declarations() -> [Declaration; 9] {
    list::declarations()
}
