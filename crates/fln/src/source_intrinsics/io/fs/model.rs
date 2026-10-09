//! Exact FilePath, open-mode and opaque Handle models from the pin.
//!
//! These terms are comparison data only. In particular, Handle's Unit default
//! and the primitive default bodies never provide executable file behavior.

use super::*;

fn name(label: &str) -> Name {
    Name::from_components(label.split('.'))
}

fn c(label: &str) -> Expr {
    Expr::const_(name(label), Vec::new())
}

fn b(index: u32) -> Expr {
    Expr::bvar(index).expect("fixed filesystem model binder")
}

fn pi(domain: Expr, body: Expr, info: BinderInfo) -> Expr {
    Expr::forall_e(Name::anonymous(), domain, body, info)
}

fn lam(domain: Expr, body: Expr) -> Expr {
    Expr::lam(Name::anonymous(), domain, body, BinderInfo::Default)
}

fn apply(head: Expr, arguments: impl IntoIterator<Item = Expr>) -> Expr {
    arguments.into_iter().fold(head, Expr::app)
}

fn base(label: &str, type_: Expr) -> ConstantVal {
    ConstantVal {
        name: name(label),
        level_params: Vec::new(),
        type_,
    }
}

fn inductive(label: &str, constructors: Vec<Name>) -> ConstantInfo {
    ConstantInfo::Induct(InductiveVal {
        base: base(label, Expr::sort(Level::one())),
        num_params: 0,
        num_indices: 0,
        all: vec![name(label)],
        ctors: constructors,
        num_nested: 0,
        is_rec: false,
        is_unsafe: false,
        is_reflexive: false,
    })
}

fn constructor(label: &str, family: &str, index: u32, fields: Vec<Expr>) -> ConstantInfo {
    ConstantInfo::Ctor(ConstructorVal {
        base: base(
            label,
            fields.iter().rev().fold(c(family), |body, field| {
                pi(field.clone(), body, BinderInfo::Default)
            }),
        ),
        induct: name(family),
        cidx: index,
        num_params: 0,
        num_fields: fields.len() as u32,
        is_unsafe: false,
    })
}

pub(super) fn handle() -> ConstantInfo {
    ConstantInfo::Opaque(OpaqueVal {
        base: base("IO.FS.Handle", Expr::sort(Level::one())),
        value: c("Unit"),
        is_unsafe: false,
        all: vec![name("IO.FS.Handle")],
    })
}

pub(super) fn open_layout() -> Vec<ConstantInfo> {
    let mut output = vec![
        inductive("System.FilePath", vec![name("System.FilePath.mk")]),
        constructor(
            "System.FilePath.mk",
            "System.FilePath",
            0,
            vec![c("String")],
        ),
        ConstantInfo::Defn(DefinitionVal {
            base: base(
                "System.FilePath.toString",
                pi(c("System.FilePath"), c("String"), BinderInfo::Default),
            ),
            value: lam(
                c("System.FilePath"),
                Expr::proj(name("System.FilePath"), 0, b(0)),
            ),
            hints: ReducibilityHints::Abbrev,
            safety: DefinitionSafety::Safe,
            all: vec![name("System.FilePath.toString")],
        }),
    ];
    let labels = ["read", "write", "writeNew", "readWrite", "append"];
    let constructors: Vec<_> = labels
        .iter()
        .map(|label| name(&format!("IO.FS.Mode.{label}")))
        .collect();
    output.push(inductive("IO.FS.Mode", constructors.clone()));
    for (index, label) in labels.into_iter().enumerate() {
        output.push(constructor(
            &format!("IO.FS.Mode.{label}"),
            "IO.FS.Mode",
            index as u32,
            Vec::new(),
        ));
    }
    let motive = pi(
        c("IO.FS.Mode"),
        Expr::sort(Level::param(name("u"))),
        BinderInfo::Default,
    );
    let minors: Vec<_> = constructors
        .iter()
        .enumerate()
        .map(|(index, constructor)| {
            Expr::app(
                b(index as u32),
                Expr::const_(constructor.clone(), Vec::new()),
            )
        })
        .collect();
    let tail = pi(c("IO.FS.Mode"), Expr::app(b(6), b(0)), BinderInfo::Default);
    let telescope = minors.iter().rev().fold(tail, |body, domain| {
        pi(domain.clone(), body, BinderInfo::Default)
    });
    let rules = constructors
        .into_iter()
        .enumerate()
        .map(|(index, ctor)| RecursorRule {
            ctor,
            nfields: 0,
            rhs: lam(
                motive.clone(),
                minors
                    .iter()
                    .rev()
                    .fold(b(4 - index as u32), |body, domain| {
                        lam(domain.clone(), body)
                    }),
            ),
        })
        .collect();
    output.push(ConstantInfo::Rec(RecursorVal {
        base: ConstantVal {
            name: name("IO.FS.Mode.rec"),
            level_params: vec![name("u")],
            type_: pi(motive, telescope, BinderInfo::Implicit),
        },
        all: vec![name("IO.FS.Mode")],
        num_params: 0,
        num_indices: 0,
        num_motives: 1,
        num_minors: 5,
        rules,
        k: false,
        is_unsafe: false,
    }));
    output
}

pub(super) fn primitive(operation: Operation) -> ConstantInfo {
    let (domains, result) = match operation {
        Operation::Open => (
            vec![c("System.FilePath"), c("IO.FS.Mode")],
            c("IO.FS.Handle"),
        ),
        Operation::PutStr => (vec![c("IO.FS.Handle"), c("String")], c("Unit")),
        Operation::GetLine => (vec![c("IO.FS.Handle")], c("String")),
    };
    let action = Expr::app(c("IO"), result.clone());
    let default = apply(
        Expr::const_(name("Inhabited.default"), vec![Level::one()]),
        [
            action.clone(),
            apply(
                c("instInhabitedEIO"),
                [c("IO.Error"), result, c("instInhabitedError")],
            ),
        ],
    );
    ConstantInfo::Opaque(OpaqueVal {
        base: ConstantVal {
            name: operation.source_name(),
            level_params: Vec::new(),
            type_: domains.iter().rev().fold(action, |body, domain| {
                pi(domain.clone(), body, BinderInfo::Default)
            }),
        },
        value: domains
            .into_iter()
            .rev()
            .fold(default, |body, domain| lam(domain, body)),
        is_unsafe: false,
        all: vec![operation.source_name()],
    })
}
