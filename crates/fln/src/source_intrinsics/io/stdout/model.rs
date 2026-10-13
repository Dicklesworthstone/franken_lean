//! Pinned layout models, checked against StdoutModels.oracle.log. Values here
//! are comparison data; none is installed into a logical environment.

use super::*;

#[derive(Clone, Copy)]
pub(crate) enum ErrorFields {
    OptionalFileCodeDetails,
    CodeDetails,
    FileCodeDetails,
    Empty,
    Message,
}

pub(crate) fn error_cases() -> [(&'static str, ErrorFields); 19] {
    use ErrorFields::*;
    [
        ("alreadyExists", OptionalFileCodeDetails),
        ("otherError", CodeDetails),
        ("resourceBusy", CodeDetails),
        ("resourceVanished", CodeDetails),
        ("unsupportedOperation", CodeDetails),
        ("hardwareFault", CodeDetails),
        ("unsatisfiedConstraints", CodeDetails),
        ("illegalOperation", CodeDetails),
        ("protocolError", CodeDetails),
        ("timeExpired", CodeDetails),
        ("interrupted", FileCodeDetails),
        ("noFileOrDirectory", FileCodeDetails),
        ("invalidArgument", OptionalFileCodeDetails),
        ("permissionDenied", OptionalFileCodeDetails),
        ("resourceExhausted", OptionalFileCodeDetails),
        ("inappropriateType", OptionalFileCodeDetails),
        ("noSuchThing", OptionalFileCodeDetails),
        ("unexpectedEof", Empty),
        ("userError", Message),
    ]
}

fn name(label: &str) -> Name {
    Name::from_components(label.split('.'))
}

fn constant(label: &str, levels: Vec<Level>) -> Expr {
    Expr::const_(name(label), levels)
}

fn c(label: &str) -> Expr {
    constant(label, vec![])
}

fn apply(head: Expr, arguments: impl IntoIterator<Item = Expr>) -> Expr {
    arguments.into_iter().fold(head, Expr::app)
}

fn b(index: u32) -> Expr {
    Expr::bvar(index).expect("fixed stdout model binder")
}

fn pi(domain: Expr, body: Expr) -> Expr {
    Expr::forall_e(Name::anonymous(), domain, body, BinderInfo::Default)
}

fn implicit(domain: Expr, body: Expr) -> Expr {
    Expr::forall_e(Name::anonymous(), domain, body, BinderInfo::Implicit)
}

fn type_() -> Expr {
    Expr::sort(Level::one())
}

fn base(label: &str, levels: Vec<Name>, type_: Expr) -> ConstantVal {
    ConstantVal {
        name: name(label),
        level_params: levels,
        type_,
    }
}

fn inductive(
    label: &str,
    levels: Vec<Name>,
    params: u32,
    type_: Expr,
    ctors: Vec<Name>,
) -> ConstantInfo {
    ConstantInfo::Induct(InductiveVal {
        base: base(label, levels, type_),
        num_params: params,
        num_indices: 0,
        all: vec![name(label)],
        ctors,
        num_nested: 0,
        is_rec: false,
        is_unsafe: false,
        is_reflexive: false,
    })
}

fn constructor(
    label: &str,
    family: &str,
    levels: Vec<Name>,
    index: u32,
    params: u32,
    fields: u32,
    type_: Expr,
) -> ConstantInfo {
    ConstantInfo::Ctor(ConstructorVal {
        base: base(label, levels, type_),
        induct: name(family),
        cidx: index,
        num_params: params,
        num_fields: fields,
        is_unsafe: false,
    })
}

fn alias(label: &str, type_: Expr, value: Expr) -> ConstantInfo {
    ConstantInfo::Defn(DefinitionVal {
        base: base(label, vec![], type_),
        value,
        hints: ReducibilityHints::Abbrev,
        safety: DefinitionSafety::Safe,
        all: vec![name(label)],
    })
}

fn of_nat(value: u64) -> Expr {
    let value = Expr::lit(fln_core::expr::Literal::Nat(NatLit::from_u64(value)));
    apply(
        constant("OfNat.ofNat", vec![Level::zero()]),
        [c("Nat"), value.clone(), Expr::app(c("instOfNatNat"), value)],
    )
}

pub(crate) fn stream_fields() -> [Expr; 6] {
    let io = |label| Expr::app(c("IO"), c(label));
    [
        io("Unit"),
        pi(c("USize"), io("ByteArray")),
        pi(c("ByteArray"), io("Unit")),
        io("String"),
        pi(c("String"), io("Unit")),
        Expr::app(c("BaseIO"), c("Bool")),
    ]
}

pub(super) fn declarations() -> Vec<ConstantInfo> {
    declarations_for(Getter::Stdout)
}

pub(super) fn declarations_for(getter: Getter) -> Vec<ConstantInfo> {
    let mut output = Vec::new();
    let stream = c("IO.FS.Stream");
    let action = Expr::app(c("BaseIO"), stream.clone());
    output.push(ConstantInfo::Opaque(OpaqueVal {
        base: ConstantVal {
            name: getter.source_name(),
            level_params: vec![],
            type_: action.clone(),
        },
        value: apply(
            constant("Inhabited.default", vec![Level::one()]),
            [
                action,
                apply(
                    constant("instInhabitedOfMonad", vec![Level::zero(); 2]),
                    [
                        stream.clone(),
                        c("BaseIO"),
                        c("instMonadBaseIO"),
                        c("IO.FS.instInhabitedStream"),
                    ],
                ),
            ],
        ),
        is_unsafe: false,
        all: vec![getter.source_name()],
    }));
    output.push(inductive(
        "IO.FS.Stream",
        vec![],
        0,
        type_(),
        vec![name("IO.FS.Stream.mk")],
    ));
    output.push(constructor(
        "IO.FS.Stream.mk",
        "IO.FS.Stream",
        vec![],
        0,
        0,
        6,
        stream_fields()
            .into_iter()
            .rev()
            .fold(stream, |body, field| pi(field, body)),
    ));
    output
}

pub(super) fn result_declarations() -> Vec<ConstantInfo> {
    let mut output = Vec::new();
    let errors = error_cases();
    output.push(inductive(
        "IO.Error",
        vec![],
        0,
        type_(),
        errors
            .iter()
            .map(|(label, _)| name(&format!("IO.Error.{label}")))
            .collect(),
    ));
    for (index, (label, shape)) in errors.into_iter().enumerate() {
        let string = c("String");
        let code = c("UInt32");
        let fields = match shape {
            ErrorFields::OptionalFileCodeDetails => vec![
                Expr::app(constant("Option", vec![Level::zero()]), string.clone()),
                code,
                string,
            ],
            ErrorFields::CodeDetails => vec![code, string],
            ErrorFields::FileCodeDetails => vec![string.clone(), code, string],
            ErrorFields::Empty => vec![],
            ErrorFields::Message => vec![string],
        };
        output.push(constructor(
            &format!("IO.Error.{label}"),
            "IO.Error",
            vec![],
            index as u32,
            0,
            fields.len() as u32,
            fields
                .into_iter()
                .rev()
                .fold(c("IO.Error"), |body, field| pi(field, body)),
        ));
    }
    let universe = name("u");
    let level = Level::param(universe.clone());
    output.extend([
        alias("Unit", type_(), constant("PUnit", vec![Level::one()])),
        alias(
            "Unit.unit",
            c("Unit"),
            constant("PUnit.unit", vec![Level::one()]),
        ),
        inductive(
            "PUnit",
            vec![universe.clone()],
            0,
            Expr::sort(level.clone()),
            vec![name("PUnit.unit")],
        ),
        constructor(
            "PUnit.unit",
            "PUnit",
            vec![universe.clone()],
            0,
            0,
            0,
            constant("PUnit", vec![level.clone()]),
        ),
        inductive("UInt32", vec![], 0, type_(), vec![name("UInt32.ofBitVec")]),
        constructor(
            "UInt32.ofBitVec",
            "UInt32",
            vec![],
            0,
            0,
            1,
            pi(Expr::app(c("BitVec"), of_nat(32)), c("UInt32")),
        ),
        inductive(
            "BitVec",
            vec![],
            1,
            pi(c("Nat"), type_()),
            vec![name("BitVec.ofFin")],
        ),
    ]);
    let pow = apply(
        constant("HPow.hPow", vec![Level::zero(); 3]),
        [
            c("Nat"),
            c("Nat"),
            c("Nat"),
            apply(
                constant("instHPow", vec![Level::zero(); 2]),
                [
                    c("Nat"),
                    c("Nat"),
                    apply(
                        constant("instPowNat", vec![Level::zero()]),
                        [c("Nat"), c("instNatPowNat")],
                    ),
                ],
            ),
            of_nat(2),
            b(0),
        ],
    );
    output.push(constructor(
        "BitVec.ofFin",
        "BitVec",
        vec![],
        0,
        1,
        1,
        implicit(
            c("Nat"),
            pi(Expr::app(c("Fin"), pow), Expr::app(c("BitVec"), b(1))),
        ),
    ));
    output.push(inductive(
        "Fin",
        vec![],
        1,
        pi(c("Nat"), type_()),
        vec![name("Fin.mk")],
    ));
    output.push(constructor(
        "Fin.mk",
        "Fin",
        vec![],
        0,
        1,
        2,
        implicit(
            c("Nat"),
            pi(
                c("Nat"),
                pi(
                    apply(
                        constant("LT.lt", vec![Level::zero()]),
                        [c("Nat"), c("instLTNat"), b(0), b(1)],
                    ),
                    Expr::app(c("Fin"), b(2)),
                ),
            ),
        ),
    ));
    let option_sort = Expr::sort(level.clone().succ().expect("fixed Option universe"));
    output.extend([
        inductive(
            "Option",
            vec![universe.clone()],
            1,
            pi(option_sort.clone(), option_sort.clone()),
            vec![name("Option.none"), name("Option.some")],
        ),
        constructor(
            "Option.none",
            "Option",
            vec![universe.clone()],
            0,
            1,
            0,
            implicit(
                option_sort.clone(),
                Expr::app(constant("Option", vec![level.clone()]), b(0)),
            ),
        ),
        constructor(
            "Option.some",
            "Option",
            vec![universe],
            1,
            1,
            1,
            implicit(
                option_sort,
                pi(b(0), Expr::app(constant("Option", vec![level]), b(1))),
            ),
        ),
    ]);
    output
}
