//! Logical-layout unit controls. These raw environment rows are test data, not
//! admission evidence; source_deriving_repr exercises actual admitted artifacts.
use super::*;
use fln_env::constants::{ConstantVal, ConstructorVal, InductiveVal};
use fln_vm::interpreter::{CompletedExecution, ExecutionUsage};

fn constant(label: &str) -> Expr {
    Expr::const_(name(label), vec![])
}

fn domain_expr(domain: Domain) -> Expr {
    match domain {
        Domain::Constant(label) => constant(label),
        Domain::BehaviorDefault => Expr::app(
            Expr::app(
                Expr::const_(name("optParam"), vec![Level::one()]),
                constant(BEHAVIOR),
            ),
            constant("Std.Format.FlattenBehavior.allOrNone"),
        ),
        Domain::ValidUtf8 => Expr::app(constant("ByteArray.IsValidUTF8"), Expr::bvar(0).unwrap()),
    }
}

fn rows() -> Vec<ConstantInfo> {
    let mut rows = Vec::new();
    for (label, recursive, specs) in [
        (FORMAT, true, FORMAT_CTORS.as_slice()),
        (BEHAVIOR, false, BEHAVIOR_CTORS.as_slice()),
        ("Int", false, INT_CTORS.as_slice()),
        ("Bool", false, BOOL_CTORS.as_slice()),
        ("Nat", true, NAT_CTORS.as_slice()),
        ("String", false, STRING_CTORS.as_slice()),
    ] {
        rows.push(ConstantInfo::Induct(InductiveVal {
            base: ConstantVal {
                name: name(label),
                level_params: vec![],
                type_: Expr::sort(Level::one()),
            },
            num_params: 0,
            num_indices: 0,
            all: vec![name(label)],
            ctors: specs.iter().map(|spec| name(spec.label)).collect(),
            num_nested: 0,
            is_rec: recursive,
            is_unsafe: false,
            is_reflexive: false,
        }));
        for (index, spec) in specs.iter().enumerate() {
            let type_ = spec
                .domains
                .iter()
                .rev()
                .fold(constant(label), |body, domain| {
                    Expr::forall_e(
                        Name::anonymous(),
                        domain_expr(*domain),
                        body,
                        BinderInfo::Default,
                    )
                });
            rows.push(ConstantInfo::Ctor(ConstructorVal {
                base: ConstantVal {
                    name: name(spec.label),
                    level_params: vec![],
                    type_,
                },
                induct: name(label),
                cidx: index as u32,
                num_params: 0,
                num_fields: spec.domains.len() as u32,
                is_unsafe: false,
            }));
        }
    }
    for (label, type_, num_params) in [
        ("ByteArray", Expr::sort(Level::one()), 0),
        (
            "ByteArray.IsValidUTF8",
            Expr::forall_e(
                Name::anonymous(),
                constant("ByteArray"),
                Expr::sort(Level::zero()),
                BinderInfo::Default,
            ),
            1,
        ),
    ] {
        rows.push(ConstantInfo::Induct(InductiveVal {
            base: ConstantVal {
                name: name(label),
                level_params: vec![],
                type_,
            },
            num_params,
            num_indices: 0,
            all: vec![name(label)],
            ctors: vec![],
            num_nested: 0,
            is_rec: false,
            is_unsafe: false,
            is_reflexive: false,
        }));
    }
    rows
}

fn environment(rows: Vec<ConstantInfo>) -> Environment {
    rows.into_iter()
        .fold(Environment::new(), |env, row| env.add_decl(row).unwrap())
}

fn usage() -> ExecutionUsage {
    ExecutionUsage {
        steps: 0,
        system_polls: 0,
        peak_stack_depth: 0,
    }
}

fn exit(value: Obj) -> VmExit {
    VmExit::Returned(CompletedExecution {
        value,
        usage: usage(),
    })
}

fn ctor(tag: u8, children: Vec<Obj>) -> Obj {
    Obj::mk_ctor(tag, children, &[])
}

fn text(value: &str) -> Obj {
    ctor(3, vec![Obj::mk_string(value)])
}

fn append(left: Obj, right: Obj) -> Obj {
    ctor(5, vec![left, right])
}

fn integer(value: i64) -> Obj {
    let magnitude = if value < 0 {
        (-1 - value) as u64
    } else {
        value as u64
    };
    ctor(u8::from(value < 0), vec![Obj::mk_mpz(&[magnitude], false)])
}

fn nest(indent: i64, inner: Obj) -> Obj {
    ctor(4, vec![integer(indent), inner])
}

fn group(inner: Obj, fill: bool) -> Obj {
    ctor(6, vec![inner, ctor(u8::from(fill), vec![])])
}

fn display(value: Obj, width: usize, limits: Limits) -> Result<String, Error> {
    render_vm(
        &environment(rows()),
        &constant(FORMAT),
        &exit(value),
        width,
        limits,
    )
}

#[test]
fn logical_constructors_preserve_unicode_nul_groups_alignment_and_ignored_tags() {
    let formatted = || {
        group(
            nest(2, append(text("α"), append(ctor(1, vec![]), text("β")))),
            false,
        )
    };
    assert_eq!(display(formatted(), 80, Limits::default()).unwrap(), "α β");
    assert_eq!(
        display(formatted(), 1, Limits::default()).unwrap(),
        "α\n  β"
    );
    assert_eq!(
        display(text("λ\0z"), usize::MAX, Limits::default()).unwrap(),
        "λ\0z"
    );
    let aligned = nest(
        2,
        append(text("."), append(ctor(2, vec![Obj::mk_nat(1)]), text("a"))),
    );
    assert_eq!(display(aligned, 80, Limits::default()).unwrap(), ". a");
    let filled = group(
        append(
            text("a"),
            append(
                ctor(1, vec![]),
                append(text("b"), append(ctor(1, vec![]), text("c"))),
            ),
        ),
        true,
    );
    assert_eq!(display(filled, 3, Limits::default()).unwrap(), "a b\nc");
    let tagged = ctor(7, vec![Obj::mk_mpz(&[0, 0, 1], false), ctor(0, vec![])]);
    assert_eq!(
        display(
            tagged,
            1,
            Limits {
                max_nodes: 3,
                max_text_bytes: 0,
                ..Limits::default()
            }
        )
        .unwrap(),
        ""
    );
    assert_eq!(
        display(nest(-3, text("a\nb")), 1, Limits::default()).unwrap(),
        "a\nb"
    );
}

#[test]
fn projection_and_renderer_limits_are_exact_and_leave_retries_unchanged() {
    let value = exit(append(text("λ"), text("y")));
    let env = environment(rows());
    let limits = Limits {
        max_nodes: 5,
        max_depth: 1,
        max_text_bytes: 3,
        ..Limits::default()
    };
    let render = |limits| render_vm(&env, &constant(FORMAT), &value, 120, limits);
    assert_eq!(render(limits).unwrap(), "λy");
    for (limits, expected) in [
        (
            Limits {
                max_nodes: 4,
                ..limits
            },
            Error::Limit {
                resource: "nodes",
                limit: 4,
                observed: 5,
            },
        ),
        (
            Limits {
                max_depth: 0,
                ..limits
            },
            Error::Limit {
                resource: "depth",
                limit: 0,
                observed: 1,
            },
        ),
        (
            Limits {
                max_text_bytes: 2,
                ..limits
            },
            Error::Limit {
                resource: "text bytes",
                limit: 2,
                observed: 3,
            },
        ),
        (
            Limits {
                rendering: FormatRenderLimits {
                    max_work: 0,
                    max_output_bytes: 3,
                },
                ..limits
            },
            Error::Render(FormatRenderError::WorkLimit { limit: 0 }),
        ),
        (
            Limits {
                rendering: FormatRenderLimits {
                    max_work: 1000,
                    max_output_bytes: 2,
                },
                ..limits
            },
            Error::Render(FormatRenderError::OutputLimit {
                limit: 2,
                requested: 3,
            }),
        ),
    ] {
        assert_eq!(render(limits), Err(expected));
        assert_eq!(expected.disposition(), ("resource", false, 3));
    }
    assert_eq!(render(limits).unwrap(), "λy");
    assert_eq!(
        display(
            text(""),
            0,
            Limits {
                max_depth: 0,
                max_text_bytes: 0,
                ..Limits::default()
            }
        )
        .unwrap(),
        ""
    );
}

#[test]
fn integer_ranges_and_owned_depth_are_bounded_before_rendering() {
    for signed in [i64::MIN, -1, 0, i64::MAX] {
        assert_eq!(
            display(nest(signed, ctor(0, vec![])), 0, Limits::default()).unwrap(),
            ""
        );
    }
    let too_large = ctor(
        4,
        vec![
            ctor(0, vec![Obj::mk_mpz(&[1 << 63], false)]),
            ctor(0, vec![]),
        ],
    );
    assert_eq!(
        display(too_large, 0, Limits::default()),
        Err(Error::IntegerRange)
    );
    let overflow = nest(-1, nest(i64::MIN, ctor(0, vec![])));
    assert_eq!(
        display(overflow, 0, Limits::default()),
        Err(Error::Render(FormatRenderError::ArithmeticOverflow))
    );
    let mut deep = ctor(0, vec![]);
    for _ in 0..=MAX_DEPTH {
        deep = nest(0, deep);
    }
    assert_eq!(
        display(
            deep,
            0,
            Limits {
                max_depth: usize::MAX,
                ..Limits::default()
            }
        ),
        Err(Error::Limit {
            resource: "depth",
            limit: MAX_DEPTH,
            observed: MAX_DEPTH + 1
        })
    );
}

#[test]
fn malformed_logical_values_cannot_acquire_native_formatting_meaning() {
    for value in [
        Obj::mk_nat(0),
        ctor(8, vec![]),
        ctor(0, vec![Obj::mk_nat(0)]),
        Obj::mk_ctor(0, vec![], &[0]),
        ctor(2, vec![Obj::mk_nat(2)]),
        ctor(2, vec![ctor(0, vec![])]),
        ctor(3, vec![Obj::mk_nat(0)]),
        ctor(4, vec![Obj::mk_int(2), ctor(0, vec![])]),
        ctor(4, vec![ctor(2, vec![Obj::mk_nat(0)]), ctor(0, vec![])]),
        ctor(
            4,
            vec![ctor(0, vec![Obj::mk_mpz(&[2], true)]), ctor(0, vec![])],
        ),
        ctor(6, vec![ctor(0, vec![]), Obj::mk_nat(0)]),
        ctor(6, vec![ctor(0, vec![]), ctor(2, vec![])]),
        ctor(7, vec![Obj::mk_mpz(&[2], true), ctor(0, vec![])]),
    ] {
        let error = display(value, 120, Limits::default()).unwrap_err();
        assert!(matches!(error, Error::Representation { .. }), "{error:?}");
        assert_eq!(error.disposition(), ("internal-fault", false, 4));
    }
}

#[test]
fn contract_guard_rejects_altered_families_constructor_types_and_layouts() {
    for mutation in 0..16 {
        let mut rows = rows();
        match mutation {
            0..=6 => {
                let ConstantInfo::Induct(row) = &mut rows[0] else {
                    unreachable!()
                };
                match mutation {
                    0 => row.is_unsafe = true,
                    1 => row.num_params = 1,
                    2 => row.ctors.swap(0, 1),
                    3 => row.base.type_ = Expr::sort(Level::zero()),
                    4 => row.all.push(name("Other")),
                    5 => row.is_rec = false,
                    6 => row.is_reflexive = true,
                    _ => unreachable!(),
                }
            }
            7..=11 => {
                let ConstantInfo::Ctor(row) = &mut rows[4] else {
                    unreachable!()
                };
                match mutation {
                    7 => row.is_unsafe = true,
                    8 => row.cidx = 2,
                    9 => row.num_fields = 0,
                    10 => {
                        row.base.type_ = Expr::forall_e(
                            Name::anonymous(),
                            constant("Nat"),
                            constant(FORMAT),
                            BinderInfo::Default,
                        )
                    }
                    11 => {
                        row.base.type_ = Expr::forall_e(
                            Name::anonymous(),
                            constant("String"),
                            constant(FORMAT),
                            BinderInfo::Implicit,
                        )
                    }
                    _ => unreachable!(),
                }
            }
            12 => rows.retain(|row| row.name() != &name("String.ofByteArray")),
            13 => {
                let row = rows
                    .iter_mut()
                    .find(|row| row.name() == &name("String.ofByteArray"))
                    .unwrap();
                let ConstantInfo::Ctor(row) = row else {
                    unreachable!()
                };
                row.base.type_ = Expr::forall_e(
                    Name::anonymous(),
                    constant("ByteArray"),
                    constant("String"),
                    BinderInfo::Default,
                );
                row.num_fields = 1;
            }
            14 | 15 => {
                let label = if mutation == 14 {
                    "ByteArray.IsValidUTF8"
                } else {
                    "ByteArray"
                };
                let row = rows
                    .iter_mut()
                    .find(|row| row.name() == &name(label))
                    .unwrap();
                let ConstantInfo::Induct(row) = row else {
                    unreachable!()
                };
                row.base.type_ = if mutation == 14 {
                    Expr::forall_e(
                        Name::anonymous(),
                        constant("ByteArray"),
                        Expr::sort(Level::one()),
                        BinderInfo::Default,
                    )
                } else {
                    Expr::sort(Level::zero())
                };
            }
            _ => unreachable!(),
        }
        let error = render_vm(
            &environment(rows),
            &constant(FORMAT),
            &exit(text("x")),
            120,
            Limits::default(),
        )
        .unwrap_err();
        assert!(
            matches!(error, Error::UnsupportedContract { .. }),
            "mutation {mutation}: {error:?}"
        );
        assert_eq!(error.disposition(), ("capability", false, 5));
    }
    let env = environment(rows());
    assert_eq!(
        render_vm(
            &env,
            &constant("String"),
            &exit(text("x")),
            120,
            Limits::default()
        ),
        Err(Error::UnexpectedType)
    );
    let failed = VmExit::Panicked {
        message: "user panic".into(),
        usage: usage(),
    };
    assert_eq!(
        render_vm(&env, &constant(FORMAT), &failed, 120, Limits::default()),
        Err(Error::NonReturningExit)
    );
}
