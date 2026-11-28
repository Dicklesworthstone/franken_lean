//! Proved constructor domains must not hide actual unmatched runtime values.
use super::super::{
    CompileLimits, SourceConstructor, SourceSignature, compile_module, validate_module,
};
use super::*;
use fln_comp::flbc::{ArgumentOwnership as Ownership, CallableResultOwnership as ResultOwnership};
use fln_core::name::Name;
use fln_olean::ir::IrType;

fn binding(id: u32, ty: fir::ValueType, operation: fir::Operation) -> fir::Binding {
    fir::Binding {
        id: fir::ValueId::new(id),
        ty,
        operation,
    }
}

fn block(id: u32, bindings: Vec<fir::Binding>, terminator: fir::Terminator) -> fir::Block {
    fir::Block {
        id: fir::BlockId::new(id),
        bindings,
        terminator,
    }
}

fn function(
    id: u32,
    parameters: Vec<fir::ValueType>,
    result: fir::ValueType,
    blocks: Vec<fir::Block>,
) -> fir::Function {
    fir::Function {
        id: fir::FunctionId::new(id),
        parameter_ownership: vec![Ownership::Borrowed; parameters.len()],
        parameters,
        result,
        result_ownership: if result == fir::ValueType::Nat {
            ResultOwnership::OwnedOrScalar
        } else {
            ResultOwnership::Owned
        },
        blocks,
    }
}

// A Boolean helper applies two captured literal closures; their constructor
// result flows through an alias to a separate two-arm constructor dispatcher.
// A third valid constructor exists globally, exactly as with a source enum.
fn raw_program(unmatched: bool, expose_dispatcher: bool) -> fir::Program {
    use fir::Operation as O;
    use fir::Terminator as T;
    use fir::ValueType::{Bool, Closure, Constructor, Nat, String as Text};
    let value = fir::ValueId::new;
    let ctor = fir::ConstructorId::new;
    let callable = fir::FunctionId::new;
    let signature = fir::ClosureTypeId::new;
    let mut entry = vec![
        binding(0, Bool, O::Bool(true)),
        binding(
            1,
            Closure(signature(0)),
            O::Closure {
                closure_type: signature(0),
                function: callable(1),
                captures: vec![value(0)],
                capture_ownership: vec![Ownership::Borrowed],
            },
        ),
        binding(
            2,
            Closure(signature(0)),
            O::Closure {
                closure_type: signature(0),
                function: callable(2),
                captures: vec![value(0)],
                capture_ownership: vec![Ownership::Borrowed],
            },
        ),
        binding(
            3,
            Constructor,
            O::Call {
                function: callable(3),
                args: vec![value(0), value(1), value(2)],
            },
        ),
        binding(4, Constructor, O::Alias(value(3))),
        binding(
            5,
            Nat,
            O::Call {
                function: callable(4),
                args: vec![value(4)],
            },
        ),
    ];
    if expose_dispatcher {
        entry.push(binding(
            6,
            Closure(signature(1)),
            O::Closure {
                closure_type: signature(1),
                function: callable(4),
                captures: vec![],
                capture_ownership: vec![],
            },
        ));
    }
    let functions = vec![
        function(
            0,
            vec![],
            Nat,
            vec![block(0, entry, T::Return { value: value(5) })],
        ),
        function(
            1,
            vec![Bool, Bool],
            Constructor,
            vec![block(
                0,
                vec![binding(
                    2,
                    Constructor,
                    O::Ctor {
                        constructor: ctor(0),
                        fields: vec![],
                    },
                )],
                T::Return { value: value(2) },
            )],
        ),
        function(
            2,
            vec![Bool, Bool],
            Constructor,
            vec![block(
                0,
                vec![binding(
                    2,
                    Constructor,
                    O::Ctor {
                        constructor: ctor(if unmatched { 2 } else { 1 }),
                        fields: vec![],
                    },
                )],
                T::Return { value: value(2) },
            )],
        ),
        function(
            3,
            vec![Bool, Closure(signature(0)), Closure(signature(0))],
            Constructor,
            vec![
                block(
                    0,
                    vec![],
                    T::BranchZero {
                        condition: value(0),
                        zero: fir::BlockId::new(1),
                        nonzero: fir::BlockId::new(2),
                    },
                ),
                block(
                    1,
                    vec![binding(
                        3,
                        Constructor,
                        O::Apply {
                            closure: value(1),
                            args: vec![value(0)],
                            argument_ownership: vec![Ownership::Borrowed],
                            result_ownership: ResultOwnership::Owned,
                        },
                    )],
                    T::Return { value: value(3) },
                ),
                block(
                    2,
                    vec![binding(
                        4,
                        Constructor,
                        O::Apply {
                            closure: value(2),
                            args: vec![value(0)],
                            argument_ownership: vec![Ownership::Borrowed],
                            result_ownership: ResultOwnership::Owned,
                        },
                    )],
                    T::Return { value: value(4) },
                ),
            ],
        ),
        function(
            4,
            vec![Constructor],
            Nat,
            vec![
                block(
                    0,
                    vec![binding(
                        1,
                        Bool,
                        O::CtorTest {
                            constructor: ctor(0),
                            value: value(0),
                        },
                    )],
                    T::BranchZero {
                        condition: value(1),
                        zero: fir::BlockId::new(2),
                        nonzero: fir::BlockId::new(1),
                    },
                ),
                block(
                    1,
                    vec![binding(2, Nat, O::Nat(42))],
                    T::Return { value: value(2) },
                ),
                block(
                    2,
                    vec![binding(
                        3,
                        Bool,
                        O::CtorTest {
                            constructor: ctor(1),
                            value: value(0),
                        },
                    )],
                    T::BranchZero {
                        condition: value(3),
                        zero: fir::BlockId::new(4),
                        nonzero: fir::BlockId::new(3),
                    },
                ),
                block(
                    3,
                    vec![binding(4, Nat, O::Nat(43))],
                    T::Return { value: value(4) },
                ),
                block(
                    4,
                    vec![binding(
                        5,
                        Text,
                        O::String("real unmatched constructor".into()),
                    )],
                    T::Panic { message: value(5) },
                ),
            ],
        ),
        // No call reaches this parameter. Bottom must not be exported as an
        // empty runtime domain or confused with a proof of impossibility.
        function(
            5,
            vec![Constructor],
            Constructor,
            vec![block(0, vec![], T::Return { value: value(0) })],
        ),
    ];
    fir::Program::new_with_closures(
        callable(0),
        (0..3)
            .map(|tag| fir::ConstructorDecl {
                id: ctor(u32::from(tag)),
                tag,
                fields: vec![],
                static_scalar_bytes: vec![],
            })
            .collect(),
        vec![],
        vec![
            fir::ClosureTypeDecl {
                id: signature(0),
                parameters: vec![Bool],
                parameter_ownership: vec![Ownership::Borrowed],
                result: Constructor,
                result_ownership: ResultOwnership::Owned,
            },
            fir::ClosureTypeDecl {
                id: signature(1),
                parameters: vec![Constructor],
                parameter_ownership: vec![Ownership::Borrowed],
                result: Nat,
                result_ownership: ResultOwnership::OwnedOrScalar,
            },
        ],
        vec![],
        functions,
    )
}

fn program(unmatched: bool, expose_dispatcher: bool) -> fir::ValidatedProgram {
    fir::validate(
        raw_program(unmatched, expose_dispatcher),
        fir::ValidationLimits::default(),
    )
    .unwrap()
}

fn constructors() -> InternalConstructors {
    let mut tags = ConstructorTags::default();
    for tag in 0..3 {
        tags.insert(tag);
    }
    InternalConstructors {
        type_name: Name::from_components(["flow_data"]),
        layouts: (0..3).map(|tag| ((tag, 0), tag)).collect(),
        packed: Default::default(),
        unboxed: false,
        tags,
    }
}

fn compile(program: &fir::ValidatedProgram) -> Result<()> {
    let mut meter = Budget(64_000_000);
    let entry = Name::from_components(["constructor_flow"]);
    let source = SourceSignature {
        name: entry.clone(),
        params: vec![],
        result: IrType::TObject,
        reduced: None,
        inferred_borrowing: false,
        constructor_fields: vec![SourceConstructor::Standard(Vec::new()); 3],
    };
    let module = compile_module(
        program,
        &entry,
        CompileLimits::default(),
        Some(&source),
        &mut meter,
    )?;
    validate_module(&module, &meter)
}

#[test]
fn captured_branch_results_prove_only_the_actual_dispatch_domain() {
    let program = program(false, false);
    let masks = parameters(&program, &constructors(), &mut Budget(64_000_000)).unwrap();
    assert!(masks[4][0].contains(0));
    assert!(masks[4][0].contains(1));
    assert!(!masks[4][0].contains(2));
    assert!(
        masks[5][0].is_empty(),
        "unvisited parameters remain unconstrained"
    );
    compile(&program).unwrap();
}

#[test]
fn partial_applications_keep_their_target_and_actual_constructor_results() {
    use fir::Operation as O;
    use fir::ValueType::{Bool, Closure, Constructor, Nat};
    let value = fir::ValueId::new;
    let partial = fir::ClosureTypeId::new(0);
    let full = fir::ClosureTypeId::new(1);
    for unmatched in [false, true] {
        let mut program = raw_program(unmatched, false);
        // The unused dispatcher closure type becomes the two-argument prefix
        // of the existing one-argument closure type, in canonical table order.
        program.closure_types[1] = fir::ClosureTypeDecl {
            id: full,
            parameters: vec![Bool, Bool],
            parameter_ownership: vec![Ownership::Borrowed; 2],
            result: Constructor,
            result_ownership: ResultOwnership::Owned,
        };
        let entry = &mut program.functions[0].blocks[0];
        entry.bindings.truncate(3);
        for binding in &mut entry.bindings[1..] {
            let O::Closure {
                closure_type,
                captures,
                capture_ownership,
                ..
            } = &mut binding.operation
            else {
                panic!("literal closure fixture");
            };
            binding.ty = Closure(full);
            *closure_type = full;
            captures.clear();
            capture_ownership.clear();
        }
        // Supply the former capture through a real Apply. The branch helper
        // later supplies the final argument to the returned partial closure.
        for closure in 1..=2 {
            entry.bindings.push(binding(
                closure + 2,
                Closure(partial),
                O::Apply {
                    closure: value(closure),
                    args: vec![value(0)],
                    argument_ownership: vec![Ownership::Borrowed],
                    result_ownership: ResultOwnership::Owned,
                },
            ));
        }
        entry.bindings.extend([
            binding(
                5,
                Constructor,
                O::Call {
                    function: fir::FunctionId::new(3),
                    args: vec![value(0), value(3), value(4)],
                },
            ),
            binding(6, Constructor, O::Alias(value(5))),
            binding(
                7,
                Nat,
                O::Call {
                    function: fir::FunctionId::new(4),
                    args: vec![value(6)],
                },
            ),
        ]);
        entry.terminator = fir::Terminator::Return { value: value(7) };
        let program = fir::validate(program, fir::ValidationLimits::default()).unwrap();
        let masks = parameters(&program, &constructors(), &mut Budget(64_000_000)).unwrap();
        assert!(masks[4][0].contains(0));
        assert_eq!(masks[4][0].contains(1), !unmatched);
        assert_eq!(masks[4][0].contains(2), unmatched);
        if unmatched {
            assert!(matches!(
                compile(&program),
                Err(CompileError::Unsupported {
                    what: "instruction outside the pure boxed subset",
                })
            ));
        } else {
            compile(&program).unwrap();
        }
    }
}

#[test]
fn captured_callback_targets_keep_their_actual_constructor_results() {
    use fir::Operation as O;
    use fir::ValueType::{Bool, Closure, Constructor, Nat};
    let value = fir::ValueId::new;
    let callback = fir::ClosureTypeId::new(0);
    for unmatched in [false, true] {
        let mut program = raw_program(unmatched, false);
        program.functions[5] = function(
            5,
            vec![Closure(callback), Bool],
            Constructor,
            vec![block(
                0,
                vec![binding(
                    2,
                    Constructor,
                    O::Apply {
                        closure: value(0),
                        args: vec![value(1)],
                        argument_ownership: vec![Ownership::Borrowed],
                        result_ownership: ResultOwnership::Owned,
                    },
                )],
                fir::Terminator::Return { value: value(2) },
            )],
        );
        let entry = &mut program.functions[0].blocks[0];
        entry.bindings.truncate(3);
        entry.bindings.extend([
            binding(
                3,
                Closure(callback),
                O::Closure {
                    closure_type: callback,
                    function: fir::FunctionId::new(5),
                    captures: vec![value(2)],
                    capture_ownership: vec![Ownership::Borrowed],
                },
            ),
            binding(
                4,
                Constructor,
                O::Apply {
                    closure: value(3),
                    args: vec![value(0)],
                    argument_ownership: vec![Ownership::Borrowed],
                    result_ownership: ResultOwnership::Owned,
                },
            ),
            binding(
                5,
                Nat,
                O::Call {
                    function: fir::FunctionId::new(4),
                    args: vec![value(4)],
                },
            ),
        ]);
        entry.terminator = fir::Terminator::Return { value: value(5) };
        let program = fir::validate(program, fir::ValidationLimits::default()).unwrap();
        let masks = parameters(&program, &constructors(), &mut Budget(64_000_000)).unwrap();
        assert_eq!(masks[4][0].contains(1), !unmatched);
        assert_eq!(masks[4][0].contains(2), unmatched);
        if unmatched {
            assert!(matches!(
                compile(&program),
                Err(CompileError::Unsupported {
                    what: "instruction outside the pure boxed subset",
                })
            ));
        } else {
            compile(&program).unwrap();
        }
    }
}

#[test]
fn captured_constructors_preserve_unmatched_values_and_every_exposed_suffix() {
    use fir::Operation as O;
    use fir::ValueType::{Bool, Closure, Constructor, Nat};
    let value = fir::ValueId::new;
    let captured = fir::ClosureTypeId::new(0);
    let exposed = fir::ClosureTypeId::new(2);
    for (tag, expose_second) in [(1_u8, false), (2, false), (1, true)] {
        let mut program = raw_program(false, false);
        program.closure_types.push(fir::ClosureTypeDecl {
            id: exposed,
            parameters: vec![Constructor, Bool],
            parameter_ownership: vec![Ownership::Borrowed; 2],
            result: Constructor,
            result_ownership: ResultOwnership::Owned,
        });
        program.functions[5] = function(
            5,
            vec![Constructor, Constructor, Bool],
            Constructor,
            vec![block(
                0,
                vec![],
                fir::Terminator::Return { value: value(1) },
            )],
        );
        let mut entry = vec![
            binding(0, Bool, O::Bool(false)),
            binding(
                1,
                Constructor,
                O::Ctor {
                    constructor: fir::ConstructorId::new(0),
                    fields: vec![],
                },
            ),
            binding(
                2,
                Constructor,
                O::Ctor {
                    constructor: fir::ConstructorId::new(u32::from(tag)),
                    fields: vec![],
                },
            ),
            binding(
                3,
                Closure(captured),
                O::Closure {
                    closure_type: captured,
                    function: fir::FunctionId::new(5),
                    captures: vec![value(1), value(2)],
                    capture_ownership: vec![Ownership::Borrowed; 2],
                },
            ),
            binding(
                4,
                Constructor,
                O::Apply {
                    closure: value(3),
                    args: vec![value(0)],
                    argument_ownership: vec![Ownership::Borrowed],
                    result_ownership: ResultOwnership::Owned,
                },
            ),
            binding(
                5,
                Nat,
                O::Call {
                    function: fir::FunctionId::new(4),
                    args: vec![value(4)],
                },
            ),
        ];
        if expose_second {
            // A second site fixes only the first slot. Even though the shown
            // application used a captured value, another caller can supply any
            // constructor to the same target's second slot through this one.
            entry.push(binding(
                6,
                Closure(exposed),
                O::Closure {
                    closure_type: exposed,
                    function: fir::FunctionId::new(5),
                    captures: vec![value(1)],
                    capture_ownership: vec![Ownership::Borrowed],
                },
            ));
        }
        program.functions[0].blocks[0] =
            block(0, entry, fir::Terminator::Return { value: value(5) });
        let program = fir::validate(program, fir::ValidationLimits::default()).unwrap();
        let masks = parameters(&program, &constructors(), &mut Budget(64_000_000)).unwrap();
        assert!(masks[5][0].contains(0), "the shared fixed prefix survives");
        assert_eq!(masks[5][1].is_empty(), expose_second);
        assert_eq!(masks[4][0].contains(tag), !expose_second);
        if tag == 1 && !expose_second {
            compile(&program).unwrap();
        } else {
            assert!(matches!(
                compile(&program),
                Err(CompileError::Unsupported {
                    what: "instruction outside the pure boxed subset",
                })
            ));
        }
    }
}

#[test]
fn a_real_unmatched_constructor_still_refuses_export() {
    let program = program(true, false);
    let masks = parameters(&program, &constructors(), &mut Budget(64_000_000)).unwrap();
    assert!(masks[4][0].contains(0));
    assert!(!masks[4][0].contains(1));
    assert!(masks[4][0].contains(2));
    assert!(matches!(
        compile(&program),
        Err(CompileError::Unsupported {
            what: "instruction outside the pure boxed subset",
        })
    ));
}

#[test]
fn address_taken_dispatchers_keep_unknown_constructor_inputs() {
    let program = program(false, true);
    let masks = parameters(&program, &constructors(), &mut Budget(64_000_000)).unwrap();
    assert!(masks[4][0].is_empty());
    assert!(matches!(
        compile(&program),
        Err(CompileError::Unsupported {
            what: "instruction outside the pure boxed subset",
        })
    ));
}

#[test]
fn constructor_flow_propagates_its_work_limit() {
    assert!(matches!(
        parameters(&program(false, false), &constructors(), &mut Budget(0)),
        Err(CompileError::Limit)
    ));
}

#[test]
fn unknown_external_callbacks_cannot_prove_a_dispatch_domain() {
    use fir::Operation as O;
    use fir::ValueType::{Bool, Closure, Constructor, Nat};
    let value = fir::ValueId::new;
    let callback = fir::ClosureTypeId::new(0);
    let exposed = fir::ClosureTypeId::new(2);
    let mut program = raw_program(false, false);
    program.closure_types.push(fir::ClosureTypeDecl {
        id: exposed,
        parameters: vec![Closure(callback)],
        parameter_ownership: vec![Ownership::Borrowed],
        result: Nat,
        result_ownership: ResultOwnership::OwnedOrScalar,
    });
    program.functions.push(function(
        6,
        vec![Closure(callback)],
        Nat,
        vec![block(
            0,
            vec![
                binding(1, Bool, O::Bool(false)),
                binding(
                    2,
                    Constructor,
                    O::Apply {
                        closure: value(0),
                        args: vec![value(1)],
                        argument_ownership: vec![Ownership::Borrowed],
                        result_ownership: ResultOwnership::Owned,
                    },
                ),
                binding(
                    3,
                    Nat,
                    O::Call {
                        function: fir::FunctionId::new(4),
                        args: vec![value(2)],
                    },
                ),
            ],
            fir::Terminator::Return { value: value(3) },
        )],
    ));
    program.functions[0].blocks[0].bindings.push(binding(
        6,
        Closure(exposed),
        O::Closure {
            closure_type: exposed,
            function: fir::FunctionId::new(6),
            captures: vec![],
            capture_ownership: vec![],
        },
    ));
    let program = fir::validate(program, fir::ValidationLimits::default()).unwrap();
    let masks = parameters(&program, &constructors(), &mut Budget(64_000_000)).unwrap();
    assert!(masks[4][0].is_empty());
    assert!(matches!(
        compile(&program),
        Err(CompileError::Unsupported {
            what: "instruction outside the pure boxed subset",
        })
    ));
}

#[test]
fn a_recursive_cycle_without_constructor_producers_stays_unconstrained() {
    use fir::Operation as O;
    use fir::ValueType::{Constructor, Nat};
    let value = fir::ValueId::new;
    let cycle = fir::FunctionId::new(5);
    let mut program = raw_program(false, false);
    program.functions[5] = function(
        5,
        vec![],
        Constructor,
        vec![block(
            0,
            vec![binding(
                0,
                Constructor,
                O::Call {
                    function: cycle,
                    args: vec![],
                },
            )],
            fir::Terminator::Return { value: value(0) },
        )],
    );
    program.functions[0].blocks[0] = block(
        0,
        vec![
            binding(
                0,
                Constructor,
                O::Call {
                    function: cycle,
                    args: vec![],
                },
            ),
            binding(
                1,
                Nat,
                O::Call {
                    function: fir::FunctionId::new(4),
                    args: vec![value(0)],
                },
            ),
        ],
        fir::Terminator::Return { value: value(1) },
    );
    let program = fir::validate(program, fir::ValidationLimits::default()).unwrap();
    let masks = parameters(&program, &constructors(), &mut Budget(64_000_000)).unwrap();
    assert!(masks[4][0].is_empty());
    assert!(matches!(
        compile(&program),
        Err(CompileError::Unsupported {
            what: "instruction outside the pure boxed subset",
        })
    ));
}

#[test]
fn packed_public_slots_require_the_same_private_scalar_carrier() {
    use fir::Operation as O;
    use fir::ValueType::{Bool, Constructor, Nat, String as Text};
    let value = fir::ValueId::new;
    let constructor = fir::ConstructorId::new(0);
    let entry = Name::from_components(["packed_collision"]);
    let source = SourceSignature {
        name: entry.clone(),
        params: vec![],
        result: IrType::Object,
        reduced: None,
        inferred_borrowing: false,
        constructor_fields: vec![SourceConstructor::Standard(vec![
            IrType::TObject,
            IrType::UInt8,
        ])],
    };
    for is_bool in [true, false] {
        let (ty, operation) = if is_bool {
            (Bool, O::Bool(true))
        } else {
            (Text, O::String("must remain an object".into()))
        };
        let program = fir::Program::new(
            fir::FunctionId::new(0),
            vec![fir::ConstructorDecl {
                id: constructor,
                tag: 0,
                fields: vec![Nat, ty],
                static_scalar_bytes: vec![],
            }],
            vec![],
            vec![],
            vec![function(
                0,
                vec![],
                Constructor,
                vec![block(
                    0,
                    vec![
                        binding(0, Nat, O::Nat(42)),
                        binding(1, ty, operation),
                        binding(
                            2,
                            Constructor,
                            O::Ctor {
                                constructor,
                                fields: vec![value(0), value(1)],
                            },
                        ),
                    ],
                    fir::Terminator::Return { value: value(2) },
                )],
            )],
        );
        let program = fir::validate(program, fir::ValidationLimits::default()).unwrap();
        let mut meter = Budget(64_000_000);
        let module = compile_module(
            &program,
            &entry,
            CompileLimits::default(),
            Some(&source),
            &mut meter,
        );
        if is_bool {
            validate_module(&module.unwrap(), &meter).unwrap();
        } else {
            // A shared ordinal and source field count cannot authorize
            // unboxing an unrelated private object's pointer as a Bool.
            assert!(matches!(
                module,
                Err(CompileError::Unsupported {
                    what: "conflicting source constructor layouts",
                })
            ));
        }
    }
}

#[test]
fn unboxed_wrappers_erase_all_header_operations_and_refuse_other_shapes() {
    use fir::Operation as O;
    use fir::ValueType::{Bool, Constructor, Nat};
    use fln_olean::ir::{IrDecl, IrExpr, IrStmt, IrTerminal};
    let value = fir::ValueId::new;
    let constructor = fir::ConstructorId::new(0);
    let projection = fir::ProjectionId::new(0);
    let entry = Name::from_components(["unboxed_wrapper"]);
    let source = SourceSignature {
        name: entry.clone(),
        params: vec![],
        result: IrType::TObject,
        reduced: None,
        inferred_borrowing: false,
        constructor_fields: vec![SourceConstructor::Unboxed(IrType::TObject)],
    };
    for other_shape in [false, true] {
        let mut constructors = vec![fir::ConstructorDecl {
            id: constructor,
            tag: 0,
            fields: vec![Nat],
            static_scalar_bytes: vec![],
        }];
        if other_shape {
            constructors.push(fir::ConstructorDecl {
                id: fir::ConstructorId::new(1),
                tag: 1,
                fields: vec![],
                static_scalar_bytes: vec![],
            });
        }
        let program = fir::Program::new(
            fir::FunctionId::new(0),
            constructors,
            vec![fir::ProjectionDecl {
                id: projection,
                constructor,
                field: 0,
            }],
            vec![],
            vec![function(
                0,
                vec![],
                Nat,
                vec![block(
                    0,
                    vec![
                        binding(0, Nat, O::Nat(42)),
                        binding(
                            1,
                            Constructor,
                            O::Ctor {
                                constructor,
                                fields: vec![value(0)],
                            },
                        ),
                        binding(
                            2,
                            Bool,
                            O::CtorTest {
                                constructor,
                                value: value(1),
                            },
                        ),
                        binding(
                            3,
                            Nat,
                            O::Project {
                                projection,
                                value: value(1),
                            },
                        ),
                    ],
                    fir::Terminator::Return { value: value(3) },
                )],
            )],
        );
        let program = fir::validate(program, fir::ValidationLimits::default()).unwrap();
        let mut meter = Budget(64_000_000);
        let result = compile_module(
            &program,
            &entry,
            CompileLimits::default(),
            Some(&source),
            &mut meter,
        );
        if other_shape {
            assert!(matches!(
                result,
                Err(CompileError::Unsupported {
                    what: "unboxed source constructor layouts",
                })
            ));
        } else {
            let module = result.unwrap();
            validate_module(&module, &meter).unwrap();
            for declaration in &module.decls {
                let IrDecl::Function { body, .. } = declaration else {
                    panic!("wrapper function")
                };
                assert!(matches!(body.terminal.as_ref(), IrTerminal::Ret(_)));
                for statement in &body.stmts {
                    assert!(!matches!(
                        statement,
                        IrStmt::VDecl {
                            expr: IrExpr::Ctor { .. } | IrExpr::Proj { .. } | IrExpr::SProj { .. },
                            ..
                        }
                    ));
                }
            }
        }
    }
}
