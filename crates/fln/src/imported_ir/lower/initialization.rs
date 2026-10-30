//! Execution-local storage and entry sequencing for selected initialized globals.
//!
//! The environment is an ordinary immutable array of checked native reference
//! cells. Each cell begins as `none` and receives `some value` only after its
//! initializer returns the Reference's successful IO-result shape. Linked
//! functions receive the array through a hidden first parameter. Lifted joins
//! retain it, while closures snapshot its readiness cells and share only their
//! initialized payloads. This prevents storing a closure-valued global from
//! making the private environment refer to itself. No IR variable can name the
//! private array or its readiness cells.

use super::*;

impl Builder<'_> {
    pub(super) fn prepend_environment(&mut self, arguments: &mut Vec<ValueId>) -> Result<()> {
        if let Some(environment) = self.global_environment {
            self.tables.capture_operands(1)?;
            arguments.insert(0, environment);
        }
        Ok(())
    }

    pub(super) fn prepend_captured_environment(
        &mut self,
        block: BlockId,
        captures: &mut Vec<ValueId>,
    ) -> Result<()> {
        if self.global_environment.is_none() {
            return Ok(());
        }
        self.tables
            .capture_operands(self.tables.global_slots.len())?;
        let mut cells = Vec::with_capacity(self.tables.global_slots.len());
        for slot in 0..self.tables.global_slots.len() {
            let cell = self.global_cell(block, slot)?;
            let stored = self.native_call(
                block,
                &Name::from_components(["ST", "Prim", "Ref", "get"]),
                vec![cell],
            )?;
            cells.push(self.native_call(
                block,
                &Name::from_components(["ST", "Prim", "mkRef"]),
                vec![stored],
            )?);
        }
        // The preparation pass orders every global a closure's code can
        // statically read before the closure-producing initializer. Copying
        // readiness cells therefore preserves its readable values, including
        // the identity of an initialized reference-cell payload, without
        // capturing the cell into which this closure may itself be stored.
        let environment = self.boxed(block, ValueType::Array, Operation::Array { items: cells })?;
        self.tables.capture_operands(1)?;
        captures.insert(0, environment);
        Ok(())
    }

    fn initialization_constructor(&mut self, tag: u8, fields: usize) -> Result<ConstructorId> {
        self.constructor(&IrCtorInfo {
            name: Name::anonymous(),
            cidx: u64::from(tag),
            size: fields as u64,
            usize: 0,
            ssize: 0,
        })
    }

    pub(super) fn initialization_envelope(
        &mut self,
        block: BlockId,
        tag: u8,
        fields: Vec<ValueId>,
    ) -> Result<ValueId> {
        let constructor = self.initialization_constructor(tag, fields.len())?;
        self.boxed(
            block,
            ValueType::Constructor,
            Operation::Ctor {
                constructor,
                fields,
            },
        )
    }

    fn initialization_shape(&mut self, block: BlockId, value: ValueId, tag: u8) -> Result<ValueId> {
        let constructor = self.initialization_constructor(tag, 1)?;
        // IO.Result has exactly one object field and no scalar storage. Test
        // the complete layout directly on the ABI value: matching tags and
        // pointer counts alone must not accept an unrelated packed record.
        self.emit(
            block,
            ValueType::Bool,
            Operation::CtorLayoutTest { constructor, value },
        )
    }

    fn initialization_payload(
        &mut self,
        block: BlockId,
        value: ValueId,
        tag: u8,
    ) -> Result<ValueId> {
        let constructor = self.initialization_constructor(tag, 1)?;
        if self.tables.projections.len() >= self.tables.limits.fir.max_projections {
            return Err(IrExecutionError::Limit("projections"));
        }
        let projection = ProjectionId::new(self.tables.projections.len() as u32);
        self.tables.projections.push(ProjectionDecl {
            id: projection,
            constructor,
            field: 0,
        });
        let value = self.emit(
            block,
            ValueType::Constructor,
            Operation::Unbox {
                value,
                ty: ValueType::Constructor,
            },
        )?;
        self.emit(
            block,
            ValueType::Abi,
            Operation::Project { projection, value },
        )
    }

    fn global_cell(&mut self, block: BlockId, slot: usize) -> Result<ValueId> {
        let environment = self
            .global_environment
            .ok_or_else(|| unsupported(self.name, "missing initialized global environment"))?;
        let slot =
            u64::try_from(slot).map_err(|_| IrExecutionError::Limit("initialized global index"))?;
        let slot = self.nat(block, &IrNat::Small(slot))?;
        self.native_call(
            block,
            &Name::from_components(["Array", "getInternal"]),
            vec![environment, slot],
        )
    }

    pub(super) fn global_value(&mut self, block: BlockId, name: &Name) -> Result<ValueId> {
        let slot = self
            .tables
            .global_slots
            .get(name)
            .copied()
            .ok_or_else(|| IrExecutionError::MissingDeclaration(name.clone()))?;
        let cell = self.global_cell(block, slot)?;
        let stored = self.native_call(
            block,
            &Name::from_components(["ST", "Prim", "Ref", "get"]),
            vec![cell],
        )?;
        // A forward read cannot receive the uninitialized marker as a user
        // value: checked projection refuses anything but `some value`.
        self.initialization_payload(block, stored, 1)
    }

    /// Allocate fresh readiness cells, then run the selected initializers in
    /// the already validated plan order. The returned block is reachable only
    /// after all initializers succeed; the caller places the entry call there.
    pub(super) fn initialize_globals(
        &mut self,
        mut block: BlockId,
        plan: &globals::InitializationPlan,
    ) -> Result<BlockId> {
        self.tables.capture_operands(plan.globals.len())?;
        let none = self.boxed(block, ValueType::Unit, Operation::Unit)?;
        let mut cells = Vec::with_capacity(plan.globals.len());
        for _ in &plan.globals {
            cells.push(self.native_call(
                block,
                &Name::from_components(["ST", "Prim", "mkRef"]),
                vec![none],
            )?);
        }
        let environment = self.boxed(block, ValueType::Array, Operation::Array { items: cells })?;
        self.global_environment = Some(environment);

        for (slot, global) in plan.globals.iter().enumerate() {
            let (function, arity) = self
                .tables
                .targets
                .get(&global.initializer)
                .copied()
                .ok_or_else(|| IrExecutionError::MissingDeclaration(global.initializer.clone()))?;
            if arity != 1 {
                return Err(unsupported(
                    &global.initializer,
                    "initializer without its single erased world parameter",
                ));
            }
            let world = self.boxed(block, ValueType::Unit, Operation::Unit)?;
            let mut args = vec![world];
            self.prepend_environment(&mut args)?;
            let result = self.emit(block, ValueType::Abi, Operation::Call { function, args })?;
            let success = self.initialization_shape(block, result, 0)?;

            // Emit blocks in their value-definition order. Both failure arms
            // return a private envelope, so neither can reach later actions.
            let failure = self.block()?;
            let io_error = self.initialization_shape(failure, result, 1)?;
            let index = self.nat(failure, &IrNat::Small(slot as u64))?;
            let error_block = self.block()?;
            let error = self.initialization_envelope(error_block, 1, vec![index, result])?;
            self.finish_block(error_block, Terminator::Return { value: error });
            let malformed_block = self.block()?;
            let malformed =
                self.initialization_envelope(malformed_block, 2, vec![index, result])?;
            self.finish_block(malformed_block, Terminator::Return { value: malformed });
            self.finish_block(
                failure,
                Terminator::BranchZero {
                    condition: io_error,
                    zero: malformed_block,
                    nonzero: error_block,
                },
            );

            let ready = self.block()?;
            let value = self.initialization_payload(ready, result, 0)?;
            let value = self.initialization_envelope(ready, 1, vec![value])?;
            let cell = self.global_cell(ready, slot)?;
            self.native_call(
                ready,
                &Name::from_components(["ST", "Prim", "Ref", "set"]),
                vec![cell, value],
            )?;
            self.finish_block(
                block,
                Terminator::BranchZero {
                    condition: success,
                    zero: failure,
                    nonzero: ready,
                },
            );
            block = ready;
        }
        Ok(block)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use fln_olean::ir::{IrArg, IrBody, IrExpr, IrLit, IrParam, IrStmt, IrTerminal};
    use fln_vm::interpreter::{ExecutionLimits, VmExit, execute, nat_decimal};

    fn name(text: &str) -> Name {
        Name::from_components(text.split('.'))
    }

    fn var(x: u64) -> IrArg {
        IrArg::Var(x)
    }

    fn bind(x: u64, expr: IrExpr) -> IrStmt {
        IrStmt::VDecl {
            x,
            ty: IrType::TObject,
            expr,
        }
    }

    fn num(x: u64, value: u64) -> IrStmt {
        bind(x, IrExpr::Lit(IrLit::Num(IrNat::Small(value))))
    }

    fn call(x: u64, target: &str, arguments: &[u64]) -> IrStmt {
        bind(
            x,
            IrExpr::Fap {
                function: name(target),
                args: arguments.iter().copied().map(var).collect(),
            },
        )
    }

    fn object(x: u64, tag: u64, fields: &[u64]) -> IrStmt {
        bind(
            x,
            IrExpr::Ctor {
                info: IrCtorInfo {
                    name: Name::anonymous(),
                    cidx: tag,
                    size: fields.len() as u64,
                    usize: 0,
                    ssize: 0,
                },
                args: fields.iter().copied().map(var).collect(),
            },
        )
    }

    fn body(stmts: Vec<IrStmt>, result: u64) -> IrBody {
        IrBody {
            stmts,
            terminal: Box::new(IrTerminal::Ret(var(result))),
        }
    }

    fn function(text: &str, arity: u64, body: IrBody) -> IrDecl {
        IrDecl::Function {
            name: name(text),
            params: (1..=arity)
                .map(|x| IrParam {
                    x,
                    borrow: true,
                    ty: IrType::TObject,
                })
                .collect(),
            result: IrType::TObject,
            body,
            sorry_dep: None,
        }
    }

    fn initializer(text: &str, body: IrBody) -> IrDecl {
        let mut declaration = function(text, 1, body);
        let IrDecl::Function { params, .. } = &mut declaration else {
            unreachable!()
        };
        params[0].ty = IrType::Void;
        declaration
    }

    fn plan(rows: &[(&str, &str)]) -> globals::InitializationPlan {
        globals::InitializationPlan {
            globals: rows
                .iter()
                .map(|(global, initializer)| globals::InitializedGlobal {
                    declaration: name(global),
                    initializer: name(initializer),
                })
                .collect(),
        }
    }

    fn prepare(
        declarations: Vec<IrDecl>,
        initialization: globals::InitializationPlan,
        entry: &str,
        native_names: &[&str],
    ) -> CompiledIr {
        let declarations = declarations
            .iter()
            .map(|declaration| (declaration.name().clone(), declaration))
            .collect();
        let mut natives = BTreeMap::new();
        for name in native_names {
            insert_helper(&mut natives, name).unwrap();
        }
        super::super::compile(
            &declarations,
            &natives,
            &name(entry),
            &[],
            IrExecutionLimits::default(),
            Some(&initialization),
            false,
        )
        .unwrap()
    }

    fn assert_replay_value(compiled: &CompiledIr, expected: &str) {
        let canonical =
            flbc::encode_canonical(compiled.program.program(), flbc::CodecLimits::default())
                .unwrap();
        let replay = flbc::decode_canonical(&canonical, flbc::CodecLimits::default()).unwrap();
        // Repeated execution must rebuild the private cells. Replay must keep
        // the same state semantics using only the canonical program bytes.
        for program in [
            compiled.program.program(),
            compiled.program.program(),
            &replay,
        ] {
            let Outcome::Complete(VmExit::Returned(result)) =
                execute(program, ExecutionLimits::default(), None)
            else {
                panic!("initialized program did not return")
            };
            assert_eq!(
                (result.value.header().tag, result.value.header().other),
                (0, 1)
            );
            let value = result.value.try_ctor_child(0).unwrap();
            assert_eq!(nat_decimal(&value).as_deref(), Some(expected));
        }
    }

    #[test]
    fn callable_entries_run_the_initializer_wrapper_with_real_arguments() {
        let declarations = [
            function("Global.value", 0, body(vec![num(1, 999)], 1)),
            initializer("Global.init", body(vec![num(2, 42), object(3, 0, &[2])], 3)),
            function(
                "Global.entry",
                1,
                body(
                    vec![call(2, "Global.value", &[]), call(3, "Nat.add", &[1, 2])],
                    3,
                ),
            ),
        ];
        let declarations = declarations
            .iter()
            .map(|declaration| (declaration.name().clone(), declaration))
            .collect();
        let mut natives = BTreeMap::new();
        insert_helper(&mut natives, "Nat.add").unwrap();
        for (initialization, expected) in [
            (globals::InitializationPlan::default(), "1006"),
            (plan(&[("Global.value", "Global.init")]), "49"),
        ] {
            let compiled = super::super::compile(
                &declarations,
                &natives,
                &name("Global.entry"),
                &[],
                IrExecutionLimits::default(),
                Some(&initialization),
                true,
            )
            .unwrap();
            let bytes =
                flbc::encode_canonical(compiled.program.program(), flbc::CodecLimits::default())
                    .unwrap();
            let replay = flbc::decode_canonical(&bytes, flbc::CodecLimits::default()).unwrap();
            let (entry, arity) = compiled.callable_entry.unwrap();
            assert_eq!(arity, 1);
            let Outcome::Complete(VmExit::Returned(closure)) =
                execute(&replay, ExecutionLimits::default(), None)
            else {
                panic!("canonical entry did not return its callable")
            };
            assert_eq!(
                fln_vm::interpreter::value_kind(&closure.value),
                fln_vm::interpreter::ValueKind::Closure
            );
            let (outcome, failure) = globals::finish(
                fln_vm::interpreter::execute_function(
                    &replay,
                    entry,
                    vec![fln_rt::obj::Obj::mk_nat(7)],
                    ExecutionLimits::default(),
                    None,
                ),
                &initialization,
            );
            assert!(failure.is_none());
            let Outcome::Complete(VmExit::Returned(result)) = outcome else {
                panic!("{outcome:?}")
            };
            assert_eq!(nat_decimal(&result.value).as_deref(), Some(expected));
        }
    }

    #[test]
    fn initialized_global_entry_uses_retained_value_instead_of_dummy_body() {
        let compiled = prepare(
            vec![
                function("Global.value", 0, body(vec![num(1, 999)], 1)),
                initializer("Global.init", body(vec![num(2, 42), object(3, 0, &[2])], 3)),
            ],
            plan(&[("Global.value", "Global.init")]),
            "Global.value",
            &[],
        );
        assert_replay_value(&compiled, "42");
        assert!(
            compiled
                .reference_functions()
                .iter()
                .all(|function| { function.name != name("Global.value") }),
            "the generated getter did not interpret the stored dummy body"
        );
    }

    #[test]
    fn environment_survives_partial_native_calls_and_lifted_joins() {
        let mut joined = body(
            vec![IrStmt::JDecl {
                j: 7,
                params: vec![IrParam {
                    x: 8,
                    borrow: true,
                    ty: IrType::TObject,
                }],
                value: body(
                    vec![call(2, "Global.value", &[]), call(9, "Nat.add", &[2, 8])],
                    9,
                ),
            }],
            1,
        );
        joined.terminal = Box::new(IrTerminal::Jmp {
            j: 7,
            args: vec![var(1)],
        });
        let compiled = prepare(
            vec![
                function("Global.value", 0, body(vec![num(1, 999)], 1)),
                initializer("Global.init", body(vec![num(2, 42), object(3, 0, &[2])], 3)),
                function("Global.add", 1, joined),
                function(
                    "Global.main",
                    0,
                    body(
                        vec![
                            num(1, 5),
                            bind(
                                2,
                                IrExpr::Pap {
                                    function: name("Global.add"),
                                    args: vec![],
                                },
                            ),
                            bind(
                                3,
                                IrExpr::Ap {
                                    x: 2,
                                    args: vec![var(1)],
                                },
                            ),
                            bind(
                                4,
                                IrExpr::Pap {
                                    function: name("Nat.add"),
                                    args: vec![var(3)],
                                },
                            ),
                            num(5, 7),
                            bind(
                                6,
                                IrExpr::Ap {
                                    x: 4,
                                    args: vec![var(5)],
                                },
                            ),
                        ],
                        6,
                    ),
                ),
            ],
            plan(&[("Global.value", "Global.init")]),
            "Global.main",
            &["Nat.add"],
        );
        assert_replay_value(&compiled, "54");
    }

    #[test]
    fn closure_global_snapshots_readiness_but_shares_initialized_reference_payloads() {
        let compiled = prepare(
            vec![
                function("Global.cell", 0, body(vec![num(1, 999)], 1)),
                function("Global.callback", 0, body(vec![num(1, 888)], 1)),
                initializer(
                    "Global.initCell",
                    body(
                        vec![
                            num(2, 0),
                            call(3, "ST.Prim.mkRef", &[2]),
                            object(4, 0, &[3]),
                        ],
                        4,
                    ),
                ),
                initializer(
                    "Global.initCallback",
                    body(
                        vec![
                            bind(
                                2,
                                IrExpr::Pap {
                                    function: name("Global.read"),
                                    args: vec![],
                                },
                            ),
                            object(3, 0, &[2]),
                        ],
                        3,
                    ),
                ),
                function(
                    "Global.read",
                    1,
                    body(
                        vec![
                            call(2, "Global.cell", &[]),
                            call(3, "ST.Prim.Ref.get", &[2]),
                            call(4, "Nat.add", &[3, 1]),
                        ],
                        4,
                    ),
                ),
                function(
                    "Global.main",
                    0,
                    body(
                        vec![
                            call(1, "Global.cell", &[]),
                            call(2, "ST.Prim.Ref.get", &[1]),
                            num(3, 1),
                            call(4, "Nat.add", &[2, 3]),
                            call(5, "ST.Prim.Ref.set", &[1, 4]),
                            call(6, "Global.callback", &[]),
                            num(7, 41),
                            bind(
                                8,
                                IrExpr::Ap {
                                    x: 6,
                                    args: vec![var(7)],
                                },
                            ),
                        ],
                        8,
                    ),
                ),
            ],
            plan(&[
                ("Global.cell", "Global.initCell"),
                ("Global.callback", "Global.initCallback"),
            ]),
            "Global.main",
            &[
                "Nat.add",
                "ST.Prim.mkRef",
                "ST.Prim.Ref.get",
                "ST.Prim.Ref.set",
            ],
        );
        assert_replay_value(&compiled, "42");
    }

    #[test]
    fn initializer_error_and_malformed_results_never_reach_entry() {
        for (tag, fields, envelope_tag) in [(1, 1, 1), (0, 2, 2), (0, 0, 2)] {
            let mut statements = vec![num(2, 17)];
            let result = if fields == 0 {
                2
            } else {
                statements.push(object(3, tag, &vec![2; fields]));
                3
            };
            let compiled = prepare(
                vec![
                    function("Global.value", 0, body(vec![num(1, 999)], 1)),
                    initializer("Global.init", body(statements, result)),
                    function(
                        "Global.main",
                        0,
                        IrBody {
                            stmts: vec![],
                            terminal: Box::new(IrTerminal::Unreachable),
                        },
                    ),
                ],
                plan(&[("Global.value", "Global.init")]),
                "Global.main",
                &[],
            );
            let Outcome::Complete(VmExit::Returned(result)) =
                execute(compiled.program.program(), ExecutionLimits::default(), None)
            else {
                panic!("initializer failure executed the entry")
            };
            assert_eq!(
                (result.value.header().tag, result.value.header().other),
                (envelope_tag, 2)
            );
            assert_eq!(
                nat_decimal(&result.value.try_ctor_child(0).unwrap()).as_deref(),
                Some("0")
            );
            let original = result.value.try_ctor_child(1).unwrap();
            if fields == 0 {
                assert_eq!(nat_decimal(&original).as_deref(), Some("17"));
            } else {
                assert_eq!(
                    (original.header().tag, original.header().other),
                    (tag as u8, fields as u8)
                );
            }
        }
    }

    #[test]
    fn initializer_results_with_hidden_scalar_storage_are_malformed() {
        for tag in [0, 1] {
            let scalar = 0xfedc_ba98_7654_3210;
            let compiled = prepare(
                vec![
                    function("Global.value", 0, body(vec![num(1, 999)], 1)),
                    initializer(
                        "Global.init",
                        body(
                            vec![
                                num(2, 17),
                                IrStmt::VDecl {
                                    x: 3,
                                    ty: IrType::UInt64,
                                    expr: IrExpr::Lit(IrLit::Num(IrNat::Small(scalar))),
                                },
                                bind(
                                    4,
                                    IrExpr::Ctor {
                                        info: IrCtorInfo {
                                            name: Name::anonymous(),
                                            cidx: tag,
                                            size: 1,
                                            usize: 0,
                                            ssize: 8,
                                        },
                                        args: vec![var(2)],
                                    },
                                ),
                                IrStmt::SSet {
                                    x: 4,
                                    i: 1,
                                    offset: 0,
                                    y: 3,
                                    ty: IrType::UInt64,
                                },
                            ],
                            4,
                        ),
                    ),
                    function(
                        "Global.main",
                        0,
                        IrBody {
                            stmts: vec![],
                            terminal: Box::new(IrTerminal::Unreachable),
                        },
                    ),
                ],
                plan(&[("Global.value", "Global.init")]),
                "Global.main",
                &[],
            );
            let canonical =
                flbc::encode_canonical(compiled.program.program(), flbc::CodecLimits::default())
                    .unwrap();
            let replay = flbc::decode_canonical(&canonical, flbc::CodecLimits::default()).unwrap();
            for program in [compiled.program.program(), &replay] {
                let Outcome::Complete(VmExit::Returned(result)) =
                    execute(program, ExecutionLimits::default(), None)
                else {
                    panic!("malformed initializer result reached the entry")
                };
                assert_eq!(
                    (result.value.header().tag, result.value.header().other),
                    (2, 2),
                    "extra scalar storage is malformed for both IO.Result tags"
                );
                assert_eq!(
                    nat_decimal(&result.value.try_ctor_child(0).unwrap()).as_deref(),
                    Some("0")
                );
                let original = result.value.try_ctor_child(1).unwrap();
                assert_eq!(
                    (original.header().tag, original.header().other),
                    (tag as u8, 1)
                );
                assert_eq!(
                    nat_decimal(&original.try_ctor_child(0).unwrap()).as_deref(),
                    Some("17")
                );
                assert_eq!(
                    original.try_ctor_scalar_u64(std::mem::size_of::<usize>()),
                    Some(scalar),
                    "the malformed result must retain its complete payload"
                );
            }
        }
    }

    #[test]
    fn unready_global_access_is_a_checked_refusal_not_a_placeholder_value() {
        let compiled = prepare(
            vec![
                function("Global.first", 0, body(vec![num(1, 999)], 1)),
                function("Global.second", 0, body(vec![num(1, 888)], 1)),
                initializer(
                    "Global.initFirst",
                    body(vec![call(2, "Global.second", &[]), object(3, 0, &[2])], 3),
                ),
                initializer(
                    "Global.initSecond",
                    body(vec![num(2, 42), object(3, 0, &[2])], 3),
                ),
            ],
            // Deliberately bypass preparation's dependency ordering to test
            // the bytecode's independent readiness protection.
            plan(&[
                ("Global.first", "Global.initFirst"),
                ("Global.second", "Global.initSecond"),
            ]),
            "Global.first",
            &[],
        );
        assert!(matches!(
            execute(compiled.program.program(), ExecutionLimits::default(), None),
            Outcome::Complete(VmExit::Refused {
                refusal: fln_vm::interpreter::VmRefusal::ConstructorProjectionTag {
                    expected: 1,
                    ..
                },
                ..
            })
        ));
    }
}
