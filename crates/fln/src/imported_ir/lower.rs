use super::*;
use fln_comp::fir::{
    Binding, Block, BlockId, ClosureTypeDecl, ClosureTypeId, ConstructorDecl, ConstructorId,
    Function, FunctionId, IntrinsicDecl, IntrinsicId, Operation, ProjectionDecl, ProjectionId,
    Terminator, ValueId, ValueType,
};
use fln_olean::ir::{IrAlt, IrArg, IrCtorInfo, IrExpr, IrLit};

type Result<T> = std::result::Result<T, IrExecutionError>;

pub(super) fn compile(
    declarations: &BTreeMap<Name, &IrDecl>,
    supplied_natives: &BTreeMap<Name, Native>,
    entry: &Name,
    arguments: &[EntryArgument],
    limits: IrExecutionLimits,
) -> Result<CompiledIr> {
    let mut helper_natives = BTreeMap::new();
    for declaration in declarations.values() {
        if let IrDecl::Function { body, .. } = declaration {
            for body in body.bodies() {
                if matches!(body.terminal.as_ref(), IrTerminal::Case { .. }) {
                    insert_helper(&mut helper_natives, "Nat.beq")?;
                }
                for stmt in &body.stmts {
                    if let IrStmt::VDecl {
                        ty,
                        expr: IrExpr::Unbox { .. },
                        ..
                    } = stmt
                    {
                        if let Some(name) = unbox_intrinsic(ty) {
                            insert_helper(&mut helper_natives, name)?;
                        }
                    }
                }
            }
        }
    }
    let native_map: BTreeMap<Name, &Native> = helper_natives
        .iter()
        .chain(supplied_natives.iter())
        .map(|(name, value)| (name.clone(), value))
        .collect();
    let mut native_order: Vec<_> = native_map.iter().collect();
    native_order.sort_by_key(|(_, native)| native.row.id);
    let intrinsics: Vec<_> = native_order
        .iter()
        .enumerate()
        .map(|(index, (_, native))| IntrinsicDecl {
            id: IntrinsicId::new(index as u32),
            row: native.row.id.to_owned(),
            arguments: vec![ValueType::Abi; native.arguments.len()],
            argument_ownership: native.arguments.clone(),
            result: ValueType::Abi,
            result_ownership: native.result,
            effect: fir::EffectClass::Pure,
        })
        .collect();
    let intrinsic_ids = native_order
        .iter()
        .enumerate()
        .map(|(index, (name, _))| ((*name).clone(), IntrinsicId::new(index as u32)))
        .collect();
    let mut names: BTreeMap<Name, usize> = declarations
        .iter()
        .map(|(name, decl)| {
            let params = match decl {
                IrDecl::Function { params, .. } | IrDecl::Extern { params, .. } => params,
            };
            (name.clone(), params.len())
        })
        .collect();
    names.extend(
        supplied_natives
            .iter()
            .map(|(name, native)| (name.clone(), native.arguments.len())),
    );
    let targets: BTreeMap<_, _> = names
        .iter()
        .enumerate()
        .map(|(i, (name, arity))| (name.clone(), (FunctionId::new(i as u32 + 1), *arity)))
        .collect();
    let (entry_id, expected) = targets
        .get(entry)
        .copied()
        .ok_or_else(|| IrExecutionError::MissingDeclaration(entry.clone()))?;
    if expected != arguments.len() {
        return Err(IrExecutionError::EntryArity {
            expected,
            actual: arguments.len(),
        });
    }
    let mut max_arity = names.values().copied().max().unwrap_or(0);
    for decl in declarations.values() {
        if let IrDecl::Function { body, .. } = decl {
            for body in body.bodies() {
                for stmt in &body.stmts {
                    if let IrStmt::VDecl {
                        expr: IrExpr::Ap { args, .. },
                        ..
                    } = stmt
                    {
                        max_arity = max_arity.max(args.len());
                    }
                }
            }
        }
    }
    if max_arity > 1024 || max_arity > limits.fir.max_closure_types {
        return Err(IrExecutionError::Limit("callable arity"));
    }
    let closure_types = (1..=max_arity)
        .map(|arity| ClosureTypeDecl {
            id: ClosureTypeId::new(arity as u32 - 1),
            parameters: vec![ValueType::Abi; arity],
            parameter_ownership: vec![flbc::ArgumentOwnership::Borrowed; arity],
            result: ValueType::Abi,
            result_ownership: flbc::CallableResultOwnership::Erased,
        })
        .collect();
    let mut tables = Tables {
        targets,
        intrinsic_ids,
        constructors: Vec::new(),
        projections: Vec::new(),
        limits,
        bindings: 0,
        blocks: 0,
    };
    let mut wrapper = Builder::new(entry, 0, &mut tables);
    let block = wrapper.block()?;
    let args = arguments
        .iter()
        .map(|arg| wrapper.argument_literal(block, arg))
        .collect::<Result<Vec<_>>>()?;
    let value = wrapper.emit(
        block,
        ValueType::Abi,
        Operation::Call {
            function: entry_id,
            args,
        },
    )?;
    wrapper.finish_block(block, Terminator::Return { value });
    let mut functions = vec![wrapper.finish(FunctionId::new(0))];
    let mut reference_functions = Vec::new();
    for (name, arity) in &names {
        let id = tables.targets[name].0;
        let mut builder = Builder::new(name, *arity, &mut tables);
        if supplied_natives.contains_key(name) {
            let block = builder.block()?;
            let args = (0..*arity).map(|i| ValueId::new(i as u32)).collect();
            let value = builder.native_call(block, name, args)?;
            builder.finish_block(block, Terminator::Return { value });
        } else {
            let Some(IrDecl::Function { body, params, .. }) = declarations.get(name) else {
                return Err(IrExecutionError::MissingDeclaration(name.clone()));
            };
            let vars = params
                .iter()
                .enumerate()
                .map(|(i, param)| {
                    (
                        param.x,
                        Local {
                            value: ValueId::new(i as u32),
                            constructor: None,
                        },
                    )
                })
                .collect();
            builder.body(body, vars)?;
            reference_functions.push(ReferenceFunction {
                name: name.clone(),
                function: flbc::FunctionId::new(id.get()),
            });
        }
        functions.push(builder.finish(id));
    }
    let program = fir::Program {
        schema_version: fir::FIR_SCHEMA_VERSION,
        entry: FunctionId::new(0),
        constructors: tables.constructors,
        projections: tables.projections,
        closure_types,
        intrinsics,
        functions,
    };
    let checked = fir::validate(program, limits.fir).map_err(IrExecutionError::FirValidation)?;
    let program = fir::lower_to_flbc_with_ownership(&checked, limits.ownership)
        .map_err(IrExecutionError::Lowering)?;
    Ok(CompiledIr {
        program,
        reference_functions,
        native_externs: native_order
            .iter()
            .map(|(_, native)| native.row.id.to_owned())
            .collect(),
    })
}

fn insert_helper(natives: &mut BTreeMap<Name, Native>, text: &str) -> Result<()> {
    let name = Name::from_components(text.split('.'));
    let row =
        native_row(&name).ok_or_else(|| IrExecutionError::MissingDeclaration(name.clone()))?;
    natives.insert(name, Native::new(row, row.arity as usize)?);
    Ok(())
}

fn unbox_intrinsic(ty: &IrType) -> Option<&'static str> {
    match ty {
        IrType::UInt8 => Some("UInt8.ofNat"),
        IrType::UInt16 => Some("UInt16.ofNat"),
        IrType::UInt32 => Some("UInt32.ofNat"),
        _ => None,
    }
}

struct Tables {
    targets: BTreeMap<Name, (FunctionId, usize)>,
    intrinsic_ids: BTreeMap<Name, IntrinsicId>,
    constructors: Vec<ConstructorDecl>,
    projections: Vec<ProjectionDecl>,
    limits: IrExecutionLimits,
    bindings: usize,
    blocks: usize,
}

#[derive(Clone, Copy)]
struct Local {
    value: ValueId,
    constructor: Option<ConstructorId>,
}

type Locals = BTreeMap<u64, Local>;

struct Builder<'a> {
    name: &'a Name,
    arity: usize,
    next_value: u32,
    blocks: Vec<Block>,
    tables: &'a mut Tables,
}

impl<'a> Builder<'a> {
    fn new(name: &'a Name, arity: usize, tables: &'a mut Tables) -> Self {
        Self {
            name,
            arity,
            next_value: arity as u32,
            blocks: Vec::new(),
            tables,
        }
    }

    fn block(&mut self) -> Result<BlockId> {
        self.tables.blocks = self.tables.blocks.saturating_add(1);
        if self.tables.blocks > self.tables.limits.fir.max_blocks {
            return Err(IrExecutionError::Limit("lowered blocks"));
        }
        let id = BlockId::new(
            u32::try_from(self.blocks.len()).map_err(|_| IrExecutionError::Limit("block ids"))?,
        );
        self.blocks.push(Block {
            id,
            bindings: Vec::new(),
            terminator: Terminator::Jump { target: id },
        });
        Ok(id)
    }

    fn emit(&mut self, block: BlockId, ty: ValueType, operation: Operation) -> Result<ValueId> {
        self.tables.bindings = self.tables.bindings.saturating_add(1);
        if self.tables.bindings > self.tables.limits.fir.max_values {
            return Err(IrExecutionError::Limit("lowered values"));
        }
        let id = ValueId::new(self.next_value);
        self.next_value = self
            .next_value
            .checked_add(1)
            .ok_or(IrExecutionError::Limit("value ids"))?;
        self.blocks[block.get() as usize]
            .bindings
            .push(Binding { id, ty, operation });
        Ok(id)
    }

    fn finish_block(&mut self, block: BlockId, terminator: Terminator) {
        self.blocks[block.get() as usize].terminator = terminator;
    }

    fn finish(self, id: FunctionId) -> Function {
        Function {
            id,
            parameters: vec![ValueType::Abi; self.arity],
            parameter_ownership: vec![flbc::ArgumentOwnership::Borrowed; self.arity],
            result: ValueType::Abi,
            result_ownership: flbc::CallableResultOwnership::Erased,
            blocks: self.blocks,
        }
    }

    fn boxed(&mut self, block: BlockId, ty: ValueType, operation: Operation) -> Result<ValueId> {
        let value = self.emit(block, ty, operation)?;
        self.emit(block, ValueType::Abi, Operation::Box(value))
    }

    fn nat(&mut self, block: BlockId, n: &IrNat) -> Result<ValueId> {
        let operation = match n {
            IrNat::Small(n) if *n <= (usize::MAX >> 1) as u64 => Operation::Nat(*n),
            IrNat::Small(n) => Operation::NatBig(vec![*n]),
            IrNat::Big(limbs) => Operation::NatBig(limbs.clone()),
        };
        self.boxed(block, ValueType::Nat, operation)
    }

    fn argument_literal(&mut self, block: BlockId, argument: &EntryArgument) -> Result<ValueId> {
        match argument {
            EntryArgument::Nat(value) => self.nat(block, value),
            EntryArgument::String(value) => {
                self.boxed(block, ValueType::String, Operation::String(value.clone()))
            }
            EntryArgument::Erased => self.boxed(block, ValueType::Unit, Operation::Unit),
        }
    }

    fn argument(&mut self, block: BlockId, arg: &IrArg, locals: &Locals) -> Result<ValueId> {
        match arg {
            IrArg::Var(x) => locals
                .get(x)
                .map(|value| value.value)
                .ok_or_else(|| unsupported(self.name, "out-of-scope variable")),
            IrArg::Erased => self.boxed(block, ValueType::Unit, Operation::Unit),
        }
    }

    fn arguments(
        &mut self,
        block: BlockId,
        args: &[IrArg],
        locals: &Locals,
    ) -> Result<Vec<ValueId>> {
        args.iter()
            .map(|arg| self.argument(block, arg, locals))
            .collect()
    }

    fn native_call(&mut self, block: BlockId, name: &Name, args: Vec<ValueId>) -> Result<ValueId> {
        let intrinsic = self
            .tables
            .intrinsic_ids
            .get(name)
            .copied()
            .ok_or_else(|| IrExecutionError::MissingDeclaration(name.clone()))?;
        self.emit(
            block,
            ValueType::Abi,
            Operation::Intrinsic { intrinsic, args },
        )
    }

    fn constructor(&mut self, info: &IrCtorInfo) -> Result<ConstructorId> {
        if info.usize != 0 || info.ssize != 0 {
            return Err(unsupported(self.name, "packed constructor fields"));
        }
        let tag =
            u8::try_from(info.cidx).map_err(|_| unsupported(self.name, "constructor tag width"))?;
        let fields = usize::try_from(info.size)
            .map_err(|_| IrExecutionError::Limit("constructor fields"))?;
        if fields >= fln_rt::abi::MAX_CTOR_FIELDS || tag > fln_rt::abi::TAG_MAX_CTOR_TAG {
            return Err(unsupported(self.name, "constructor layout"));
        }
        if let Some(existing) = self
            .tables
            .constructors
            .iter()
            .find(|c| c.tag == tag && c.fields.len() == fields)
        {
            return Ok(existing.id);
        }
        if self.tables.constructors.len() >= self.tables.limits.fir.max_constructors {
            return Err(IrExecutionError::Limit("constructors"));
        }
        let id = ConstructorId::new(self.tables.constructors.len() as u32);
        self.tables.constructors.push(ConstructorDecl {
            id,
            tag,
            fields: vec![ValueType::Abi; fields],
            static_scalar_bytes: Vec::new(),
        });
        Ok(id)
    }

    fn expression(
        &mut self,
        block: BlockId,
        ty: &IrType,
        expr: &IrExpr,
        locals: &Locals,
    ) -> Result<Local> {
        let mut constructor = None;
        let value =
            match expr {
                IrExpr::Lit(IrLit::Num(n)) => {
                    let mask = match ty {
                        IrType::UInt8 => Some(0xff),
                        IrType::UInt16 => Some(0xffff),
                        IrType::UInt32 => Some(0xffff_ffff),
                        _ => None,
                    };
                    if let Some(mask) = mask {
                        let low = match n {
                            IrNat::Small(n) => *n,
                            IrNat::Big(limbs) => limbs.first().copied().unwrap_or(0),
                        };
                        self.nat(block, &IrNat::Small(low & mask))?
                    } else {
                        self.nat(block, n)?
                    }
                }
                IrExpr::Lit(IrLit::Str(text)) => {
                    self.boxed(block, ValueType::String, Operation::String(text.clone()))?
                }
                IrExpr::Fap { function, args } => {
                    let args = self.arguments(block, args, locals)?;
                    if self.tables.intrinsic_ids.contains_key(function) {
                        self.native_call(block, function, args)?
                    } else {
                        let (function, _) =
                            self.tables.targets.get(function).copied().ok_or_else(|| {
                                IrExecutionError::MissingDeclaration(function.clone())
                            })?;
                        self.emit(block, ValueType::Abi, Operation::Call { function, args })?
                    }
                }
                IrExpr::Pap { function, args } => {
                    let (function, arity) =
                        self.tables.targets.get(function).copied().ok_or_else(|| {
                            IrExecutionError::MissingDeclaration(function.clone())
                        })?;
                    let remaining = arity
                        .checked_sub(args.len())
                        .filter(|n| *n > 0)
                        .ok_or_else(|| unsupported(self.name, "saturated partial application"))?;
                    let captures = self.arguments(block, args, locals)?;
                    let closure_type = ClosureTypeId::new(remaining as u32 - 1);
                    let capture_ownership = vec![flbc::ArgumentOwnership::Borrowed; captures.len()];
                    self.boxed(
                        block,
                        ValueType::Closure(closure_type),
                        Operation::Closure {
                            closure_type,
                            function,
                            captures,
                            capture_ownership,
                        },
                    )?
                }
                IrExpr::Ap { x, args } => {
                    if args.is_empty() {
                        return Err(unsupported(self.name, "empty closure application"));
                    }
                    let closure = self.argument(block, &IrArg::Var(*x), locals)?;
                    let ty = ValueType::Closure(ClosureTypeId::new(args.len() as u32 - 1));
                    let closure = self.emit(block, ty, Operation::Unbox { value: closure, ty })?;
                    let args = self.arguments(block, args, locals)?;
                    let argument_ownership = vec![flbc::ArgumentOwnership::Borrowed; args.len()];
                    self.emit(
                        block,
                        ValueType::Abi,
                        Operation::Apply {
                            closure,
                            args,
                            argument_ownership,
                            result_ownership: flbc::CallableResultOwnership::Erased,
                        },
                    )?
                }
                IrExpr::Box { ty, x } => {
                    if !matches!(ty, IrType::UInt8 | IrType::UInt16 | IrType::UInt32) {
                        return Err(unsupported(self.name, "scalar boxing representation"));
                    }
                    self.argument(block, &IrArg::Var(*x), locals)?
                }
                IrExpr::Unbox { x } => {
                    let helper = unbox_intrinsic(ty)
                        .ok_or_else(|| unsupported(self.name, "scalar unboxing representation"))?;
                    let value = self.argument(block, &IrArg::Var(*x), locals)?;
                    self.native_call(
                        block,
                        &Name::from_components(helper.split('.')),
                        vec![value],
                    )?
                }
                IrExpr::Ctor { info, args } => {
                    let id = self.constructor(info)?;
                    constructor = Some(id);
                    if info.size == 0 {
                        self.nat(block, &IrNat::Small(info.cidx))?
                    } else {
                        let fields = self.arguments(block, args, locals)?;
                        self.boxed(
                            block,
                            ValueType::Constructor,
                            Operation::Ctor {
                                constructor: id,
                                fields,
                            },
                        )?
                    }
                }
                IrExpr::Proj { i, x } => {
                    let local = locals
                        .get(x)
                        .ok_or_else(|| unsupported(self.name, "out-of-scope projection"))?;
                    let id = local.constructor.ok_or_else(|| {
                        unsupported(self.name, "projection without a known constructor shape")
                    })?;
                    let field = u16::try_from(*i)
                        .map_err(|_| unsupported(self.name, "projection width"))?;
                    if self.tables.projections.len() >= self.tables.limits.fir.max_projections {
                        return Err(IrExecutionError::Limit("projections"));
                    }
                    let projection = ProjectionId::new(self.tables.projections.len() as u32);
                    self.tables.projections.push(ProjectionDecl {
                        id: projection,
                        constructor: id,
                        field,
                    });
                    let value = self.emit(
                        block,
                        ValueType::Constructor,
                        Operation::Unbox {
                            value: local.value,
                            ty: ValueType::Constructor,
                        },
                    )?;
                    self.emit(
                        block,
                        ValueType::Abi,
                        Operation::Project { projection, value },
                    )?
                }
                IrExpr::Reset { .. } | IrExpr::Reuse { .. } | IrExpr::IsShared { .. } => {
                    return Err(unsupported(
                        self.name,
                        "reference-count observation or constructor reuse",
                    ));
                }
                IrExpr::UProj { .. } | IrExpr::SProj { .. } => {
                    return Err(unsupported(self.name, "packed scalar projection"));
                }
            };
        Ok(Local { value, constructor })
    }

    fn body(&mut self, body: &IrBody, mut locals: Locals) -> Result<BlockId> {
        let block = self.block()?;
        for stmt in &body.stmts {
            match stmt {
                IrStmt::VDecl { x, ty, expr } => {
                    let value = self.expression(block, ty, expr, &locals)?;
                    locals.insert(*x, value);
                }
                // The immutable subset is lowered to managed values. The
                // independent ownership pass reconstructs actual final uses.
                IrStmt::Inc { .. } | IrStmt::Dec { .. } | IrStmt::Del { .. } => {}
                _ => return Err(unsupported(self.name, "mutable IR statement or join point")),
            }
        }
        match body.terminal.as_ref() {
            IrTerminal::Ret(arg) => {
                let value = self.argument(block, arg, &locals)?;
                self.finish_block(block, Terminator::Return { value });
            }
            IrTerminal::Case {
                x, x_type, alts, ..
            } => self.case(block, *x, x_type, alts, locals)?,
            IrTerminal::Unreachable => self.unreachable(block)?,
            IrTerminal::Jmp { .. } => return Err(unsupported(self.name, "join-point jump")),
        }
        Ok(block)
    }

    fn unreachable(&mut self, block: BlockId) -> Result<()> {
        let message = self.emit(
            block,
            ValueType::String,
            Operation::String(format!(
                "unreachable imported IR in {}",
                self.name.to_display_string()
            )),
        )?;
        self.finish_block(block, Terminator::Panic { message });
        Ok(())
    }

    fn case(
        &mut self,
        block: BlockId,
        x: u64,
        ty: &IrType,
        alts: &[IrAlt],
        locals: Locals,
    ) -> Result<()> {
        let value = locals
            .get(&x)
            .ok_or_else(|| unsupported(self.name, "case variable"))?
            .value;
        let scalar = matches!(
            ty,
            IrType::UInt8 | IrType::UInt16 | IrType::UInt32 | IrType::Tagged
        );
        let mut arms: Vec<_> = alts
            .iter()
            .filter_map(|alt| match alt {
                IrAlt::Ctor { info, body } => Some((info, body)),
                _ => None,
            })
            .collect();
        let default = alts.iter().find_map(|alt| match alt {
            IrAlt::Default { body } => Some(body),
            _ => None,
        });
        if !scalar {
            // Check object cases before scalar nullary constructors. No
            // reference-count test or guessed object-to-number conversion.
            arms.sort_by_key(|(info, _)| info.size == 0);
            if default.is_some() && arms.iter().any(|(info, _)| info.size == 0) {
                return Err(unsupported(
                    self.name,
                    "mixed scalar/object case with a default",
                ));
            }
        }
        self.case_arm(block, x, value, &arms, default, locals)
    }

    fn case_arm(
        &mut self,
        block: BlockId,
        x: u64,
        value: ValueId,
        arms: &[(&IrCtorInfo, &IrBody)],
        default: Option<&IrBody>,
        locals: Locals,
    ) -> Result<()> {
        let Some(((info, body), rest)) = arms.split_first() else {
            if let Some(body) = default {
                let target = self.body(body, locals)?;
                self.finish_block(block, Terminator::Jump { target });
            } else {
                self.unreachable(block)?;
            }
            return Ok(());
        };
        let constructor = self.constructor(info)?;
        let condition = if info.size == 0 {
            let tag = self.nat(block, &IrNat::Small(info.cidx))?;
            let equal = self.native_call(
                block,
                &Name::from_components(["Nat", "beq"]),
                vec![value, tag],
            )?;
            self.emit(
                block,
                ValueType::Bool,
                Operation::Unbox {
                    value: equal,
                    ty: ValueType::Bool,
                },
            )?
        } else {
            let object = self.emit(
                block,
                ValueType::Constructor,
                Operation::Unbox {
                    value,
                    ty: ValueType::Constructor,
                },
            )?;
            self.emit(
                block,
                ValueType::Bool,
                Operation::CtorTest {
                    constructor,
                    value: object,
                },
            )?
        };
        let mut matching = locals.clone();
        matching.insert(
            x,
            Local {
                value,
                constructor: Some(constructor),
            },
        );
        let nonzero = self.body(body, matching)?;
        let zero = self.block()?;
        self.case_arm(zero, x, value, rest, default, locals)?;
        self.finish_block(
            block,
            Terminator::BranchZero {
                condition,
                zero,
                nonzero,
            },
        );
        Ok(())
    }
}
