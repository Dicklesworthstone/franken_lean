use super::*;
use fln_comp::fir::{
    Binding, Block, BlockId, ClosureTypeDecl, ClosureTypeId, ConstructorDecl, ConstructorId,
    Function, FunctionId, IntrinsicDecl, IntrinsicId, Operation, ProjectionDecl, ProjectionId,
    Terminator, ValueId, ValueType,
};
use fln_olean::ir::{IrAlt, IrArg, IrCtorInfo, IrExpr, IrLit, IrParam};
use std::sync::Arc;

type Result<T> = std::result::Result<T, IrExecutionError>;

pub(super) fn compile(
    declarations: &BTreeMap<Name, &IrDecl>,
    supplied_natives: &BTreeMap<Name, Native>,
    entry: &Name,
    arguments: &[EntryArgument],
    limits: IrExecutionLimits,
) -> Result<CompiledIr> {
    let entry_parameters: &[IrParam] = match declarations.get(entry) {
        Some(IrDecl::Function { params, .. }) => params,
        _ => &[],
    };
    let mut helper_natives = BTreeMap::new();
    for argument in arguments {
        if matches!(argument, EntryArgument::FloatBits(_)) {
            insert_helper(&mut helper_natives, "UInt64.ofNat")?;
        }
    }
    for param in entry_parameters {
        if let Some(wide) = wide_scalar(&param.ty) {
            insert_helper(&mut helper_natives, wide.of_nat)?;
        } else if let Some(float) = floating_scalar(&param.ty) {
            insert_helper(&mut helper_natives, float.to_bits)?;
        }
    }
    for declaration in declarations.values() {
        if let IrDecl::Function { body, .. } = declaration {
            for body in body.bodies() {
                if let IrTerminal::Case { x_type, .. } = body.terminal.as_ref() {
                    if let Some(wide) = wide_scalar(x_type) {
                        insert_helper(&mut helper_natives, wide.of_nat)?;
                        insert_helper(&mut helper_natives, wide.equal)?;
                    } else {
                        insert_helper(&mut helper_natives, "Nat.beq")?;
                    }
                }
                for stmt in &body.stmts {
                    let setter_check = match stmt {
                        IrStmt::USet { .. } => Some("USize.toNat"),
                        IrStmt::SSet { ty, .. } => floating_scalar(ty)
                            .map(|float| float.to_bits)
                            .or_else(|| packed_scalar_kind(ty).map(packed_scalar_to_nat)),
                        _ => None,
                    };
                    if let Some(check) = setter_check {
                        insert_helper(&mut helper_natives, check)?;
                    }
                    let IrStmt::VDecl { ty, expr, .. } = stmt else {
                        continue;
                    };
                    match expr {
                        IrExpr::Unbox { .. } => {
                            if let Some(wide) = wide_scalar(ty) {
                                insert_helper(&mut helper_natives, wide.to_nat)?;
                                insert_helper(&mut helper_natives, wide.of_nat)?;
                            } else if let Some(float) = floating_scalar(ty) {
                                insert_helper(&mut helper_natives, float.to_bits)?;
                            } else if let Some(name) = unbox_intrinsic(ty) {
                                insert_helper(&mut helper_natives, name)?;
                            }
                        }
                        IrExpr::Box { ty, .. } => {
                            if let Some(wide) = wide_scalar(ty) {
                                insert_helper(&mut helper_natives, wide.to_nat)?;
                                insert_helper(&mut helper_natives, wide.of_nat)?;
                            } else if let Some(float) = floating_scalar(ty) {
                                insert_helper(&mut helper_natives, float.to_bits)?;
                            }
                        }
                        IrExpr::Lit(IrLit::Num(_)) | IrExpr::Ctor { .. } => {
                            if let Some(wide) = wide_scalar(ty) {
                                insert_helper(&mut helper_natives, wide.of_nat)?;
                            }
                        }
                        _ => {}
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
            effect: native.effect,
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
    let function_count = names
        .len()
        .checked_add(1)
        .filter(|count| *count <= limits.fir.max_functions)
        .and_then(|count| u32::try_from(count).ok())
        .ok_or(IrExecutionError::Limit("lowered functions"))?;
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
        intrinsics,
        constructors: Vec::new(),
        projections: Vec::new(),
        limits,
        bindings: 0,
        blocks: 0,
        next_function: function_count,
        helper_functions: Vec::new(),
        helper_provenance: Vec::new(),
        scope_work: 0,
        capture_operands: 0,
        packed_operands: 0,
        packed_scalar_bytes: 0,
    };
    let mut wrapper = Builder::new(entry, 0, &mut tables)?;
    let block = wrapper.block()?;
    let args = arguments
        .iter()
        .enumerate()
        .map(|(index, arg)| {
            let value = wrapper.argument_literal(block, arg)?;
            if let Some(wide) = entry_parameters
                .get(index)
                .and_then(|param| wide_scalar(&param.ty))
            {
                wrapper.native_call(
                    block,
                    &Name::from_components(wide.of_nat.split('.')),
                    vec![value],
                )
            } else if let Some(float) = entry_parameters
                .get(index)
                .and_then(|param| floating_scalar(&param.ty))
            {
                wrapper.validate_float(block, float, value)
            } else {
                Ok(value)
            }
        })
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
        let mut builder = Builder::new(name, *arity, &mut tables)?;
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
            builder.body(body, vars, Joins::new())?;
            reference_functions.push(ReferenceFunction {
                name: name.clone(),
                function: flbc::FunctionId::new(id.get()),
            });
        }
        functions.push(builder.finish(id));
    }
    functions.append(&mut tables.helper_functions);
    functions.sort_by_key(|function| function.id);
    reference_functions.append(&mut tables.helper_provenance);
    reference_functions.sort_by_key(|function| function.function);
    let program = fir::Program {
        schema_version: fir::FIR_SCHEMA_VERSION,
        entry: FunctionId::new(0),
        constructors: tables.constructors,
        projections: tables.projections,
        closure_types,
        intrinsics: tables.intrinsics,
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

struct WideScalar {
    of_nat: &'static str,
    to_nat: &'static str,
    equal: &'static str,
}

fn wide_scalar(ty: &IrType) -> Option<WideScalar> {
    match ty {
        IrType::UInt64 => Some(WideScalar {
            of_nat: "UInt64.ofNat",
            to_nat: "UInt64.toNat",
            equal: "UInt64.decEq",
        }),
        IrType::USize => Some(WideScalar {
            of_nat: "USize.ofNat",
            to_nat: "USize.toNat",
            equal: "USize.decEq",
        }),
        _ => None,
    }
}

struct FloatingScalar {
    to_bits: &'static str,
}

fn floating_scalar(ty: &IrType) -> Option<FloatingScalar> {
    match ty {
        IrType::Float => Some(FloatingScalar {
            to_bits: "Float.toBits",
        }),
        IrType::Float32 => Some(FloatingScalar {
            to_bits: "Float32.toBits",
        }),
        _ => None,
    }
}

fn is_scalar_case(ty: &IrType) -> bool {
    matches!(
        ty,
        IrType::UInt8
            | IrType::UInt16
            | IrType::UInt32
            | IrType::UInt64
            | IrType::USize
            | IrType::Tagged
    )
}

fn packed_scalar_kind(ty: &IrType) -> Option<flbc::ScalarKind> {
    match ty {
        IrType::UInt8 => Some(flbc::ScalarKind::UInt8),
        IrType::UInt16 => Some(flbc::ScalarKind::UInt16),
        IrType::UInt32 | IrType::Float32 => Some(flbc::ScalarKind::UInt32),
        IrType::UInt64 | IrType::Float => Some(flbc::ScalarKind::UInt64),
        IrType::USize => Some(flbc::ScalarKind::USize),
        _ => None,
    }
}

fn packed_scalar_to_nat(kind: flbc::ScalarKind) -> &'static str {
    match kind {
        flbc::ScalarKind::UInt8 => "UInt8.toNat",
        flbc::ScalarKind::UInt16 => "UInt16.toNat",
        flbc::ScalarKind::UInt32 => "UInt32.toNat",
        flbc::ScalarKind::UInt64 => "UInt64.toNat",
        flbc::ScalarKind::USize => "USize.toNat",
    }
}

fn fieldless_constructor(info: &IrCtorInfo) -> bool {
    info.size == 0 && info.usize == 0 && info.ssize == 0
}

struct Tables {
    targets: BTreeMap<Name, (FunctionId, usize)>,
    intrinsic_ids: BTreeMap<Name, IntrinsicId>,
    intrinsics: Vec<IntrinsicDecl>,
    constructors: Vec<ConstructorDecl>,
    projections: Vec<ProjectionDecl>,
    limits: IrExecutionLimits,
    bindings: usize,
    blocks: usize,
    next_function: u32,
    helper_functions: Vec<Function>,
    helper_provenance: Vec<ReferenceFunction>,
    scope_work: u64,
    capture_operands: usize,
    packed_operands: usize,
    packed_scalar_bytes: usize,
}

impl Tables {
    fn helper_id(&mut self) -> Result<FunctionId> {
        if self.next_function as usize >= self.limits.fir.max_functions {
            return Err(IrExecutionError::Limit("lowered functions"));
        }
        let id = FunctionId::new(self.next_function);
        self.next_function = self
            .next_function
            .checked_add(1)
            .ok_or(IrExecutionError::Limit("function ids"))?;
        Ok(id)
    }

    // Scope snapshots and lifted arguments can be much larger than the source
    // body. Bound them before allocation, as well as validating the final FIR.
    fn scope_work(&mut self, count: usize) -> Result<()> {
        self.scope_work = self.scope_work.saturating_add(count as u64);
        if self.scope_work > self.limits.ir.max_work {
            return Err(IrExecutionError::Limit("lowering scope work"));
        }
        Ok(())
    }

    fn capture_operands(&mut self, count: usize) -> Result<()> {
        self.capture_operands = self.capture_operands.saturating_add(count);
        if self.capture_operands > self.limits.fir.max_operands {
            return Err(IrExecutionError::Limit("join capture operands"));
        }
        Ok(())
    }

    fn packed_operands(&mut self, count: usize) -> Result<()> {
        self.packed_operands = self.packed_operands.saturating_add(count);
        if self.packed_operands > self.limits.fir.max_operands {
            return Err(IrExecutionError::Limit("packed constructor operands"));
        }
        Ok(())
    }
}

#[derive(Clone, Copy)]
struct Local {
    value: ValueId,
    constructor: Option<ConstructorId>,
}

type Locals = BTreeMap<u64, Local>;

struct PendingConstructor {
    constructor: ConstructorId,
    fields: Vec<ValueId>,
    scalars: BTreeMap<u16, flbc::PackedScalar<ValueId>>,
    object_bytes: usize,
    scalar_bytes: usize,
}

type PendingConstructors = BTreeMap<u64, PendingConstructor>;

struct Join {
    function: FunctionId,
    parameters: usize,
    captures: Vec<u64>,
}

// Sharing descriptors prevents a chain of joins from recursively copying all
// preceding captures whenever a lexical scope is copied.
type Joins = BTreeMap<u64, Arc<Join>>;

struct Builder<'a> {
    name: &'a Name,
    arity: usize,
    next_value: u32,
    blocks: Vec<Block>,
    pending_values: usize,
    tables: &'a mut Tables,
}

impl<'a> Builder<'a> {
    fn new(name: &'a Name, arity: usize, tables: &'a mut Tables) -> Result<Self> {
        tables.bindings = tables.bindings.saturating_add(arity);
        if tables.bindings > tables.limits.fir.max_values {
            return Err(IrExecutionError::Limit("lowered values"));
        }
        let next_value =
            u32::try_from(arity).map_err(|_| IrExecutionError::Limit("parameter ids"))?;
        Ok(Self {
            name,
            arity,
            next_value,
            blocks: Vec::new(),
            pending_values: 0,
            tables,
        })
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
        if self.tables.bindings.saturating_add(self.pending_values)
            > self.tables.limits.fir.max_values
        {
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

    fn wide_literal(&mut self, block: BlockId, wide: WideScalar, n: &IrNat) -> Result<ValueId> {
        let value = self.nat(block, n)?;
        self.native_call(
            block,
            &Name::from_components(wide.of_nat.split('.')),
            vec![value],
        )
    }

    fn canonicalize_wide(
        &mut self,
        block: BlockId,
        wide: WideScalar,
        value: ValueId,
    ) -> Result<ValueId> {
        // Golem stores wide scalars in checked boxes containing all 64 bits.
        // A Nat intermediate checks the input carrier before rebuilding that
        // box; an ordinary object must never be reinterpreted as scalar bits.
        let value = self.native_call(
            block,
            &Name::from_components(wide.to_nat.split('.')),
            vec![value],
        )?;
        self.native_call(
            block,
            &Name::from_components(wide.of_nat.split('.')),
            vec![value],
        )
    }

    fn argument_literal(&mut self, block: BlockId, argument: &EntryArgument) -> Result<ValueId> {
        match argument {
            EntryArgument::Nat(value) => self.nat(block, value),
            EntryArgument::String(value) => {
                self.boxed(block, ValueType::String, Operation::String(value.clone()))
            }
            EntryArgument::FloatBits(bits) => {
                let value = self.nat(block, &IrNat::Small(*bits))?;
                // UInt64 and Float share the exact 64-bit scalar carrier.
                // Public Float.ofBits canonicalizes NaNs, so it is not a
                // representation-preserving box for an imported raw value.
                self.native_call(
                    block,
                    &Name::from_components(["UInt64", "ofNat"]),
                    vec![value],
                )
            }
            EntryArgument::Float32Bits(bits) => {
                let value = self.nat(block, &IrNat::Small(u64::from(*bits)))?;
                self.box_float32_bits(block, value)
            }
            EntryArgument::Erased => self.boxed(block, ValueType::Unit, Operation::Unit),
        }
    }

    fn box_float32_bits(&mut self, block: BlockId, value: ValueId) -> Result<ValueId> {
        // Float32's four-byte scalar carrier differs from tagged UInt32.
        // Reuse checked packed construction to copy the raw bits without
        // invoking public Float32.ofBits, which deliberately normalizes NaNs.
        let kind = flbc::ScalarKind::UInt32;
        let constructor = self.constructor(&IrCtorInfo {
            name: Name::anonymous(),
            cidx: 0,
            size: 0,
            usize: 0,
            ssize: kind.width() as u64,
        })?;
        self.tables.packed_operands(1)?;
        self.boxed(
            block,
            ValueType::Constructor,
            Operation::CtorPacked {
                constructor,
                fields: vec![],
                scalars: vec![flbc::PackedScalar {
                    offset: 0,
                    kind,
                    value,
                }],
            },
        )
    }

    fn validate_float(
        &mut self,
        block: BlockId,
        float: FloatingScalar,
        value: ValueId,
    ) -> Result<ValueId> {
        // The native boundary checks the boxed scalar carrier. Keep the
        // original value: public toBits canonicalizes NaNs, while IR box,
        // unbox and packed fields must preserve every payload bit.
        self.native_call(
            block,
            &Name::from_components(float.to_bits.split('.')),
            vec![value],
        )?;
        Ok(value)
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

    fn native_call(
        &mut self,
        block: BlockId,
        name: &Name,
        mut args: Vec<ValueId>,
    ) -> Result<ValueId> {
        let intrinsic = self
            .tables
            .intrinsic_ids
            .get(name)
            .copied()
            .ok_or_else(|| IrExecutionError::MissingDeclaration(name.clone()))?;
        for (index, argument) in args.iter_mut().enumerate() {
            if self.tables.intrinsics[intrinsic.get() as usize]
                .argument_ownership
                .get(index)
                == Some(&flbc::ArgumentOwnership::Owned)
            {
                // Imported locals remain reusable after a consuming native
                // call, including when one local supplies several operands.
                // Give each owned operand a distinct reference; the checked
                // ownership pass can turn its last-use copy into a move.
                // Unique operands retain their separate exclusivity contract.
                *argument = self.emit(block, ValueType::Abi, Operation::Alias(*argument))?;
            }
        }
        self.emit(
            block,
            ValueType::Abi,
            Operation::Intrinsic { intrinsic, args },
        )
    }

    fn constructor(&mut self, info: &IrCtorInfo) -> Result<ConstructorId> {
        let tag =
            u8::try_from(info.cidx).map_err(|_| unsupported(self.name, "constructor tag width"))?;
        let fields = usize::try_from(info.size)
            .map_err(|_| IrExecutionError::Limit("constructor fields"))?;
        let scalar_bytes = info
            .usize
            .checked_mul(std::mem::size_of::<usize>() as u64)
            .and_then(|bytes| bytes.checked_add(info.ssize))
            .and_then(|bytes| usize::try_from(bytes).ok())
            .ok_or_else(|| unsupported(self.name, "packed constructor size"))?;
        if fields >= fln_rt::abi::MAX_CTOR_FIELDS
            || scalar_bytes >= fln_rt::abi::MAX_CTOR_SCALARS_SIZE
            || tag > fln_rt::abi::TAG_MAX_CTOR_TAG
        {
            return Err(unsupported(self.name, "constructor layout"));
        }
        if let Some(existing) = self.tables.constructors.iter().find(|c| {
            c.tag == tag && c.fields.len() == fields && c.static_scalar_bytes.len() == scalar_bytes
        }) {
            return Ok(existing.id);
        }
        if self.tables.constructors.len() >= self.tables.limits.fir.max_constructors {
            return Err(IrExecutionError::Limit("constructors"));
        }
        self.tables.packed_scalar_bytes =
            self.tables.packed_scalar_bytes.saturating_add(scalar_bytes);
        if self.tables.packed_scalar_bytes > self.tables.limits.fir.max_literal_bytes {
            return Err(IrExecutionError::Limit("packed constructor bytes"));
        }
        let id = ConstructorId::new(self.tables.constructors.len() as u32);
        self.tables.constructors.push(ConstructorDecl {
            id,
            tag,
            fields: vec![ValueType::Abi; fields],
            static_scalar_bytes: vec![0; scalar_bytes],
        });
        Ok(id)
    }

    fn packed_offset(&self, slots: u64, bytes: u64) -> Result<u16> {
        slots
            .checked_mul(std::mem::size_of::<usize>() as u64)
            .and_then(|offset| offset.checked_add(bytes))
            .and_then(|offset| u16::try_from(offset).ok())
            .ok_or_else(|| unsupported(self.name, "packed scalar offset"))
    }

    fn begin_packed_constructor(
        &mut self,
        block: BlockId,
        x: u64,
        info: &IrCtorInfo,
        args: &[IrArg],
        locals: &Locals,
        pending: &mut PendingConstructors,
    ) -> Result<()> {
        let constructor = self.constructor(info)?;
        self.pending_values = self.pending_values.saturating_add(2);
        if self.tables.bindings.saturating_add(self.pending_values)
            > self.tables.limits.fir.max_values
        {
            return Err(IrExecutionError::Limit("lowered values"));
        }
        self.tables.packed_operands(args.len())?;
        let fields = self.arguments(block, args, locals)?;
        let declaration = &self.tables.constructors[constructor.get() as usize];
        pending.insert(
            x,
            PendingConstructor {
                constructor,
                fields,
                scalars: BTreeMap::new(),
                object_bytes: declaration.fields.len() * std::mem::size_of::<usize>(),
                scalar_bytes: declaration.static_scalar_bytes.len(),
            },
        );
        Ok(())
    }

    fn initialize_packed_scalar(
        &mut self,
        block: BlockId,
        x: u64,
        scalar: flbc::PackedScalar<u64>,
        float: Option<FloatingScalar>,
        locals: &Locals,
        pending: &mut PendingConstructors,
    ) -> Result<()> {
        let flbc::PackedScalar {
            offset,
            kind,
            value: y,
        } = scalar;
        let constructor = pending
            .get_mut(&x)
            .ok_or_else(|| unsupported(self.name, "packed mutation after read or escape"))?;
        let end = usize::from(offset).saturating_add(kind.width());
        if usize::from(offset) < constructor.object_bytes
            || end
                > constructor
                    .object_bytes
                    .saturating_add(constructor.scalar_bytes)
            || constructor
                .scalars
                .range(..offset)
                .next_back()
                .is_some_and(|(_, prior)| {
                    usize::from(offset) < usize::from(prior.offset) + prior.kind.width()
                })
            || constructor
                .scalars
                .range(offset..)
                .next()
                .is_some_and(|(_, next)| usize::from(next.offset) < end)
        {
            return Err(unsupported(
                self.name,
                "packed scalar initialization layout",
            ));
        }
        let value = locals
            .get(&y)
            .ok_or_else(|| unsupported(self.name, "packed scalar initializer"))?
            .value;
        self.tables.packed_operands(1)?;
        // Validate the carrier at the original store, before any intervening
        // call can produce effects or a different refusal. Only allocation is
        // deferred; the checked original operand remains the packed value.
        self.native_call(
            block,
            &Name::from_components(
                float
                    .as_ref()
                    .map_or_else(|| packed_scalar_to_nat(kind), |float| float.to_bits)
                    .split('.'),
            ),
            vec![value],
        )?;
        let value = if float.is_some() {
            // Read the checked carrier's raw bytes, bypassing public toBits'
            // NaN normalization. Integer packed operations already preserve
            // these exact bits and validate their destination bounds.
            self.emit(
                block,
                ValueType::Abi,
                Operation::ProjectScalar {
                    value,
                    offset: 0,
                    kind,
                },
            )?
        } else {
            value
        };
        constructor.scalars.insert(
            offset,
            flbc::PackedScalar {
                offset,
                kind,
                value,
            },
        );
        Ok(())
    }

    fn materialize_packed_constructor(
        &mut self,
        block: BlockId,
        x: u64,
        locals: &mut Locals,
        pending: &mut PendingConstructors,
    ) -> Result<()> {
        let Some(constructor) = pending.remove(&x) else {
            return Ok(());
        };
        // The pin packs scalar fields without interior padding, but emits
        // their stores in source order. Evaluate values in that order, then
        // arrange the disjoint writes by their physical byte positions.
        let mut initialized = constructor.object_bytes;
        for scalar in constructor.scalars.values() {
            if usize::from(scalar.offset) != initialized {
                return Err(unsupported(self.name, "uninitialized packed constructor"));
            }
            initialized += scalar.kind.width();
        }
        if initialized != constructor.object_bytes + constructor.scalar_bytes {
            return Err(unsupported(self.name, "uninitialized packed constructor"));
        }
        self.pending_values -= 2;
        let value = self.boxed(
            block,
            ValueType::Constructor,
            Operation::CtorPacked {
                constructor: constructor.constructor,
                fields: constructor.fields,
                scalars: constructor.scalars.into_values().collect(),
            },
        )?;
        locals.insert(
            x,
            Local {
                value,
                constructor: Some(constructor.constructor),
            },
        );
        Ok(())
    }

    fn materialize_packed_arguments(
        &mut self,
        block: BlockId,
        args: &[IrArg],
        locals: &mut Locals,
        pending: &mut PendingConstructors,
    ) -> Result<()> {
        for arg in args {
            if let IrArg::Var(x) = arg {
                self.materialize_packed_constructor(block, *x, locals, pending)?;
            }
        }
        Ok(())
    }

    fn materialize_packed_reads(
        &mut self,
        block: BlockId,
        expr: &IrExpr,
        locals: &mut Locals,
        pending: &mut PendingConstructors,
    ) -> Result<()> {
        match expr {
            IrExpr::Ctor { args, .. } | IrExpr::Fap { args, .. } | IrExpr::Pap { args, .. } => {
                self.materialize_packed_arguments(block, args, locals, pending)
            }
            IrExpr::Ap { x, args } | IrExpr::Reuse { x, args, .. } => {
                self.materialize_packed_constructor(block, *x, locals, pending)?;
                self.materialize_packed_arguments(block, args, locals, pending)
            }
            IrExpr::Proj { x, .. }
            | IrExpr::UProj { x, .. }
            | IrExpr::SProj { x, .. }
            | IrExpr::Box { x, .. }
            | IrExpr::Unbox { x }
            | IrExpr::Reset { x, .. }
            | IrExpr::IsShared { x } => {
                self.materialize_packed_constructor(block, *x, locals, pending)
            }
            IrExpr::Lit(_) => Ok(()),
        }
    }

    fn materialize_all_packed(
        &mut self,
        block: BlockId,
        locals: &mut Locals,
        pending: &mut PendingConstructors,
    ) -> Result<()> {
        while let Some(x) = pending.keys().next().copied() {
            self.materialize_packed_constructor(block, x, locals, pending)?;
        }
        Ok(())
    }

    fn expression(
        &mut self,
        block: BlockId,
        ty: &IrType,
        expr: &IrExpr,
        locals: &Locals,
    ) -> Result<Local> {
        let mut constructor = None;
        let value = match expr {
            IrExpr::Lit(IrLit::Num(n)) => {
                if let Some(wide) = wide_scalar(ty) {
                    self.wide_literal(block, wide, n)?
                } else {
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
                let (function, arity) = self
                    .tables
                    .targets
                    .get(function)
                    .copied()
                    .ok_or_else(|| IrExecutionError::MissingDeclaration(function.clone()))?;
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
                let value = self.argument(block, &IrArg::Var(*x), locals)?;
                if let Some(wide) = wide_scalar(ty) {
                    self.canonicalize_wide(block, wide, value)?
                } else if let Some(float) = floating_scalar(ty) {
                    self.validate_float(block, float, value)?
                } else if matches!(ty, IrType::UInt8 | IrType::UInt16 | IrType::UInt32) {
                    value
                } else {
                    return Err(unsupported(self.name, "scalar boxing representation"));
                }
            }
            IrExpr::Unbox { x } => {
                let value = self.argument(block, &IrArg::Var(*x), locals)?;
                if let Some(wide) = wide_scalar(ty) {
                    self.canonicalize_wide(block, wide, value)?
                } else if let Some(float) = floating_scalar(ty) {
                    self.validate_float(block, float, value)?
                } else {
                    let helper = unbox_intrinsic(ty)
                        .ok_or_else(|| unsupported(self.name, "scalar unboxing representation"))?;
                    self.native_call(
                        block,
                        &Name::from_components(helper.split('.')),
                        vec![value],
                    )?
                }
            }
            IrExpr::Ctor { info, args } => {
                if fieldless_constructor(info) {
                    // Fieldless constructors are scalar tags. Their index
                    // does not occupy the bounded heap-header tag field.
                    match wide_scalar(ty) {
                        Some(wide) => self.wide_literal(block, wide, &IrNat::Small(info.cidx))?,
                        None => self.nat(block, &IrNat::Small(info.cidx))?,
                    }
                } else {
                    let id = self.constructor(info)?;
                    constructor = Some(id);
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
                let field =
                    u16::try_from(*i).map_err(|_| unsupported(self.name, "projection width"))?;
                if let Some(id) = local.constructor {
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
                } else {
                    self.emit(
                        block,
                        ValueType::Abi,
                        Operation::ProjectObject {
                            value: local.value,
                            field,
                        },
                    )?
                }
            }
            IrExpr::Reset { .. } | IrExpr::Reuse { .. } | IrExpr::IsShared { .. } => {
                return Err(unsupported(
                    self.name,
                    "reference-count observation or constructor reuse",
                ));
            }
            IrExpr::UProj { i, x } => {
                let value = self.argument(block, &IrArg::Var(*x), locals)?;
                let offset = self.packed_offset(*i, 0)?;
                self.emit(
                    block,
                    ValueType::Abi,
                    Operation::ProjectScalar {
                        value,
                        offset,
                        kind: flbc::ScalarKind::USize,
                    },
                )?
            }
            IrExpr::SProj { n, offset, x } => {
                let kind = packed_scalar_kind(ty)
                    .filter(|kind| *kind != flbc::ScalarKind::USize)
                    .ok_or_else(|| unsupported(self.name, "packed scalar projection type"))?;
                let value = self.argument(block, &IrArg::Var(*x), locals)?;
                let offset = self.packed_offset(*n, *offset)?;
                let value = self.emit(
                    block,
                    ValueType::Abi,
                    Operation::ProjectScalar {
                        value,
                        offset,
                        kind,
                    },
                )?;
                if *ty == IrType::Float32 {
                    self.box_float32_bits(block, value)?
                } else {
                    // A projected UInt64 already has Float's raw carrier.
                    value
                }
            }
        };
        Ok(Local { value, constructor })
    }

    fn join(
        &mut self,
        j: u64,
        params: &[IrParam],
        body: &IrBody,
        locals: &Locals,
        joins: &mut Joins,
    ) -> Result<()> {
        let arity = locals
            .len()
            .checked_add(params.len())
            .ok_or(IrExecutionError::Limit("join parameters"))?;
        if arity > usize::from(u16::MAX)
            || arity
                > self
                    .tables
                    .limits
                    .fir
                    .max_values
                    .saturating_sub(self.tables.bindings)
        {
            return Err(IrExecutionError::Limit("join parameters"));
        }
        let function = self.tables.helper_id()?;
        self.tables.scope_work(
            locals
                .len()
                .saturating_mul(2)
                .saturating_add(joins.len())
                .saturating_add(params.len()),
        )?;
        self.tables.capture_operands(locals.len())?;

        // Lambda lifting gives each join a normal checked FIR function. Capture
        // lexical values in structural index order, followed by explicit jump
        // arguments. Known constructor shapes survive the parameter remapping.
        let captures: Vec<_> = locals.keys().copied().collect();
        let mut helper_locals: Locals = locals
            .iter()
            .enumerate()
            .map(|(i, (x, local))| {
                (
                    *x,
                    Local {
                        value: ValueId::new(i as u32),
                        constructor: local.constructor,
                    },
                )
            })
            .collect();
        for (i, param) in params.iter().enumerate() {
            helper_locals.insert(
                param.x,
                Local {
                    value: ValueId::new((captures.len() + i) as u32),
                    constructor: None,
                },
            );
        }
        let prior_joins = joins.clone();
        let mut helper = Builder::new(self.name, arity, self.tables)?;
        helper.body(body, helper_locals, prior_joins)?;
        let lowered = helper.finish(function);
        self.tables.helper_functions.push(lowered);
        self.tables.helper_provenance.push(ReferenceFunction {
            name: self.name.clone(),
            function: flbc::FunctionId::new(function.get()),
        });

        // The Reference validator makes a join visible only after its body.
        // In particular it cannot jump to itself, or to a later declaration.
        joins.insert(
            j,
            Arc::new(Join {
                function,
                parameters: params.len(),
                captures,
            }),
        );
        Ok(())
    }

    fn body(&mut self, body: &IrBody, mut locals: Locals, mut joins: Joins) -> Result<BlockId> {
        let block = self.block()?;
        let mut pending = PendingConstructors::new();
        for stmt in &body.stmts {
            match stmt {
                IrStmt::VDecl { x, ty, expr } => {
                    self.materialize_packed_reads(block, expr, &mut locals, &mut pending)?;
                    if let IrExpr::Ctor { info, args } = expr
                        && (info.usize != 0 || info.ssize != 0)
                    {
                        self.begin_packed_constructor(
                            block,
                            *x,
                            info,
                            args,
                            &locals,
                            &mut pending,
                        )?;
                    } else {
                        let value = self.expression(block, ty, expr, &locals)?;
                        locals.insert(*x, value);
                    }
                }
                IrStmt::JDecl { j, params, value } => {
                    // Lifted joins capture their lexical scope. Complete any
                    // pending value before it becomes part of that capture.
                    self.materialize_all_packed(block, &mut locals, &mut pending)?;
                    self.join(*j, params, value, &locals, &mut joins)?;
                }
                IrStmt::USet { x, i, y } => {
                    let offset = self.packed_offset(*i, 0)?;
                    self.initialize_packed_scalar(
                        block,
                        *x,
                        flbc::PackedScalar {
                            offset,
                            kind: flbc::ScalarKind::USize,
                            value: *y,
                        },
                        None,
                        &locals,
                        &mut pending,
                    )?;
                }
                IrStmt::SSet {
                    x,
                    i,
                    offset,
                    y,
                    ty,
                } => {
                    let kind = packed_scalar_kind(ty)
                        .filter(|kind| *kind != flbc::ScalarKind::USize)
                        .ok_or_else(|| unsupported(self.name, "packed scalar initializer type"))?;
                    let offset = self.packed_offset(*i, *offset)?;
                    self.initialize_packed_scalar(
                        block,
                        *x,
                        flbc::PackedScalar {
                            offset,
                            kind,
                            value: *y,
                        },
                        floating_scalar(ty),
                        &locals,
                        &mut pending,
                    )?;
                }
                // The immutable subset is lowered to managed values. The
                // independent ownership pass reconstructs actual final uses.
                IrStmt::Inc { .. } | IrStmt::Dec { .. } | IrStmt::Del { .. } => {}
                _ => return Err(unsupported(self.name, "mutable IR statement")),
            }
        }
        self.materialize_all_packed(block, &mut locals, &mut pending)?;
        match body.terminal.as_ref() {
            IrTerminal::Ret(arg) => {
                let value = self.argument(block, arg, &locals)?;
                self.finish_block(block, Terminator::Return { value });
            }
            IrTerminal::Case {
                x, x_type, alts, ..
            } => self.case(block, *x, x_type, alts, locals, joins)?,
            IrTerminal::Unreachable => self.unreachable(block)?,
            IrTerminal::Jmp { j, args } => {
                let join = joins
                    .get(j)
                    .ok_or_else(|| unsupported(self.name, "out-of-scope join point"))?;
                if args.len() != join.parameters {
                    return Err(unsupported(self.name, "join-point arity"));
                }
                self.tables
                    .capture_operands(join.captures.len().saturating_add(args.len()))?;
                let mut values = join
                    .captures
                    .iter()
                    .map(|x| self.argument(block, &IrArg::Var(*x), &locals))
                    .collect::<Result<Vec<_>>>()?;
                values.extend(self.arguments(block, args, &locals)?);
                let value = self.emit(
                    block,
                    ValueType::Abi,
                    Operation::Call {
                        function: join.function,
                        args: values,
                    },
                )?;
                // FIR lowers this exact call/return pair to a frame-transferring
                // tail call. A chain of joins does not grow the VM call stack.
                self.finish_block(block, Terminator::Return { value });
            }
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
        joins: Joins,
    ) -> Result<()> {
        let value = locals
            .get(&x)
            .ok_or_else(|| unsupported(self.name, "case variable"))?
            .value;
        let scalar = is_scalar_case(ty);
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
            arms.sort_by_key(|(info, _)| fieldless_constructor(info));
            if default.is_some() && arms.iter().any(|(info, _)| fieldless_constructor(info)) {
                return Err(unsupported(
                    self.name,
                    "mixed scalar/object case with a default",
                ));
            }
        }
        self.case_arm(block, x, value, &arms, default, (locals, joins, ty))
    }

    fn case_arm(
        &mut self,
        block: BlockId,
        x: u64,
        value: ValueId,
        arms: &[(&IrCtorInfo, &IrBody)],
        default: Option<&IrBody>,
        scope: (Locals, Joins, &IrType),
    ) -> Result<()> {
        let (locals, joins, ty) = scope;
        let scalar = is_scalar_case(ty);
        let Some(((info, body), rest)) = arms.split_first() else {
            if let Some(body) = default {
                let target = self.body(body, locals, joins)?;
                self.finish_block(block, Terminator::Jump { target });
            } else {
                self.unreachable(block)?;
            }
            return Ok(());
        };
        let fieldless = fieldless_constructor(info);
        let heap_tag = info.cidx <= u64::from(fln_rt::abi::TAG_MAX_CTOR_TAG);
        let constructor = if fieldless && (scalar || !heap_tag) {
            None
        } else {
            Some(self.constructor(info)?)
        };
        let condition = match constructor {
            Some(constructor) => {
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
            }
            None => {
                let (tag, equal) = if let Some(wide) = wide_scalar(ty) {
                    let equal = wide.equal;
                    let tag = self.wide_literal(block, wide, &IrNat::Small(info.cidx))?;
                    (tag, equal)
                } else {
                    (self.nat(block, &IrNat::Small(info.cidx))?, "Nat.beq")
                };
                let equal = self.native_call(
                    block,
                    &Name::from_components(equal.split('.')),
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
            }
        };
        self.tables
            .scope_work(locals.len().saturating_add(joins.len()))?;
        let mut matching = locals.clone();
        matching.insert(x, Local { value, constructor });
        let nonzero = self.body(body, matching, joins.clone())?;
        let zero = self.block()?;
        if fieldless && !scalar && constructor.is_some() {
            // Native data bridges can return a fieldless heap constructor,
            // while Reference IR boxes the same nullary tag as a scalar.
            // Both representations enter the same body without evaluating
            // the receiver or its continuation a second time.
            let tag = self.nat(zero, &IrNat::Small(info.cidx))?;
            let equal = self.native_call(
                zero,
                &Name::from_components(["Nat", "beq"]),
                vec![value, tag],
            )?;
            let scalar_condition = self.emit(
                zero,
                ValueType::Bool,
                Operation::Unbox {
                    value: equal,
                    ty: ValueType::Bool,
                },
            )?;
            let scalar_miss = self.block()?;
            self.case_arm(scalar_miss, x, value, rest, default, (locals, joins, ty))?;
            self.finish_block(
                zero,
                Terminator::BranchZero {
                    condition: scalar_condition,
                    zero: scalar_miss,
                    nonzero,
                },
            );
        } else {
            self.case_arm(zero, x, value, rest, default, (locals, joins, ty))?;
        }
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
