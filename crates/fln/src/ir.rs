//! Native compilation of pure, straight-line FIR to the pinned boxed IR.
//!
//! The existing FIR lowering and independently checked ownership pass supply
//! the register program. Every emitted function uses a boxed calling convention;
//! the named entry has no parameters and returns the compiled expression value.
//! This is not the source declaration's unboxed/exported ABI, nor a certificate
//! of kernel admission or faithful byte identity. Module publication must bind
//! the entry and additional names to its own checked declaration/ABI contract.
//! `compile_source_definition` additionally exports closed Nat/String function
//! signatures under their source names, with owned object arguments. Erased,
//! dependent, polymorphic and scalar source conventions remain unsupported.

use fln_comp::{fir, flbc};
use fln_core::name::Name;
use fln_olean::ir::{
    IrArg, IrBody, IrDecl, IrExpr, IrLit, IrModule, IrNat, IrParam, IrStmt, IrTerminal, IrType,
};

#[derive(Debug, Clone, Copy)]
pub struct CompileLimits {
    pub ownership: flbc::OwnershipLimits,
    pub max_work: u64,
}

impl Default for CompileLimits {
    fn default() -> Self {
        Self {
            ownership: flbc::OwnershipLimits::default(),
            max_work: 64_000_000,
        }
    }
}

#[derive(Debug)]
pub enum CompileError {
    Unsupported { what: &'static str },
    Limit,
    Allocation,
    Invariant { what: &'static str },
    Lowering(fir::LoweringError),
    Validation(fln_olean::ir_types::IrTypeValidationError),
}

impl std::fmt::Display for CompileError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Unsupported { what } => write!(f, "IR compilation does not support {what}"),
            Self::Limit => f.write_str("IR compilation work budget exhausted"),
            Self::Allocation => f.write_str("IR compilation allocation refused"),
            Self::Invariant { what } => write!(f, "IR compiler invariant: {what}"),
            Self::Lowering(error) => error.fmt(f),
            Self::Validation(error) => error.fmt(f),
        }
    }
}
impl std::error::Error for CompileError {}

type Result<T> = std::result::Result<T, CompileError>;
fn unsupported(what: &'static str) -> CompileError {
    CompileError::Unsupported { what }
}
fn invariant(what: &'static str) -> CompileError {
    CompileError::Invariant { what }
}

struct Budget(u64);
impl Budget {
    fn charge(&mut self, n: usize) -> Result<()> {
        self.0 = self.0.checked_sub(n as u64).ok_or(CompileError::Limit)?;
        Ok(())
    }
}

fn carrier(ty: fir::ValueType) -> Result<()> {
    match ty {
        fir::ValueType::Unit
        | fir::ValueType::Bool
        | fir::ValueType::Nat
        | fir::ValueType::String
        | fir::ValueType::Closure(_) => Ok(()),
        _ => Err(unsupported("non-pure boxed carrier")),
    }
}

fn operand_policy(ty: fir::ValueType, policy: flbc::ArgumentOwnership) -> Result<()> {
    match policy {
        flbc::ArgumentOwnership::Unique => Err(unsupported("uniqueness preconditions")),
        flbc::ArgumentOwnership::Scalar
            if !matches!(ty, fir::ValueType::Unit | fir::ValueType::Bool) =>
        {
            Err(unsupported("unproved scalar operand"))
        }
        _ => Ok(()),
    }
}

fn signature(
    types: &[fir::ValueType],
    ownership: &[flbc::ArgumentOwnership],
    result: fir::ValueType,
    result_ownership: flbc::CallableResultOwnership,
    meter: &mut Budget,
) -> Result<()> {
    meter.charge(types.len().saturating_add(1))?;
    carrier(result)?;
    let valid_result = match result {
        fir::ValueType::Unit | fir::ValueType::Bool => {
            result_ownership == flbc::CallableResultOwnership::Scalar
        }
        fir::ValueType::Nat => result_ownership == flbc::CallableResultOwnership::OwnedOrScalar,
        fir::ValueType::String | fir::ValueType::Closure(_) => {
            result_ownership == flbc::CallableResultOwnership::Owned
        }
        _ => false,
    };
    if !valid_result {
        return Err(unsupported("result carrier/ownership contract"));
    }
    if types.len() != ownership.len() {
        return Err(invariant("parameter ownership arity"));
    }
    for (ty, ownership) in types.iter().zip(ownership) {
        carrier(*ty)?;
        match ownership {
            flbc::ArgumentOwnership::Unique => return Err(unsupported("uniqueness preconditions")),
            flbc::ArgumentOwnership::Scalar
                if !matches!(ty, fir::ValueType::Unit | fir::ValueType::Bool) =>
            {
                return Err(unsupported("unproved scalar parameter"));
            }
            _ => {}
        }
    }
    Ok(())
}

#[derive(Clone, Copy)]
struct Value {
    index: u64,
    owned: bool,
}

struct Function<'a> {
    names: &'a [Name],
    registers: Vec<Option<Value>>,
    next: u64,
    stmts: Vec<IrStmt>,
    meter: &'a mut Budget,
}

impl Function<'_> {
    fn emit(&mut self, stmt: IrStmt) -> Result<()> {
        self.meter.charge(1)?;
        self.stmts
            .try_reserve(1)
            .map_err(|_| CompileError::Allocation)?;
        self.stmts.push(stmt);
        Ok(())
    }
    fn get(&self, r: flbc::Register) -> Result<Value> {
        self.registers
            .get(usize::from(r.get()))
            .copied()
            .flatten()
            .ok_or_else(|| invariant("empty register"))
    }
    fn take(&mut self, r: flbc::Register) -> Result<Value> {
        self.registers
            .get_mut(usize::from(r.get()))
            .and_then(Option::take)
            .ok_or_else(|| invariant("empty consumed register"))
    }
    fn retain(&mut self, value: Value) -> Result<()> {
        self.emit(IrStmt::Inc {
            x: value.index,
            n: 1,
            checked: true,
            persistent: false,
        })
    }
    fn drop_value(&mut self, value: Value) -> Result<()> {
        if value.owned {
            self.emit(IrStmt::Dec {
                x: value.index,
                n: 1,
                checked: true,
                persistent: false,
            })?;
        }
        Ok(())
    }
    fn set(&mut self, r: flbc::Register, value: Value) -> Result<()> {
        let slot = self
            .registers
            .get_mut(usize::from(r.get()))
            .ok_or_else(|| invariant("destination register"))?;
        let old = slot.replace(value);
        if let Some(old) = old {
            self.drop_value(old)?;
        }
        Ok(())
    }
    fn bind(&mut self, ty: IrType, expr: IrExpr) -> Result<Value> {
        let index = self.next;
        self.next = self.next.checked_add(1).ok_or(CompileError::Limit)?;
        self.emit(IrStmt::VDecl { x: index, ty, expr })?;
        Ok(Value { index, owned: true })
    }
    fn name(&self, id: flbc::FunctionId) -> Result<Name> {
        self.names
            .get(id.get() as usize)
            .cloned()
            .ok_or_else(|| invariant("callee name"))
    }
    fn args(
        &mut self,
        args: &[flbc::Register],
        ownership: &[flbc::ArgumentOwnership],
        boxed: bool,
    ) -> Result<Vec<IrArg>> {
        if args.len() != ownership.len() {
            return Err(invariant("call argument arity"));
        }
        self.meter.charge(args.len())?;
        let mut out = Vec::new();
        out.try_reserve_exact(args.len())
            .map_err(|_| CompileError::Allocation)?;
        // Borrowed arguments can alias an owned operand transferred later in
        // the same call. Read all variables before invalidating any register.
        for (r, policy) in args.iter().zip(ownership) {
            let value = self.get(*r)?;
            if boxed && !policy.consumes() {
                self.retain(value)?;
            }
            out.push(IrArg::Var(value.index));
        }
        for (r, policy) in args.iter().zip(ownership) {
            if policy.consumes() {
                self.take(*r)?;
            }
        }
        Ok(out)
    }
    fn call(
        &mut self,
        function: Name,
        args: &[flbc::Register],
        ownership: &[flbc::ArgumentOwnership],
    ) -> Result<Value> {
        // Golem keeps each borrowed operand alive for the whole call. The
        // same register may also supply a consuming operand, whose callee
        // can drop it before reading the borrow. Preserve that lifetime even
        // when this caller no longer owns a separate reference afterwards.
        self.meter.charge(args.len())?;
        let mut borrowed = Vec::new();
        borrowed
            .try_reserve_exact(args.len())
            .map_err(|_| CompileError::Allocation)?;
        for (r, policy) in args.iter().zip(ownership) {
            if !policy.consumes() {
                let value = self.get(*r)?;
                self.retain(value)?;
                borrowed.push(Value {
                    owned: true,
                    ..value
                });
            }
        }
        let args = self.args(args, ownership, false)?;
        let constant = args.is_empty();
        let result = self.bind(IrType::TObject, IrExpr::Fap { function, args })?;
        // A nullary FAP loads a borrowed value from the interpreter's
        // constant cache. FLBC calls return an owned value instead.
        if constant {
            self.retain(result)?;
        }
        for value in borrowed {
            self.drop_value(value)?;
        }
        Ok(result)
    }
    fn finish(mut self, value: Value) -> Result<IrBody> {
        if !value.owned {
            self.retain(value)?;
        }
        for i in 0..self.registers.len() {
            self.meter.charge(1)?;
            if let Some(other) = self.registers[i].take() {
                self.drop_value(other)?;
            }
        }
        Ok(IrBody {
            stmts: self.stmts,
            terminal: Box::new(IrTerminal::Ret(IrArg::Var(value.index))),
        })
    }
}

fn compile_function(
    function: &flbc::Function,
    names: &[Name],
    meter: &mut Budget,
) -> Result<IrDecl> {
    meter.charge(usize::from(function.register_count))?;
    let mut registers = Vec::new();
    registers
        .try_reserve_exact(usize::from(function.register_count))
        .map_err(|_| CompileError::Allocation)?;
    registers.resize(usize::from(function.register_count), None);
    let mut params = Vec::new();
    for (i, policy) in function.parameter_ownership.iter().enumerate() {
        let borrow = !policy.consumes();
        registers[i] = Some(Value {
            index: i as u64 + 1,
            owned: !borrow,
        });
        params.push(IrParam {
            x: i as u64 + 1,
            borrow,
            ty: IrType::TObject,
        });
    }
    let name = names
        .get(function.id.get() as usize)
        .cloned()
        .ok_or_else(|| invariant("function name"))?;
    let mut out = Function {
        names,
        registers,
        next: u64::from(function.arity) + 1,
        stmts: Vec::new(),
        meter,
    };
    for instruction in &function.code {
        out.meter.charge(1)?;
        use flbc::Instruction as I;
        match instruction {
            I::Nat { dst, value } => {
                let v = out.bind(
                    IrType::TObject,
                    IrExpr::Lit(IrLit::Num(IrNat::Small(*value))),
                )?;
                out.set(*dst, v)?;
            }
            I::NatBig { dst, limbs_le } => {
                out.meter.charge(limbs_le.len())?;
                let v = out.bind(
                    IrType::TObject,
                    IrExpr::Lit(IrLit::Num(IrNat::Big(limbs_le.clone()))),
                )?;
                out.set(*dst, v)?;
            }
            I::String { dst, value } => {
                out.meter.charge(value.len())?;
                let v = out.bind(IrType::Object, IrExpr::Lit(IrLit::Str(value.clone())))?;
                out.set(*dst, v)?;
            }
            I::Copy { dst, src } => {
                let v = out.get(*src)?;
                out.retain(v)?;
                out.set(*dst, Value { owned: true, ..v })?;
            }
            I::Move { dst, src } => {
                let v = out.take(*src)?;
                if !v.owned {
                    out.retain(v)?;
                }
                out.set(*dst, Value { owned: true, ..v })?;
            }
            I::Drop { src } => {
                let v = out.take(*src)?;
                out.drop_value(v)?;
            }
            I::Call {
                dst,
                function,
                args,
                argument_ownership,
                ..
            } => {
                let function = out.name(*function)?;
                let v = out.call(function, args, argument_ownership)?;
                out.set(*dst, v)?;
            }
            I::Closure {
                dst,
                function,
                captures,
                capture_ownership,
            } => {
                // Applying a closure consumes all arguments, including its
                // captures. The boxed entry releases the base's borrows.
                let function = Name::str(out.name(*function)?, "_boxed");
                let args = out.args(captures, capture_ownership, true)?;
                let v = out.bind(IrType::Object, IrExpr::Pap { function, args })?;
                out.set(*dst, v)?;
            }
            I::Apply {
                dst,
                closure,
                args,
                argument_ownership,
                ..
            } => {
                let closure = out.get(*closure)?;
                out.retain(closure)?;
                let args = out.args(args, argument_ownership, true)?;
                let v = out.bind(
                    IrType::TObject,
                    IrExpr::Ap {
                        x: closure.index,
                        args,
                    },
                )?;
                out.set(*dst, v)?;
            }
            I::TailCall {
                function,
                args,
                argument_ownership,
                ..
            } => {
                let function = out.name(*function)?;
                let v = out.call(function, args, argument_ownership)?;
                return Ok(IrDecl::Function {
                    name,
                    params,
                    result: IrType::TObject,
                    body: out.finish(v)?,
                    sorry_dep: None,
                });
            }
            I::TailApply {
                closure,
                args,
                argument_ownership,
                ..
            } => {
                let closure = out.get(*closure)?;
                out.retain(closure)?;
                let args = out.args(args, argument_ownership, true)?;
                let v = out.bind(
                    IrType::TObject,
                    IrExpr::Ap {
                        x: closure.index,
                        args,
                    },
                )?;
                return Ok(IrDecl::Function {
                    name,
                    params,
                    result: IrType::TObject,
                    body: out.finish(v)?,
                    sorry_dep: None,
                });
            }
            I::Return { src } => {
                let v = out.take(*src)?;
                return Ok(IrDecl::Function {
                    name,
                    params,
                    result: IrType::TObject,
                    body: out.finish(v)?,
                    sorry_dep: None,
                });
            }
            _ => {
                return Err(unsupported(
                    "instruction outside the pure straight-line subset",
                ));
            }
        }
    }
    Err(invariant("function has no return"))
}

fn boxed_wrapper(declaration: &IrDecl, meter: &mut Budget) -> Result<IrDecl> {
    let IrDecl::Function { name, params, .. } = declaration else {
        return Err(invariant("native function"));
    };
    meter.charge(params.len().saturating_mul(3).saturating_add(1))?;
    let mut stmts = vec![IrStmt::VDecl {
        x: params.len() as u64 + 1,
        ty: IrType::TObject,
        expr: IrExpr::Fap {
            function: name.clone(),
            args: params.iter().map(|p| IrArg::Var(p.x)).collect(),
        },
    }];
    for p in params {
        if p.borrow {
            stmts.push(IrStmt::Dec {
                x: p.x,
                n: 1,
                checked: true,
                persistent: false,
            });
        }
    }
    Ok(IrDecl::Function {
        name: Name::str(name.clone(), "_boxed"),
        params: params
            .iter()
            .map(|p| IrParam {
                borrow: false,
                ..p.clone()
            })
            .collect(),
        result: IrType::TObject,
        body: IrBody {
            stmts,
            terminal: Box::new(IrTerminal::Ret(IrArg::Var(params.len() as u64 + 1))),
        },
        sorry_dep: None,
    })
}

/// Compile a validated pure FIR program into boxed pinned IR. `entry` names
/// its nullary value entry; all other symbols are deterministic children of it.
/// Callers must include every returned name in their IR extra-name table.
/// Nothing executes here. Refusal returns no partial module. Tail transfers
/// retain ordinary call continuations in this first backend: exact fuel,
/// stack-use parity and source export ABI are not established by this API.
pub fn compile(
    program: &fir::ValidatedProgram,
    entry: &Name,
    limits: CompileLimits,
) -> Result<IrModule> {
    let mut meter = Budget(limits.max_work);
    let module = compile_module(program, entry, limits, &mut meter)?;
    validate_module(&module, &meter)?;
    Ok(module)
}

fn compile_module(
    program: &fir::ValidatedProgram,
    entry: &Name,
    limits: CompileLimits,
    meter: &mut Budget,
) -> Result<IrModule> {
    if entry.is_anonymous() {
        return Err(unsupported("anonymous entry name"));
    }
    for function in program.functions() {
        signature(
            &function.parameters,
            &function.parameter_ownership,
            function.result,
            function.result_ownership,
            meter,
        )?;
        if function.blocks.len() != 1
            || !matches!(
                function.blocks[0].terminator,
                fir::Terminator::Return { .. }
            )
        {
            return Err(unsupported("control-flow graph"));
        }
        for binding in &function.blocks[0].bindings {
            meter.charge(1)?;
            carrier(binding.ty)?;
        }
        let mut types: std::collections::BTreeMap<_, _> = function
            .parameters
            .iter()
            .enumerate()
            .map(|(i, ty)| (fir::ValueId::new(i as u32), *ty))
            .collect();
        for binding in &function.blocks[0].bindings {
            let operands = match &binding.operation {
                fir::Operation::Closure {
                    captures,
                    capture_ownership,
                    ..
                } => Some((captures, capture_ownership)),
                fir::Operation::Apply {
                    args,
                    argument_ownership,
                    ..
                } => Some((args, argument_ownership)),
                _ => None,
            };
            if let Some((args, policies)) = operands {
                meter.charge(args.len())?;
                for (arg, policy) in args.iter().zip(policies) {
                    operand_policy(
                        *types
                            .get(arg)
                            .ok_or_else(|| invariant("FIR operand type"))?,
                        *policy,
                    )?;
                }
            }
            types.insert(binding.id, binding.ty);
        }
    }
    for closure in program.closure_types() {
        signature(
            &closure.parameters,
            &closure.parameter_ownership,
            closure.result,
            closure.result_ownership,
            meter,
        )?;
    }
    let lowered = fir::lower_to_flbc_with_ownership(program, limits.ownership)
        .map_err(CompileError::Lowering)?;
    let mut names = Vec::new();
    for function in lowered.program().functions() {
        meter.charge(1)?;
        names.push(if function.id.get() == program.entry().get() {
            entry.clone()
        } else {
            Name::num(
                Name::str(entry.clone(), "_fln_fn"),
                u64::from(function.id.get()),
            )
        });
    }
    let mut declarations = Vec::new();
    for function in lowered.program().functions() {
        let declaration = compile_function(function, &names, meter)?;
        // A boxed application always owns its operands. The wrapper releases
        // those whose base function borrows them, just as the pin's wrappers do.
        if !function.parameter_ownership.is_empty() {
            declarations.push(boxed_wrapper(&declaration, meter)?);
        }
        declarations.push(declaration);
    }
    declarations.sort_by(|a, b| a.name().quick_cmp(b.name()));
    Ok(IrModule {
        decls: declarations,
        ..IrModule::default()
    })
}

fn validate_module(module: &IrModule, meter: &Budget) -> Result<()> {
    fln_olean::ir_types::validate_ir_types(
        std::slice::from_ref(module),
        &std::collections::BTreeMap::new(),
        fln_olean::ir_validate::IrValidationLimits {
            max_declarations: module.decls.len(),
            max_work: meter.0,
            ..fln_olean::ir_validate::IrValidationLimits::default()
        },
    )
    .map_err(CompileError::Validation)?;
    Ok(())
}

struct SourceSignature {
    name: Name,
    params: Vec<IrParam>,
    result: IrType,
}

// Walk source types before erasure. In particular, a proof/type argument must
// not disappear and silently change the exported source calling convention.
fn source_carrier(ty: &fln_core::expr::Expr, meter: &mut Budget) -> Result<IrType> {
    use fln_core::expr::ExprNode;
    let nat = Name::from_components(["Nat"]);
    let string = Name::from_components(["String"]);
    let mut pending = vec![ty];
    let mut result = None;
    while let Some(ty) = pending.pop() {
        meter.charge(1)?;
        let carrier = match ty.node() {
            ExprNode::Const { name, levels } if levels.is_empty() && name == &nat => {
                IrType::TObject
            }
            ExprNode::Const { name, levels } if levels.is_empty() && name == &string => {
                IrType::Object
            }
            ExprNode::ForallE {
                binder_type, body, ..
            } => {
                pending
                    .try_reserve(2)
                    .map_err(|_| CompileError::Allocation)?;
                pending.push(body);
                pending.push(binder_type);
                IrType::Object
            }
            ExprNode::MData { expr, .. } => {
                pending.push(expr);
                continue;
            }
            _ => return Err(unsupported("source export carrier")),
        };
        result.get_or_insert(carrier);
    }
    result.ok_or_else(|| invariant("source carrier"))
}

fn source_signature(
    definition: &fln_env::constants::DefinitionVal,
    meter: &mut Budget,
) -> Result<SourceSignature> {
    use fln_core::expr::ExprNode;
    if !definition.base.level_params.is_empty() {
        return Err(unsupported("universe-polymorphic source export"));
    }
    let mut params = Vec::new();
    let mut ty = &definition.base.type_;
    let result = loop {
        meter.charge(1)?;
        match ty.node() {
            ExprNode::ForallE {
                binder_type, body, ..
            } => {
                let carrier = source_carrier(binder_type, meter)?;
                params
                    .try_reserve(1)
                    .map_err(|_| CompileError::Allocation)?;
                params.push(IrParam {
                    x: params.len() as u64 + 1,
                    borrow: false,
                    ty: carrier,
                });
                ty = body;
            }
            ExprNode::MData { expr, .. } => ty = expr,
            _ => break source_carrier(ty, meter)?,
        }
    };
    Ok(SourceSignature {
        name: definition.base.name.clone(),
        params,
        result,
    })
}

fn export_source(
    signature: SourceSignature,
    value_entry: &Name,
    meter: &mut Budget,
) -> Result<IrDecl> {
    meter.charge(signature.params.len().saturating_mul(2).saturating_add(8))?;
    let closure = signature.params.len() as u64 + 1;
    let result = closure.checked_add(1).ok_or(CompileError::Limit)?;
    let mut stmts = vec![
        IrStmt::VDecl {
            x: closure,
            ty: IrType::TObject,
            expr: IrExpr::Fap {
                function: value_entry.clone(),
                args: vec![],
            },
        },
        // The value producer is nullary: its constant-cache result is borrowed.
        IrStmt::Inc {
            x: closure,
            n: 1,
            checked: true,
            persistent: false,
        },
    ];
    let returned = if signature.params.is_empty() {
        closure
    } else {
        stmts.push(IrStmt::VDecl {
            x: result,
            ty: signature.result.clone(),
            expr: IrExpr::Ap {
                x: closure,
                args: signature.params.iter().map(|p| IrArg::Var(p.x)).collect(),
            },
        });
        result
    };
    Ok(IrDecl::Function {
        name: signature.name,
        params: signature.params,
        result: signature.result,
        body: IrBody {
            stmts,
            terminal: Box::new(IrTerminal::Ret(IrArg::Var(returned))),
        },
        sorry_dep: None,
    })
}

/// A compiled, council-admitted definition. The base engine is unchanged;
/// callers receive its checked successor only when the whole compilation works.
#[derive(Debug)]
pub struct DefinitionCompilation {
    pub admission: crate::SourceDeclarationAdmission,
    pub runtime_type: fln_core::expr::Expr,
    pub entry: Name,
    pub module: IrModule,
}

#[derive(Debug)]
pub enum DefinitionCompileError {
    Engine(crate::EngineExecutionError),
    Ir(CompileError),
}
impl std::fmt::Display for DefinitionCompileError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Engine(error) => error.fmt(f),
            Self::Ir(error) => error.fmt(f),
        }
    }
}
impl std::error::Error for DefinitionCompileError {}

/// Admit and compile without executing the definition. This shares the exact
/// admission, erasure, catalog and FIR preparation path used by Golem execution.
/// The explicit entry names a nullary boxed value producer, including when that
/// value is itself a function. It does not replace a source declaration's ABI.
pub fn compile_definition(
    engine: &crate::Engine,
    declaration: crate::Declaration,
    entry: &Name,
    options: &fln_core::options::KVMap,
    engine_limits: crate::EngineExecutionLimits,
    limits: CompileLimits,
) -> std::result::Result<fln_core::outcome::Outcome<DefinitionCompilation>, DefinitionCompileError>
{
    compile_definition_impl(
        engine,
        declaration,
        Some(entry),
        options,
        engine_limits,
        limits,
    )
}

/// Export a checked definition under its source name and source argument count.
/// Supported types are closed arrows over Nat/String (including higher-order
/// arguments), using owned object parameters. No erased argument is dropped.
/// The source signature is projected from the same declaration submitted
/// unchanged to both checkers; success requires their admission and complete
/// IR validation. This does not establish faithful bytes or general source ABI.
pub fn compile_source_definition(
    engine: &crate::Engine,
    declaration: crate::Declaration,
    options: &fln_core::options::KVMap,
    engine_limits: crate::EngineExecutionLimits,
    limits: CompileLimits,
) -> std::result::Result<fln_core::outcome::Outcome<DefinitionCompilation>, DefinitionCompileError>
{
    compile_definition_impl(engine, declaration, None, options, engine_limits, limits)
}

fn compile_definition_impl(
    engine: &crate::Engine,
    declaration: crate::Declaration,
    entry: Option<&Name>,
    options: &fln_core::options::KVMap,
    engine_limits: crate::EngineExecutionLimits,
    limits: CompileLimits,
) -> std::result::Result<fln_core::outcome::Outcome<DefinitionCompilation>, DefinitionCompileError>
{
    let mut meter = Budget(limits.max_work);
    let signature = match (&declaration, entry) {
        (crate::Declaration::Defn(definition), None) => {
            Some(source_signature(definition, &mut meter).map_err(DefinitionCompileError::Ir)?)
        }
        _ => None,
    };
    let prepared = engine
        .prepare_definition_entry_with_helpers(
            declaration,
            &[],
            options,
            engine_limits,
            crate::source_evaluation::Entry::Value,
        )
        .map_err(DefinitionCompileError::Engine)?;
    use fln_core::outcome::Outcome;
    match prepared {
        Outcome::Inconclusive(reason) => Ok(Outcome::Inconclusive(reason)),
        Outcome::InternalFault(fault) => Ok(Outcome::InternalFault(fault)),
        Outcome::Complete(prepared) => {
            let exported = signature.as_ref().map(|s| s.name.clone());
            let entry = entry.cloned().or(exported).ok_or_else(|| {
                DefinitionCompileError::Ir(invariant("admitted source definition"))
            })?;
            let value_entry = if signature.is_some() {
                Name::str(entry.clone(), "_fln_value")
            } else {
                entry.clone()
            };
            let mut module = compile_module(&prepared.fir, &value_entry, limits, &mut meter)
                .map_err(DefinitionCompileError::Ir)?;
            if let Some(signature) = signature {
                module.decls.push(
                    export_source(signature, &value_entry, &mut meter)
                        .map_err(DefinitionCompileError::Ir)?,
                );
                module.decls.sort_by(|a, b| a.name().quick_cmp(b.name()));
            }
            validate_module(&module, &meter).map_err(DefinitionCompileError::Ir)?;
            Ok(Outcome::Complete(DefinitionCompilation {
                admission: prepared.admission,
                runtime_type: prepared.runtime_type,
                entry,
                module,
            }))
        }
    }
}
