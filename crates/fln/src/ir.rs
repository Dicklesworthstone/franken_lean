//! Native compilation of pure FIR to the pinned boxed IR.
//!
//! The existing FIR lowering and independently checked ownership pass supply
//! the register program. Internal value functions use a boxed calling convention;
//! the named entry has no parameters and returns the compiled expression value.
//! This is not the source declaration's unboxed/exported ABI, nor a certificate
//! of kernel admission or faithful byte identity. Module publication must bind
//! the entry and additional names to its own checked declaration/ABI contract.
//! `compile_source_definition` additionally exports closed Nat/String/Bool
//! function signatures under their source names, with owned object arguments
//! and the pin's UInt8 Boolean convention. Type-dependent runtime carriers and
//! other scalar conventions remain unsupported. Acyclic control flow preserves
//! reachable branches and their ownership cleanup; expansion is work/depth bounded.
//! Type/proof slots retain their original source positions.
//! Closed source exports may use private boxed data and dictionaries internally.
//! Their object layouts receive private tags, preserving both tag and field-count
//! tests even when unrelated records share a source tag. These objects cannot
//! cross the source ABI; arbitrary FIR cannot enable this profile or claim the
//! pin's source data representation. Packed/scalar payloads remain unsupported.

use fln_comp::{fir, flbc};
use fln_core::name::Name;
use fln_olean::ir::{
    IrAlt, IrArg, IrBody, IrCtorInfo, IrDecl, IrExpr, IrLit, IrModule, IrNat, IrParam, IrStmt,
    IrTerminal, IrType,
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

fn carrier(ty: fir::ValueType, internal_constructors: bool) -> Result<()> {
    match ty {
        fir::ValueType::Unit
        | fir::ValueType::Bool
        | fir::ValueType::Nat
        | fir::ValueType::String
        | fir::ValueType::Closure(_) => Ok(()),
        fir::ValueType::Constructor if internal_constructors => Ok(()),
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
    internal_constructors: bool,
    meter: &mut Budget,
) -> Result<()> {
    meter.charge(types.len().saturating_add(1))?;
    carrier(result, internal_constructors)?;
    let valid_result = match result {
        fir::ValueType::Unit | fir::ValueType::Bool => {
            result_ownership == flbc::CallableResultOwnership::Scalar
        }
        fir::ValueType::Nat => result_ownership == flbc::CallableResultOwnership::OwnedOrScalar,
        fir::ValueType::String | fir::ValueType::Closure(_) | fir::ValueType::Constructor => {
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
        carrier(*ty, internal_constructors)?;
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

/// These operations already have pinned, generated native contracts. Keeping
/// the value types explicit prevents caller-authored FIR from applying a Nat
/// extern to a String merely by choosing a familiar row name.
fn native_signature(row: &str) -> Result<(&'static [fir::ValueType], fir::ValueType)> {
    use fir::ValueType::{Bool, Nat, String as Text};
    match row {
        "extern:Nat.add"
        | "extern:Nat.sub"
        | "extern:Nat.mul"
        | "extern:Nat.div"
        | "extern:Nat.mod"
        | "extern:Nat.gcd"
        | "extern:Nat.pow"
        | "extern:Nat.land"
        | "extern:Nat.lor"
        | "extern:Nat.xor"
        | "extern:Nat.shiftLeft"
        | "extern:Nat.shiftRight" => Ok((&[Nat, Nat], Nat)),
        "extern:Nat.pred" | "extern:Nat.log2" => Ok((&[Nat], Nat)),
        // Preparation has already checked the decision models and adapts
        // their scalar ABI tags to its private Decidable representation. At
        // the pin all three raw decision entries return UInt8, just like beq
        // and ble; no proof field crosses this native call or the source ABI.
        "extern:Nat.beq" | "extern:Nat.ble" | "extern:Nat.decEq" | "extern:Nat.decLe"
        | "extern:Nat.decLt" => Ok((&[Nat, Nat], Bool)),
        // Most native ABIs share the checked FIR ownership. The two consuming
        // Bootstrap predicates below use an explicit borrowed-to-owned bridge.
        "extern:String.append" | "extern:String.Internal.append" => Ok((&[Text, Text], Text)),
        "extern:String.length" | "extern:String.Internal.length" | "extern:String.utf8ByteSize" => {
            Ok((&[Text], Nat))
        }
        "extern:String.decEq" | "extern:String.Internal.isPrefixOf" => Ok((&[Text, Text], Bool)),
        "extern:String.Internal.isEmpty" => Ok((&[Text], Bool)),
        _ => Err(unsupported("native intrinsic signature")),
    }
}

// Bootstrap.lean's raw declarations own their String arguments, unlike the
// generated Golem rows. This exception is deliberately exact: other native
// signatures continue to use their validated ownership contracts unchanged.
fn native_consumes_borrowed_strings(row: &str) -> bool {
    matches!(
        row,
        "extern:String.Internal.isEmpty" | "extern:String.Internal.isPrefixOf"
    )
}

fn native_name(row: &str) -> Result<Name> {
    native_signature(row)?;
    let generated = fln_vm::extern_table_generated::EXTERN_ROWS
        .iter()
        .find(|candidate| candidate.id == row)
        .ok_or_else(|| invariant("pinned native row"))?;
    Ok(Name::from_components(generated.name.split('.')))
}

fn validate_native(intrinsic: &fir::IntrinsicDecl, meter: &mut Budget) -> Result<()> {
    meter.charge(intrinsic.arguments.len().saturating_add(1))?;
    let (arguments, result) = native_signature(&intrinsic.row)?;
    if intrinsic.arguments != arguments
        || intrinsic.result != result
        || intrinsic.effect != fir::EffectClass::Pure
    {
        return Err(unsupported("native intrinsic type or effect contract"));
    }
    let row = fln_vm::extern_table_generated::EXTERN_ROWS
        .iter()
        .find(|row| row.id == intrinsic.row)
        .ok_or_else(|| invariant("pinned native row"))?;
    if row.effect != "pure" || row.entry_class != "standard" || row.entry_scope != "all" {
        return Err(unsupported("pinned native entry contract"));
    }
    let contract = fln_vm::extern_row::Ownership::parse(row.ownership)
        .map_err(|_| invariant("pinned native ownership"))?;
    let arguments = contract
        .argument_ownership(arguments.len())
        .map_err(|_| invariant("pinned native argument ownership"))?;
    let result = contract
        .result_ownership()
        .map_err(|_| invariant("pinned native result ownership"))?;
    if arguments.len() != intrinsic.argument_ownership.len()
        || arguments
            .iter()
            .zip(&intrinsic.argument_ownership)
            .any(|(expected, actual)| expected.as_str() != actual.token())
        || result.as_str() != intrinsic.result_ownership.token()
    {
        return Err(unsupported("native intrinsic ownership contract"));
    }
    Ok(())
}

/// A fixed-size set covers the pin's complete byte-sized constructor tag space.
/// Empty means that a register has not yet acquired a more precise shape fact.
#[derive(Clone, Copy, Default, PartialEq, Eq)]
struct ConstructorTags([u64; 4]);

impl ConstructorTags {
    fn singleton(tag: u8) -> Self {
        let mut result = Self::default();
        result.0[usize::from(tag) / 64] = 1 << (tag % 64);
        result
    }
    fn insert(&mut self, tag: u8) {
        self.0[usize::from(tag) / 64] |= 1 << (tag % 64);
    }
    fn contains(self, tag: u8) -> bool {
        self.0[usize::from(tag) / 64] & (1 << (tag % 64)) != 0
    }
    fn without(mut self, tag: u8) -> Self {
        self.0[usize::from(tag) / 64] &= !(1 << (tag % 64));
        self
    }
    fn is_empty(self) -> bool {
        self == Self::default()
    }
}

/// Native source data has an all-boxed representation, independent of the pin's
/// source compiler. Only a closed source ABI lets us keep that representation
/// private. Assigning tags by the *whole* layout preserves the VM's shape tests:
/// two constructors with tag zero but different field counts must stay distinct.
struct InternalConstructors {
    type_name: Name,
    layouts: std::collections::BTreeMap<(u8, u16), u8>,
    tags: ConstructorTags,
}

impl InternalConstructors {
    fn tag(&self, tag: u8, fields: u16) -> Result<u8> {
        self.layouts
            .get(&(tag, fields))
            .copied()
            .ok_or_else(|| unsupported("unproved internal constructor layout"))
    }
    fn info(&self, tag: u8, fields: u16) -> IrCtorInfo {
        IrCtorInfo {
            name: Name::num(self.type_name.clone(), u64::from(tag)),
            cidx: u64::from(tag),
            size: u64::from(fields),
            usize: 0,
            ssize: 0,
        }
    }
}

#[derive(Clone, Copy)]
struct Value {
    index: u64,
    owned: bool,
    natural: Option<u64>,
    constructor_tags: ConstructorTags,
}

struct Function<'a> {
    names: &'a [Name],
    registers: Vec<Option<Value>>,
    next: u64,
    stmts: Vec<IrStmt>,
    constructors: &'a InternalConstructors,
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
        let natural = match &expr {
            IrExpr::Lit(IrLit::Num(IrNat::Small(value))) => Some(*value),
            _ => None,
        };
        self.emit(IrStmt::VDecl { x: index, ty, expr })?;
        Ok(Value {
            index,
            owned: true,
            natural,
            constructor_tags: ConstructorTags::default(),
        })
    }
    fn name(&self, id: flbc::FunctionId) -> Result<Name> {
        self.names
            .get(id.get() as usize)
            .cloned()
            .ok_or_else(|| invariant("callee name"))
    }
    fn snapshot(&mut self) -> Result<Vec<Option<Value>>> {
        self.meter.charge(self.registers.len())?;
        let mut saved = Vec::new();
        saved
            .try_reserve_exact(self.registers.len())
            .map_err(|_| CompileError::Allocation)?;
        saved.extend_from_slice(&self.registers);
        Ok(saved)
    }
    fn refine_constructor(&mut self, index: u64, tags: ConstructorTags) -> Result<()> {
        self.meter.charge(self.registers.len())?;
        for value in self.registers.iter_mut().flatten() {
            if value.index == index {
                value.constructor_tags = tags;
            }
        }
        Ok(())
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
        self.call_typed(function, args, ownership, IrType::TObject)
    }
    fn call_typed(
        &mut self,
        function: Name,
        args: &[flbc::Register],
        ownership: &[flbc::ArgumentOwnership],
        result: IrType,
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
        let result = self.bind(result, IrExpr::Fap { function, args })?;
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
    fn finish(&mut self, value: Value) -> Result<IrBody> {
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
            stmts: std::mem::take(&mut self.stmts),
            terminal: Box::new(IrTerminal::Ret(IrArg::Var(value.index))),
        })
    }
}

fn compile_function(
    function: &flbc::Function,
    names: &[Name],
    constructors: &InternalConstructors,
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
            natural: None,
            constructor_tags: ConstructorTags::default(),
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
        constructors,
        meter,
    };
    let mut active = Vec::new();
    out.meter.charge(function.code.len())?;
    active
        .try_reserve_exact(function.code.len())
        .map_err(|_| CompileError::Allocation)?;
    active.resize(function.code.len(), false);
    let body = compile_body(function, &mut out, 0, &mut active, 0)?;
    Ok(IrDecl::Function {
        name,
        params,
        result: IrType::TObject,
        body,
        sorry_dep: None,
    })
}

/// FLBC has already passed its independent ownership check. Branch expansion
/// copies only the compile-time register map; each runtime path retains its
/// original moves and drops. Global variable numbering is shared by all arms,
/// matching the pin's declaration-wide uniqueness rule.
fn compile_body(
    function: &flbc::Function,
    out: &mut Function<'_>,
    start: usize,
    active: &mut [bool],
    depth: usize,
) -> Result<IrBody> {
    if depth >= 128 {
        return Err(CompileError::Limit);
    }
    let mut path = Vec::new();
    let result = (|| {
        let mut pc = start;
        loop {
            let visiting = active
                .get_mut(pc)
                .ok_or_else(|| invariant("control-flow target"))?;
            if *visiting {
                return Err(unsupported("cyclic control-flow graph"));
            }
            *visiting = true;
            path.try_reserve(1).map_err(|_| CompileError::Allocation)?;
            path.push(pc);
            let instruction = function
                .code
                .get(pc)
                .ok_or_else(|| invariant("control-flow instruction"))?;
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
                I::Ctor {
                    dst,
                    tag,
                    fields,
                    scalar_bytes,
                } => {
                    if !scalar_bytes.is_empty() {
                        return Err(unsupported("internal constructor scalar payload"));
                    }
                    let field_count =
                        u16::try_from(fields.len()).map_err(|_| CompileError::Limit)?;
                    let tag = out.constructors.tag(*tag, field_count)?;
                    // FIR constructors borrow fields; IR constructors consume
                    // them. Keep an independent owner for every stored slot,
                    // including repeated aliases and captured closures.
                    out.meter.charge(fields.len())?;
                    let mut args = Vec::new();
                    args.try_reserve_exact(fields.len())
                        .map_err(|_| CompileError::Allocation)?;
                    for field in fields {
                        let value = out.get(*field)?;
                        out.retain(value)?;
                        args.push(IrArg::Var(value.index));
                    }
                    let mut value = out.bind(
                        if fields.is_empty() {
                            IrType::Tagged
                        } else {
                            IrType::Object
                        },
                        IrExpr::Ctor {
                            info: out.constructors.info(tag, field_count),
                            args,
                        },
                    )?;
                    value.constructor_tags = ConstructorTags::singleton(tag);
                    out.set(*dst, value)?;
                }
                I::CtorTest {
                    dst,
                    src,
                    expected_tag,
                    expected_fields,
                } => {
                    let tag = out.constructors.tag(*expected_tag, *expected_fields)?;
                    let source = out.get(*src)?;
                    let possible = if source.constructor_tags.is_empty() {
                        out.constructors.tags
                    } else {
                        source.constructor_tags
                    };
                    let matched = ConstructorTags::singleton(tag);
                    if !possible.contains(tag) || possible == matched {
                        let value = out.bind(
                            IrType::Tagged,
                            IrExpr::Lit(IrLit::Num(IrNat::Small(u64::from(possible == matched)))),
                        )?;
                        out.set(*dst, value)?;
                    } else {
                        // Split while the borrowed source is alive. Its register
                        // may be dropped or overwritten before the later branch
                        // reads the independently stored Boolean result.
                        let saved = out.snapshot()?;
                        let prefix = std::mem::take(&mut out.stmts);
                        out.refine_constructor(source.index, matched)?;
                        let value =
                            out.bind(IrType::Tagged, IrExpr::Lit(IrLit::Num(IrNat::Small(1))))?;
                        out.set(*dst, value)?;
                        let yes = compile_body(function, out, pc + 1, active, depth + 1)?;
                        out.registers = saved;
                        out.refine_constructor(source.index, possible.without(tag))?;
                        let value =
                            out.bind(IrType::Tagged, IrExpr::Lit(IrLit::Num(IrNat::Small(0))))?;
                        out.set(*dst, value)?;
                        let no = compile_body(function, out, pc + 1, active, depth + 1)?;
                        return Ok(IrBody {
                            stmts: prefix,
                            terminal: Box::new(IrTerminal::Case {
                                type_name: out.constructors.type_name.clone(),
                                x: source.index,
                                x_type: IrType::TObject,
                                alts: vec![
                                    IrAlt::Ctor {
                                        info: out.constructors.info(tag, *expected_fields),
                                        body: yes,
                                    },
                                    IrAlt::Default { body: no },
                                ],
                            }),
                        });
                    }
                }
                I::CtorField {
                    dst,
                    src,
                    expected_tag,
                    expected_fields,
                    field,
                } => {
                    let tag = out.constructors.tag(*expected_tag, *expected_fields)?;
                    if field >= expected_fields {
                        return Err(invariant("constructor projection field"));
                    }
                    let source = out.get(*src)?;
                    let possible = if source.constructor_tags.is_empty() {
                        out.constructors.tags
                    } else {
                        source.constructor_tags
                    };
                    if !possible.contains(tag) {
                        return Err(unsupported("internal constructor projection shape"));
                    }
                    let matched = ConstructorTags::singleton(tag);
                    let prefix = if possible != matched {
                        Some(std::mem::take(&mut out.stmts))
                    } else {
                        None
                    };
                    out.refine_constructor(source.index, matched)?;
                    // IR projection borrows the field. The FLBC instruction
                    // returns an owner, which must survive releasing its parent
                    // or replacing the source register with the field itself.
                    let value = out.bind(
                        IrType::TObject,
                        IrExpr::Proj {
                            i: u64::from(*field),
                            x: source.index,
                        },
                    )?;
                    out.retain(value)?;
                    out.set(*dst, value)?;
                    if let Some(prefix) = prefix {
                        let body = compile_body(function, out, pc + 1, active, depth + 1)?;
                        // A checked source projection selects its constructor.
                        // Retain a runtime tag guard before the unchecked pin
                        // projection when calls have hidden the precise shape.
                        // A wrong tag cannot reach an out-of-bounds field read.
                        return Ok(IrBody {
                            stmts: prefix,
                            terminal: Box::new(IrTerminal::Case {
                                type_name: out.constructors.type_name.clone(),
                                x: source.index,
                                x_type: IrType::TObject,
                                alts: vec![
                                    IrAlt::Ctor {
                                        info: out.constructors.info(tag, *expected_fields),
                                        body,
                                    },
                                    IrAlt::Default {
                                        body: IrBody {
                                            stmts: Vec::new(),
                                            terminal: Box::new(IrTerminal::Unreachable),
                                        },
                                    },
                                ],
                            }),
                        });
                    }
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
                I::Intrinsic {
                    dst,
                    row,
                    args,
                    argument_ownership,
                    ..
                } => {
                    let (_, result) = native_signature(row)?;
                    let function = native_name(row)?;
                    let ty = match result {
                        fir::ValueType::Nat => IrType::TObject,
                        fir::ValueType::String => IrType::Object,
                        fir::ValueType::Bool => IrType::UInt8,
                        _ => return Err(invariant("native result carrier")),
                    };
                    let mut value = if native_consumes_borrowed_strings(row) {
                        // Each borrowed occurrence donates its own retained
                        // owner to the consuming native ABI, including aliases.
                        // The callee releases those donations: a post-call Dec
                        // here would invalidate the still-live FIR operands.
                        let args = out.args(args, argument_ownership, true)?;
                        out.bind(ty, IrExpr::Fap { function, args })?
                    } else {
                        out.call_typed(function, args, argument_ownership, ty)?
                    };
                    if result == fir::ValueType::Bool {
                        value = out.bind(
                            IrType::Tagged,
                            IrExpr::Box {
                                ty: IrType::UInt8,
                                x: value.index,
                            },
                        )?;
                    }
                    out.set(*dst, value)?;
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
                    return out.finish(v);
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
                    return out.finish(v);
                }
                I::Return { src } => {
                    let v = out.take(*src)?;
                    return out.finish(v);
                }
                I::Jump { target } => {
                    pc = usize::try_from(target.get()).map_err(|_| CompileError::Limit)?;
                    continue;
                }
                I::JumpIfZero {
                    cond,
                    zero,
                    nonzero,
                } => {
                    let condition = out.get(*cond)?;
                    if let Some(value) = condition.natural {
                        pc = usize::try_from(if value == 0 { zero } else { nonzero }.get())
                            .map_err(|_| CompileError::Limit)?;
                        continue;
                    }
                    let saved = out.snapshot()?;
                    let prefix = std::mem::take(&mut out.stmts);
                    let zero = compile_body(
                        function,
                        out,
                        usize::try_from(zero.get()).map_err(|_| CompileError::Limit)?,
                        active,
                        depth + 1,
                    )?;
                    out.registers = saved;
                    let nonzero = compile_body(
                        function,
                        out,
                        usize::try_from(nonzero.get()).map_err(|_| CompileError::Limit)?,
                        active,
                        depth + 1,
                    )?;
                    // The FIR validator admits only Nat/Bool conditions. Zero is
                    // the scalar tag zero for both. Every positive Nat, including
                    // heap magnitudes, takes the default arm, as does Bool.true.
                    return Ok(IrBody {
                        stmts: prefix,
                        terminal: Box::new(IrTerminal::Case {
                            type_name: Name::from_components(["Nat"]),
                            x: condition.index,
                            x_type: IrType::TObject,
                            alts: vec![
                                IrAlt::Ctor {
                                    info: IrCtorInfo {
                                        name: Name::from_components(["Nat", "zero"]),
                                        cidx: 0,
                                        size: 0,
                                        usize: 0,
                                        ssize: 0,
                                    },
                                    body: zero,
                                },
                                IrAlt::Default { body: nonzero },
                            ],
                        }),
                    });
                }
                _ => {
                    return Err(unsupported("instruction outside the pure boxed subset"));
                }
            }
            pc = pc.checked_add(1).ok_or(CompileError::Limit)?;
        }
    })();
    for pc in path {
        active[pc] = false;
    }
    result
}

fn boxed_wrapper(declaration: &IrDecl, meter: &mut Budget) -> Result<IrDecl> {
    let IrDecl::Function {
        name,
        params,
        result,
        ..
    } = declaration
    else {
        return Err(invariant("native function"));
    };
    meter.charge(params.len().saturating_mul(3).saturating_add(1))?;
    let mut next = params.len() as u64 + 1;
    let mut stmts = Vec::new();
    let mut args = Vec::new();
    for p in params {
        args.push(if p.ty == IrType::Erased {
            IrArg::Erased
        } else if p.ty == IrType::UInt8 {
            let x = next;
            next = next.checked_add(1).ok_or(CompileError::Limit)?;
            stmts.push(IrStmt::VDecl {
                x,
                ty: IrType::UInt8,
                expr: IrExpr::Unbox { x: p.x },
            });
            IrArg::Var(x)
        } else {
            IrArg::Var(p.x)
        });
    }
    let called = next;
    next = next.checked_add(1).ok_or(CompileError::Limit)?;
    stmts.push(IrStmt::VDecl {
        x: called,
        ty: result.clone(),
        expr: IrExpr::Fap {
            function: name.clone(),
            args,
        },
    });
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
    let returned = if *result == IrType::UInt8 {
        meter.charge(1)?;
        stmts.push(IrStmt::VDecl {
            x: next,
            ty: IrType::Tagged,
            expr: IrExpr::Box {
                ty: IrType::UInt8,
                x: called,
            },
        });
        next
    } else {
        called
    };
    Ok(IrDecl::Function {
        name: Name::str(name.clone(), "_boxed"),
        params: params
            .iter()
            .map(|p| IrParam {
                borrow: false,
                ty: if p.ty == IrType::Erased {
                    IrType::TObject
                } else if p.ty == IrType::UInt8 {
                    IrType::Tagged
                } else {
                    p.ty.clone()
                },
                ..p.clone()
            })
            .collect(),
        result: if *result == IrType::UInt8 {
            IrType::Tagged
        } else {
            result.clone()
        },
        body: IrBody {
            stmts,
            terminal: Box::new(IrTerminal::Ret(IrArg::Var(returned))),
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
    let module = compile_module(program, entry, limits, None, &mut meter)?;
    validate_module(&module, &meter)?;
    Ok(module)
}

fn compile_module(
    program: &fir::ValidatedProgram,
    entry: &Name,
    limits: CompileLimits,
    source_exports: Option<&SourceSignature>,
    meter: &mut Budget,
) -> Result<IrModule> {
    if entry.is_anonymous() {
        return Err(unsupported("anonymous entry name"));
    }
    // No constructor can enter or leave a closed Nat/String/Bool source ABI,
    // recursively through callbacks. ABI casts and constructor externs remain
    // refused. Every internal object therefore comes from these checked boxed
    // layouts, including objects reached through a constructor's object fields.
    // The arbitrary-FIR API has no such guarantee and keeps this table empty.
    let mut constructors = InternalConstructors {
        type_name: Name::str(entry.clone(), "_fln_data"),
        layouts: std::collections::BTreeMap::new(),
        tags: ConstructorTags::default(),
    };
    if source_exports.is_some() {
        for constructor in program.constructors() {
            meter.charge(constructor.fields.len().saturating_add(1))?;
            if !constructor.static_scalar_bytes.is_empty() {
                return Err(unsupported("internal constructor scalar payload"));
            }
            for field in &constructor.fields {
                carrier(*field, true)?;
            }
            let fields =
                u16::try_from(constructor.fields.len()).map_err(|_| CompileError::Limit)?;
            let next = constructors.layouts.len();
            if let std::collections::btree_map::Entry::Vacant(layout) =
                constructors.layouts.entry((constructor.tag, fields))
            {
                let tag = u8::try_from(next).map_err(|_| CompileError::Limit)?;
                if tag > fln_rt::abi::TAG_MAX_CTOR_TAG {
                    return Err(unsupported("private constructor tag capacity"));
                }
                layout.insert(tag);
                constructors.tags.insert(tag);
            }
        }
    }
    let internal_constructors = !constructors.tags.is_empty();
    for function in program.functions() {
        signature(
            &function.parameters,
            &function.parameter_ownership,
            function.result,
            function.result_ownership,
            internal_constructors,
            meter,
        )?;
        let mut types: std::collections::BTreeMap<_, _> = function
            .parameters
            .iter()
            .enumerate()
            .map(|(i, ty)| (fir::ValueId::new(i as u32), *ty))
            .collect();
        // Canonical block numbering need not be a topological order. FIR has
        // already proved dominance; record every binding's type before looking
        // up captures and application operands on any control-flow path.
        for binding in function.blocks.iter().flat_map(|block| &block.bindings) {
            meter.charge(1)?;
            carrier(binding.ty, internal_constructors)?;
            if binding.ty == fir::ValueType::Constructor
                && !matches!(
                    binding.operation,
                    fir::Operation::Ctor { .. }
                        | fir::Operation::Project { .. }
                        | fir::Operation::Alias(_)
                        | fir::Operation::Call { .. }
                        | fir::Operation::Apply { .. }
                )
            {
                return Err(unsupported("unproved internal constructor producer"));
            }
            types.insert(binding.id, binding.ty);
        }
        for binding in function.blocks.iter().flat_map(|block| &block.bindings) {
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
        }
    }
    for intrinsic in program.intrinsics() {
        validate_native(intrinsic, meter)?;
    }
    for closure in program.closure_types() {
        signature(
            &closure.parameters,
            &closure.parameter_ownership,
            closure.result,
            closure.result_ownership,
            internal_constructors,
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
        let declaration = compile_function(function, &names, &constructors, meter)?;
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
    let externs: std::collections::BTreeMap<_, _> = fln_vm::extern_table_generated::EXTERN_ROWS
        .iter()
        .filter_map(|row| {
            native_signature(row.id)
                .ok()
                .map(|(arguments, _)| (Name::from_components(row.name.split('.')), arguments.len()))
        })
        .collect();
    fln_olean::ir_types::validate_ir_types(
        std::slice::from_ref(module),
        &externs,
        fln_olean::ir_validate::IrValidationLimits {
            max_declarations: module
                .decls
                .len()
                .checked_add(externs.len())
                .ok_or(CompileError::Limit)?,
            max_work: meter.0,
            one_based_variables: true,
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
    reduced: Option<Vec<ReducedArgument>>,
}

enum ReducedArgument {
    Parameter(u64),
    Literal(IrLit, IrType),
    Erased,
}

fn source_without_metadata<'a>(
    mut expression: &'a fln_core::expr::Expr,
    meter: &mut Budget,
) -> Result<&'a fln_core::expr::Expr> {
    while let fln_core::expr::ExprNode::MData { expr, .. } = expression.node() {
        meter.charge(1)?;
        expression = expr;
    }
    Ok(expression)
}

fn source_spine<'a, const N: usize>(
    expression: &'a fln_core::expr::Expr,
    meter: &mut Budget,
) -> Result<Option<(&'a fln_core::expr::Expr, [&'a fln_core::expr::Expr; N])>> {
    use fln_core::expr::ExprNode;
    let mut head = expression;
    let mut arguments = [expression; N];
    for argument in arguments.iter_mut().rev() {
        meter.charge(1)?;
        head = source_without_metadata(head, meter)?;
        let ExprNode::App { f, a } = head.node() else {
            return Ok(None);
        };
        *argument = source_without_metadata(a, meter)?;
        head = f;
    }
    let head = source_without_metadata(head, meter)?;
    Ok((!matches!(head.node(), ExprNode::App { .. })).then_some((head, arguments)))
}

// Reduction metadata can inline the full entry and call `f._redArg` instead.
// Analyze an explicit lambda telescope, with closed let initializers. Calls
// through source parameters stay opaque. A dynamic Boolean conditional uses
// its scrutinee and both arms; its closed motive contributes no runtime uses.
// Other named/local/beta-redex calls refuse when they could change a reduction mask.
// This is a bounded source subset, not a guess about general simplification.
fn source_boolean_case<'a>(
    expression: &'a fln_core::expr::Expr,
    meter: &mut Budget,
) -> Result<Option<[&'a fln_core::expr::Expr; 3]>> {
    use fln_core::expr::ExprNode;
    if let Some((head, [motive, no, yes, condition])) = source_spine::<4>(expression, meter)?
        && matches!(head.node(), ExprNode::Const { name, levels }
            if name == &Name::from_components(["Bool", "rec"]) && levels.len() == 1)
    {
        let ExprNode::Lam { body, .. } = motive.node() else {
            return Err(unsupported("source Boolean case motive"));
        };
        source_carrier(body, meter)?;
        return Ok(Some([condition, no, yes]));
    }
    let Some((head, [ty, proposition, decision, yes, no])) = source_spine::<5>(expression, meter)?
    else {
        return Ok(None);
    };
    if !matches!(head.node(), ExprNode::Const { name, levels }
        if name == &Name::from_components(["ite"]) && levels.len() == 1)
    {
        return Ok(None);
    }
    source_carrier(ty, meter)?;
    let Some((equality, [boolean, condition, truth])) = source_spine::<3>(proposition, meter)?
    else {
        return Ok(None);
    };
    let constant = |expr: &fln_core::expr::Expr, parts: &[&str]| {
        matches!(expr.node(), ExprNode::Const { name, levels }
            if name == &Name::from_components(parts.iter().copied()) && levels.is_empty())
    };
    if !matches!(equality.node(), ExprNode::Const { name, levels }
        if name == &Name::from_components(["Eq"]) && levels.len() == 1)
        || !constant(boolean, &["Bool"])
        || !constant(truth, &["Bool", "true"])
    {
        return Ok(None);
    }
    // An arbitrary decision procedure can have additional runtime dependencies.
    // Only the canonical Bool equality application has this exact use mask.
    let Some((dictionary, [left, right])) = source_spine::<2>(decision, meter)? else {
        return Ok(None);
    };
    if !(constant(dictionary, &["instDecidableEqBool"]) || constant(dictionary, &["Bool", "decEq"]))
        || left != condition
        || right != truth
    {
        return Ok(None);
    }
    Ok(Some([condition, no, yes]))
}

fn simple_source_parameter_uses(
    value: &fln_core::expr::Expr,
    arity: usize,
    meter: &mut Budget,
) -> Result<Vec<bool>> {
    use fln_core::expr::ExprNode;
    let mut levels = Vec::new();
    let mut pending = Vec::new();
    let mut depth = 0_u64;
    let mut body = value;
    while levels.len() < arity {
        meter.charge(1)?;
        match body.node() {
            ExprNode::Lam { body: next, .. } => {
                levels
                    .try_reserve(1)
                    .map_err(|_| CompileError::Allocation)?;
                levels.push(depth);
                depth = depth.checked_add(1).ok_or(CompileError::Limit)?;
                body = next;
            }
            ExprNode::LetE {
                value, body: next, ..
            } => {
                pending
                    .try_reserve(1)
                    .map_err(|_| CompileError::Allocation)?;
                pending.push((value, depth, true));
                depth = depth.checked_add(1).ok_or(CompileError::Limit)?;
                body = next;
            }
            ExprNode::MData { expr, .. } => body = expr,
            _ => return Err(unsupported("source export lambda telescope")),
        }
    }
    pending
        .try_reserve(1)
        .map_err(|_| CompileError::Allocation)?;
    pending.push((body, depth, false));
    let mut used = Vec::new();
    used.try_reserve_exact(arity)
        .map_err(|_| CompileError::Allocation)?;
    used.resize(arity, false);
    while let Some((expr, depth, initializer)) = pending.pop() {
        meter.charge(1)?;
        pending
            .try_reserve(2)
            .map_err(|_| CompileError::Allocation)?;
        match expr.node() {
            ExprNode::BVar { idx } => {
                let level = depth
                    .checked_sub(u64::from(*idx) + 1)
                    .ok_or_else(|| unsupported("open source export"))?;
                if let Ok(index) = levels.binary_search(&level) {
                    if initializer && arity > 1 {
                        return Err(unsupported("parameter-dependent source initializer"));
                    }
                    used[index] = true;
                }
            }
            ExprNode::App { f, a } => {
                if let Some([condition, no, yes]) = source_boolean_case(expr, meter)? {
                    // A literal scrutinee can erase an arm before the pin
                    // chooses its reduced entry. Leave that optimization out
                    // of multiargument source exports until it is modeled.
                    if arity > 1 && !matches!(condition.node(), ExprNode::BVar { .. }) {
                        return Err(unsupported("specializable Boolean source case"));
                    }
                    if arity > 1 {
                        let original_parameter = |part: &fln_core::expr::Expr| {
                            let ExprNode::BVar { idx } = part.node() else {
                                return false;
                            };
                            depth
                                .checked_sub(u64::from(*idx) + 1)
                                .is_some_and(|level| levels.binary_search(&level).is_ok())
                        };
                        if !original_parameter(condition) {
                            return Err(unsupported("local Boolean source discriminator"));
                        }
                        for arm in [no, yes] {
                            if matches!(arm.node(), ExprNode::BVar { .. })
                                && !original_parameter(arm)
                            {
                                return Err(unsupported("local Boolean source arm"));
                            }
                        }
                        let leaf = |part: &fln_core::expr::Expr| match part.node() {
                            ExprNode::BVar { .. } => part != condition,
                            ExprNode::Lit { .. } => true,
                            ExprNode::Const { name, levels } => {
                                levels.is_empty()
                                    && (name == &Name::from_components(["Bool", "true"])
                                        || name == &Name::from_components(["Bool", "false"]))
                            }
                            _ => false,
                        };
                        if no == yes || !leaf(no) || !leaf(yes) {
                            return Err(unsupported("specializable Boolean source arms"));
                        }
                    }
                    pending
                        .try_reserve(3)
                        .map_err(|_| CompileError::Allocation)?;
                    for part in [condition, no, yes] {
                        pending.push((part, depth, initializer));
                    }
                    continue;
                }
                if !initializer && arity > 1 {
                    let mut head = f;
                    loop {
                        meter.charge(1)?;
                        match head.node() {
                            ExprNode::App { f, .. } => head = f,
                            ExprNode::MData { expr, .. } => head = expr,
                            _ => break,
                        }
                    }
                    let ExprNode::BVar { idx } = head.node() else {
                        return Err(unsupported("specializable source call"));
                    };
                    let level = depth
                        .checked_sub(u64::from(*idx) + 1)
                        .ok_or_else(|| unsupported("open source call"))?;
                    if levels.binary_search(&level).is_err() {
                        return Err(unsupported("local source call"));
                    }
                }
                pending.push((f, depth, initializer));
                pending.push((a, depth, initializer));
            }
            ExprNode::Lam { body, .. } => pending.push((
                body,
                depth.checked_add(1).ok_or(CompileError::Limit)?,
                initializer,
            )),
            ExprNode::LetE { value, body, .. } => {
                pending.push((value, depth, true));
                pending.push((
                    body,
                    depth.checked_add(1).ok_or(CompileError::Limit)?,
                    initializer,
                ));
            }
            ExprNode::MData { expr, .. } => pending.push((expr, depth, initializer)),
            ExprNode::Const { .. } | ExprNode::Lit { .. } => {}
            _ => return Err(unsupported("source reduction expression")),
        }
    }
    Ok(used)
}

struct SourceUse {
    parameters: Vec<bool>,
    discardable: bool,
}

struct SourceUseBinding {
    parameter: bool,
    value: SourceUse,
}

/// The pin folds addition/append constants and neutral elements, but neither
/// operation can erase a dynamic operand. This smaller analysis follows that
/// exact dependency law through lets. Other named calls retain their refusal:
/// e.g. `Nat.mul x 0` may erase x before the pin chooses its `_redArg` entry.
struct SourceUses<'a, 'b> {
    environment: &'a crate::Environment,
    arity: usize,
    ingress: fln_comp::ingress::IngressLimits,
    meter: &'b mut Budget,
    externs: Option<fln_elab::externs::ExternTable>,
    replacements: Option<fln_elab::implemented_by::ImplementedByTable>,
    natives: std::collections::BTreeSet<Name>,
}

impl SourceUses<'_, '_> {
    fn empty(&mut self, discardable: bool) -> Result<SourceUse> {
        self.meter.charge(self.arity)?;
        let mut parameters = Vec::new();
        parameters
            .try_reserve_exact(self.arity)
            .map_err(|_| CompileError::Allocation)?;
        parameters.resize(self.arity, false);
        Ok(SourceUse {
            parameters,
            discardable,
        })
    }

    fn merge(&mut self, into: &mut SourceUse, other: &SourceUse) -> Result<()> {
        self.meter.charge(self.arity)?;
        for (left, right) in into.parameters.iter_mut().zip(&other.parameters) {
            *left |= right;
        }
        into.discardable &= other.discardable;
        Ok(())
    }

    fn expression_work(&mut self, expression: &fln_core::expr::Expr) -> Result<()> {
        use fln_core::expr::ExprNode;
        let mut pending = vec![expression];
        while let Some(expression) = pending.pop() {
            self.meter.charge(1)?;
            pending
                .try_reserve(3)
                .map_err(|_| CompileError::Allocation)?;
            match expression.node() {
                ExprNode::App { f, a } => pending.extend([f, a]),
                ExprNode::Lam {
                    binder_type, body, ..
                }
                | ExprNode::ForallE {
                    binder_type, body, ..
                } => pending.extend([binder_type, body]),
                ExprNode::LetE {
                    type_, value, body, ..
                } => pending.extend([type_, value, body]),
                ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => pending.push(expr),
                _ => {}
            }
        }
        Ok(())
    }

    fn ingress_error(error: fln_comp::ingress::IngressError) -> CompileError {
        if error.is_resource_exhaustion() {
            CompileError::Limit
        } else {
            unsupported("unproved source operation contract")
        }
    }

    fn metadata(&mut self) -> Result<()> {
        if self.replacements.is_none() {
            use fln_elab::implemented_by::{ImplementedByError, ImplementedByReadError};
            self.replacements = Some(
                fln_elab::implemented_by::ImplementedByTable::read_metered(
                    self.environment,
                    |work| self.meter.charge(work),
                )
                .map_err(|error| match error {
                    ImplementedByReadError::Budget(error) => error,
                    ImplementedByReadError::Registry(ImplementedByError::Limit) => {
                        CompileError::Limit
                    }
                    _ => unsupported("invalid source executable replacement metadata"),
                })?,
            );
        }
        let mut visited = 0;
        let mut limits = self.ingress;
        limits.max_nodes = limits
            .max_nodes
            .min(usize::try_from(self.meter.0).unwrap_or(usize::MAX));
        let result = crate::source_intrinsics::read_extern_attributes(
            self.environment,
            &mut self.externs,
            &mut visited,
            limits,
        );
        self.meter.charge(visited)?;
        result.map_err(Self::ingress_error)
    }

    fn native(&mut self, name: &Name) -> Result<()> {
        if self.natives.contains(name) {
            return self.meter.charge(1);
        }
        self.metadata()?;
        if self.replacements.as_ref().unwrap().get(name).is_some() {
            return Err(unsupported(
                "source operation with an executable replacement",
            ));
        }
        let mut visited = 0;
        let mut limits = self.ingress;
        limits.max_nodes = limits
            .max_nodes
            .min(usize::try_from(self.meter.0).unwrap_or(usize::MAX));
        let result = crate::executable_intrinsic_binding_cached(
            self.environment,
            name,
            &mut visited,
            limits,
            &mut self.externs,
        );
        self.meter.charge(visited)?;
        if result.map_err(Self::ingress_error)?.is_none() {
            return Err(unsupported("unproved source operation contract"));
        }
        self.natives.insert(name.clone());
        Ok(())
    }

    fn primitive(name: &Name) -> bool {
        name == &Name::from_components(["Nat", "add"])
            || name == &Name::from_components(["String", "append"])
    }

    fn dictionary_name(name: &Name) -> bool {
        [
            "HAdd.hAdd",
            "Add.add",
            "instHAdd",
            "instAddNat",
            "HAppend.hAppend",
            "Append.append",
            "instHAppendOfAppend",
            "instAppendString",
        ]
        .iter()
        .any(|label| name == &Name::from_components(label.split('.')))
    }

    /// Resolve only the closed dictionary spine, with symbolic runtime operands.
    /// Actual checked bodies select the field; names alone authorize nothing.
    /// Universes occur only in its erased type arguments and are not rewritten
    /// into a source or runtime product. Externs/replacements on any unfolded
    /// dictionary refuse, even when its logical body looks like the usual one.
    fn dictionary(
        &mut self,
        mut expression: fln_core::expr::Expr,
        depth: usize,
    ) -> Result<fln_core::expr::Expr> {
        use fln_core::expr::{Expr, ExprNode};
        use fln_env::constants::{ConstantInfo, DefinitionSafety};
        if depth >= 128 {
            return Err(CompileError::Limit);
        }
        loop {
            self.meter.charge(1)?;
            let mut head = source_without_metadata(&expression, self.meter)?.clone();
            let mut arguments = Vec::new();
            while let ExprNode::App { f, a } = head.node() {
                self.meter.charge(1)?;
                arguments
                    .try_reserve(1)
                    .map_err(|_| CompileError::Allocation)?;
                arguments.push(a.clone());
                head = source_without_metadata(f, self.meter)?.clone();
            }
            arguments.reverse();
            let next = match head.node() {
                ExprNode::Const { name, .. } if Self::primitive(name) => return Ok(expression),
                ExprNode::Const { name, .. }
                    if matches!(self.environment.find(name), Some(ConstantInfo::Ctor(_))) =>
                {
                    self.metadata()?;
                    if self.externs.as_ref().unwrap().get(name).is_some()
                        || self.replacements.as_ref().unwrap().get(name).is_some()
                    {
                        return Err(unsupported("source operator dictionary replacement"));
                    }
                    return Ok(expression);
                }
                ExprNode::Const { name, levels } if Self::dictionary_name(name) => {
                    self.metadata()?;
                    if self.externs.as_ref().unwrap().get(name).is_some()
                        || self.replacements.as_ref().unwrap().get(name).is_some()
                    {
                        return Err(unsupported("source operator dictionary replacement"));
                    }
                    let Some(ConstantInfo::Defn(definition)) = self.environment.find(name) else {
                        return Err(unsupported("source operator dictionary definition"));
                    };
                    if definition.safety != DefinitionSafety::Safe
                        || definition.base.level_params.len() != levels.len()
                    {
                        return Err(unsupported("source operator dictionary definition"));
                    }
                    self.expression_work(&definition.value)?;
                    definition.value.clone()
                }
                ExprNode::Lam { body, .. } if !arguments.is_empty() => {
                    self.expression_work(body)?;
                    let argument = arguments.remove(0);
                    body.subst_loose(0, &[argument])
                        .map_err(|_| CompileError::Limit)?
                }
                ExprNode::LetE { value, body, .. } => {
                    self.expression_work(body)?;
                    self.expression_work(value)?;
                    body.subst_loose(0, std::slice::from_ref(value))
                        .map_err(|_| CompileError::Limit)?
                }
                ExprNode::Proj {
                    struct_name,
                    idx,
                    expr,
                } => {
                    let constructor = self.dictionary(expr.clone(), depth + 1)?;
                    let mut head = source_without_metadata(&constructor, self.meter)?;
                    let mut fields = Vec::new();
                    while let ExprNode::App { f, a } = head.node() {
                        self.meter.charge(1)?;
                        fields
                            .try_reserve(1)
                            .map_err(|_| CompileError::Allocation)?;
                        fields.push(a);
                        head = source_without_metadata(f, self.meter)?;
                    }
                    let ExprNode::Const { name, .. } = head.node() else {
                        return Err(unsupported("source operator dictionary constructor"));
                    };
                    let Some(ConstantInfo::Ctor(info)) = self.environment.find(name) else {
                        return Err(unsupported("source operator dictionary constructor"));
                    };
                    if &info.induct != struct_name
                        || *idx >= u64::from(info.num_fields)
                        || fields.len() as u64
                            != u64::from(info.num_params) + u64::from(info.num_fields)
                    {
                        return Err(unsupported("source operator dictionary projection"));
                    }
                    fields[fields.len() - 1 - (u64::from(info.num_params) + idx) as usize].clone()
                }
                _ => return Err(unsupported("source operator dictionary")),
            };
            expression = arguments.into_iter().fold(next, Expr::app);
        }
    }

    fn binary_arguments<'e>(
        &mut self,
        expression: &'e fln_core::expr::Expr,
    ) -> Result<Option<[&'e fln_core::expr::Expr; 2]>> {
        use fln_core::expr::{Expr, ExprNode, FVarId};
        if let Some((head, arguments)) = source_spine::<2>(expression, self.meter)?
            && let ExprNode::Const { name, levels } = head.node()
            && levels.is_empty()
            && Self::primitive(name)
        {
            self.native(name)?;
            return Ok(Some(arguments));
        }
        let Some((head, [a, b, result, dictionary, left, right])) =
            source_spine::<6>(expression, self.meter)?
        else {
            return Ok(None);
        };
        let ExprNode::Const { name, levels } = head.node() else {
            return Ok(None);
        };
        let primitive = if name == &Name::from_components(["HAdd", "hAdd"]) {
            Name::from_components(["Nat", "add"])
        } else if name == &Name::from_components(["HAppend", "hAppend"]) {
            Name::from_components(["String", "append"])
        } else {
            return Ok(None);
        };
        let carrier = if primitive == Name::from_components(["Nat", "add"]) {
            Name::from_components(["Nat"])
        } else {
            Name::from_components(["String"])
        };
        if levels.len() != 3
            || [a, b, result].iter().any(|ty| {
                !matches!(ty.node(), ExprNode::Const { name, levels }
                    if name == &carrier && levels.is_empty())
            })
            || dictionary.has_loose_bvars()
            || dictionary.has_fvar()
        {
            return Err(unsupported("source operator dictionary arguments"));
        }
        let x = Expr::fvar(FVarId(Name::from_components(["_fln_ir_source_left"])));
        let y = Expr::fvar(FVarId(Name::from_components(["_fln_ir_source_right"])));
        let application = [a, b, result, dictionary]
            .into_iter()
            .cloned()
            .chain([x.clone(), y.clone()])
            .fold(head.clone(), Expr::app);
        let resolved = self.dictionary(application, 0)?;
        let Some((head, [actual_left, actual_right])) = source_spine::<2>(&resolved, self.meter)?
        else {
            return Err(unsupported("source operator dictionary result"));
        };
        if !matches!(head.node(), ExprNode::Const { name, levels }
            if name == &primitive && levels.is_empty())
            || actual_left != &x
            || actual_right != &y
        {
            return Err(unsupported("source operator dictionary result"));
        }
        self.native(&primitive)?;
        Ok(Some([left, right]))
    }

    fn value(
        &mut self,
        expression: &fln_core::expr::Expr,
        locals: &mut Vec<SourceUseBinding>,
        depth: usize,
    ) -> Result<SourceUse> {
        use fln_core::expr::ExprNode;
        if depth >= 128 {
            return Err(CompileError::Limit);
        }
        self.meter.charge(1)?;
        if !expression.has_loose_bvars() {
            self.expression_work(expression)?;
            return self.empty(false);
        }
        let expression = source_without_metadata(expression, self.meter)?;
        match expression.node() {
            ExprNode::BVar { idx } => {
                let index = locals
                    .len()
                    .checked_sub(*idx as usize + 1)
                    .ok_or_else(|| unsupported("open source export"))?;
                let mut used = self.empty(true)?;
                self.merge(&mut used, &locals[index].value)?;
                // Reading a let-bound value does not run its initializer again.
                used.discardable = true;
                Ok(used)
            }
            ExprNode::App { .. } => {
                if let Some(arguments) = self.binary_arguments(expression)? {
                    let mut used = self.empty(true)?;
                    let mut discardable = true;
                    for argument in arguments {
                        let argument = self.value(argument, locals, depth + 1)?;
                        discardable &=
                            argument.discardable || !argument.parameters.iter().any(|used| *used);
                        self.merge(&mut used, &argument)?;
                    }
                    // Closed subexpressions carry no parameter dependencies;
                    // their effects cannot change which source slots are used.
                    used.discardable = discardable;
                    return Ok(used);
                }
                let mut head = expression;
                let mut arguments = Vec::new();
                while let ExprNode::App { f, a } = head.node() {
                    self.meter.charge(1)?;
                    arguments
                        .try_reserve(1)
                        .map_err(|_| CompileError::Allocation)?;
                    arguments.push(a);
                    head = source_without_metadata(f, self.meter)?;
                }
                let ExprNode::BVar { idx } = head.node() else {
                    return Err(unsupported("specializable source call"));
                };
                let index = locals
                    .len()
                    .checked_sub(*idx as usize + 1)
                    .ok_or_else(|| unsupported("open source call"))?;
                if !locals[index].parameter {
                    return Err(unsupported("local source call"));
                }
                let mut used = self.value(head, locals, depth + 1)?;
                for argument in arguments {
                    let argument = self.value(argument, locals, depth + 1)?;
                    self.merge(&mut used, &argument)?;
                }
                used.discardable = false;
                Ok(used)
            }
            ExprNode::LetE { value, body, .. } => {
                self.push_let(value, locals, depth)?;
                let result = self.value(body, locals, depth + 1);
                locals.pop();
                result
            }
            ExprNode::Lam { body, .. } => {
                let value = self.empty(true)?;
                locals
                    .try_reserve(1)
                    .map_err(|_| CompileError::Allocation)?;
                locals.push(SourceUseBinding {
                    parameter: false,
                    value,
                });
                let result = self.value(body, locals, depth + 1);
                locals.pop();
                result.map(|mut used| {
                    used.discardable = true;
                    used
                })
            }
            _ => Err(unsupported("source reduction expression")),
        }
    }

    fn push_let(
        &mut self,
        value: &fln_core::expr::Expr,
        locals: &mut Vec<SourceUseBinding>,
        depth: usize,
    ) -> Result<()> {
        let value = self.value(value, locals, depth + 1)?;
        if !value.discardable && value.parameters.iter().any(|used| *used) {
            return Err(unsupported("parameter-dependent source initializer"));
        }
        locals
            .try_reserve(1)
            .map_err(|_| CompileError::Allocation)?;
        locals.push(SourceUseBinding {
            parameter: false,
            value,
        });
        Ok(())
    }

    fn parameters(&mut self, value: &fln_core::expr::Expr) -> Result<Vec<bool>> {
        use fln_core::expr::ExprNode;
        let mut body = value;
        let mut count = 0;
        let mut locals = Vec::new();
        while count < self.arity {
            self.meter.charge(1)?;
            match body.node() {
                ExprNode::Lam { body: next, .. } => {
                    let mut value = self.empty(true)?;
                    value.parameters[count] = true;
                    locals
                        .try_reserve(1)
                        .map_err(|_| CompileError::Allocation)?;
                    locals.push(SourceUseBinding {
                        parameter: true,
                        value,
                    });
                    count += 1;
                    body = next;
                }
                ExprNode::LetE {
                    value, body: next, ..
                } => {
                    self.push_let(value, &mut locals, 0)?;
                    body = next;
                }
                ExprNode::MData { expr, .. } => body = expr,
                _ => return Err(unsupported("source export lambda telescope")),
            }
        }
        Ok(self.value(body, &mut locals, 0)?.parameters)
    }
}

fn source_parameter_uses(
    value: &fln_core::expr::Expr,
    arity: usize,
    environment: &crate::Environment,
    ingress: fln_comp::ingress::IngressLimits,
    meter: &mut Budget,
) -> Result<Vec<bool>> {
    match simple_source_parameter_uses(value, arity, meter) {
        Err(CompileError::Unsupported {
            what: "specializable source call" | "parameter-dependent source initializer",
        }) => SourceUses {
            environment,
            arity,
            ingress,
            meter,
            externs: None,
            replacements: None,
            natives: std::collections::BTreeSet::new(),
        }
        .parameters(value),
        result => result,
    }
}

// Walk source types before erasure. In particular, a proof/type argument must
// not disappear and silently change the exported source calling convention.
fn source_carrier(ty: &fln_core::expr::Expr, meter: &mut Budget) -> Result<IrType> {
    use fln_core::expr::ExprNode;
    let nat = Name::from_components(["Nat"]);
    let string = Name::from_components(["String"]);
    let boolean = Name::from_components(["Bool"]);
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
            ExprNode::Const { name, levels } if levels.is_empty() && name == &boolean => {
                IrType::UInt8
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
    erasures: &[bool],
    environment: &crate::Environment,
    ingress: fln_comp::ingress::IngressLimits,
    meter: &mut Budget,
) -> Result<SourceSignature> {
    use fln_core::expr::ExprNode;
    let mut params = Vec::new();
    let mut function_parameters = Vec::new();
    let mut ty = &definition.base.type_;
    let result = loop {
        meter.charge(1)?;
        match ty.node() {
            ExprNode::ForallE {
                binder_type, body, ..
            } => {
                let erased = erasures
                    .get(params.len())
                    .copied()
                    .ok_or_else(|| invariant("source erasure telescope"))?;
                let carrier = if erased {
                    IrType::Erased
                } else {
                    source_carrier(binder_type, meter)?
                };
                let mut parameter = binder_type;
                while let ExprNode::MData { expr, .. } = parameter.node() {
                    meter.charge(1)?;
                    parameter = expr;
                }
                function_parameters
                    .try_reserve(1)
                    .map_err(|_| CompileError::Allocation)?;
                function_parameters.push(matches!(parameter.node(), ExprNode::ForallE { .. }));
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
    if params.len() != erasures.len() {
        return Err(invariant("source erasure arity"));
    }
    let reduced = if !params.is_empty() {
        let mut used =
            source_parameter_uses(&definition.value, params.len(), environment, ingress, meter)?;
        for (used, erased) in used.iter_mut().zip(erasures) {
            *used &= !erased;
        }
        let count = used.iter().filter(|used| **used).count();
        // The pin deliberately keeps a completely unused telescope: reducing
        // it to a constant could evaluate an otherwise unreachable body.
        if count > 0 && count < params.len() {
            let mut args = Vec::new();
            args.try_reserve_exact(params.len())
                .map_err(|_| CompileError::Allocation)?;
            let mut next = 1;
            for (index, param) in params.iter().enumerate() {
                if used[index] {
                    args.push(ReducedArgument::Parameter(next));
                    next += 1;
                } else if param.ty == IrType::Erased {
                    args.push(ReducedArgument::Erased);
                } else if function_parameters[index] {
                    return Err(unsupported("unused higher-order source parameter"));
                } else if param.ty == IrType::TObject {
                    args.push(ReducedArgument::Literal(
                        IrLit::Num(IrNat::Small(0)),
                        IrType::TObject,
                    ));
                } else if param.ty == IrType::UInt8 {
                    args.push(ReducedArgument::Literal(
                        IrLit::Num(IrNat::Small(0)),
                        IrType::UInt8,
                    ));
                } else {
                    args.push(ReducedArgument::Literal(
                        IrLit::Str(String::new()),
                        IrType::Object,
                    ));
                }
            }
            Some(args)
        } else {
            None
        }
    } else {
        None
    };
    Ok(SourceSignature {
        name: definition.base.name.clone(),
        params,
        result,
        reduced,
    })
}

fn export_source(
    signature: SourceSignature,
    value_entry: &Name,
    meter: &mut Budget,
) -> Result<Vec<IrDecl>> {
    meter.charge(signature.params.len().saturating_mul(2).saturating_add(8))?;
    let closure = signature.params.len() as u64 + 1;
    let mut next = closure.checked_add(1).ok_or(CompileError::Limit)?;
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
        // Closure application takes boxed operands, while the source-facing
        // Boolean entry takes UInt8. Keep that boundary explicit in both
        // directions; the internal FIR program remains entirely boxed.
        let mut args = Vec::new();
        for p in &signature.params {
            args.push(if p.ty == IrType::Erased {
                IrArg::Erased
            } else if p.ty == IrType::UInt8 {
                let x = next;
                next = next.checked_add(1).ok_or(CompileError::Limit)?;
                stmts.push(IrStmt::VDecl {
                    x,
                    ty: IrType::Tagged,
                    expr: IrExpr::Box {
                        ty: IrType::UInt8,
                        x: p.x,
                    },
                });
                IrArg::Var(x)
            } else {
                IrArg::Var(p.x)
            });
        }
        let result = next;
        next = next.checked_add(1).ok_or(CompileError::Limit)?;
        stmts.push(IrStmt::VDecl {
            x: result,
            ty: if signature.result == IrType::UInt8 {
                IrType::TObject
            } else {
                signature.result.clone()
            },
            expr: IrExpr::Ap { x: closure, args },
        });
        result
    };
    let returned = if signature.result == IrType::UInt8 {
        meter.charge(1)?;
        stmts.push(IrStmt::VDecl {
            x: next,
            ty: IrType::UInt8,
            expr: IrExpr::Unbox { x: returned },
        });
        next
    } else {
        returned
    };
    let public = IrDecl::Function {
        name: signature.name.clone(),
        params: signature.params.clone(),
        result: signature.result.clone(),
        body: IrBody {
            stmts,
            terminal: Box::new(IrTerminal::Ret(IrArg::Var(returned))),
        },
        sorry_dep: None,
    };
    let mut declarations = Vec::new();
    declarations
        .try_reserve_exact(4)
        .map_err(|_| CompileError::Allocation)?;
    if !signature.params.is_empty() {
        declarations.push(boxed_wrapper(&public, meter)?);
    }
    declarations.push(public);
    if let Some(reduced) = signature.reduced {
        meter.charge(reduced.len().saturating_mul(3).saturating_add(4))?;
        let mut params = Vec::new();
        params
            .try_reserve_exact(reduced.len())
            .map_err(|_| CompileError::Allocation)?;
        for (original, arg) in signature.params.iter().zip(&reduced) {
            if let ReducedArgument::Parameter(x) = arg {
                params.push(IrParam {
                    x: *x,
                    ..original.clone()
                });
            }
        }
        let mut next = params.len() as u64 + 1;
        let mut stmts = Vec::new();
        let mut args = Vec::new();
        stmts
            .try_reserve_exact(reduced.len() + 1)
            .map_err(|_| CompileError::Allocation)?;
        args.try_reserve_exact(reduced.len())
            .map_err(|_| CompileError::Allocation)?;
        for arg in reduced {
            args.push(match arg {
                ReducedArgument::Parameter(x) => IrArg::Var(x),
                ReducedArgument::Erased => IrArg::Erased,
                ReducedArgument::Literal(literal, ty) => {
                    let x = next;
                    next = next.checked_add(1).ok_or(CompileError::Limit)?;
                    stmts.push(IrStmt::VDecl {
                        x,
                        ty,
                        expr: IrExpr::Lit(literal),
                    });
                    IrArg::Var(x)
                }
            });
        }
        stmts.push(IrStmt::VDecl {
            x: next,
            ty: signature.result.clone(),
            expr: IrExpr::Fap {
                function: signature.name.clone(),
                args,
            },
        });
        let adapter = IrDecl::Function {
            name: Name::str(signature.name, "_redArg"),
            params,
            result: signature.result,
            body: IrBody {
                stmts,
                terminal: Box::new(IrTerminal::Ret(IrArg::Var(next))),
            },
            sorry_dep: None,
        };
        declarations.push(boxed_wrapper(&adapter, meter)?);
        declarations.push(adapter);
    }
    Ok(declarations)
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
/// Runtime types are closed arrows over Nat/String (including higher-order
/// arguments), using owned object parameters. Source type/proof slots are
/// classified in their original telescope and retained as erased parameters.
/// A runtime carrier depending on a source type parameter remains unsupported.
/// Source arrows require an explicit lambda telescope. Multiple arguments allow
/// opaque calls through source parameters and checked Nat.add/String.append
/// expressions, including their ordinary notation and dependency-preserving
/// let bindings. Other specializable calls, ambiguous Boolean reductions and
/// unused higher-order arguments refuse instead of guessing a `_redArg` ABI.
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

fn checked_recursive_companion(
    engine: &crate::Engine,
    logical: &Name,
    engine_limits: crate::EngineExecutionLimits,
    meter: &mut Budget,
) -> std::result::Result<Option<fln_env::constants::DefinitionVal>, DefinitionCompileError> {
    meter.charge(1).map_err(DefinitionCompileError::Ir)?;
    let mut ingress = engine_limits.ingress;
    ingress.max_nodes = ingress
        .max_nodes
        .min(usize::try_from(meter.0).unwrap_or(usize::MAX));
    let runtime = engine.runtime_environment(ingress).map_err(|error| {
        DefinitionCompileError::Engine(crate::EngineExecutionError::Ingress(error))
    })?;
    let (companion, work) = crate::runtime::Preparation::new(&runtime.environment, ingress)
        .with_executable_opaques(&runtime.executable_opaques)
        .with_runtime_initializers(&runtime.runtime_initializers)
        .source_recursive_companion(logical)
        .map_err(|error| {
            DefinitionCompileError::Engine(crate::EngineExecutionError::Ingress(error))
        })?;
    meter.charge(work).map_err(DefinitionCompileError::Ir)?;
    if companion
        .as_ref()
        .is_some_and(|definition| definition.all.len() != 1)
    {
        return Err(DefinitionCompileError::Ir(unsupported(
            "mutual recursive source exports",
        )));
    }
    Ok(companion)
}

/// A module may omit only the exact checked companion of a logical declaration
/// it also owns and exports. The caller checks ownership; the runtime checks the
/// admitted relationship, full group, type, universes and initializer posture.
pub(crate) fn is_checked_recursive_companion(
    engine: &crate::Engine,
    companion: &Name,
    engine_limits: crate::EngineExecutionLimits,
    limits: CompileLimits,
) -> std::result::Result<bool, DefinitionCompileError> {
    if !matches!(
        companion.leaf_view(),
        fln_core::name::LeafView::Str("_unsafe_rec")
    ) {
        return Ok(false);
    }
    let mut meter = Budget(limits.max_work);
    Ok(
        checked_recursive_companion(engine, &companion.parent(), engine_limits, &mut meter)?
            .is_some_and(|definition| &definition.base.name == companion),
    )
}

/// Compile a safe reference to the logical interface, so normal preparation
/// selects its checked executable companion. Never re-admit a Partial body as
/// Safe or export a partial opaque's arbitrary inhabitant. A single closed
/// runtime slot has no smaller nonempty reduced-argument ABI, regardless of
/// body use. The ordinary source exporter owns its boxing and result ABI.
fn recursive_source_wrapper(
    definition: &mut fln_env::constants::DefinitionVal,
    meter: &mut Budget,
) -> Result<()> {
    use fln_core::expr::{Expr, ExprNode};
    let carriers = [
        Name::from_components(["Nat"]),
        Name::from_components(["String"]),
        Name::from_components(["Bool"]),
    ];
    let scalar = |expression: &Expr| {
        matches!(expression.node(), ExprNode::Const { name, levels }
            if levels.is_empty() && carriers.contains(name))
    };
    let ty = source_without_metadata(&definition.base.type_, meter)?;
    let ExprNode::ForallE {
        binder_name,
        binder_type,
        body,
        binder_info,
    } = ty.node()
    else {
        return Err(unsupported(
            "recursive source exports require unary Nat/String/Bool signatures",
        ));
    };
    if !definition.base.level_params.is_empty()
        || !scalar(source_without_metadata(binder_type, meter)?)
        || !scalar(source_without_metadata(body, meter)?)
    {
        return Err(unsupported(
            "recursive source exports require unary Nat/String/Bool signatures",
        ));
    }
    meter.charge(5)?;
    definition.value = Expr::lam(
        binder_name.clone(),
        binder_type.clone(),
        Expr::app(
            Expr::const_(definition.base.name.clone(), Vec::new()),
            Expr::bvar(0).expect("zero source parameter index"),
        ),
        *binder_info,
    );
    Ok(())
}

/// Compile an exact definition or safe opaque body from a module's privately
/// retained checked environment. The temporary admission is confined to a fresh
/// private definition alias: neither that alias nor a successor environment is a
/// module product, and an opaque source declaration stays logically opaque.
///
/// The source signature still belongs to the original declaration. In
/// particular, naming an existing definition cannot replace its exported ABI
/// with the nullary value entry used internally by the compiler.
pub(crate) fn compile_checked_source_definition(
    engine: &crate::Engine,
    name: &Name,
    options: &fln_core::options::KVMap,
    engine_limits: crate::EngineExecutionLimits,
    limits: CompileLimits,
) -> std::result::Result<fln_core::outcome::Outcome<IrModule>, DefinitionCompileError> {
    use fln_core::outcome::Outcome;
    use fln_env::constants::{ConstantInfo, DefinitionSafety, DefinitionVal, ReducibilityHints};
    use std::borrow::Cow;

    let mut meter = Budget(limits.max_work);
    meter.charge(1).map_err(DefinitionCompileError::Ir)?;
    let mut definition = match engine.environment().find(name) {
        Some(ConstantInfo::Defn(definition)) => Cow::Borrowed(definition),
        Some(ConstantInfo::Opaque(opaque)) => {
            if opaque.is_unsafe {
                return Err(DefinitionCompileError::Ir(unsupported(
                    "unsafe or partial source export",
                )));
            }
            meter
                .charge(
                    opaque
                        .base
                        .level_params
                        .len()
                        .saturating_add(opaque.all.len()),
                )
                .map_err(DefinitionCompileError::Ir)?;
            // The implementation was checked in the retained private world.
            // Recheck its body under a fresh alias only for compilation; never
            // replace the opaque constant or publish this transparent view.
            Cow::Owned(DefinitionVal {
                base: opaque.base.clone(),
                value: opaque.value.clone(),
                hints: ReducibilityHints::Opaque,
                safety: DefinitionSafety::Safe,
                all: opaque.all.clone(),
            })
        }
        _ => {
            return Err(DefinitionCompileError::Ir(unsupported(
                "non-definition source export",
            )));
        }
    };
    if definition.safety != DefinitionSafety::Safe {
        return Err(DefinitionCompileError::Ir(unsupported(
            "unsafe or partial source export",
        )));
    }
    // Executable replacement and extern journals may change the body without
    // changing its logical definition. Never export that logical body as if it
    // were the separately selected executable implementation.
    for journal in [
        fln_elab::noncomputable::journal_name(),
        fln_elab::implemented_by::journal_name(),
        fln_elab::externs::journal_name(),
    ] {
        if let Some(state) = engine.environment().extension(&journal) {
            for entry in state.entries() {
                meter
                    .charge(entry.payload.len().saturating_add(1))
                    .map_err(DefinitionCompileError::Ir)?;
            }
        }
    }
    let noncomputable = fln_elab::noncomputable::read(engine.environment()).map_err(|error| {
        DefinitionCompileError::Ir(match error {
            fln_elab::noncomputable::NoncomputableError::Limit => CompileError::Limit,
            _ => unsupported("invalid source noncomputable metadata"),
        })
    })?;
    if noncomputable.contains(name) {
        return Err(DefinitionCompileError::Ir(unsupported(
            "noncomputable source export",
        )));
    }
    let replacements =
        fln_elab::implemented_by::ImplementedByTable::read_metered(engine.environment(), |work| {
            meter.charge(work)
        })
        .map_err(|error| {
            use fln_elab::implemented_by::{ImplementedByError, ImplementedByReadError};
            DefinitionCompileError::Ir(match error {
                ImplementedByReadError::Budget(error) => error,
                ImplementedByReadError::Registry(ImplementedByError::Limit) => CompileError::Limit,
                _ => unsupported("invalid source executable replacement metadata"),
            })
        })?;
    let externs = fln_elab::externs::ExternTable::read_metered(engine.environment(), |work| {
        meter.charge(work)
    })
    .map_err(|error| {
        use fln_elab::externs::{ExternError, ExternReadError};
        DefinitionCompileError::Ir(match error {
            ExternReadError::Budget(error) => error,
            ExternReadError::Registry(ExternError::Limit) => CompileError::Limit,
            _ => unsupported("invalid source extern metadata"),
        })
    })?;
    if replacements.get(name).is_some() || externs.get(name).is_some() {
        return Err(DefinitionCompileError::Ir(unsupported(
            "source export with an executable replacement or extern",
        )));
    }
    if let Some(companion) = checked_recursive_companion(engine, name, engine_limits, &mut meter)? {
        if noncomputable.contains(&companion.base.name) {
            return Err(DefinitionCompileError::Ir(unsupported(
                "noncomputable recursive source companion",
            )));
        }
        if replacements.get(&companion.base.name).is_some()
            || externs.get(&companion.base.name).is_some()
        {
            return Err(DefinitionCompileError::Ir(unsupported(
                "recursive source companion with an executable replacement or extern",
            )));
        }
        recursive_source_wrapper(definition.to_mut(), &mut meter)
            .map_err(DefinitionCompileError::Ir)?;
    }
    let mut ingress = engine_limits.ingress;
    ingress.max_nodes = ingress
        .max_nodes
        .min(usize::try_from(meter.0).unwrap_or(usize::MAX));
    let (erasures, work) = crate::runtime::Preparation::new(engine.environment(), ingress)
        .source_parameter_erasures(&definition.base.type_)
        .map_err(|error| {
            DefinitionCompileError::Engine(crate::EngineExecutionError::Ingress(error))
        })?;
    meter.charge(work).map_err(DefinitionCompileError::Ir)?;
    let signature = source_signature(
        &definition,
        &erasures,
        engine.environment(),
        ingress,
        &mut meter,
    )
    .map_err(DefinitionCompileError::Ir)?;
    let mut alias = definition.into_owned();
    let alias_root = Name::str(name.clone(), "_fln_compile");
    let mut ordinal = 0_u64;
    loop {
        meter.charge(1).map_err(DefinitionCompileError::Ir)?;
        alias.base.name = Name::num(alias_root.clone(), ordinal);
        if !engine.environment().contains(&alias.base.name) {
            break;
        }
        ordinal = ordinal
            .checked_add(1)
            .ok_or(DefinitionCompileError::Ir(CompileError::Limit))?;
    }
    alias.all = vec![alias.base.name.clone()];
    let prepared = engine
        .prepare_definition_entry_with_helpers(
            crate::Declaration::Defn(alias),
            &[],
            options,
            engine_limits,
            crate::source_evaluation::Entry::SourceValue,
        )
        .map_err(DefinitionCompileError::Engine)?;
    let prepared = match prepared {
        Outcome::Complete(prepared) => prepared,
        Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
        Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
    };
    let value_entry = Name::str(name.clone(), "_fln_value");
    let mut module = compile_module(
        &prepared.fir,
        &value_entry,
        limits,
        Some(&signature),
        &mut meter,
    )
    .map_err(DefinitionCompileError::Ir)?;
    module.decls.extend(
        export_source(signature, &value_entry, &mut meter).map_err(DefinitionCompileError::Ir)?,
    );
    module.decls.sort_by(|a, b| a.name().quick_cmp(b.name()));
    validate_module(&module, &meter).map_err(DefinitionCompileError::Ir)?;
    Ok(Outcome::Complete(module))
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
    meter.charge(1).map_err(DefinitionCompileError::Ir)?;
    let signature = match (&declaration, entry) {
        (crate::Declaration::Defn(definition), None) => {
            let mut ingress = engine_limits.ingress;
            ingress.max_nodes = ingress
                .max_nodes
                .min(usize::try_from(meter.0).unwrap_or(usize::MAX));
            let (erasures, work) = crate::runtime::Preparation::new(engine.environment(), ingress)
                .source_parameter_erasures(&definition.base.type_)
                .map_err(|error| {
                    DefinitionCompileError::Engine(crate::EngineExecutionError::Ingress(error))
                })?;
            meter.charge(work).map_err(DefinitionCompileError::Ir)?;
            Some(
                source_signature(
                    definition,
                    &erasures,
                    engine.environment(),
                    ingress,
                    &mut meter,
                )
                .map_err(DefinitionCompileError::Ir)?,
            )
        }
        _ => None,
    };
    let prepared = engine
        .prepare_definition_entry_with_helpers(
            declaration,
            &[],
            options,
            engine_limits,
            if signature.is_some() {
                crate::source_evaluation::Entry::SourceValue
            } else {
                crate::source_evaluation::Entry::Value
            },
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
            let mut module = compile_module(
                &prepared.fir,
                &value_entry,
                limits,
                signature.as_ref(),
                &mut meter,
            )
            .map_err(DefinitionCompileError::Ir)?;
            if let Some(signature) = signature {
                module.decls.extend(
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

#[cfg(test)]
mod recursion_tests;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn compiler_expands_shared_control_flow_and_refuses_cycles() {
        use fir::{Binding, Block, BlockId, FunctionId, Operation, Terminator, ValueId, ValueType};
        let block = BlockId::new;
        let value = ValueId::new;
        let mut program = fir::Program::new(
            FunctionId::new(0),
            vec![],
            vec![],
            vec![],
            vec![
                fir::Function {
                    id: FunctionId::new(0),
                    parameters: vec![],
                    parameter_ownership: vec![],
                    result: ValueType::String,
                    result_ownership: flbc::CallableResultOwnership::Owned,
                    blocks: vec![Block {
                        id: block(0),
                        bindings: vec![
                            Binding {
                                id: value(0),
                                ty: ValueType::Nat,
                                operation: Operation::Nat(0),
                            },
                            Binding {
                                id: value(1),
                                ty: ValueType::String,
                                operation: Operation::Call {
                                    function: FunctionId::new(1),
                                    args: vec![value(0)],
                                },
                            },
                        ],
                        terminator: Terminator::Return { value: value(1) },
                    }],
                },
                fir::Function {
                    id: FunctionId::new(1),
                    // Keep the shared-tail condition dynamic in this function;
                    // a literal in the entry would be folded before either arm.
                    parameters: vec![ValueType::Nat],
                    parameter_ownership: vec![flbc::ArgumentOwnership::Borrowed],
                    result: ValueType::String,
                    result_ownership: flbc::CallableResultOwnership::Owned,
                    blocks: vec![
                        Block {
                            id: block(0),
                            bindings: vec![Binding {
                                id: value(1),
                                ty: ValueType::String,
                                operation: Operation::String("owned across both arms".into()),
                            }],
                            terminator: Terminator::BranchZero {
                                condition: value(0),
                                zero: block(1),
                                nonzero: block(2),
                            },
                        },
                        Block {
                            id: block(1),
                            bindings: vec![],
                            terminator: Terminator::Jump { target: block(3) },
                        },
                        Block {
                            id: block(2),
                            bindings: vec![],
                            terminator: Terminator::Jump { target: block(3) },
                        },
                        Block {
                            id: block(3),
                            bindings: vec![],
                            terminator: Terminator::Return { value: value(1) },
                        },
                    ],
                },
            ],
        );
        let entry = Name::from_components(["sharedBranch"]);
        let checked = fir::validate(program.clone(), Default::default()).unwrap();
        compile(&checked, &entry, CompileLimits::default()).unwrap();
        assert!(matches!(
            compile(
                &checked,
                &entry,
                CompileLimits {
                    max_work: 8,
                    ..CompileLimits::default()
                }
            ),
            Err(CompileError::Limit)
        ));

        // The same public FIR boundary admits a well-formed nonterminating
        // loop. This backend refuses it instead of recursively expanding it
        // forever or returning a partly compiled artifact.
        program.functions[0].blocks = vec![
            Block {
                id: block(0),
                bindings: vec![],
                terminator: Terminator::Jump { target: block(1) },
            },
            Block {
                id: block(1),
                bindings: vec![],
                terminator: Terminator::Jump { target: block(1) },
            },
        ];
        program.functions.truncate(1);
        let cyclic = fir::validate(program, Default::default()).unwrap();
        assert!(matches!(
            compile(&cyclic, &entry, CompileLimits::default()),
            Err(CompileError::Unsupported {
                what: "cyclic control-flow graph"
            })
        ));
    }

    #[test]
    fn compiler_refuses_forged_native_intrinsic_contracts() {
        use fir::ValueType::{Bool, Nat, String as Text};
        use flbc::ArgumentOwnership::{Borrowed, Owned};
        use flbc::ResultOwnership;
        for (row, arguments, argument_ownership, result, result_ownership) in [
            (
                "extern:Nat.add",
                vec![Nat, Nat],
                vec![Borrowed; 2],
                Nat,
                ResultOwnership::Owned,
            ),
            (
                "extern:Nat.decEq",
                vec![Nat, Nat],
                vec![Borrowed; 2],
                Bool,
                ResultOwnership::Scalar,
            ),
            (
                "extern:Nat.decLe",
                vec![Nat, Nat],
                vec![Borrowed; 2],
                Bool,
                ResultOwnership::Scalar,
            ),
            (
                "extern:Nat.decLt",
                vec![Nat, Nat],
                vec![Borrowed; 2],
                Bool,
                ResultOwnership::Scalar,
            ),
            (
                "extern:String.append",
                vec![Text, Text],
                vec![Owned, Borrowed],
                Text,
                ResultOwnership::Owned,
            ),
            (
                "extern:String.Internal.append",
                vec![Text, Text],
                vec![Owned, Borrowed],
                Text,
                ResultOwnership::Owned,
            ),
            (
                "extern:String.length",
                vec![Text],
                vec![Borrowed],
                Nat,
                ResultOwnership::Owned,
            ),
            (
                "extern:String.Internal.length",
                vec![Text],
                vec![Borrowed],
                Nat,
                ResultOwnership::Owned,
            ),
            (
                "extern:String.utf8ByteSize",
                vec![Text],
                vec![Borrowed],
                Nat,
                ResultOwnership::Owned,
            ),
            (
                "extern:String.decEq",
                vec![Text, Text],
                vec![Borrowed; 2],
                Bool,
                ResultOwnership::Scalar,
            ),
            (
                "extern:String.Internal.isEmpty",
                vec![Text],
                vec![Borrowed],
                Bool,
                ResultOwnership::Owned,
            ),
            (
                "extern:String.Internal.isPrefixOf",
                vec![Text, Text],
                vec![Borrowed; 2],
                Bool,
                ResultOwnership::Owned,
            ),
        ] {
            let valid = fir::IntrinsicDecl {
                id: fir::IntrinsicId::new(0),
                row: row.into(),
                arguments,
                argument_ownership,
                result,
                result_ownership,
                effect: fir::EffectClass::Pure,
            };
            validate_native(&valid, &mut Budget(1_000)).unwrap();
            for changed in 0..5 {
                let mut forged = valid.clone();
                match changed {
                    0 => {
                        forged.arguments[0] = if valid.arguments[0] == Text {
                            Nat
                        } else {
                            Text
                        }
                    }
                    1 => forged.result = if valid.result == Bool { Nat } else { Bool },
                    2 => {
                        forged.argument_ownership[0] = if valid.argument_ownership[0] == Borrowed {
                            Owned
                        } else {
                            Borrowed
                        }
                    }
                    3 => forged.effect = fir::EffectClass::Io,
                    4 => forged.result_ownership = ResultOwnership::Borrowed,
                    _ => unreachable!(),
                }
                assert!(
                    matches!(
                        validate_native(&forged, &mut Budget(1_000)),
                        Err(CompileError::Unsupported { .. })
                    ),
                    "{row}: mutation {changed}"
                );
            }
        }
        for row in ["extern:String.hash", "extern:String.Internal.toArray"] {
            assert!(matches!(
                native_signature(row),
                Err(CompileError::Unsupported {
                    what: "native intrinsic signature"
                })
            ));
        }
    }

    #[test]
    fn export_validation_refuses_zero_variables_and_accepts_the_one_based_control() {
        let mut module = IrModule {
            decls: vec![IrDecl::Function {
                name: Name::str(Name::anonymous(), "exported"),
                params: vec![IrParam {
                    x: 0,
                    borrow: false,
                    ty: IrType::TObject,
                }],
                result: IrType::TObject,
                body: IrBody {
                    stmts: vec![],
                    terminal: Box::new(IrTerminal::Ret(IrArg::Var(0))),
                },
                sorry_dep: None,
            }],
            ..IrModule::default()
        };
        let failure = validate_module(&module, &Budget(1_000)).unwrap_err();
        assert!(matches!(
            failure,
            CompileError::Validation(fln_olean::ir_types::IrTypeValidationError::Structural(
                fln_olean::ir_validate::IrValidationError {
                    kind: fln_olean::ir_validate::IrValidationErrorKind::ZeroVariableIndex,
                    ..
                }
            ))
        ));
        let IrDecl::Function { params, body, .. } = &mut module.decls[0] else {
            unreachable!()
        };
        params[0].x = 1;
        *body.terminal = IrTerminal::Ret(IrArg::Var(1));
        validate_module(&module, &Budget(1_000)).unwrap();
    }
}
