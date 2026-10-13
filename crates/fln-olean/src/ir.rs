//! Data-only decoding of the pinned IR declarations stored in a module's `.ir`
//! file (bead `fln-ir-decoder-call-graph-sjzl`).
//!
//! The pin writes a module's compiled code beside its `.olean` as a second
//! `ModuleData` whose extension entries hold one `Lean.IR.Decl` per compiled
//! declaration (`exportIREntries`, vendored `src/Lean/Compiler/IR/CompilerM.lean`).
//! The container is the ordinary compacted region the `.olean` reader already
//! opens; this module interprets the `Lean.IR.declMapExt` entries.
//!
//! Constructor tags and field slots come from the generated [`crate::ir_format`]
//! (`scripts/extract/gen_ir_contract.py`), never from a hand-written table.
//!
//! Decoding grants no authority and executes nothing. It does not show that
//! Golem can run a declaration, and it takes no position on whether it may.
use crate::ir_format as format;
use crate::region::OpaqueExtensionBlock;
use fln_core::name::Name;
use fln_rt::convert::{Conversion, ConvertError};
use fln_rt::obj::Obj;
use fln_rt::region::{RegionFault, audit, materialize};
use std::collections::BTreeSet;

pub mod graph;

/// A variable or join-point index (`VarId.idx`, `JoinPointId.idx`).
pub type IrIndex = u64;

/// A `Nat` in a literal: the pin stores small ones boxed and large ones as limbs.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IrNat {
    Small(u64),
    /// Little-endian 64-bit limbs of a value that does not fit one word.
    Big(Vec<u64>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IrType {
    Float,
    UInt8,
    UInt16,
    UInt32,
    UInt64,
    USize,
    Erased,
    Object,
    TObject,
    Float32,
    Struct {
        lean_type: Option<Name>,
        types: Vec<IrType>,
    },
    Union {
        lean_type: Name,
        types: Vec<IrType>,
    },
    Tagged,
    Void,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IrArg {
    Var(IrIndex),
    Erased,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IrLit {
    Num(IrNat),
    Str(String),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IrCtorInfo {
    pub name: Name,
    pub cidx: u64,
    pub size: u64,
    pub usize: u64,
    pub ssize: u64,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IrExpr {
    Ctor {
        info: IrCtorInfo,
        args: Vec<IrArg>,
    },
    Reset {
        n: u64,
        x: IrIndex,
    },
    Reuse {
        x: IrIndex,
        info: IrCtorInfo,
        update_header: bool,
        args: Vec<IrArg>,
    },
    Proj {
        i: u64,
        x: IrIndex,
    },
    UProj {
        i: u64,
        x: IrIndex,
    },
    SProj {
        n: u64,
        offset: u64,
        x: IrIndex,
    },
    Fap {
        function: Name,
        args: Vec<IrArg>,
    },
    Pap {
        function: Name,
        args: Vec<IrArg>,
    },
    Ap {
        x: IrIndex,
        args: Vec<IrArg>,
    },
    Box {
        ty: IrType,
        x: IrIndex,
    },
    Unbox {
        x: IrIndex,
    },
    Lit(IrLit),
    IsShared {
        x: IrIndex,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IrParam {
    pub x: IrIndex,
    pub borrow: bool,
    pub ty: IrType,
}

/// One non-terminal instruction of a body, in order.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IrStmt {
    VDecl {
        x: IrIndex,
        ty: IrType,
        expr: IrExpr,
    },
    /// A join point: `value` is its body; the enclosing body continues after it.
    JDecl {
        j: IrIndex,
        params: Vec<IrParam>,
        value: IrBody,
    },
    Set {
        x: IrIndex,
        i: u64,
        y: IrArg,
    },
    SetTag {
        x: IrIndex,
        cidx: u64,
    },
    USet {
        x: IrIndex,
        i: u64,
        y: IrIndex,
    },
    SSet {
        x: IrIndex,
        i: u64,
        offset: u64,
        y: IrIndex,
        ty: IrType,
    },
    Inc {
        x: IrIndex,
        n: u64,
        checked: bool,
        persistent: bool,
    },
    Dec {
        x: IrIndex,
        n: u64,
        checked: bool,
        persistent: bool,
    },
    Del {
        x: IrIndex,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IrAlt {
    Ctor { info: IrCtorInfo, body: IrBody },
    Default { body: IrBody },
}

/// How a body ends.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IrTerminal {
    Case {
        type_name: Name,
        x: IrIndex,
        x_type: IrType,
        alts: Vec<IrAlt>,
    },
    Ret(IrArg),
    Jmp {
        j: IrIndex,
        args: Vec<IrArg>,
    },
    Unreachable,
}

/// A function body. The pin's `FnBody` is a chain in which every instruction
/// holds the rest of the body; it is flattened here so that a body of a hundred
/// thousand instructions does not need a hundred thousand host stack frames.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IrBody {
    pub stmts: Vec<IrStmt>,
    pub terminal: Box<IrTerminal>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IrExternEntry {
    Adhoc { backend: Name },
    Inline { backend: Name, pattern: String },
    Standard { backend: Name, function: String },
    Opaque,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IrDecl {
    Function {
        name: Name,
        params: Vec<IrParam>,
        result: IrType,
        body: IrBody,
        /// `DeclInfo.sorryDep?`.
        sorry_dep: Option<Name>,
    },
    Extern {
        name: Name,
        params: Vec<IrParam>,
        result: IrType,
        entries: Vec<IrExternEntry>,
    },
}

impl IrBody {
    /// This body and every body nested in it (join-point values and `case`
    /// arms), outermost first. Iterative: nesting depth costs no host stack.
    pub fn bodies(&self) -> Vec<&IrBody> {
        let mut out = Vec::new();
        let mut pending = vec![self];
        while let Some(body) = pending.pop() {
            out.push(body);
            for stmt in &body.stmts {
                if let IrStmt::JDecl { value, .. } = stmt {
                    pending.push(value);
                }
            }
            if let IrTerminal::Case { alts, .. } = body.terminal.as_ref() {
                for alt in alts {
                    match alt {
                        IrAlt::Ctor { body, .. } | IrAlt::Default { body } => pending.push(body),
                    }
                }
            }
        }
        out
    }
}

impl IrDecl {
    pub fn name(&self) -> &Name {
        match self {
            Self::Function { name, .. } | Self::Extern { name, .. } => name,
        }
    }

    /// Every declaration this one names: a full application (`fap`) or a
    /// partial one (`pap`), anywhere in its body. The IR is first-order, so
    /// these are all of its static call edges; a call through a closure value
    /// (`ap`) names no declaration and is not an edge. An extern has none.
    pub fn callees(&self) -> BTreeSet<&Name> {
        let mut out = BTreeSet::new();
        let Self::Function { body, .. } = self else {
            return out;
        };
        for nested in body.bodies() {
            for stmt in &nested.stmts {
                if let IrStmt::VDecl {
                    expr: IrExpr::Fap { function, .. } | IrExpr::Pap { function, .. },
                    ..
                } = stmt
                {
                    out.insert(function);
                }
            }
        }
        out
    }
}

/// The IR declarations of one module, in the pin's stored (name-sorted) order.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct IrModule {
    pub decls: Vec<IrDecl>,
    /// Extension blocks of the `.ir` file this decoder does not interpret
    /// (the initializer and package tables), by name, with entries present.
    pub uninterpreted: Vec<Name>,
}

#[derive(Debug, Clone, Copy)]
pub struct IrDecodeLimits {
    pub max_bytes: usize,
    pub max_objects: u64,
    pub max_decls: usize,
    /// Decoded IR nodes (types, expressions, instructions, arguments) in total.
    pub max_nodes: u64,
    /// Nesting of join-point bodies, `case` arms and aggregate types.
    pub max_depth: u32,
}

impl Default for IrDecodeLimits {
    fn default() -> Self {
        Self {
            max_bytes: 256 * 1024 * 1024,
            max_objects: 16_000_000,
            max_decls: 1 << 20,
            max_nodes: 64_000_000,
            max_depth: 512,
        }
    }
}

#[derive(Debug)]
pub enum IrDecodeError {
    Limit { resource: &'static str },
    Shape { detail: &'static str },
    Region(RegionFault),
    Conversion(ConvertError),
}

impl std::fmt::Display for IrDecodeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "IR decode: {self:?}")
    }
}

impl std::error::Error for IrDecodeError {}

impl IrDecodeError {
    pub fn is_resource(&self) -> bool {
        matches!(
            self,
            Self::Limit { .. }
                | Self::Conversion(ConvertError::NodeBudgetExhausted { .. })
                | Self::Conversion(ConvertError::NativeOverflow { .. })
        )
    }
}

type R<T> = Result<T, IrDecodeError>;

fn shape(detail: &'static str) -> IrDecodeError {
    IrDecodeError::Shape { detail }
}

fn limit(resource: &'static str) -> IrDecodeError {
    IrDecodeError::Limit { resource }
}

/// The constructor tag of a constructor object, or of a boxed field-less one.
fn tag_of(obj: &Obj) -> R<u8> {
    u8::try_from(obj.obj_tag()).map_err(|_| shape("constructor tag out of range"))
}

/// Require a constructor object with exactly `pointers` object fields.
fn fields(obj: &Obj, pointers: usize) -> R<()> {
    if obj.is_scalar() || usize::from(obj.header().other) != pointers {
        return Err(shape("unexpected object-field count"));
    }
    Ok(())
}

fn field(obj: &Obj, index: usize) -> R<Obj> {
    obj.try_ctor_child(index)
        .ok_or_else(|| shape("missing constructor field"))
}

/// One of a constructor's scalar bytes, which follow its `pointers` fields.
fn scalar_byte(obj: &Obj, pointers: usize, index: usize) -> R<u8> {
    let word = obj
        .try_ctor_scalar_u64(pointers * 8)
        .ok_or_else(|| shape("missing scalar storage"))?;
    word.to_le_bytes()
        .get(index)
        .copied()
        .ok_or_else(|| shape("scalar byte outside the first word"))
}

fn boolean(byte: u8) -> R<bool> {
    match byte {
        0 => Ok(false),
        1 => Ok(true),
        _ => Err(shape("Bool scalar is neither 0 nor 1")),
    }
}

fn nat(obj: &Obj) -> R<IrNat> {
    if obj.is_scalar() {
        return Ok(IrNat::Small(obj.unbox() as u64));
    }
    let Some((_, sign, limbs)) = obj.try_mpz_view() else {
        return Err(shape("expected a Nat"));
    };
    if sign < 0 {
        return Err(shape("negative Nat"));
    }
    match limbs {
        [] => Ok(IrNat::Small(0)),
        [value] => Ok(IrNat::Small(*value)),
        many => Ok(IrNat::Big(many.to_vec())),
    }
}

fn word(obj: &Obj) -> R<u64> {
    match nat(obj)? {
        IrNat::Small(value) => Ok(value),
        IrNat::Big(_) => Err(limit("index or size exceeds one word")),
    }
}

fn string(obj: &Obj) -> R<String> {
    let Some((size, _, _, bytes)) = obj.try_string_view() else {
        return Err(shape("expected a String"));
    };
    String::from_utf8(bytes[..size - 1].to_vec()).map_err(|_| shape("String is not UTF-8"))
}

struct Reader {
    conversion: Conversion,
    nodes_left: u64,
    max_depth: u32,
}

impl Reader {
    fn node(&mut self) -> R<()> {
        self.nodes_left = self
            .nodes_left
            .checked_sub(1)
            .ok_or_else(|| limit("IR nodes"))?;
        Ok(())
    }

    fn deeper(&self, depth: u32) -> R<u32> {
        if depth >= self.max_depth {
            return Err(limit("IR nesting depth"));
        }
        Ok(depth + 1)
    }

    fn name(&mut self, obj: &Obj) -> R<Name> {
        self.conversion
            .project_name(obj)
            .map_err(IrDecodeError::Conversion)
    }

    fn array<T>(&mut self, obj: &Obj, mut each: impl FnMut(&mut Self, &Obj) -> R<T>) -> R<Vec<T>> {
        let Some((size, _)) = obj.try_array_view() else {
            return Err(shape("expected an Array"));
        };
        self.nodes_left = self
            .nodes_left
            .checked_sub(size as u64)
            .ok_or_else(|| limit("IR nodes"))?;
        let mut out = Vec::new();
        out.try_reserve_exact(size)
            .map_err(|_| limit("array allocation"))?;
        for index in 0..size {
            out.push(each(self, &obj.array_child(index))?);
        }
        Ok(out)
    }

    fn option_name(&mut self, obj: &Obj) -> R<Option<Name>> {
        if obj.is_scalar() {
            return match obj.unbox() {
                0 => Ok(None),
                _ => Err(shape("unknown field-less Option constructor")),
            };
        }
        if tag_of(obj)? != 1 {
            return Err(shape("unknown Option constructor"));
        }
        fields(obj, 1)?;
        Ok(Some(self.name(&field(obj, 0)?)?))
    }

    fn ty(&mut self, obj: &Obj, depth: u32) -> R<IrType> {
        self.node()?;
        let tag = tag_of(obj)?;
        if obj.is_scalar() {
            return match tag {
                format::IR_TYPE_FLOAT => Ok(IrType::Float),
                format::IR_TYPE_UINT8 => Ok(IrType::UInt8),
                format::IR_TYPE_UINT16 => Ok(IrType::UInt16),
                format::IR_TYPE_UINT32 => Ok(IrType::UInt32),
                format::IR_TYPE_UINT64 => Ok(IrType::UInt64),
                format::IR_TYPE_USIZE => Ok(IrType::USize),
                format::IR_TYPE_ERASED => Ok(IrType::Erased),
                format::IR_TYPE_OBJECT => Ok(IrType::Object),
                format::IR_TYPE_TOBJECT => Ok(IrType::TObject),
                format::IR_TYPE_FLOAT32 => Ok(IrType::Float32),
                format::IR_TYPE_TAGGED => Ok(IrType::Tagged),
                format::IR_TYPE_VOID => Ok(IrType::Void),
                _ => Err(shape("unknown field-less IRType")),
            };
        }
        let depth = self.deeper(depth)?;
        match tag {
            format::IR_TYPE_STRUCT => {
                fields(obj, format::IR_TYPE_STRUCT_POINTERS)?;
                let lean_type =
                    self.option_name(&field(obj, format::IR_TYPE_STRUCT_LEAN_TYPE_NAME)?)?;
                let types = self.array(&field(obj, format::IR_TYPE_STRUCT_TYPES)?, |r, o| {
                    r.ty(o, depth)
                })?;
                Ok(IrType::Struct { lean_type, types })
            }
            format::IR_TYPE_UNION => {
                fields(obj, format::IR_TYPE_UNION_POINTERS)?;
                let lean_type = self.name(&field(obj, format::IR_TYPE_UNION_LEAN_TYPE_NAME)?)?;
                let types = self.array(&field(obj, format::IR_TYPE_UNION_TYPES)?, |r, o| {
                    r.ty(o, depth)
                })?;
                Ok(IrType::Union { lean_type, types })
            }
            _ => Err(shape("unknown IRType constructor")),
        }
    }

    fn arg(&mut self, obj: &Obj) -> R<IrArg> {
        let tag = tag_of(obj)?;
        if obj.is_scalar() {
            return match tag {
                format::ARG_ERASED => Ok(IrArg::Erased),
                _ => Err(shape("unknown field-less Arg")),
            };
        }
        match tag {
            format::ARG_VAR => {
                fields(obj, format::ARG_VAR_POINTERS)?;
                Ok(IrArg::Var(word(&field(obj, format::ARG_VAR_ID)?)?))
            }
            _ => Err(shape("unknown Arg constructor")),
        }
    }

    fn args(&mut self, obj: &Obj) -> R<Vec<IrArg>> {
        self.array(obj, |r, o| r.arg(o))
    }

    fn ctor_info(&mut self, obj: &Obj) -> R<IrCtorInfo> {
        self.node()?;
        if tag_of(obj)? != 0 {
            return Err(shape("unknown CtorInfo constructor"));
        }
        fields(obj, format::CTOR_INFO_POINTERS)?;
        Ok(IrCtorInfo {
            name: self.name(&field(obj, format::CTOR_INFO_NAME)?)?,
            cidx: word(&field(obj, format::CTOR_INFO_CIDX)?)?,
            size: word(&field(obj, format::CTOR_INFO_SIZE)?)?,
            usize: word(&field(obj, format::CTOR_INFO_USIZE)?)?,
            ssize: word(&field(obj, format::CTOR_INFO_SSIZE)?)?,
        })
    }

    fn lit(&mut self, obj: &Obj) -> R<IrLit> {
        if obj.is_scalar() {
            return Err(shape("field-less LitVal"));
        }
        match tag_of(obj)? {
            format::LIT_NUM => {
                fields(obj, format::LIT_NUM_POINTERS)?;
                Ok(IrLit::Num(nat(&field(obj, format::LIT_NUM_V)?)?))
            }
            format::LIT_STR => {
                fields(obj, format::LIT_STR_POINTERS)?;
                Ok(IrLit::Str(string(&field(obj, format::LIT_STR_V)?)?))
            }
            _ => Err(shape("unknown LitVal constructor")),
        }
    }

    fn expr(&mut self, obj: &Obj) -> R<IrExpr> {
        self.node()?;
        if obj.is_scalar() {
            return Err(shape("field-less Expr"));
        }
        let var = |o: &Obj, i: usize| -> R<IrIndex> { word(&field(o, i)?) };
        match tag_of(obj)? {
            format::EXPR_CTOR => {
                fields(obj, format::EXPR_CTOR_POINTERS)?;
                Ok(IrExpr::Ctor {
                    info: self.ctor_info(&field(obj, format::EXPR_CTOR_I)?)?,
                    args: self.args(&field(obj, format::EXPR_CTOR_YS)?)?,
                })
            }
            format::EXPR_RESET => {
                fields(obj, format::EXPR_RESET_POINTERS)?;
                Ok(IrExpr::Reset {
                    n: var(obj, format::EXPR_RESET_N)?,
                    x: var(obj, format::EXPR_RESET_X)?,
                })
            }
            format::EXPR_REUSE => {
                fields(obj, format::EXPR_REUSE_POINTERS)?;
                Ok(IrExpr::Reuse {
                    x: var(obj, format::EXPR_REUSE_X)?,
                    info: self.ctor_info(&field(obj, format::EXPR_REUSE_I)?)?,
                    update_header: boolean(scalar_byte(
                        obj,
                        format::EXPR_REUSE_POINTERS,
                        format::EXPR_REUSE_UPDT_HEADER_SCALAR,
                    )?)?,
                    args: self.args(&field(obj, format::EXPR_REUSE_YS)?)?,
                })
            }
            format::EXPR_PROJ => {
                fields(obj, format::EXPR_PROJ_POINTERS)?;
                Ok(IrExpr::Proj {
                    i: var(obj, format::EXPR_PROJ_I)?,
                    x: var(obj, format::EXPR_PROJ_X)?,
                })
            }
            format::EXPR_UPROJ => {
                fields(obj, format::EXPR_UPROJ_POINTERS)?;
                Ok(IrExpr::UProj {
                    i: var(obj, format::EXPR_UPROJ_I)?,
                    x: var(obj, format::EXPR_UPROJ_X)?,
                })
            }
            format::EXPR_SPROJ => {
                fields(obj, format::EXPR_SPROJ_POINTERS)?;
                Ok(IrExpr::SProj {
                    n: var(obj, format::EXPR_SPROJ_N)?,
                    offset: var(obj, format::EXPR_SPROJ_OFFSET)?,
                    x: var(obj, format::EXPR_SPROJ_X)?,
                })
            }
            format::EXPR_FAP => {
                fields(obj, format::EXPR_FAP_POINTERS)?;
                Ok(IrExpr::Fap {
                    function: self.name(&field(obj, format::EXPR_FAP_C)?)?,
                    args: self.args(&field(obj, format::EXPR_FAP_YS)?)?,
                })
            }
            format::EXPR_PAP => {
                fields(obj, format::EXPR_PAP_POINTERS)?;
                Ok(IrExpr::Pap {
                    function: self.name(&field(obj, format::EXPR_PAP_C)?)?,
                    args: self.args(&field(obj, format::EXPR_PAP_YS)?)?,
                })
            }
            format::EXPR_AP => {
                fields(obj, format::EXPR_AP_POINTERS)?;
                Ok(IrExpr::Ap {
                    x: var(obj, format::EXPR_AP_X)?,
                    args: self.args(&field(obj, format::EXPR_AP_YS)?)?,
                })
            }
            format::EXPR_BOX => {
                fields(obj, format::EXPR_BOX_POINTERS)?;
                Ok(IrExpr::Box {
                    ty: self.ty(&field(obj, format::EXPR_BOX_TY)?, 0)?,
                    x: var(obj, format::EXPR_BOX_X)?,
                })
            }
            format::EXPR_UNBOX => {
                fields(obj, format::EXPR_UNBOX_POINTERS)?;
                Ok(IrExpr::Unbox {
                    x: var(obj, format::EXPR_UNBOX_X)?,
                })
            }
            format::EXPR_LIT => {
                fields(obj, format::EXPR_LIT_POINTERS)?;
                Ok(IrExpr::Lit(self.lit(&field(obj, format::EXPR_LIT_V)?)?))
            }
            format::EXPR_IS_SHARED => {
                fields(obj, format::EXPR_IS_SHARED_POINTERS)?;
                Ok(IrExpr::IsShared {
                    x: var(obj, format::EXPR_IS_SHARED_X)?,
                })
            }
            _ => Err(shape("unknown Expr constructor")),
        }
    }

    fn param(&mut self, obj: &Obj) -> R<IrParam> {
        if tag_of(obj)? != 0 {
            return Err(shape("unknown Param constructor"));
        }
        fields(obj, format::PARAM_POINTERS)?;
        Ok(IrParam {
            x: word(&field(obj, format::PARAM_X)?)?,
            borrow: boolean(scalar_byte(
                obj,
                format::PARAM_POINTERS,
                format::PARAM_BORROW_SCALAR,
            )?)?,
            ty: self.ty(&field(obj, format::PARAM_TY)?, 0)?,
        })
    }

    fn params(&mut self, obj: &Obj) -> R<Vec<IrParam>> {
        self.array(obj, |r, o| r.param(o))
    }

    fn alt(&mut self, obj: &Obj, depth: u32) -> R<IrAlt> {
        self.node()?;
        if obj.is_scalar() {
            return Err(shape("field-less Alt"));
        }
        match tag_of(obj)? {
            format::ALT_CTOR => {
                fields(obj, format::ALT_CTOR_POINTERS)?;
                Ok(IrAlt::Ctor {
                    info: self.ctor_info(&field(obj, format::ALT_CTOR_INFO)?)?,
                    body: self.body(field(obj, format::ALT_CTOR_B)?, depth)?,
                })
            }
            format::ALT_DEFAULT => {
                fields(obj, format::ALT_DEFAULT_POINTERS)?;
                Ok(IrAlt::Default {
                    body: self.body(field(obj, format::ALT_DEFAULT_B)?, depth)?,
                })
            }
            _ => Err(shape("unknown Alt constructor")),
        }
    }

    /// Decode a body. The chain of instructions is walked in a loop; only a
    /// join point's own body and a `case`'s arms recurse, under `max_depth`.
    fn body(&mut self, mut obj: Obj, depth: u32) -> R<IrBody> {
        let depth = self.deeper(depth)?;
        let mut stmts = Vec::new();
        loop {
            self.node()?;
            let tag = tag_of(&obj)?;
            if obj.is_scalar() {
                return match tag {
                    format::BODY_UNREACHABLE => Ok(IrBody {
                        stmts,
                        terminal: Box::new(IrTerminal::Unreachable),
                    }),
                    _ => Err(shape("unknown field-less FnBody")),
                };
            }
            let var = |o: &Obj, i: usize| -> R<IrIndex> { word(&field(o, i)?) };
            let next = match tag {
                format::BODY_VDECL => {
                    fields(&obj, format::BODY_VDECL_POINTERS)?;
                    stmts.push(IrStmt::VDecl {
                        x: var(&obj, format::BODY_VDECL_X)?,
                        ty: self.ty(&field(&obj, format::BODY_VDECL_TY)?, 0)?,
                        expr: self.expr(&field(&obj, format::BODY_VDECL_E)?)?,
                    });
                    field(&obj, format::BODY_VDECL_B)?
                }
                format::BODY_JDECL => {
                    fields(&obj, format::BODY_JDECL_POINTERS)?;
                    stmts.push(IrStmt::JDecl {
                        j: var(&obj, format::BODY_JDECL_J)?,
                        params: self.params(&field(&obj, format::BODY_JDECL_XS)?)?,
                        value: self.body(field(&obj, format::BODY_JDECL_V)?, depth)?,
                    });
                    field(&obj, format::BODY_JDECL_B)?
                }
                format::BODY_SET => {
                    fields(&obj, format::BODY_SET_POINTERS)?;
                    stmts.push(IrStmt::Set {
                        x: var(&obj, format::BODY_SET_X)?,
                        i: var(&obj, format::BODY_SET_I)?,
                        y: self.arg(&field(&obj, format::BODY_SET_Y)?)?,
                    });
                    field(&obj, format::BODY_SET_B)?
                }
                format::BODY_SET_TAG => {
                    fields(&obj, format::BODY_SET_TAG_POINTERS)?;
                    stmts.push(IrStmt::SetTag {
                        x: var(&obj, format::BODY_SET_TAG_X)?,
                        cidx: var(&obj, format::BODY_SET_TAG_CIDX)?,
                    });
                    field(&obj, format::BODY_SET_TAG_B)?
                }
                format::BODY_USET => {
                    fields(&obj, format::BODY_USET_POINTERS)?;
                    stmts.push(IrStmt::USet {
                        x: var(&obj, format::BODY_USET_X)?,
                        i: var(&obj, format::BODY_USET_I)?,
                        y: var(&obj, format::BODY_USET_Y)?,
                    });
                    field(&obj, format::BODY_USET_B)?
                }
                format::BODY_SSET => {
                    fields(&obj, format::BODY_SSET_POINTERS)?;
                    stmts.push(IrStmt::SSet {
                        x: var(&obj, format::BODY_SSET_X)?,
                        i: var(&obj, format::BODY_SSET_I)?,
                        offset: var(&obj, format::BODY_SSET_OFFSET)?,
                        y: var(&obj, format::BODY_SSET_Y)?,
                        ty: self.ty(&field(&obj, format::BODY_SSET_TY)?, 0)?,
                    });
                    field(&obj, format::BODY_SSET_B)?
                }
                format::BODY_INC => {
                    fields(&obj, format::BODY_INC_POINTERS)?;
                    stmts.push(IrStmt::Inc {
                        x: var(&obj, format::BODY_INC_X)?,
                        n: var(&obj, format::BODY_INC_N)?,
                        checked: boolean(scalar_byte(
                            &obj,
                            format::BODY_INC_POINTERS,
                            format::BODY_INC_C_SCALAR,
                        )?)?,
                        persistent: boolean(scalar_byte(
                            &obj,
                            format::BODY_INC_POINTERS,
                            format::BODY_INC_PERSISTENT_SCALAR,
                        )?)?,
                    });
                    field(&obj, format::BODY_INC_B)?
                }
                format::BODY_DEC => {
                    fields(&obj, format::BODY_DEC_POINTERS)?;
                    stmts.push(IrStmt::Dec {
                        x: var(&obj, format::BODY_DEC_X)?,
                        n: var(&obj, format::BODY_DEC_N)?,
                        checked: boolean(scalar_byte(
                            &obj,
                            format::BODY_DEC_POINTERS,
                            format::BODY_DEC_C_SCALAR,
                        )?)?,
                        persistent: boolean(scalar_byte(
                            &obj,
                            format::BODY_DEC_POINTERS,
                            format::BODY_DEC_PERSISTENT_SCALAR,
                        )?)?,
                    });
                    field(&obj, format::BODY_DEC_B)?
                }
                format::BODY_DEL => {
                    fields(&obj, format::BODY_DEL_POINTERS)?;
                    stmts.push(IrStmt::Del {
                        x: var(&obj, format::BODY_DEL_X)?,
                    });
                    field(&obj, format::BODY_DEL_B)?
                }
                format::BODY_CASE => {
                    fields(&obj, format::BODY_CASE_POINTERS)?;
                    let terminal = IrTerminal::Case {
                        type_name: self.name(&field(&obj, format::BODY_CASE_TID)?)?,
                        x: var(&obj, format::BODY_CASE_X)?,
                        x_type: self.ty(&field(&obj, format::BODY_CASE_X_TYPE)?, 0)?,
                        alts: self
                            .array(&field(&obj, format::BODY_CASE_CS)?, |r, o| r.alt(o, depth))?,
                    };
                    return Ok(IrBody {
                        stmts,
                        terminal: Box::new(terminal),
                    });
                }
                format::BODY_RET => {
                    fields(&obj, format::BODY_RET_POINTERS)?;
                    let terminal = IrTerminal::Ret(self.arg(&field(&obj, format::BODY_RET_X)?)?);
                    return Ok(IrBody {
                        stmts,
                        terminal: Box::new(terminal),
                    });
                }
                format::BODY_JMP => {
                    fields(&obj, format::BODY_JMP_POINTERS)?;
                    let terminal = IrTerminal::Jmp {
                        j: var(&obj, format::BODY_JMP_J)?,
                        args: self.args(&field(&obj, format::BODY_JMP_YS)?)?,
                    };
                    return Ok(IrBody {
                        stmts,
                        terminal: Box::new(terminal),
                    });
                }
                _ => return Err(shape("unknown FnBody constructor")),
            };
            obj = next;
        }
    }

    fn extern_entry(&mut self, obj: &Obj) -> R<IrExternEntry> {
        self.node()?;
        let tag = tag_of(obj)?;
        if obj.is_scalar() {
            return match tag {
                format::EXTERN_ENTRY_OPAQUE => Ok(IrExternEntry::Opaque),
                _ => Err(shape("unknown field-less ExternEntry")),
            };
        }
        match tag {
            format::EXTERN_ENTRY_ADHOC => {
                fields(obj, format::EXTERN_ENTRY_ADHOC_POINTERS)?;
                Ok(IrExternEntry::Adhoc {
                    backend: self.name(&field(obj, format::EXTERN_ENTRY_ADHOC_BACKEND)?)?,
                })
            }
            format::EXTERN_ENTRY_INLINE => {
                fields(obj, format::EXTERN_ENTRY_INLINE_POINTERS)?;
                Ok(IrExternEntry::Inline {
                    backend: self.name(&field(obj, format::EXTERN_ENTRY_INLINE_BACKEND)?)?,
                    pattern: string(&field(obj, format::EXTERN_ENTRY_INLINE_PATTERN)?)?,
                })
            }
            format::EXTERN_ENTRY_STANDARD => {
                fields(obj, format::EXTERN_ENTRY_STANDARD_POINTERS)?;
                Ok(IrExternEntry::Standard {
                    backend: self.name(&field(obj, format::EXTERN_ENTRY_STANDARD_BACKEND)?)?,
                    function: string(&field(obj, format::EXTERN_ENTRY_STANDARD_FN)?)?,
                })
            }
            _ => Err(shape("unknown ExternEntry constructor")),
        }
    }

    /// `List ExternEntry`: `nil` is the boxed tag 0, `cons` is tag 1 with two fields.
    fn extern_entries(&mut self, obj: &Obj) -> R<Vec<IrExternEntry>> {
        let mut out = Vec::new();
        let mut cursor = obj.clone_ref();
        loop {
            if cursor.is_scalar() {
                return match cursor.unbox() {
                    0 => Ok(out),
                    _ => Err(shape("unknown field-less List constructor")),
                };
            }
            if tag_of(&cursor)? != 1 {
                return Err(shape("unknown List constructor"));
            }
            fields(&cursor, 2)?;
            out.push(self.extern_entry(&field(&cursor, 0)?)?);
            cursor = field(&cursor, 1)?;
        }
    }

    fn decl(&mut self, obj: &Obj) -> R<IrDecl> {
        self.node()?;
        if obj.is_scalar() {
            return Err(shape("field-less Decl"));
        }
        match tag_of(obj)? {
            format::DECL_FDECL => {
                fields(obj, format::DECL_FDECL_POINTERS)?;
                Ok(IrDecl::Function {
                    name: self.name(&field(obj, format::DECL_FDECL_F)?)?,
                    params: self.params(&field(obj, format::DECL_FDECL_XS)?)?,
                    result: self.ty(&field(obj, format::DECL_FDECL_TYPE)?, 0)?,
                    body: self.body(field(obj, format::DECL_FDECL_BODY)?, 0)?,
                    // `DeclInfo` has one field, so the pin stores that field itself.
                    sorry_dep: self.option_name(&field(obj, format::DECL_FDECL_INFO)?)?,
                })
            }
            format::DECL_EXTERN => {
                fields(obj, format::DECL_EXTERN_POINTERS)?;
                Ok(IrDecl::Extern {
                    name: self.name(&field(obj, format::DECL_EXTERN_F)?)?,
                    params: self.params(&field(obj, format::DECL_EXTERN_XS)?)?,
                    result: self.ty(&field(obj, format::DECL_EXTERN_TYPE)?, 0)?,
                    // `ExternAttrData` has one field, so the pin stores that field itself.
                    entries: self.extern_entries(&field(obj, format::DECL_EXTERN_EXT)?)?,
                })
            }
            _ => Err(shape("unknown Decl constructor")),
        }
    }
}

/// Decode the IR declarations from the extension blocks of one `.ir` file.
///
/// `blocks` is what [`crate::region::MappedOlean::extension_payloads`] returns
/// for that file. A file with no declaration block, or an empty one, decodes to
/// an empty module. Any other block is named in `uninterpreted`, never read.
pub fn decode_ir(blocks: &[OpaqueExtensionBlock], limits: IrDecodeLimits) -> R<IrModule> {
    let wanted = Name::from_components(format::DECL_MAP_EXTENSION.split('.'));
    let mut reader = Reader {
        conversion: Conversion::new(),
        nodes_left: limits.max_nodes,
        max_depth: limits.max_depth,
    };
    let mut out = IrModule::default();
    let mut seen = false;
    let mut bytes_left = limits.max_bytes;
    let mut objects_left = limits.max_objects;
    for block in blocks {
        if block.name != wanted {
            if !block.entries.is_empty() {
                out.uninterpreted.push(block.name.clone());
            }
            continue;
        }
        if seen {
            return Err(shape("duplicate IR declaration block"));
        }
        seen = true;
        if block.entries.len() > limits.max_decls {
            return Err(limit("IR declarations"));
        }
        out.decls
            .try_reserve_exact(block.entries.len())
            .map_err(|_| limit("declaration allocation"))?;
        for payload in &block.entries {
            bytes_left = bytes_left
                .checked_sub(payload.len())
                .ok_or_else(|| limit("payload bytes"))?;
            let report = audit(payload, 0).map_err(IrDecodeError::Region)?;
            objects_left = objects_left
                .checked_sub(report.objects)
                .ok_or_else(|| limit("objects"))?;
            let obj = materialize(payload, 0).map_err(IrDecodeError::Region)?;
            out.decls.push(reader.decl(&obj)?);
        }
    }
    Ok(out)
}
