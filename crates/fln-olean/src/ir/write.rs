//! Fresh, data-only emission of the pin's IR companion container.
//!
//! This writes supplied native IR; it neither compiles terms nor grants
//! execution authority. The generated contract supplies every IR field slot.
//! Body chains, nested cases, join points and aggregate types are traversed
//! iteratively. One work budget covers the whole input; the existing module
//! writer accounts for the complete output, including additional extensions.

use super::{
    IrAlt, IrArg, IrBody, IrCtorInfo, IrDecl, IrExpr, IrExternEntry, IrLit, IrNat, IrParam, IrStmt,
    IrTerminal, IrType,
};
use crate::extension_write::{Builder, ModuleExtensionInput, encode_module_with_extensions};
use crate::ir_format as format;
use crate::source_extension_format as source;
use crate::write::{EncodedModule, ModuleWriteInput, OleanWriteHeader, WriteBudget, WriteError};
use fln_core::name::Name;
use fln_rt::obj::Obj;
use std::collections::BTreeSet;

/// IR declarations and journals for a fresh companion. `module.constants`
/// must be empty, as in the pin's `mkIRData`. Additional extension graphs are
/// explicit: a decoder's uninterpreted-name inventory cannot reconstruct them.
pub struct IrWriteInput<'a> {
    pub module: ModuleWriteInput<'a>,
    pub declarations: &'a [IrDecl],
    pub initializers: &'a [crate::initializers::InitEntry],
    pub additional_extensions: &'a [ModuleExtensionInput<'a>],
}

#[derive(Debug, Clone, Copy)]
pub struct IrWriteLimits {
    pub max_entries: usize,
    /// Scheduled typed nodes, including scalar operands and array elements.
    pub max_nodes: u64,
    pub container: WriteBudget,
}

impl Default for IrWriteLimits {
    fn default() -> Self {
        Self {
            max_entries: 1 << 20,
            max_nodes: 64_000_000,
            container: WriteBudget::default(),
        }
    }
}

#[derive(Debug)]
pub enum IrWriteError {
    Limit { resource: &'static str },
    Write(WriteError),
}

impl From<WriteError> for IrWriteError {
    fn from(error: WriteError) -> Self {
        Self::Write(error)
    }
}

impl std::fmt::Display for IrWriteError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Limit { resource } => write!(f, "IR writer limit: {resource}"),
            Self::Write(error) => error.fmt(f),
        }
    }
}

impl std::error::Error for IrWriteError {}

type Result<T> = std::result::Result<T, IrWriteError>;

fn contract(what: &'static str) -> IrWriteError {
    WriteError::Contract { what }.into()
}

#[derive(Clone, Copy)]
enum Node<'a> {
    Nat(u64),
    Name(&'a Name),
    String(&'a str),
    OptionName(Option<&'a Name>),
    Type(&'a IrType),
    Types(&'a [IrType]),
    Arg(IrArg),
    Args(&'a [IrArg]),
    Param(&'a IrParam),
    Params(&'a [IrParam]),
    Ctor(&'a IrCtorInfo),
    Expr(&'a IrExpr),
    Lit(&'a IrLit),
    Decl(&'a IrDecl),
    Externs(&'a [IrExternEntry]),
    Extern(&'a IrExternEntry),
    Body(&'a IrBody, usize),
    Terminal(&'a IrTerminal),
    Alts(&'a [IrAlt]),
    Alt(&'a IrAlt),
}

enum Task<'a> {
    Visit(Node<'a>),
    Ctor {
        tag: u8,
        slots: Vec<usize>,
        scalars: Vec<u8>,
    },
    Array(usize),
    List(usize),
}

struct Writer {
    graph: Builder,
    nodes_left: u64,
}

impl Writer {
    fn schedule<'a>(&mut self, stack: &mut Vec<Task<'a>>, node: Node<'a>) -> Result<()> {
        self.nodes_left = self
            .nodes_left
            .checked_sub(1)
            .ok_or(IrWriteError::Limit { resource: "nodes" })?;
        stack.try_reserve(1).map_err(|_| IrWriteError::Limit {
            resource: "work allocation",
        })?;
        stack.push(Task::Visit(node));
        Ok(())
    }

    fn ctor<'a>(
        &mut self,
        stack: &mut Vec<Task<'a>>,
        tag: u8,
        pointers: usize,
        fields: &[(usize, Node<'a>)],
        scalars: &[u8],
    ) -> Result<()> {
        if fields.len() != pointers
            || fields.iter().any(|(i, _)| *i >= pointers)
            || fields.iter().map(|(i, _)| i).collect::<BTreeSet<_>>().len() != pointers
        {
            return Err(contract(
                "IR constructor slots disagree with generated contract",
            ));
        }
        self.charge_object(pointers, scalars.len())?;
        stack.push(Task::Ctor {
            tag,
            slots: fields.iter().map(|(i, _)| *i).collect(),
            scalars: scalars.to_vec(),
        });
        for (_, node) in fields.iter().rev() {
            self.schedule(stack, *node)?;
        }
        Ok(())
    }

    fn array<'a, T>(
        &mut self,
        stack: &mut Vec<Task<'a>>,
        values: &'a [T],
        each: impl Fn(&'a T) -> Node<'a>,
    ) -> Result<()> {
        if values.len() as u64 > self.nodes_left {
            return Err(IrWriteError::Limit { resource: "nodes" });
        }
        let bytes = (values.len() as u64)
            .checked_mul(8)
            .and_then(|n| n.checked_add(24))
            .ok_or_else(|| contract("IR array size overflow"))?;
        self.graph.charge(bytes)?;
        stack.push(Task::Array(values.len()));
        for value in values.iter().rev() {
            self.schedule(stack, each(value))?;
        }
        Ok(())
    }

    fn nat(&mut self, value: u64) -> Result<Obj> {
        if let Ok(small) = usize::try_from(value)
            && small <= usize::MAX >> 1
        {
            Ok(Obj::mk_nat(small))
        } else {
            self.graph.charge(32)?;
            Ok(Obj::mk_mpz(&[value], false))
        }
    }

    fn charge_object(&mut self, pointers: usize, scalars: usize) -> Result<()> {
        let bytes = (pointers as u64)
            .checked_mul(8)
            .and_then(|n| n.checked_add(8))
            .and_then(|n| n.checked_add(scalars as u64))
            .and_then(|n| n.checked_add(7))
            .map(|n| n / 8 * 8)
            .ok_or_else(|| contract("IR object size overflow"))?;
        self.graph.charge(bytes)?;
        Ok(())
    }

    fn object(&mut self, tag: u8, children: Vec<Obj>, scalars: &[u8]) -> Result<Obj> {
        self.charge_object(children.len(), scalars.len())?;
        Ok(Obj::mk_ctor(tag, children, scalars))
    }

    fn encode(&mut self, root: Node<'_>) -> Result<Obj> {
        let mut stack = Vec::new();
        let mut values = Vec::new();
        self.schedule(&mut stack, root)?;
        while let Some(task) = stack.pop() {
            match task {
                Task::Ctor {
                    tag,
                    slots,
                    scalars,
                } => {
                    let start = values
                        .len()
                        .checked_sub(slots.len())
                        .ok_or_else(|| contract("IR value stack underflow"))?;
                    let mut fields: Vec<_> = (0..slots.len()).map(|_| Obj::mk_nat(0)).collect();
                    for (slot, value) in slots.into_iter().zip(values.drain(start..)) {
                        fields[slot] = value;
                    }
                    values.push(Obj::mk_ctor(tag, fields, &scalars));
                }
                Task::Array(count) => {
                    let start = values
                        .len()
                        .checked_sub(count)
                        .ok_or_else(|| contract("IR array stack underflow"))?;
                    let array = Obj::mk_array(values.drain(start..).collect());
                    values.push(array);
                }
                Task::List(count) => {
                    let start = values
                        .len()
                        .checked_sub(count)
                        .ok_or_else(|| contract("IR list stack underflow"))?;
                    let mut list = Obj::mk_nat(source::LIST_NIL.into());
                    for head in values.drain(start..).rev() {
                        let mut fields: Vec<_> = (0..source::LIST_CONS_POINTERS)
                            .map(|_| Obj::mk_nat(0))
                            .collect();
                        fields[source::LIST_CONS_HEAD] = head;
                        fields[source::LIST_CONS_TAIL] = list;
                        list = Obj::mk_ctor(source::LIST_CONS, fields, &[]);
                    }
                    values.push(list);
                }
                Task::Visit(node) => self.visit(node, &mut stack, &mut values)?,
            }
        }
        if values.len() != 1 {
            return Err(contract("IR value stack has trailing objects"));
        }
        values.pop().ok_or_else(|| contract("IR root missing"))
    }

    fn visit<'a>(
        &mut self,
        node: Node<'a>,
        stack: &mut Vec<Task<'a>>,
        out: &mut Vec<Obj>,
    ) -> Result<()> {
        use Node as N;
        use format as f;
        match node {
            N::Nat(value) => out.push(self.nat(value)?),
            N::Name(name) => out.push(self.graph.name(name)?),
            N::String(text) => out.push(self.graph.string(text)?),
            N::OptionName(None) => out.push(Obj::mk_nat(source::OPTION_NONE)),
            N::OptionName(Some(name)) => self.ctor(
                stack,
                source::OPTION_SOME,
                source::OPTION_SOME_POINTERS,
                &[(source::OPTION_SOME_VAL, N::Name(name))],
                &[],
            )?,
            N::Types(types) => self.array(stack, types, N::Type)?,
            N::Args(args) => self.array(stack, args, |arg| N::Arg(*arg))?,
            N::Params(params) => self.array(stack, params, N::Param)?,
            N::Alts(alts) => self.array(stack, alts, N::Alt)?,
            N::Type(ty) => {
                let tag = match ty {
                    IrType::Float => f::IR_TYPE_FLOAT,
                    IrType::UInt8 => f::IR_TYPE_UINT8,
                    IrType::UInt16 => f::IR_TYPE_UINT16,
                    IrType::UInt32 => f::IR_TYPE_UINT32,
                    IrType::UInt64 => f::IR_TYPE_UINT64,
                    IrType::USize => f::IR_TYPE_USIZE,
                    IrType::Erased => f::IR_TYPE_ERASED,
                    IrType::Object => f::IR_TYPE_OBJECT,
                    IrType::TObject => f::IR_TYPE_TOBJECT,
                    IrType::Float32 => f::IR_TYPE_FLOAT32,
                    IrType::Tagged => f::IR_TYPE_TAGGED,
                    IrType::Void => f::IR_TYPE_VOID,
                    IrType::Struct { lean_type, types } => {
                        self.ctor(
                            stack,
                            f::IR_TYPE_STRUCT,
                            f::IR_TYPE_STRUCT_POINTERS,
                            &[
                                (
                                    f::IR_TYPE_STRUCT_LEAN_TYPE_NAME,
                                    N::OptionName(lean_type.as_ref()),
                                ),
                                (f::IR_TYPE_STRUCT_TYPES, N::Types(types)),
                            ],
                            &[],
                        )?;
                        return Ok(());
                    }
                    IrType::Union { lean_type, types } => {
                        self.ctor(
                            stack,
                            f::IR_TYPE_UNION,
                            f::IR_TYPE_UNION_POINTERS,
                            &[
                                (f::IR_TYPE_UNION_LEAN_TYPE_NAME, N::Name(lean_type)),
                                (f::IR_TYPE_UNION_TYPES, N::Types(types)),
                            ],
                            &[],
                        )?;
                        return Ok(());
                    }
                };
                out.push(Obj::mk_nat(tag.into()));
            }
            N::Arg(IrArg::Erased) => out.push(Obj::mk_nat(f::ARG_ERASED.into())),
            N::Arg(IrArg::Var(x)) => self.ctor(
                stack,
                f::ARG_VAR,
                f::ARG_VAR_POINTERS,
                &[(f::ARG_VAR_ID, N::Nat(x))],
                &[],
            )?,
            N::Param(param) => {
                let mut scalars = vec![0; f::PARAM_SCALAR_BYTES];
                scalars[f::PARAM_BORROW_SCALAR] = u8::from(param.borrow);
                self.ctor(
                    stack,
                    0,
                    f::PARAM_POINTERS,
                    &[
                        (f::PARAM_X, N::Nat(param.x)),
                        (f::PARAM_TY, N::Type(&param.ty)),
                    ],
                    &scalars,
                )?;
            }
            N::Ctor(info) => self.ctor(
                stack,
                0,
                f::CTOR_INFO_POINTERS,
                &[
                    (f::CTOR_INFO_NAME, N::Name(&info.name)),
                    (f::CTOR_INFO_CIDX, N::Nat(info.cidx)),
                    (f::CTOR_INFO_SIZE, N::Nat(info.size)),
                    (f::CTOR_INFO_USIZE, N::Nat(info.usize)),
                    (f::CTOR_INFO_SSIZE, N::Nat(info.ssize)),
                ],
                &[],
            )?,
            N::Lit(IrLit::Str(text)) => self.ctor(
                stack,
                f::LIT_STR,
                f::LIT_STR_POINTERS,
                &[(f::LIT_STR_V, N::String(text))],
                &[],
            )?,
            N::Lit(IrLit::Num(IrNat::Small(n))) => self.ctor(
                stack,
                f::LIT_NUM,
                f::LIT_NUM_POINTERS,
                &[(f::LIT_NUM_V, N::Nat(*n))],
                &[],
            )?,
            N::Lit(IrLit::Num(IrNat::Big(limbs))) => {
                if limbs.len() < 2 || limbs.last() == Some(&0) {
                    return Err(contract("noncanonical IR big Nat"));
                }
                let bytes = (limbs.len() as u64)
                    .checked_mul(8)
                    .and_then(|n| n.checked_add(24))
                    .ok_or_else(|| contract("IR Nat size overflow"))?;
                if bytes > u64::from(u16::MAX) {
                    return Err(contract("IR Nat exceeds runtime object size"));
                }
                self.graph.charge(bytes)?;
                let nat = Obj::mk_mpz(limbs, false);
                let mut fields: Vec<_> = (0..f::LIT_NUM_POINTERS).map(|_| Obj::mk_nat(0)).collect();
                fields[f::LIT_NUM_V] = nat;
                out.push(self.object(f::LIT_NUM, fields, &[])?);
            }
            N::Expr(expr) => match expr {
                IrExpr::Ctor { info, args } => self.ctor(
                    stack,
                    f::EXPR_CTOR,
                    f::EXPR_CTOR_POINTERS,
                    &[
                        (f::EXPR_CTOR_I, N::Ctor(info)),
                        (f::EXPR_CTOR_YS, N::Args(args)),
                    ],
                    &[],
                )?,
                IrExpr::Reset { n, x } => self.ctor(
                    stack,
                    f::EXPR_RESET,
                    f::EXPR_RESET_POINTERS,
                    &[(f::EXPR_RESET_N, N::Nat(*n)), (f::EXPR_RESET_X, N::Nat(*x))],
                    &[],
                )?,
                IrExpr::Reuse {
                    x,
                    info,
                    update_header,
                    args,
                } => {
                    let mut scalars = vec![0; f::EXPR_REUSE_SCALAR_BYTES];
                    scalars[f::EXPR_REUSE_UPDT_HEADER_SCALAR] = u8::from(*update_header);
                    self.ctor(
                        stack,
                        f::EXPR_REUSE,
                        f::EXPR_REUSE_POINTERS,
                        &[
                            (f::EXPR_REUSE_X, N::Nat(*x)),
                            (f::EXPR_REUSE_I, N::Ctor(info)),
                            (f::EXPR_REUSE_YS, N::Args(args)),
                        ],
                        &scalars,
                    )?;
                }
                IrExpr::Proj { i, x } => self.ctor(
                    stack,
                    f::EXPR_PROJ,
                    f::EXPR_PROJ_POINTERS,
                    &[(f::EXPR_PROJ_I, N::Nat(*i)), (f::EXPR_PROJ_X, N::Nat(*x))],
                    &[],
                )?,
                IrExpr::UProj { i, x } => self.ctor(
                    stack,
                    f::EXPR_UPROJ,
                    f::EXPR_UPROJ_POINTERS,
                    &[(f::EXPR_UPROJ_I, N::Nat(*i)), (f::EXPR_UPROJ_X, N::Nat(*x))],
                    &[],
                )?,
                IrExpr::SProj { n, offset, x } => self.ctor(
                    stack,
                    f::EXPR_SPROJ,
                    f::EXPR_SPROJ_POINTERS,
                    &[
                        (f::EXPR_SPROJ_N, N::Nat(*n)),
                        (f::EXPR_SPROJ_OFFSET, N::Nat(*offset)),
                        (f::EXPR_SPROJ_X, N::Nat(*x)),
                    ],
                    &[],
                )?,
                IrExpr::Fap { function, args } => self.ctor(
                    stack,
                    f::EXPR_FAP,
                    f::EXPR_FAP_POINTERS,
                    &[
                        (f::EXPR_FAP_C, N::Name(function)),
                        (f::EXPR_FAP_YS, N::Args(args)),
                    ],
                    &[],
                )?,
                IrExpr::Pap { function, args } => self.ctor(
                    stack,
                    f::EXPR_PAP,
                    f::EXPR_PAP_POINTERS,
                    &[
                        (f::EXPR_PAP_C, N::Name(function)),
                        (f::EXPR_PAP_YS, N::Args(args)),
                    ],
                    &[],
                )?,
                IrExpr::Ap { x, args } => self.ctor(
                    stack,
                    f::EXPR_AP,
                    f::EXPR_AP_POINTERS,
                    &[(f::EXPR_AP_X, N::Nat(*x)), (f::EXPR_AP_YS, N::Args(args))],
                    &[],
                )?,
                IrExpr::Box { ty, x } => self.ctor(
                    stack,
                    f::EXPR_BOX,
                    f::EXPR_BOX_POINTERS,
                    &[(f::EXPR_BOX_TY, N::Type(ty)), (f::EXPR_BOX_X, N::Nat(*x))],
                    &[],
                )?,
                IrExpr::Unbox { x } => self.ctor(
                    stack,
                    f::EXPR_UNBOX,
                    f::EXPR_UNBOX_POINTERS,
                    &[(f::EXPR_UNBOX_X, N::Nat(*x))],
                    &[],
                )?,
                IrExpr::Lit(lit) => self.ctor(
                    stack,
                    f::EXPR_LIT,
                    f::EXPR_LIT_POINTERS,
                    &[(f::EXPR_LIT_V, N::Lit(lit))],
                    &[],
                )?,
                IrExpr::IsShared { x } => self.ctor(
                    stack,
                    f::EXPR_IS_SHARED,
                    f::EXPR_IS_SHARED_POINTERS,
                    &[(f::EXPR_IS_SHARED_X, N::Nat(*x))],
                    &[],
                )?,
            },
            N::Decl(IrDecl::Function {
                name,
                params,
                result,
                body,
                sorry_dep,
            }) => self.ctor(
                stack,
                f::DECL_FDECL,
                f::DECL_FDECL_POINTERS,
                &[
                    (f::DECL_FDECL_F, N::Name(name)),
                    (f::DECL_FDECL_XS, N::Params(params)),
                    (f::DECL_FDECL_TYPE, N::Type(result)),
                    (f::DECL_FDECL_BODY, N::Body(body, 0)),
                    (f::DECL_FDECL_INFO, N::OptionName(sorry_dep.as_ref())),
                ],
                &[],
            )?,
            N::Decl(IrDecl::Extern {
                name,
                params,
                result,
                entries,
            }) => self.ctor(
                stack,
                f::DECL_EXTERN,
                f::DECL_EXTERN_POINTERS,
                &[
                    (f::DECL_EXTERN_F, N::Name(name)),
                    (f::DECL_EXTERN_XS, N::Params(params)),
                    (f::DECL_EXTERN_TYPE, N::Type(result)),
                    (f::DECL_EXTERN_EXT, N::Externs(entries)),
                ],
                &[],
            )?,
            N::Externs(entries) => {
                if entries.len() as u64 > self.nodes_left {
                    return Err(IrWriteError::Limit { resource: "nodes" });
                }
                for _ in entries {
                    self.charge_object(source::LIST_CONS_POINTERS, 0)?;
                }
                stack.push(Task::List(entries.len()));
                for entry in entries.iter().rev() {
                    self.schedule(stack, N::Extern(entry))?;
                }
            }
            N::Extern(entry) => match entry {
                IrExternEntry::Adhoc { backend } => self.ctor(
                    stack,
                    f::EXTERN_ENTRY_ADHOC,
                    f::EXTERN_ENTRY_ADHOC_POINTERS,
                    &[(f::EXTERN_ENTRY_ADHOC_BACKEND, N::Name(backend))],
                    &[],
                )?,
                IrExternEntry::Inline { backend, pattern } => self.ctor(
                    stack,
                    f::EXTERN_ENTRY_INLINE,
                    f::EXTERN_ENTRY_INLINE_POINTERS,
                    &[
                        (f::EXTERN_ENTRY_INLINE_BACKEND, N::Name(backend)),
                        (f::EXTERN_ENTRY_INLINE_PATTERN, N::String(pattern)),
                    ],
                    &[],
                )?,
                IrExternEntry::Standard { backend, function } => self.ctor(
                    stack,
                    f::EXTERN_ENTRY_STANDARD,
                    f::EXTERN_ENTRY_STANDARD_POINTERS,
                    &[
                        (f::EXTERN_ENTRY_STANDARD_BACKEND, N::Name(backend)),
                        (f::EXTERN_ENTRY_STANDARD_FN, N::String(function)),
                    ],
                    &[],
                )?,
                IrExternEntry::Opaque => out.push(Obj::mk_nat(f::EXTERN_ENTRY_OPAQUE.into())),
            },
            N::Alt(IrAlt::Ctor { info, body }) => self.ctor(
                stack,
                f::ALT_CTOR,
                f::ALT_CTOR_POINTERS,
                &[
                    (f::ALT_CTOR_INFO, N::Ctor(info)),
                    (f::ALT_CTOR_B, N::Body(body, 0)),
                ],
                &[],
            )?,
            N::Alt(IrAlt::Default { body }) => self.ctor(
                stack,
                f::ALT_DEFAULT,
                f::ALT_DEFAULT_POINTERS,
                &[(f::ALT_DEFAULT_B, N::Body(body, 0))],
                &[],
            )?,
            N::Terminal(terminal) => match terminal {
                IrTerminal::Case {
                    type_name,
                    x,
                    x_type,
                    alts,
                } => self.ctor(
                    stack,
                    f::BODY_CASE,
                    f::BODY_CASE_POINTERS,
                    &[
                        (f::BODY_CASE_TID, N::Name(type_name)),
                        (f::BODY_CASE_X, N::Nat(*x)),
                        (f::BODY_CASE_X_TYPE, N::Type(x_type)),
                        (f::BODY_CASE_CS, N::Alts(alts)),
                    ],
                    &[],
                )?,
                IrTerminal::Ret(arg) => self.ctor(
                    stack,
                    f::BODY_RET,
                    f::BODY_RET_POINTERS,
                    &[(f::BODY_RET_X, N::Arg(*arg))],
                    &[],
                )?,
                IrTerminal::Jmp { j, args } => self.ctor(
                    stack,
                    f::BODY_JMP,
                    f::BODY_JMP_POINTERS,
                    &[(f::BODY_JMP_J, N::Nat(*j)), (f::BODY_JMP_YS, N::Args(args))],
                    &[],
                )?,
                IrTerminal::Unreachable => out.push(Obj::mk_nat(f::BODY_UNREACHABLE.into())),
            },
            N::Body(body, index) => {
                let Some(stmt) = body.stmts.get(index) else {
                    self.schedule(stack, N::Terminal(&body.terminal))?;
                    return Ok(());
                };
                let next = N::Body(body, index + 1);
                match stmt {
                    IrStmt::VDecl { x, ty, expr } => self.ctor(
                        stack,
                        f::BODY_VDECL,
                        f::BODY_VDECL_POINTERS,
                        &[
                            (f::BODY_VDECL_X, N::Nat(*x)),
                            (f::BODY_VDECL_TY, N::Type(ty)),
                            (f::BODY_VDECL_E, N::Expr(expr)),
                            (f::BODY_VDECL_B, next),
                        ],
                        &[],
                    )?,
                    IrStmt::JDecl { j, params, value } => self.ctor(
                        stack,
                        f::BODY_JDECL,
                        f::BODY_JDECL_POINTERS,
                        &[
                            (f::BODY_JDECL_J, N::Nat(*j)),
                            (f::BODY_JDECL_XS, N::Params(params)),
                            (f::BODY_JDECL_V, N::Body(value, 0)),
                            (f::BODY_JDECL_B, next),
                        ],
                        &[],
                    )?,
                    IrStmt::Set { x, i, y } => self.ctor(
                        stack,
                        f::BODY_SET,
                        f::BODY_SET_POINTERS,
                        &[
                            (f::BODY_SET_X, N::Nat(*x)),
                            (f::BODY_SET_I, N::Nat(*i)),
                            (f::BODY_SET_Y, N::Arg(*y)),
                            (f::BODY_SET_B, next),
                        ],
                        &[],
                    )?,
                    IrStmt::SetTag { x, cidx } => self.ctor(
                        stack,
                        f::BODY_SET_TAG,
                        f::BODY_SET_TAG_POINTERS,
                        &[
                            (f::BODY_SET_TAG_X, N::Nat(*x)),
                            (f::BODY_SET_TAG_CIDX, N::Nat(*cidx)),
                            (f::BODY_SET_TAG_B, next),
                        ],
                        &[],
                    )?,
                    IrStmt::USet { x, i, y } => self.ctor(
                        stack,
                        f::BODY_USET,
                        f::BODY_USET_POINTERS,
                        &[
                            (f::BODY_USET_X, N::Nat(*x)),
                            (f::BODY_USET_I, N::Nat(*i)),
                            (f::BODY_USET_Y, N::Nat(*y)),
                            (f::BODY_USET_B, next),
                        ],
                        &[],
                    )?,
                    IrStmt::SSet {
                        x,
                        i,
                        offset,
                        y,
                        ty,
                    } => self.ctor(
                        stack,
                        f::BODY_SSET,
                        f::BODY_SSET_POINTERS,
                        &[
                            (f::BODY_SSET_X, N::Nat(*x)),
                            (f::BODY_SSET_I, N::Nat(*i)),
                            (f::BODY_SSET_OFFSET, N::Nat(*offset)),
                            (f::BODY_SSET_Y, N::Nat(*y)),
                            (f::BODY_SSET_TY, N::Type(ty)),
                            (f::BODY_SSET_B, next),
                        ],
                        &[],
                    )?,
                    IrStmt::Inc {
                        x,
                        n,
                        checked,
                        persistent,
                    } => {
                        let mut scalars = vec![0; f::BODY_INC_SCALAR_BYTES];
                        scalars[f::BODY_INC_C_SCALAR] = u8::from(*checked);
                        scalars[f::BODY_INC_PERSISTENT_SCALAR] = u8::from(*persistent);
                        self.ctor(
                            stack,
                            f::BODY_INC,
                            f::BODY_INC_POINTERS,
                            &[
                                (f::BODY_INC_X, N::Nat(*x)),
                                (f::BODY_INC_N, N::Nat(*n)),
                                (f::BODY_INC_B, next),
                            ],
                            &scalars,
                        )?;
                    }
                    IrStmt::Dec {
                        x,
                        n,
                        checked,
                        persistent,
                    } => {
                        let mut scalars = vec![0; f::BODY_DEC_SCALAR_BYTES];
                        scalars[f::BODY_DEC_C_SCALAR] = u8::from(*checked);
                        scalars[f::BODY_DEC_PERSISTENT_SCALAR] = u8::from(*persistent);
                        self.ctor(
                            stack,
                            f::BODY_DEC,
                            f::BODY_DEC_POINTERS,
                            &[
                                (f::BODY_DEC_X, N::Nat(*x)),
                                (f::BODY_DEC_N, N::Nat(*n)),
                                (f::BODY_DEC_B, next),
                            ],
                            &scalars,
                        )?;
                    }
                    IrStmt::Del { x } => self.ctor(
                        stack,
                        f::BODY_DEL,
                        f::BODY_DEL_POINTERS,
                        &[(f::BODY_DEL_X, N::Nat(*x)), (f::BODY_DEL_B, next)],
                        &[],
                    )?,
                }
            }
        }
        Ok(())
    }
}

/// Emit an IR `ModuleData`, sorting declarations by the pin's `Name.quickLt`
/// (`IR.sortDecls`) and preserving initializer and additional-extension order.
/// Callers own the import header, extra-name table and companion publication. Semantic
/// and ownership validation are separate; serialization is not a validator.
pub fn encode_ir(
    input: IrWriteInput<'_>,
    header: OleanWriteHeader<'_>,
    limits: IrWriteLimits,
) -> Result<EncodedModule> {
    if !input.module.constants.is_empty() {
        return Err(contract("IR container cannot hold logical constants"));
    }
    let count = input
        .declarations
        .len()
        .checked_add(input.initializers.len())
        .ok_or(IrWriteError::Limit {
            resource: "entries",
        })?;
    if count > limits.max_entries {
        return Err(IrWriteError::Limit {
            resource: "entries",
        });
    }
    let mut writer = Writer {
        graph: Builder::new(limits.container),
        nodes_left: limits.max_nodes,
    };
    let mut seen = BTreeSet::new();
    let mut declarations = Vec::new();
    let mut ordered: Vec<_> = input.declarations.iter().collect();
    ordered.sort_by(|a, b| a.name().quick_cmp(b.name()));
    for decl in ordered {
        if !seen.insert(decl.name()) {
            return Err(contract("duplicate IR declaration"));
        }
        declarations.push(writer.encode(Node::Decl(decl))?);
    }
    let mut initialized = BTreeSet::new();
    let mut initializers = Vec::new();
    for entry in input.initializers {
        if entry.declaration.is_anonymous()
            || !initialized.insert(&entry.declaration)
            || entry.initializer.as_ref().is_some_and(Name::is_anonymous)
        {
            return Err(contract("invalid or duplicate IR initializer"));
        }
        let declaration = writer.encode(Node::Name(&entry.declaration))?;
        let initializer = match &entry.initializer {
            Some(name) => writer.encode(Node::Name(name))?,
            None => Obj::mk_nat(0),
        };
        let mut fields: Vec<_> = (0..source::PROD_POINTERS).map(|_| Obj::mk_nat(0)).collect();
        fields[source::PROD_FST] = declaration;
        fields[source::PROD_SND] = initializer;
        initializers.push(writer.object(0, fields, &[])?);
    }
    let decl_name = Name::from_components(format::DECL_MAP_EXTENSION.split('.'));
    let init_name = Name::from_components(crate::initializers::REGULAR_INIT_EXTENSION.split('.'));
    let mut extensions = vec![
        ModuleExtensionInput {
            name: &decl_name,
            entries: &declarations,
        },
        ModuleExtensionInput {
            name: &init_name,
            entries: &initializers,
        },
    ];
    extensions.extend_from_slice(input.additional_extensions);
    Ok(encode_module_with_extensions(
        input.module,
        &extensions,
        header,
        limits.container,
    )?)
}

#[cfg(test)]
#[path = "write_tests.rs"]
mod tests;
