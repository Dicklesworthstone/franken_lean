//! Budgeted operand reads shared by join lifting and constructor normalization.

use super::IrExecutionError;
use fln_olean::ir::{IrArg, IrExpr, IrStmt, IrTerminal};

type Result<T> = std::result::Result<T, IrExecutionError>;

pub(super) fn visit_stmt_reads(
    stmt: &IrStmt,
    mut visit: impl FnMut(u64),
    mut charge: impl FnMut(usize) -> Result<()>,
) -> Result<()> {
    match stmt {
        IrStmt::VDecl { expr, .. } => {
            let args = match expr {
                IrExpr::Ctor { args, .. } | IrExpr::Fap { args, .. } | IrExpr::Pap { args, .. } => {
                    args.as_slice()
                }
                IrExpr::Reuse { x, args, .. } | IrExpr::Ap { x, args } => {
                    charge(1)?;
                    visit(*x);
                    args.as_slice()
                }
                IrExpr::Reset { x, .. }
                | IrExpr::Proj { x, .. }
                | IrExpr::UProj { x, .. }
                | IrExpr::SProj { x, .. }
                | IrExpr::Box { x, .. }
                | IrExpr::Unbox { x }
                | IrExpr::IsShared { x } => {
                    charge(1)?;
                    visit(*x);
                    &[]
                }
                IrExpr::Lit(_) => &[],
            };
            for arg in args {
                charge(1)?;
                if let IrArg::Var(x) = arg {
                    visit(*x);
                }
            }
        }
        IrStmt::Set { x, y, .. } => {
            charge(2)?;
            visit(*x);
            if let IrArg::Var(y) = y {
                visit(*y);
            }
        }
        IrStmt::USet { x, y, .. } | IrStmt::SSet { x, y, .. } => {
            charge(2)?;
            visit(*x);
            visit(*y);
        }
        IrStmt::SetTag { x, .. }
        | IrStmt::Inc { x, .. }
        | IrStmt::Dec { x, .. }
        | IrStmt::Del { x } => {
            charge(1)?;
            visit(*x);
        }
        IrStmt::JDecl { .. } => {}
    }
    Ok(())
}

pub(super) fn visit_terminal_reads(
    terminal: &IrTerminal,
    mut visit: impl FnMut(u64),
    mut charge: impl FnMut(usize) -> Result<()>,
) -> Result<()> {
    match terminal {
        IrTerminal::Case { x, .. } => {
            charge(1)?;
            visit(*x);
        }
        IrTerminal::Ret(IrArg::Var(x)) => {
            charge(1)?;
            visit(*x);
        }
        IrTerminal::Jmp { args, .. } => {
            for arg in args {
                charge(1)?;
                if let IrArg::Var(x) = arg {
                    visit(*x);
                }
            }
        }
        IrTerminal::Ret(IrArg::Erased) | IrTerminal::Unreachable => {}
    }
    Ok(())
}
