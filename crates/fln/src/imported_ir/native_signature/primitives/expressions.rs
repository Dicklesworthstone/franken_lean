//! Pinned Expr extern representations, independent of supplied IR bodies.

use super::{GeneratedExternRow, IrType, PrimitiveSignature, Review};

pub(super) fn review(row: &GeneratedExternRow) -> Option<Review> {
    let (name, symbol, parameters, result): (_, _, &'static [IrType], &'static IrType) =
        match row.id {
            "extern:Lean.Expr.data" => (
                "Lean.Expr.data",
                "lean_expr_data",
                &[IrType::Object],
                &IrType::UInt64,
            ),
            "extern:Lean.Expr.mkData" => (
                "Lean.Expr.mkData",
                "lean_expr_mk_data",
                &[
                    IrType::UInt64,
                    IrType::TObject,
                    IrType::UInt32,
                    IrType::UInt8,
                    IrType::UInt8,
                    IrType::UInt8,
                    IrType::UInt8,
                ],
                &IrType::UInt64,
            ),
            "extern:Lean.Expr.mkAppData" => (
                "Lean.Expr.mkAppData",
                "lean_expr_mk_app_data",
                &[IrType::UInt64, IrType::UInt64],
                &IrType::UInt64,
            ),
            "extern:Lean.Expr.equal" => (
                "Lean.Expr.equal",
                "lean_expr_equal",
                &[IrType::Object, IrType::Object],
                &IrType::UInt8,
            ),
            "extern:Lean.Expr.hasLooseBVar" => (
                "Lean.Expr.hasLooseBVar",
                "lean_expr_has_loose_bvar",
                &[IrType::Object, IrType::TObject],
                &IrType::UInt8,
            ),
            "extern:Lean.Expr.liftLooseBVars" => (
                "Lean.Expr.liftLooseBVars",
                "lean_expr_lift_loose_bvars",
                &[IrType::Object, IrType::TObject, IrType::TObject],
                &IrType::Object,
            ),
            "extern:Lean.Expr.instantiate1" => (
                "Lean.Expr.instantiate1",
                "lean_expr_instantiate1",
                &[IrType::Object, IrType::Object],
                &IrType::Object,
            ),
            "extern:Lean.Expr.instantiate" => (
                "Lean.Expr.instantiate",
                "lean_expr_instantiate",
                &[IrType::Object, IrType::Object],
                &IrType::Object,
            ),
            "extern:Lean.Expr.instantiateRev" => (
                "Lean.Expr.instantiateRev",
                "lean_expr_instantiate_rev",
                &[IrType::Object, IrType::Object],
                &IrType::Object,
            ),
            "extern:Lean.Expr.replaceImpl" => (
                "Lean.Expr.replaceImpl",
                "lean_replace_expr",
                &[IrType::Object, IrType::Object],
                &IrType::Object,
            ),
            "extern:Lean.Expr.findImpl?" => (
                "Lean.Expr.findImpl?",
                "lean_find_expr",
                &[IrType::Object, IrType::Object],
                &IrType::TObject,
            ),
            "extern:Lean.Expr.findExtImpl?" => (
                "Lean.Expr.findExtImpl?",
                "lean_find_ext_expr",
                &[IrType::Object, IrType::Object],
                &IrType::TObject,
            ),
            _ => return None,
        };
    Some(Review {
        name,
        symbol,
        module: match row.id {
            "extern:Lean.Expr.replaceImpl" => "Lean.Util.ReplaceExpr",
            "extern:Lean.Expr.findImpl?" | "extern:Lean.Expr.findExtImpl?" => "Lean.Util.FindExpr",
            _ => "Lean.Expr",
        },
        kind: if row.id == "extern:Lean.Expr.data" {
            "defn"
        } else {
            "opaque"
        },
        ownership: if row.id == "extern:Lean.Expr.data" {
            "abi((expr: owned_arg) -> value)"
        } else {
            "rule(borrowed-args,owned-result)"
        },
        signature: PrimitiveSignature {
            parameters,
            result,
            exact_borrowed: match row.id {
                "extern:Lean.Expr.data" => Some(&[true]),
                "extern:Lean.Expr.mkData" => Some(&[false; 7]),
                "extern:Lean.Expr.mkAppData" => Some(&[false; 2]),
                _ => None,
            },
        },
    })
}
