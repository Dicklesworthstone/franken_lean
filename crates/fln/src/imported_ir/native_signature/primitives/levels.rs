//! Pin-derived IR representations for universe-level externs. Their generic
//! census ownership stays authoritative; scalar types describe the native IR
//! boundary and the boxed wrappers synthesized by the compiler.

use super::{GeneratedExternRow, IrType, PrimitiveSignature, Review};

pub(super) fn review(row: &GeneratedExternRow) -> Option<Review> {
    let (name, symbol, parameters, result): (_, _, &'static [IrType], &'static IrType) =
        match row.id {
            "extern:Lean.Level.beq" => (
                "Lean.Level.beq",
                "lean_level_eq",
                &[IrType::TObject, IrType::TObject],
                &IrType::UInt8,
            ),
            "extern:Lean.Level.mkData" => (
                "Lean.Level.mkData",
                "lean_level_mk_data",
                &[
                    IrType::UInt64,
                    IrType::TObject,
                    IrType::UInt8,
                    IrType::UInt8,
                ],
                &IrType::UInt64,
            ),
            _ => return None,
        };
    Some(Review {
        name,
        symbol,
        module: "Lean.Level",
        kind: "opaque",
        ownership: "rule(borrowed-args,owned-result)",
        signature: PrimitiveSignature {
            parameters,
            result,
            exact_borrowed: Some(if row.id == "extern:Lean.Level.mkData" {
                &[false; 4]
            } else {
                &[true; 2]
            }),
        },
    })
}
