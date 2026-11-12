//! Reviewed native IR prototype of the pin's Name equality extern.

use super::{GeneratedExternRow, IrType, PrimitiveSignature, Review};

pub(super) fn review(row: &GeneratedExternRow) -> Option<Review> {
    (row.id == "extern:Lean.Name.beq").then_some(Review {
        name: "Lean.Name.beq",
        symbol: "lean_name_eq",
        module: "Init.Prelude",
        kind: "defn",
        ownership: "abi((n1: borrowed_arg, n2: borrowed_arg) -> value)",
        signature: PrimitiveSignature {
            exact_borrowed: None,
            parameters: &[IrType::TObject, IrType::TObject],
            result: &IrType::UInt8,
        },
    })
}
