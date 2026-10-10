//! Canonical callback ids apply to native rows as well as ordinary functions.

use super::*;
use fln_comp::fir::EffectClass;
use fln_comp::flbc::{ArgumentOwnership, ResultOwnership};

#[test]
fn native_callback_interfaces_use_canonical_ids_in_arguments_and_results() {
    fn finalized(order: [usize; 3]) -> IntrinsicBinding {
        // This is compiler-private interface metadata, not an admitted native
        // source declaration. Real String.foldl source execution separately
        // checks the generated extern contract and its callable operand.
        let environment = Environment::new();
        let mut preparation = Preparation::new(&environment, IngressLimits::default());
        let mut callbacks = [ValueType::Unit; 3];
        for index in order {
            let (parameters, result) = match index {
                0 => (vec![ValueType::String, ValueType::Nat], ValueType::String),
                1 => (vec![ValueType::String], ValueType::String),
                2 => (vec![ValueType::Nat], ValueType::Nat),
                _ => unreachable!(),
            };
            callbacks[index] = preparation
                .register_function_type(
                    Expr::const_(Name::num(name("interface"), index as u64), vec![]),
                    parameters,
                    result,
                )
                .unwrap();
        }
        let mut rows = [IntrinsicBinding {
            name: name("privateCallbackRow"),
            universe_arity: 0,
            row: "test:privateCallbackRow".to_owned(),
            arguments: vec![callbacks[0], ValueType::Nat, callbacks[1]],
            argument_ownership: vec![
                ArgumentOwnership::Borrowed,
                ArgumentOwnership::Scalar,
                ArgumentOwnership::Owned,
            ],
            result: callbacks[0],
            result_ownership: ResultOwnership::Owned,
            effect: EffectClass::Pure,
        }];
        preparation.finalize_callables(&mut [], &mut rows).unwrap();
        let [row] = rows;
        row
    }

    let row = finalized([0, 1, 2]);
    assert_eq!(row, finalized([2, 1, 0]));
    // Canonical order also includes the partially applied Nat -> String
    // suffix: Nat -> Nat, Nat -> String, String -> String, String -> Nat -> String.
    let fold = ValueType::Closure(ClosureTypeId::new(3));
    assert_eq!(
        row.arguments,
        [
            fold,
            ValueType::Nat,
            ValueType::Closure(ClosureTypeId::new(2))
        ]
    );
    assert_eq!(row.result, fold);
    assert_eq!(
        row.argument_ownership,
        [
            ArgumentOwnership::Borrowed,
            ArgumentOwnership::Scalar,
            ArgumentOwnership::Owned,
        ]
    );
    assert_eq!(row.result_ownership, ResultOwnership::Owned);
    assert_eq!(row.effect, EffectClass::Pure);
}
