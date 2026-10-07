//! Real pinned library declarations pass both checkers and execute on Golem.
//! The Reference is read only as `.olean` data; no Reference process is launched.
#![forbid(unsafe_code)]

use fln::source_check::modules::imported::SourceOleanImportLimits;
use fln::{
    Budget, ClosedVmValue, Engine, EngineExecutionLimits, Environment, KVMap, Name,
    OleanCheckLimits, OleanModuleInput,
};
use std::path::PathBuf;

const STACK: usize = 256 * 1024 * 1024;

#[test]
fn admitted_prelude_arithmetic_and_recursive_consumers_run_without_a_seed() {
    let lib = std::env::var_os("FLN_REFERENCE_LIB")
        .map(PathBuf::from)
        .or_else(|| {
            std::env::var_os("HOME").map(|home| {
                PathBuf::from(home).join(".elan/toolchains/leanprover--lean4---v4.32.0/lib/lean")
            })
        })
        .filter(|path| path.is_dir());
    let Some(lib) = lib else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "FLN_REQUIRE_REFERENCE is set but the pinned Reference is absent"
        );
        eprintln!("SKIP: pinned Reference lib/lean is absent");
        return;
    };
    std::thread::Builder::new().stack_size(STACK).spawn(move || {
        let path = lib.join("Init/Prelude.olean");
        let parts = [std::fs::read(&path).unwrap(),
            std::fs::read(path.with_extension("olean.server")).unwrap(),
            std::fs::read(path.with_extension("olean.private")).unwrap()];
        let name = Name::from_components(["Init", "Prelude"]);
        let inputs = [OleanModuleInput { name: &name, artifact: &parts[0],
            server_artifact: Some(&parts[1]), private_artifact: Some(&parts[2]) }];
        let options = KVMap::new();
        let imported = Engine::from_environment(Environment::new())
            .import_olean_modules_for_source(&inputs, std::slice::from_ref(&name), &options,
                SourceOleanImportLimits::new(OleanCheckLimits::new(256 * 1024 * 1024,
                    Budget::for_stack_bytes(STACK))))
            .unwrap().into_complete().unwrap();
        let engine = &imported.engine;
        let root = engine.logical_root(&options);
        let cases = [
            ("#eval Nat.add 20 22", 42),
            ("#eval 20 + 22", 42),
            ("#eval Nat.add 0 42", 42),
            ("#eval Nat.add 42 0", 42),
            ("def total (xs : List Nat) : Nat := match xs with | [] => 0 | x :: tail => x + total tail\n#eval total [20, 22]", 42),
            ("def twice (f : Nat -> Nat) (n : Nat) : Nat := f (f n)\n#eval twice (Nat.add 1) 40", 42),
            ("def extract (x : Option Nat) : Nat := match x with | none => 0 | some n => n\n#eval extract (Option.map (fun n => n + 1) (some 41))", 42),
            ("def extract (x : Option Nat) : Nat := match x with | none => 42 | some n => n\n#eval extract (Option.map (fun n => n + 1) (none : Option Nat))", 42),
            ("#eval Nat.pred 0", 0),
            ("#eval Nat.pred 43", 42),
            ("#eval Nat.beq 0 0", 1),
            ("#eval Nat.beq 0 42", 0),
            ("#eval Nat.beq 42 0", 0),
            ("#eval Nat.beq 42 42", 1),
            ("#eval Nat.beq 18446744073709551616 18446744073709551616", 1),
            ("#eval Nat.beq 18446744073709551616 18446744073709551617", 0),
            ("#eval Nat.ble 0 0", 1),
            ("#eval Nat.ble 0 42", 1),
            ("#eval Nat.ble 42 0", 0),
            ("#eval Nat.ble 41 42", 1),
            ("#eval Nat.ble 42 42", 1),
            ("#eval Nat.ble 43 42", 0),
            ("#eval Nat.ble 18446744073709551616 18446744073709551616", 1),
            ("#eval Nat.ble 18446744073709551616 18446744073709551617", 1),
            ("#eval Nat.ble 18446744073709551617 18446744073709551616", 0),
            ("#eval Nat.mul 6 7", 42),
            ("#eval 6 * 7", 42),
            ("#eval Nat.mul 0 42", 0),
            ("#eval Nat.mul 42 0", 0),
            ("#eval Nat.sub 45 3", 42),
            ("#eval 45 - 3", 42),
            ("#eval Nat.sub 3 45", 0),
            ("#eval Nat.sub 18446744073709551658 18446744073709551616", 42),
            ("#eval Nat.pow 0 0", 1),
            ("#eval Nat.pow 0 5", 0),
            ("#eval Nat.pow 42 0", 1),
            ("#eval Nat.pow 42 1", 42),
            ("#eval Nat.pow 2 5", 32),
            ("#eval Nat.pow 1 65536", 1),
            ("def twice (f : Nat -> Nat) (n : Nat) : Nat := f (f n)\n#eval twice (Nat.pow 2) 3", 256),
            ("def apply (f : Nat -> Bool) : Nat := if f 3 then 42 else 0\n#eval apply (Nat.ble 2)", 42),
            ("def bounded (n m : Nat) : Nat := if Nat.ble n m then 42 else 0\n#eval bounded 41 42", 42),
            ("def bounded (n m : Nat) : Nat := if Nat.ble n m then 42 else 0\n#eval bounded 43 42", 0),
            ("def count (n : Nat) : Nat := match n with | 0 => 0 | Nat.succ k => count k + 1\n#eval count 42", 42),
            ("def factorial (n : Nat) : Nat := match n with | 0 => 1 | Nat.succ k => Nat.mul (Nat.succ k) (factorial k)\n#eval factorial 5", 120),
            ("def total (xs : List Nat) : Nat := match xs with | [] => 0 | x :: tail => x + total tail\n#eval total (List.append [20] [22])", 42),
            ("def total (xs : List Nat) : Nat := match xs with | [] => 0 | x :: tail => x + total tail\n#eval total (List.append [] [20, 22])", 42),
            ("def total (xs : List Nat) : Nat := match xs with | [] => 0 | x :: tail => x + total tail\n#eval total (List.append [20, 22] [])", 42),
            ("def total (xs : List Nat) : Nat := match xs with | [] => 0 | x :: tail => x + total tail\n#eval total (List.append [] [])", 0),
            ("def total (xs : List Nat) : Nat := match xs with | [] => 0 | x :: tail => x + total tail\n#eval total (List.map (fun n => n + 1) [19, 21])", 42),
            ("def total (xs : List Nat) : Nat := match xs with | [] => 0 | x :: tail => x + total tail\n#eval total (List.map (fun n => n + 1) [])", 0),
            ("def total (xs : List Nat) : Nat := match xs with | [] => 0 | x :: tail => x + total tail\ndef shifted (k : Nat) : List Nat := List.map (fun n => n + k) [19, 21]\n#eval total (shifted 1)", 42),
            ("def total (xs : List Nat) : Nat := match xs with | [] => 0 | x :: tail => x + total tail\ndef classified (limit : Nat) : List Nat := List.map (fun n => if Nat.ble n limit then 20 else 22) [2, 4]\n#eval total (classified 3)", 42),
            ("def total (xs : List Nat) : Nat := match xs with | [] => 0 | x :: tail => x + total tail\ndef powered (base : Nat) : List Nat := List.map (Nat.pow base) [1, 2, 3]\n#eval total (powered 3)", 39),
            ("def total (xs : List Nat) : Nat := match xs with | [] => 0 | x :: tail => x + total tail\n#eval total (List.map (fun (b : Bool) => if b then 20 else 22) [true, false])", 42),
            ("def applyTotal (fs : List (Nat -> Nat)) (n : Nat) : Nat := match fs with | [] => 0 | f :: rest => f n + applyTotal rest n\n#eval applyTotal (List.map (fun k => fun n => k + n) [19, 21]) 1", 42),
        ].into_iter().map(|(source, value)| (source, ClosedVmValue::Scalar(value))).chain([
            ("#eval Nat.pred 18446744073709551617", ClosedVmValue::NonnegativeMpz("18446744073709551616".to_owned())),
            ("#eval Nat.mul 4294967296 4294967296", ClosedVmValue::NonnegativeMpz("18446744073709551616".to_owned())),
            ("#eval Nat.pow 2 64", ClosedVmValue::NonnegativeMpz("18446744073709551616".to_owned())),
            ("#eval Nat.pow 18446744073709551617 2", ClosedVmValue::NonnegativeMpz("340282366920938463500268095579187314689".to_owned())),
        ]);
        for (source, expected) in cases {
            let execute = || engine.execute_source_commands_with_checks(source.as_bytes(), &options,
                EngineExecutionLimits::new(Budget::for_stack_bytes(STACK)))
                .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
                .into_complete().unwrap_or_else(|outcome| panic!("{source}\n{outcome:?}"));
            let first = execute();
            let last = first.batch.executions.last().unwrap();
            assert_eq!(fln::closed_vm_value(&last.exit).unwrap(), Some(expected), "{source}");
            let second = execute();
            assert_eq!(last.flbc_artifact, second.batch.executions.last().unwrap().flbc_artifact, "deterministic imported execution: {source}");
            assert_eq!(root, engine.logical_root(&options));
        }
    }).unwrap().join().unwrap();
}
