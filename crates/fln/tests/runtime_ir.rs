//! Native compilation, including actual Reference interpretation of the output.
#![forbid(unsafe_code)]

use fln::ir::{self, CompileLimits};
use fln::{Budget, Engine, EngineAdmissionLimits, EngineExecutionLimits, VmExit};
use fln_core::{name::Name, options::KVMap};
use fln_olean::ir::write::{IrWriteInput, IrWriteLimits, encode_ir};
use fln_olean::ir::{IrArg, IrBody, IrDecl, IrExpr, IrLit, IrNat, IrStmt, IrTerminal, IrType};
use fln_olean::region::{OleanView, WalkBudget};
use fln_olean::write::{ModuleWriteInput, OleanWriteHeader};
use std::{
    collections::{BTreeMap, BTreeSet},
    path::{Path, PathBuf},
    process::Command,
};

const HELPERS: &str = "def keep (x : Nat) : Nat := x\ndef invoke (f : Nat -> Nat) (x : Nat) : Nat := f x\ndef invokeString (f : Nat -> String) (x : Nat) : String := f x\n";

fn name(s: &str) -> Name {
    Name::from_components(s.split('.'))
}
fn limits() -> EngineExecutionLimits {
    EngineExecutionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}
fn base() -> Engine {
    let limits = limits();
    let options = KVMap::new();
    let seed = Engine::with_source_seed(EngineAdmissionLimits::new(limits.kernel))
        .unwrap()
        .into_complete()
        .unwrap();
    seed.execute_source_definitions(&[HELPERS.as_bytes()], &options, limits)
        .unwrap()
        .into_complete()
        .unwrap()
        .engine
}

fn cases() -> [(&'static str, &'static str, &'static str); 5] {
    [
        ("Nat", "42", "42"),
        ("Nat", "184467440737095516160", "184467440737095516160"),
        ("String", "\"native IR\"", "\"native IR\""),
        ("Nat", "invoke (fun x => keep x) 42", "42"),
        (
            "String",
            "let saved := \"captured IR\"; invokeString (fun _ => saved) 7",
            "\"captured IR\"",
        ),
    ]
}

// Source type, body, downstream application, result type/value, source arity.
fn export_cases() -> [(
    &'static str,
    &'static str,
    &'static str,
    &'static str,
    &'static str,
    usize,
); 52] {
    [
        ("Nat", "42", "compiled", "Nat", "42", 0),
        (
            "String",
            "\"source export\"",
            "compiled",
            "String",
            "\"source export\"",
            0,
        ),
        ("Nat -> Nat", "fun x => x", "compiled 42", "Nat", "42", 1),
        (
            "Nat -> Nat",
            "fun x => x",
            "compiled 184467440737095516160",
            "Nat",
            "184467440737095516160",
            1,
        ),
        (
            "String -> String",
            "fun x => x",
            "compiled \"caller string\"",
            "String",
            "\"caller string\"",
            1,
        ),
        (
            "(Nat -> String) -> Nat -> String",
            "fun f x => f x",
            "compiled (fun _ => \"caller callback\") 7",
            "String",
            "\"caller callback\"",
            2,
        ),
        (
            "Nat -> String",
            "let saved := \"source capture\"; fun _ => saved",
            "compiled 7",
            "String",
            "\"source capture\"",
            1,
        ),
        (
            "Nat -> Nat -> Nat",
            "fun x _ => x",
            "compiled 184467440737095516160 5",
            "Nat",
            "184467440737095516160",
            2,
        ),
        (
            "Nat -> Nat",
            "fun x => x",
            "(fun (f : Nat -> Nat) => f 42) compiled",
            "Nat",
            "42",
            1,
        ),
        (
            "Nat -> Nat -> String",
            "fun _ => let saved := \"partial capture\"; fun _ => saved",
            "let f := compiled 7; f 9",
            "String",
            "\"partial capture\"",
            2,
        ),
        (
            "String -> Nat -> Nat",
            "fun _ x => x",
            "compiled \"unused\" 42",
            "Nat",
            "42",
            2,
        ),
        (
            "Nat -> Nat -> Nat -> Nat",
            "fun _ x _ => x",
            "compiled 7 184467440737095516160 9",
            "Nat",
            "184467440737095516160",
            3,
        ),
        (
            "Nat -> String -> String",
            "fun _ x => x",
            "compiled 7 \"retained string\"",
            "String",
            "\"retained string\"",
            2,
        ),
        (
            "∀ (x : Nat), x = x -> Nat",
            "fun x _ => x",
            "compiled 42 rfl",
            "Nat",
            "42",
            2,
        ),
        (
            "(0 = 0) -> String",
            "fun _ => \"erased proof\"",
            "compiled rfl",
            "String",
            "\"erased proof\"",
            1,
        ),
        (
            "Type -> Nat -> Nat",
            "fun _ x => x",
            "compiled String 184467440737095516160",
            "Nat",
            "184467440737095516160",
            2,
        ),
        (
            "Prop -> Nat -> Nat",
            "fun _ x => x",
            "compiled (0 = 0) 42",
            "Nat",
            "42",
            2,
        ),
        (
            "Type -> Nat",
            "fun _ => 42",
            "compiled String",
            "Nat",
            "42",
            1,
        ),
        (
            "(0 = 0) -> Nat",
            "fun _ => 42",
            "compiled rfl",
            "Nat",
            "42",
            1,
        ),
        (
            "Type -> String -> String",
            "fun _ x => x",
            "compiled Nat \"erased type string\"",
            "String",
            "\"erased type string\"",
            2,
        ),
        (
            "Type -> Nat -> String",
            "fun _ => let saved := \"type-slot capture\"; fun _ => saved",
            "let f := compiled String; f 7",
            "String",
            "\"type-slot capture\"",
            2,
        ),
        (
            "Nat -> Type -> Nat",
            "fun x _ => x",
            "compiled 184467440737095516160 String",
            "Nat",
            "184467440737095516160",
            2,
        ),
        (
            "Type -> (Nat -> String) -> Nat -> String",
            "fun _ f x => f x",
            "compiled Nat (fun _ => \"typed callback\") 7",
            "String",
            "\"typed callback\"",
            3,
        ),
        ("Bool", "true", "compiled", "Bool", "true", 0),
        ("Bool", "false", "compiled", "Bool", "false", 0),
        (
            "Bool -> Bool",
            "fun x => x",
            "compiled true",
            "Bool",
            "true",
            1,
        ),
        (
            "Bool -> Bool",
            "fun x => x",
            "compiled false",
            "Bool",
            "false",
            1,
        ),
        (
            "Bool -> Bool",
            "fun x => x",
            "(fun (f : Bool -> Bool) => f false) compiled",
            "Bool",
            "false",
            1,
        ),
        (
            "Bool -> Nat -> Nat",
            "fun _ x => x",
            "compiled false 42",
            "Nat",
            "42",
            2,
        ),
        (
            "Nat -> Bool -> Bool",
            "fun _ x => x",
            "compiled 7 true",
            "Bool",
            "true",
            2,
        ),
        (
            "(Bool -> Bool) -> Bool -> Bool",
            "fun f x => f x",
            "compiled (fun _ => false) true",
            "Bool",
            "false",
            2,
        ),
        (
            "Type -> Bool -> Bool",
            "fun _ x => x",
            "compiled Nat true",
            "Bool",
            "true",
            2,
        ),
        (
            "Bool -> String -> String",
            "fun _ x => x",
            "compiled true \"retained Boolean string\"",
            "String",
            "\"retained Boolean string\"",
            2,
        ),
        (
            "Bool -> Bool",
            "fun _ => true",
            "compiled false",
            "Bool",
            "true",
            1,
        ),
        (
            "Bool -> Bool -> Bool",
            "fun x _ => x",
            "compiled true false",
            "Bool",
            "true",
            2,
        ),
        (
            "(Bool -> Bool) -> Bool -> Bool",
            "fun f x => f x",
            "compiled (fun x => x) true",
            "Bool",
            "true",
            2,
        ),
        (
            "Bool -> Nat",
            "fun b => if b then 42 else 7",
            "compiled true",
            "Nat",
            "42",
            1,
        ),
        (
            "Bool -> Nat",
            "fun b => if b then 42 else 7",
            "compiled false",
            "Nat",
            "7",
            1,
        ),
        (
            "Bool -> String",
            "fun b => if b then \"yes branch\" else \"no branch\"",
            "compiled true",
            "String",
            "\"yes branch\"",
            1,
        ),
        (
            "Bool -> String",
            "fun b => if b then \"yes branch\" else \"no branch\"",
            "compiled false",
            "String",
            "\"no branch\"",
            1,
        ),
        (
            "Nat -> Nat",
            "fun n => n + 1",
            "compiled 41",
            "Nat",
            "42",
            1,
        ),
        (
            "Nat -> Nat",
            "fun n => n + 1",
            "compiled 184467440737095516160",
            "Nat",
            "184467440737095516161",
            1,
        ),
        (
            "Nat -> Bool",
            "fun n => Nat.beq n 42",
            "compiled 42",
            "Bool",
            "true",
            1,
        ),
        (
            "Nat -> Bool",
            "fun n => Nat.beq n 42",
            "compiled 184467440737095516160",
            "Bool",
            "false",
            1,
        ),
        (
            "Bool -> Nat -> Nat -> Nat",
            "fun b x y => if b then x else y",
            "compiled true 42 7",
            "Nat",
            "42",
            3,
        ),
        (
            "Bool -> Nat -> Nat -> Nat",
            "fun b x y => if b then x else y",
            "compiled false 7 184467440737095516160",
            "Nat",
            "184467440737095516160",
            3,
        ),
        (
            "String -> String",
            "fun text => String.append text \"!\"",
            "compiled \"native\"",
            "String",
            "\"native!\"",
            1,
        ),
        (
            "Nat -> Nat",
            "fun n => if Nat.beq n 0 then 7 else n + 1",
            "compiled 0",
            "Nat",
            "7",
            1,
        ),
        (
            "Nat -> Nat",
            "fun n => if Nat.beq n 0 then 7 else n + 1",
            "compiled 41",
            "Nat",
            "42",
            1,
        ),
        (
            "Nat -> Nat",
            "fun n => if Nat.beq n 0 then 7 else n + 1",
            "compiled 184467440737095516160",
            "Nat",
            "184467440737095516161",
            1,
        ),
        (
            "Bool -> Nat",
            "fun b => if b then (if b then 42 else 7) else 99",
            "compiled true",
            "Nat",
            "42",
            1,
        ),
        (
            "Bool -> Nat -> String",
            "fun b _ => if b then \"yes\" else \"no\"",
            "compiled false 7",
            "String",
            "\"no\"",
            2,
        ),
    ]
}

fn erased_positions(index: usize) -> &'static [usize] {
    match index {
        13 | 21 => &[1],
        14..=20 => &[0],
        22 | 31 => &[0],
        _ => &[],
    }
}

fn boolean_positions(index: usize) -> &'static [usize] {
    match index {
        25..=28 | 32 | 33 | 36..=39 | 44 | 45 | 50 | 51 => &[0],
        29..=31 | 35 => &[1],
        34 => &[0, 1],
        _ => &[],
    }
}

fn checked_definition(base: &Engine, source: &str) -> (fln::Declaration, Engine) {
    let checked = base
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            fln::SourceCheckLimits::new(EngineAdmissionLimits::new(limits().kernel)),
        )
        .unwrap_or_else(|e| panic!("{source}: {e:?}"))
        .into_complete()
        .unwrap();
    let environment = checked.engine.environment();
    let fln::ConstantInfo::Defn(definition) = environment.find(&name("compiled")).unwrap() else {
        panic!("source definition")
    };
    (fln::Declaration::Defn(definition.clone()), checked.engine)
}

#[test]
fn arbitrary_fir_cannot_claim_the_closed_source_constructor_boundary() {
    use fln_comp::fir::*;
    let value = ValueId::new;
    let constructor = ConstructorId::new(0);
    let program = fln_comp::fir::validate(
        Program::new(
            FunctionId::new(0),
            vec![ConstructorDecl {
                id: constructor,
                tag: 0,
                fields: vec![ValueType::Bool],
                static_scalar_bytes: vec![],
            }],
            vec![],
            vec![],
            vec![Function {
                id: FunctionId::new(0),
                parameters: vec![],
                parameter_ownership: vec![],
                result: ValueType::Constructor,
                result_ownership: fln_comp::flbc::CallableResultOwnership::Owned,
                blocks: vec![Block {
                    id: BlockId::new(0),
                    bindings: vec![
                        Binding {
                            id: value(0),
                            ty: ValueType::Bool,
                            operation: Operation::Bool(false),
                        },
                        Binding {
                            id: value(1),
                            ty: ValueType::Constructor,
                            operation: Operation::Ctor {
                                constructor,
                                fields: vec![value(0)],
                            },
                        },
                    ],
                    terminator: Terminator::Return { value: value(1) },
                }],
            }],
        ),
        ValidationLimits::default(),
    )
    .unwrap();
    assert!(matches!(
        ir::compile(&program, &name("untrustedEntry"), CompileLimits::default()),
        Err(ir::CompileError::Unsupported {
            what: "non-pure boxed carrier"
        })
    ));
}

#[test]
fn source_exports_keep_source_arguments_and_compile_without_execution() {
    let base = base();
    let options = KVMap::new();
    let original = base.logical_root(&options);
    for (index, (ty, expression, application, result_type, expected, arity)) in
        export_cases().into_iter().enumerate()
    {
        let source = format!("def compiled : {ty} := {expression}");
        let (declaration, checked) = checked_definition(&base, &source);
        let mut no_execution = limits();
        no_execution.vm.max_steps = 0;
        let compiled = ir::compile_source_definition(
            &base,
            declaration.clone(),
            &options,
            no_execution,
            CompileLimits::default(),
        )
        .unwrap_or_else(|e| panic!("{source}: {e:?}"))
        .into_complete()
        .unwrap();
        assert_eq!(compiled.entry, name("compiled"));
        assert_eq!(
            compiled.admission.result_logical_root,
            checked.logical_root(&options)
        );
        let public = compiled
            .module
            .decls
            .iter()
            .find(|d| d.name() == &name("compiled"))
            .unwrap();
        let IrDecl::Function { params, result, .. } = public else {
            panic!("source function entry")
        };
        assert_eq!(params.len(), arity, "{source}");
        assert!(params.iter().all(|p| !p.borrow));
        assert_eq!(
            params
                .iter()
                .enumerate()
                .filter_map(|(i, p)| (p.ty == IrType::UInt8).then_some(i))
                .collect::<Vec<_>>(),
            boolean_positions(index),
            "the independently specified Boolean source slots are UInt8: {source}",
        );
        assert_eq!(
            *result,
            match result_type {
                "Bool" => IrType::UInt8,
                "Nat" => IrType::TObject,
                _ => IrType::Object,
            },
            "source result carrier: {source}",
        );
        assert_eq!(
            params
                .iter()
                .enumerate()
                .filter_map(|(i, p)| (p.ty == IrType::Erased).then_some(i))
                .collect::<Vec<_>>(),
            erased_positions(index),
            "erased source slots retain their exact positions: {source}",
        );
        if !erased_positions(index).is_empty() || !boolean_positions(index).is_empty() {
            let boxed = compiled
                .module
                .decls
                .iter()
                .find(|d| d.name() == &name("compiled._boxed"))
                .unwrap();
            let IrDecl::Function {
                params: boxed,
                result: boxed_result,
                ..
            } = boxed
            else {
                panic!("source boxed entry")
            };
            assert_eq!(boxed.len(), arity);
            for &position in erased_positions(index) {
                assert_eq!(boxed[position].ty, IrType::TObject);
            }
            for &position in boolean_positions(index) {
                assert_eq!(boxed[position].ty, IrType::Tagged);
            }
            if result_type == "Bool" {
                assert_eq!(*boxed_result, IrType::Tagged);
            }
        }
        let source = format!("def result : {result_type} := {application}");
        let executed = checked
            .execute_source_definitions(&[source.as_bytes()], &options, limits())
            .unwrap_or_else(|e| panic!("{source}: {e:?}"))
            .into_complete()
            .unwrap();
        let VmExit::Returned(value) = &executed.executions[0].exit else {
            panic!("native source application")
        };
        if result_type == "Nat" {
            assert_eq!(
                fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
                Some(expected)
            );
        } else if result_type == "Bool" {
            assert!(value.value.is_scalar());
            assert_eq!(value.value.unbox(), usize::from(expected == "true"));
        } else {
            let string = value.value.try_string_view().unwrap();
            assert_eq!(
                &string.3[..string.0 - 1],
                expected.trim_matches('"').as_bytes()
            );
        }
        assert!(matches!(
            ir::compile_source_definition(
                &base,
                declaration,
                &options,
                no_execution,
                CompileLimits {
                    max_work: 0,
                    ..CompileLimits::default()
                },
            ),
            Err(ir::DefinitionCompileError::Ir(ir::CompileError::Limit))
        ));
        assert_eq!(base.logical_root(&options), original);
    }
    // Retain the exact formerly unsupported input as a positive, including its
    // dependent proof domain, rather than merely dropping it from the negatives.
    let source = "def compiled (x : Nat) (_h : x = x) : Nat := x";
    let (declaration, checked) = checked_definition(&base, source);
    let compiled = ir::compile_source_definition(
        &base,
        declaration,
        &options,
        limits(),
        CompileLimits::default(),
    )
    .unwrap()
    .into_complete()
    .unwrap();
    assert_eq!(
        compiled.admission.result_logical_root,
        checked.logical_root(&options)
    );
    assert_eq!(base.logical_root(&options), original);
    for source in [
        "def compiled {A : Type} (x : A) : A := x",
        "universe u\ndef compiled {A : Type u} (x : A) : A := x",
        "def compiled {A : Type} (x : A) : Nat := 42",
        "def compiled (P : Prop) : P -> P := fun x => x",
        "def compiled : Nat -> Type := fun _ => Nat",
        "def compiled : (Nat -> Nat) -> Nat -> Nat := invoke",
        "def compiled (x y : Nat) : Nat := keep x",
        "def compiled (x y : Nat) : Nat := let saved := x; saved",
        "def compiled (f : Nat -> Nat) (x : Nat) : Nat := x",
    ] {
        let (declaration, _) = checked_definition(&base, source);
        assert!(
            matches!(
                ir::compile_source_definition(
                    &base,
                    declaration,
                    &options,
                    limits(),
                    CompileLimits::default(),
                ),
                Err(ir::DefinitionCompileError::Ir(
                    ir::CompileError::Unsupported { .. }
                ))
            ),
            "{source}"
        );
        assert_eq!(base.logical_root(&options), original);
    }
    for (source, refused) in [
        (
            "def compiled (x y : Nat) : Nat := let b := true; if b then x else y",
            "local Boolean source discriminator",
        ),
        (
            "def compiled (h : Nat -> Nat) (b : Bool) : Nat := let x := 0; let y := 0; h (if b then x else y)",
            "local Boolean source arm",
        ),
    ] {
        let (declaration, _) = checked_definition(&base, source);
        assert!(
            matches!(
                ir::compile_source_definition(
                    &base,
                    declaration,
                    &options,
                    limits(),
                    CompileLimits::default(),
                ),
                Err(ir::DefinitionCompileError::Ir(ir::CompileError::Unsupported { what }))
                    if what == refused
            ),
            "a local constant must not change the guessed reduced ABI: {source}"
        );
        assert_eq!(base.logical_root(&options), original);
    }
    let (fln::Declaration::Defn(mut wrong), _) =
        checked_definition(&base, "def compiled : Nat := 42")
    else {
        panic!("ordinary definition")
    };
    wrong.value = fln_core::expr::Expr::lit(fln_core::expr::Literal::Str("not a Nat".into()));
    assert!(matches!(
        ir::compile_source_definition(
            &base,
            fln::Declaration::Defn(wrong),
            &options,
            limits(),
            CompileLimits::default(),
        ),
        Err(ir::DefinitionCompileError::Engine(_))
    ));
    assert_eq!(base.logical_root(&options), original);
}

// Valid FIR permits a borrowed argument to alias a consumed argument. Unlike
// source parameters (normally borrowed), this exercises that mixed contract
// directly, with a freshly allocated closure whose last owner is transferred.
fn aliased_borrow_program(tail: bool) -> fln_comp::fir::ValidatedProgram {
    use fln_comp::fir::{self, *};
    use fln_comp::flbc::{ArgumentOwnership as A, CallableResultOwnership as R};
    let v = ValueId::new;
    let f = FunctionId::new;
    let signature = ClosureTypeId::new(0);
    let closure = ValueType::Closure(signature);
    let binding = |id, ty, operation| Binding {
        id: v(id),
        ty,
        operation,
    };
    let apply = |closure, arg| Operation::Apply {
        closure: v(closure),
        args: vec![v(arg)],
        argument_ownership: vec![A::Borrowed],
        result_ownership: R::Owned,
    };
    let block = |bindings, result| {
        vec![Block {
            id: BlockId::new(0),
            bindings,
            terminator: Terminator::Return { value: v(result) },
        }]
    };
    let mut entry = vec![
        binding(
            0,
            ValueType::String,
            Operation::String("aliased borrow".into()),
        ),
        binding(
            1,
            closure,
            Operation::Closure {
                closure_type: signature,
                function: f(2),
                captures: vec![v(0)],
                capture_ownership: vec![A::Borrowed],
            },
        ),
        binding(
            2,
            if tail { ValueType::String } else { closure },
            Operation::Call {
                function: f(1),
                args: vec![v(1), v(1)],
            },
        ),
    ];
    if !tail {
        entry.push(binding(3, ValueType::Nat, Operation::Nat(7)));
        entry.push(binding(4, ValueType::String, apply(2, 3)));
    }
    let alias_body = if tail {
        block(
            vec![
                binding(2, ValueType::Nat, Operation::Nat(7)),
                binding(3, ValueType::String, apply(1, 2)),
            ],
            3,
        )
    } else {
        block(vec![], 1)
    };
    fir::validate(
        Program::new_with_closures(
            f(0),
            vec![],
            vec![],
            vec![ClosureTypeDecl {
                id: signature,
                parameters: vec![ValueType::Nat],
                parameter_ownership: vec![A::Borrowed],
                result: ValueType::String,
                result_ownership: R::Owned,
            }],
            vec![],
            vec![
                Function {
                    id: f(0),
                    parameters: vec![],
                    parameter_ownership: vec![],
                    result: ValueType::String,
                    result_ownership: R::Owned,
                    blocks: block(entry, if tail { 2 } else { 4 }),
                },
                Function {
                    id: f(1),
                    parameters: vec![closure, closure],
                    parameter_ownership: vec![A::Owned, A::Borrowed],
                    result: if tail { ValueType::String } else { closure },
                    result_ownership: R::Owned,
                    blocks: alias_body,
                },
                Function {
                    id: f(2),
                    parameters: vec![ValueType::String, ValueType::Nat],
                    parameter_ownership: vec![A::Borrowed, A::Borrowed],
                    result: ValueType::String,
                    result_ownership: R::Owned,
                    blocks: block(vec![], 0),
                },
            ],
        ),
        ValidationLimits::default(),
    )
    .unwrap()
}

fn cached_closure_program() -> fln_comp::fir::ValidatedProgram {
    use fln_comp::fir::{self, *};
    use fln_comp::flbc::{ArgumentOwnership as A, CallableResultOwnership as R};
    let template = aliased_borrow_program(false);
    let closure = ValueType::Closure(ClosureTypeId::new(0));
    let v = ValueId::new;
    let binding = |id, ty, operation| Binding {
        id: v(id),
        ty,
        operation,
    };
    let call = || Operation::Call {
        function: FunctionId::new(1),
        args: vec![],
    };
    let apply = |id| Operation::Apply {
        closure: v(id),
        args: vec![v(1)],
        argument_ownership: vec![A::Borrowed],
        result_ownership: R::Owned,
    };
    let block = |bindings, result| {
        vec![Block {
            id: BlockId::new(0),
            bindings,
            terminator: Terminator::Return { value: v(result) },
        }]
    };
    let mut functions = template.functions().to_vec();
    functions[0].blocks = block(
        vec![
            binding(0, closure, call()),
            binding(1, ValueType::Nat, Operation::Nat(7)),
            binding(2, ValueType::String, apply(0)),
            binding(3, closure, call()),
            binding(4, ValueType::String, apply(3)),
        ],
        4,
    );
    functions[1] = Function {
        id: FunctionId::new(1),
        parameters: vec![],
        parameter_ownership: vec![],
        result: closure,
        result_ownership: R::Owned,
        blocks: block(
            vec![
                binding(
                    0,
                    ValueType::String,
                    Operation::String("cached closure".into()),
                ),
                binding(
                    1,
                    closure,
                    Operation::Closure {
                        closure_type: ClosureTypeId::new(0),
                        function: FunctionId::new(2),
                        captures: vec![v(0)],
                        capture_ownership: vec![A::Borrowed],
                    },
                ),
            ],
            1,
        ),
    };
    fir::validate(
        Program::new_with_closures(
            FunctionId::new(0),
            vec![],
            vec![],
            template.closure_types().to_vec(),
            vec![],
            functions,
        ),
        ValidationLimits::default(),
    )
    .unwrap()
}

fn replace_result(params: &[fln_olean::ir::IrParam], body: &mut IrBody, ty: &str) {
    let mut stmts: Vec<_> = params
        .iter()
        .filter(|p| !p.borrow && p.ty != IrType::Erased && p.ty != IrType::UInt8)
        .map(|p| IrStmt::Dec {
            x: p.x,
            n: 1,
            checked: true,
            persistent: false,
        })
        .collect();
    let result = params.iter().map(|p| p.x).max().unwrap_or(0) + 1;
    stmts.push(IrStmt::VDecl {
        x: result,
        ty: if ty == "Nat" {
            IrType::Tagged
        } else {
            IrType::Object
        },
        expr: IrExpr::Lit(if ty == "Nat" {
            IrLit::Num(IrNat::Small(99))
        } else {
            IrLit::Str("changed IR".into())
        }),
    });
    *body = IrBody {
        stmts,
        terminal: Box::new(IrTerminal::Ret(IrArg::Var(result))),
    };
}

fn replace_boolean_result(
    params: &[fln_olean::ir::IrParam],
    body: &mut IrBody,
    carrier: IrType,
    value: bool,
) {
    let mut stmts: Vec<_> = params
        .iter()
        .filter(|p| !p.borrow && matches!(p.ty, IrType::Object | IrType::TObject | IrType::Tagged))
        .map(|p| IrStmt::Dec {
            x: p.x,
            n: 1,
            checked: true,
            persistent: false,
        })
        .collect();
    let x = params.iter().map(|p| p.x).max().unwrap_or(0) + 1;
    stmts.push(IrStmt::VDecl {
        x,
        ty: carrier,
        expr: IrExpr::Lit(IrLit::Num(IrNat::Small(u64::from(value)))),
    });
    *body = IrBody {
        stmts,
        terminal: Box::new(IrTerminal::Ret(IrArg::Var(x))),
    };
}

#[test]
fn admitted_definitions_compile_without_execution_and_keep_their_root() {
    let base = base();
    let options = KVMap::new();
    let original = base.logical_root(&options);
    for (ty, expression, expected) in cases() {
        let source = format!("def generated : {ty} := {expression}");
        let run = base
            .execute_source_definitions(&[source.as_bytes()], &options, limits())
            .unwrap()
            .into_complete()
            .unwrap();
        let execution = &run.executions[0];
        let VmExit::Returned(value) = &execution.exit else {
            panic!("{source}: {:?}", execution.exit)
        };
        if ty == "Nat" {
            assert_eq!(
                fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
                Some(expected)
            );
        } else {
            assert_eq!(
                value.value.try_string_view().unwrap().3
                    [..value.value.try_string_view().unwrap().0 - 1],
                expected.trim_matches('"').as_bytes()[..]
            );
        }
        let mut no_execution = limits();
        no_execution.vm.max_steps = 0;
        let compiled = ir::compile_definition(
            &base,
            execution.declaration.clone(),
            &name("compiled"),
            &options,
            no_execution,
            CompileLimits::default(),
        )
        .unwrap_or_else(|e| panic!("{source}: {e:?}"))
        .into_complete()
        .unwrap();
        assert_eq!(
            compiled.admission.result_logical_root,
            run.result_logical_root
        );
        assert_eq!(base.logical_root(&options), original);
        fln_olean::ir_validate::validate_ir(
            std::slice::from_ref(&compiled.module),
            &BTreeMap::new(),
            Default::default(),
        )
        .unwrap();
        if expression.contains("invoke") {
            assert!(
                compiled.module.decls.len() > 2,
                "callbacks must reach the backend"
            );
            assert!(
                compiled.module.decls.iter().any(|d| match d {
                    IrDecl::Function { body, .. } => body.stmts.iter().any(|s| matches!(
                        s,
                        IrStmt::VDecl {
                            expr: IrExpr::Ap { .. },
                            ..
                        }
                    )),
                    _ => false,
                }),
                "the callback application cannot be folded out of this control"
            );
        }
        let stopped = ir::compile_definition(
            &base,
            execution.declaration.clone(),
            &name("compiled"),
            &options,
            no_execution,
            CompileLimits {
                max_work: 0,
                ..CompileLimits::default()
            },
        );
        assert!(matches!(
            stopped,
            Err(ir::DefinitionCompileError::Ir(ir::CompileError::Limit))
        ));
        assert_eq!(base.logical_root(&options), original);
    }
}

fn reference() -> Option<PathBuf> {
    let lean = std::env::var_os("FLN_REFERENCE_LEAN")
        .map(PathBuf::from)
        .or_else(|| {
            std::env::var_os("HOME").map(|p| {
                PathBuf::from(p).join(".elan/toolchains/leanprover--lean4---v4.32.0/bin/lean")
            })
        })?;
    lean.is_file().then_some(lean)
}

fn imported_strings(lib: &Path, stack: usize) -> Engine {
    use fln::source_check::modules::imported::SourceOleanImportLimits;
    use fln::{
        Environment, OleanCheckLimits, OleanDecodeLimits, OleanFrontierJobs, OleanModuleInput,
    };

    type Parts = (Vec<u8>, Option<Vec<u8>>, Option<Vec<u8>>);
    let root = name("Init.Data.String.Length");
    let mut pending = vec![root.clone()];
    let mut artifacts = BTreeMap::<Name, Parts>::new();
    while let Some(module) = pending.pop() {
        if artifacts.contains_key(&module) {
            continue;
        }
        let path = lib
            .join(module.to_display_string().replace('.', "/"))
            .with_extension("olean");
        let public = std::fs::read(&path).unwrap();
        pending.extend(fln::olean_module_imports(&public, OleanDecodeLimits::new(stack)).unwrap());
        let optional = |path| match std::fs::read(path) {
            Ok(bytes) => Some(bytes),
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => None,
            Err(error) => panic!("read companion: {error}"),
        };
        artifacts.insert(
            module,
            (
                public,
                optional(path.with_extension("olean.server")),
                optional(path.with_extension("olean.private")),
            ),
        );
    }
    let inputs: Vec<_> = artifacts
        .iter()
        .map(|(name, (public, server, private))| OleanModuleInput {
            name,
            artifact: public,
            server_artifact: server.as_deref(),
            private_artifact: private.as_deref(),
        })
        .collect();
    let mut admission =
        SourceOleanImportLimits::new(OleanCheckLimits::new(stack, Budget::for_stack_bytes(stack)));
    admission.jobs = OleanFrontierJobs {
        threads: std::num::NonZeroUsize::new(1).unwrap(),
        worker_stack_bytes: stack,
    };
    Engine::from_environment(Environment::new())
        .import_olean_modules_for_source(&inputs, &[root], &KVMap::new(), admission)
        .unwrap()
        .into_complete()
        .unwrap()
        .engine
}

fn encode(module: &fln_olean::ir::IrModule, original: &[u8]) -> Vec<u8> {
    let view = OleanView::parse(original).unwrap();
    let metadata = view.module_data(WalkBudget::default()).unwrap();
    let blocks = view
        .extension_payloads(WalkBudget::default(), 64 * 1024 * 1024)
        .unwrap();
    let extras: Vec<_> = blocks
        .iter()
        .filter(|b| b.name != name("Lean.IR.declMapExt") && b.name != name("Lean.regularInitAttr"))
        .map(|b| {
            (
                b.name.clone(),
                b.entries
                    .iter()
                    .map(|p| fln_rt::region::materialize(p, 0).unwrap())
                    .collect::<Vec<_>>(),
            )
        })
        .collect();
    let extensions: Vec<_> = extras
        .iter()
        .map(|(name, entries)| fln_olean::ModuleExtensionInput { name, entries })
        .collect();
    let mut extra_names: BTreeSet<_> = view
        .extra_const_names(WalkBudget::default())
        .unwrap()
        .into_iter()
        .collect();
    extra_names.extend(module.decls.iter().map(|d| d.name().clone()));
    let extra_names: Vec<_> = extra_names.into_iter().collect();
    encode_ir(
        IrWriteInput {
            module: ModuleWriteInput {
                is_module: metadata.is_module,
                imports: &metadata.imports,
                constants: &[],
                extra_const_names: &extra_names,
            },
            declarations: &module.decls,
            initializers: &module.initializers,
            additional_extensions: &extensions,
        },
        OleanWriteHeader {
            version: view.header.version,
            flags: view.header.flags,
            lean_version: &view.header.lean_version,
            githash: &view.header.githash,
            base_addr: view.header.base_addr,
        },
        IrWriteLimits::default(),
    )
    .unwrap()
    .bytes
}

fn consume(lean: &Path, dir: &Path) -> std::process::Output {
    Command::new(lean)
        .current_dir(dir)
        .env("LEAN_PATH", dir)
        .arg("Consumer.lean")
        .output()
        .unwrap()
}

struct RuntimeProbe<'a> {
    ty: &'a str,
    application: &'a str,
    entry: &'a str,
    check_meta: bool,
    higher_universe: bool,
    heap_call: Option<&'a str>,
}

fn consume_ir(
    lean: &Path,
    dir: &Path,
    label: &str,
    probe: &RuntimeProbe<'_>,
) -> std::process::Output {
    // Import only Lean statically. Loading the target and retrieving its value
    // at runtime prevents compiler inlining of logical companion bodies from
    // making an IR-body mutation invisible. Types come from the checked source
    // signature; generated reduced entries use independently specified cases.
    // The pin's public evalConst fixes its value universe at Type 0. A source
    // type such as Type -> Nat -> Nat is in Type 1. Lift only the lookup
    // function's erased universe, preserving all runtime arguments, its meta
    // check, and the EXACT original source type passed to the lookup. This is
    // an unsafe Reference-oracle adapter, never production Rust or a cast of
    // the target value to a different source telescope. The pin-original IR
    // positive below must pass through this same adapter before native IR.
    let (adapter, evaluation) = if probe.higher_universe {
        (
            "universe u\nprivate unsafe def evalConstAt :\n    (α : Type u) -> Lean.Environment -> Lean.Options -> Lean.Name -> Bool -> Except String α :=\n  unsafeCast (@Lean.Environment.evalConst)\n",
            format!(
                "evalConstAt ({}) env {{}} `{} {}",
                probe.ty, probe.entry, probe.check_meta,
            ),
        )
    } else {
        (
            "",
            format!(
                "env.evalConst ({}) {{}} `{} (checkMeta := {})",
                probe.ty, probe.entry, probe.check_meta,
            ),
        )
    };
    let mut source = format!(
        "import Lean\n{adapter}unsafe def main : IO Unit := do\n  Lean.enableInitializersExecution\n  let env ← Lean.importModules #[{{ module := `NativeIrCase, isMeta := true }}] {{}} (loadExts := true)\n  match {evaluation} with\n  | .error message => throw (IO.userError message)\n  | .ok compiled => do\n    IO.println (reprStr ({}))\n    IO.println (reprStr ({}))\n",
        probe.application, probe.application,
    );
    if let Some(call) = probe.heap_call {
        source.push_str(&format!("    let saved ← IO.FS.readFile \"heap-input.txt\"\n    let got := {call}\n    IO.println (reprStr (got, saved))\n"));
    }
    let filename = format!("Runtime-{label}.lean");
    std::fs::write(dir.join(&filename), source).unwrap();
    Command::new(lean)
        .current_dir(dir)
        .env("LEAN_PATH", dir)
        .args(["-j", "1", "--run", &filename])
        .output()
        .unwrap()
}

fn assert_probe(output: std::process::Output, dir: &Path, label: &str, expected: &str) {
    std::fs::write(dir.join(format!("{label}.stdout")), &output.stdout).unwrap();
    std::fs::write(dir.join(format!("{label}.stderr")), &output.stderr).unwrap();
    assert!(
        output.status.success(),
        "{label}: {:?}: {} {}",
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(
        String::from_utf8(output.stdout).unwrap().trim(),
        expected,
        "{label}"
    );
}

fn reduced_case(index: usize) -> Option<(&'static str, &'static str)> {
    match index {
        7 | 11 => Some(("Nat -> Nat", "compiled 184467440737095516160")),
        10 => Some(("Nat -> Nat", "compiled 42")),
        12 => Some(("String -> String", "compiled \"retained string\"")),
        19 => Some(("String -> String", "compiled \"erased type string\"")),
        13 | 16 => Some(("Nat -> Nat", "compiled 42")),
        15 | 21 => Some(("Nat -> Nat", "compiled 184467440737095516160")),
        22 => Some((
            "(Nat -> String) -> Nat -> String",
            "compiled (fun _ => \"typed callback\") 7",
        )),
        28 => Some(("Nat -> Nat", "compiled 42")),
        29 | 31 | 34 => Some(("Bool -> Bool", "compiled true")),
        32 => Some(("String -> String", "compiled \"retained Boolean string\"")),
        51 => Some(("Bool -> String", "compiled false")),
        _ => None,
    }
}

#[test]
fn the_pin_executes_native_compiler_output_and_observes_changed_bodies() {
    let Some(lean) = reference() else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "pinned Reference is required"
        );
        eprintln!("SKIP: native IR compilation consumer requires the pin");
        return;
    };
    let pin = include_str!("../../../SUITE.lock")
        .lines()
        .find(|s| s.starts_with("reference "))
        .unwrap()
        .split_whitespace()
        .find_map(|s| s.strip_prefix("commit="))
        .unwrap();
    let identity = Command::new(&lean).arg("--githash").output().unwrap();
    assert!(identity.status.success());
    assert_eq!(String::from_utf8(identity.stdout).unwrap().trim(), pin);
    let base = base();
    let options = KVMap::new();
    let root = std::env::var_os("FLN_IR_REFERENCE_ARTIFACTS")
        .map(PathBuf::from)
        .unwrap_or_else(std::env::temp_dir);
    for (index, (ty, expression, expected)) in cases()
        .into_iter()
        .chain([
            ("String", "\"aliased borrow\"", "\"aliased borrow\""),
            ("String", "\"aliased borrow\"", "\"aliased borrow\""),
            ("String", "\"cached closure\"", "\"cached closure\""),
        ])
        .enumerate()
    {
        let unique = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let dir = root.join(format!(
            "native-ir-compiler-{}-{unique}-{index}",
            std::process::id()
        ));
        std::fs::create_dir_all(&dir).unwrap();
        let source = format!("def generated : {ty} := {expression}");
        let run = base
            .execute_source_definitions(&[source.as_bytes()], &options, limits())
            .unwrap()
            .into_complete()
            .unwrap();
        let mut compiled = ir::compile_definition(
            &base,
            run.executions[0].declaration.clone(),
            &name("compiled"),
            &options,
            limits(),
            CompileLimits::default(),
        )
        .unwrap_or_else(|e| panic!("{source}: {e:?}"))
        .into_complete()
        .unwrap();
        if index >= cases().len() {
            // These final three are lower-level FIR compiler controls, not
            // claims that this FIR was derived from the source declaration.
            let program = if index == cases().len() + 2 {
                cached_closure_program()
            } else {
                aliased_borrow_program(index == cases().len() + 1)
            };
            let lowered =
                fln_comp::fir::lower_to_flbc_with_ownership(&program, Default::default()).unwrap();
            let bytes =
                fln_comp::flbc::encode_canonical(lowered.program(), Default::default()).unwrap();
            let execution = fln::execute_flbc_artifact(&bytes, &options, Default::default())
                .unwrap()
                .into_complete()
                .unwrap();
            let VmExit::Returned(value) = execution else {
                panic!("valid aliased-borrow FIR must execute")
            };
            let view = value.value.try_string_view().unwrap();
            assert_eq!(
                view.3[..view.0 - 1],
                expected.trim_matches('"').as_bytes()[..]
            );
            compiled.module =
                ir::compile(&program, &name("compiled"), CompileLimits::default()).unwrap();
        }
        // The oracle supplies the logical companions only. Its IR bodies are
        // retained as a control and never supplied to the native compiler.
        std::fs::write(
            dir.join("NativeIrCase.lean"),
            format!("module\n{HELPERS}\npublic opaque compiled : {ty} := {expression}\n"),
        )
        .unwrap();
        let generated = Command::new(&lean)
            .current_dir(&dir)
            .args(["-o", "NativeIrCase.olean", "NativeIrCase.lean"])
            .output()
            .unwrap();
        std::fs::write(dir.join("compile.stdout"), &generated.stdout).unwrap();
        std::fs::write(dir.join("compile.stderr"), &generated.stderr).unwrap();
        assert!(
            generated.status.success(),
            "{}{}",
            String::from_utf8_lossy(&generated.stdout),
            String::from_utf8_lossy(&generated.stderr)
        );
        let original = std::fs::read(dir.join("NativeIrCase.ir")).unwrap();
        std::fs::write(dir.join("original.ir"), &original).unwrap();
        let bytes = encode(&compiled.module, &original);
        std::fs::write(dir.join("NativeIrCase.ir"), &bytes).unwrap();
        std::fs::write(
            dir.join("Consumer.lean"),
            "module\nmeta import NativeIrCase\n#eval compiled\n",
        )
        .unwrap();
        let result = consume(&lean, &dir);
        std::fs::write(dir.join("native.stdout"), &result.stdout).unwrap();
        std::fs::write(dir.join("native.stderr"), &result.stderr).unwrap();
        assert!(
            result.status.success(),
            "{source} in {} ({:?}): {}{}",
            dir.display(),
            result.status,
            String::from_utf8_lossy(&result.stdout),
            String::from_utf8_lossy(&result.stderr)
        );
        assert_eq!(
            String::from_utf8(result.stdout).unwrap().trim(),
            expected,
            "{source}"
        );
        let mut mutant = compiled.module.clone();
        let target = mutant
            .decls
            .iter_mut()
            .find(|d| d.name() == &name("compiled"))
            .unwrap();
        let IrDecl::Function { body, .. } = target else {
            panic!("entry is a function")
        };
        let (ir_type, literal, wanted) = if ty == "Nat" {
            (IrType::Tagged, IrLit::Num(IrNat::Small(99)), "99")
        } else {
            (
                IrType::Object,
                IrLit::Str("changed IR".into()),
                "\"changed IR\"",
            )
        };
        *body = IrBody {
            stmts: vec![IrStmt::VDecl {
                x: 1,
                ty: ir_type,
                expr: IrExpr::Lit(literal),
            }],
            terminal: Box::new(IrTerminal::Ret(IrArg::Var(1))),
        };
        std::fs::write(dir.join("NativeIrCase.ir"), encode(&mutant, &original)).unwrap();
        let changed = consume(&lean, &dir);
        std::fs::write(dir.join("mutant.stdout"), &changed.stdout).unwrap();
        std::fs::write(dir.join("mutant.stderr"), &changed.stderr).unwrap();
        assert!(changed.status.success());
        assert_eq!(String::from_utf8(changed.stdout).unwrap().trim(), wanted);
        if expression.contains("invoke") {
            // Keep the root unchanged: the Reference must reach a callback
            // application emitted by this backend, rather than an unused one.
            let mut mutant = compiled.module.clone();
            let mut changed_functions = 0;
            for declaration in &mut mutant.decls {
                let IrDecl::Function { params, body, .. } = declaration else {
                    continue;
                };
                if !body.stmts.iter().any(|stmt| {
                    matches!(
                        stmt,
                        IrStmt::VDecl {
                            expr: IrExpr::Ap { .. },
                            ..
                        }
                    )
                }) {
                    continue;
                }
                changed_functions += 1;
                replace_result(params, body, ty);
            }
            assert!(changed_functions > 0);
            std::fs::write(dir.join("NativeIrCase.ir"), encode(&mutant, &original)).unwrap();
            let changed = consume(&lean, &dir);
            std::fs::write(dir.join("callback-mutant.stdout"), &changed.stdout).unwrap();
            std::fs::write(dir.join("callback-mutant.stderr"), &changed.stderr).unwrap();
            assert!(changed.status.success());
            assert_eq!(String::from_utf8(changed.stdout).unwrap().trim(), wanted);
        }
        // Change only boxed entry bodies. A PAP aimed at the borrowing base
        // would ignore this control and leak the operands it is given to own.
        let mut mutant = compiled.module.clone();
        let mut boxed_entries = 0;
        for declaration in &mut mutant.decls {
            let IrDecl::Function {
                name, params, body, ..
            } = declaration
            else {
                continue;
            };
            if name.to_display_string().ends_with("._boxed") {
                replace_result(params, body, ty);
                boxed_entries += 1;
            }
        }
        if expression.contains("invoke") || index >= cases().len() {
            assert!(
                boxed_entries > 0,
                "the boxed-entry control must not be vacuous"
            );
            std::fs::write(dir.join("NativeIrCase.ir"), encode(&mutant, &original)).unwrap();
            let changed = consume(&lean, &dir);
            std::fs::write(dir.join("boxed-mutant.stdout"), &changed.stdout).unwrap();
            std::fs::write(dir.join("boxed-mutant.stderr"), &changed.stderr).unwrap();
            assert!(
                changed.status.success(),
                "boxed mutant: {:?}",
                changed.status
            );
            assert_eq!(String::from_utf8(changed.stdout).unwrap().trim(), wanted);
        }
        std::fs::write(dir.join("NativeIrCase.ir"), bytes).unwrap();
    }
}

#[test]
fn the_pin_executes_imported_string_source_exports() {
    let Some(lean) = reference() else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "pinned Reference is required"
        );
        eprintln!("SKIP: imported String IR exports require the pin");
        return;
    };
    let lib = std::env::var_os("FLN_REFERENCE_LIB")
        .map(PathBuf::from)
        .unwrap_or_else(|| lean.parent().unwrap().parent().unwrap().join("lib/lean"));
    assert!(lib.is_dir(), "the pinned Reference library is required");
    let pin = include_str!("../../../SUITE.lock")
        .lines()
        .find(|s| s.starts_with("reference "))
        .unwrap()
        .split_whitespace()
        .find_map(|s| s.strip_prefix("commit="))
        .unwrap();
    let identity = Command::new(&lean).arg("--githash").output().unwrap();
    assert!(identity.status.success());
    assert_eq!(String::from_utf8(identity.stdout).unwrap().trim(), pin);

    // Import the real checked String declarations, including their extern
    // journal and private/server companions. A name-shaped fixture is not
    // sufficient authority for these source intrinsics.
    let stack = 256 * 1024 * 1024;
    std::thread::Builder::new()
        .stack_size(stack)
        .spawn(move || {
            let base = imported_strings(&lib, stack);
            let options = KVMap::new();
            let original_root = base.logical_root(&options);
            let root = std::env::var_os("FLN_IR_REFERENCE_ARTIFACTS")
                .map(PathBuf::from)
                .unwrap_or_else(std::env::temp_dir);
            struct Case {
                native: &'static str,
                ty: &'static str,
                expression: &'static str,
                application: &'static str,
                expected: &'static str,
                heap_expected: &'static str,
            }
            for case in [
                Case {
                    native: "String.length",
                    ty: "String -> Nat",
                    expression: "fun s => String.length s",
                    application: "(compiled \"\", compiled \"é😀a\", compiled \"é\")",
                    expected: "(0, 3, 2)",
                    heap_expected: "(8, \"fresh λ😀\")",
                },
                Case {
                    native: "String.Internal.length",
                    ty: "String -> Nat",
                    expression: "fun s => String.Internal.length s",
                    application: "(compiled \"\", compiled \"é😀a\", compiled \"é\")",
                    expected: "(0, 3, 2)",
                    heap_expected: "(8, \"fresh λ😀\")",
                },
                Case {
                    native: "String.utf8ByteSize",
                    ty: "String -> Nat",
                    expression: "fun s => String.utf8ByteSize s",
                    application: "(compiled \"\", compiled \"é😀a\", compiled \"é\")",
                    expected: "(0, 7, 3)",
                    heap_expected: "(12, \"fresh λ😀\")",
                },
                Case {
                    native: "String.Internal.append",
                    ty: "String -> String",
                    expression: "fun s => String.Internal.append s s",
                    application: "(compiled \"\", compiled \"é😀a\", compiled \"é\")",
                    expected: "(\"\", \"é😀aé😀a\", \"éé\")",
                    heap_expected: "(\"fresh λ😀fresh λ😀\", \"fresh λ😀\")",
                },
                Case {
                    native: "String.append",
                    ty: "String -> String",
                    expression: "fun s => String.append s s",
                    application: "(compiled \"\", compiled \"é😀a\", compiled \"é\")",
                    expected: "(\"\", \"é😀aé😀a\", \"éé\")",
                    heap_expected: "(\"fresh λ😀fresh λ😀\", \"fresh λ😀\")",
                },
                Case {
                    native: "String.decEq",
                    ty: "String -> Bool",
                    expression: "fun s => decide (s = \"fresh λ😀\")",
                    application: "(compiled \"\", compiled \"fresh λ😀\", compiled \"fresh λ😃\")",
                    expected: "(false, true, false)",
                    heap_expected: "(true, \"fresh λ😀\")",
                },
            ] {
                let source = format!("def compiled : {} := {}", case.ty, case.expression);
                let (declaration, checked) = checked_definition(&base, &source);
                let mut no_execution = EngineExecutionLimits::new(Budget::for_stack_bytes(stack));
                no_execution.vm.max_steps = 0;
                let compiled = ir::compile_source_definition(
                    &base,
                    declaration,
                    &options,
                    no_execution,
                    CompileLimits::default(),
                )
                .unwrap_or_else(|error| panic!("{source}: {error:?}"))
                .into_complete()
                .unwrap();
                assert_eq!(compiled.admission.result_logical_root, checked.logical_root(&options));
                assert_eq!(base.logical_root(&options), original_root);
                let native = name(case.native);
                assert!(compiled.module.decls.iter().any(|declaration| {
                    let IrDecl::Function { body, .. } = declaration else { return false };
                    body.bodies().iter().any(|body| body.stmts.iter().any(|stmt| {
                        matches!(stmt, IrStmt::VDecl { expr: IrExpr::Fap { function, .. }, .. } if function == &native)
                    }))
                }), "{} must actually call its native primitive", case.native);

                let unique = std::time::SystemTime::now()
                    .duration_since(std::time::UNIX_EPOCH)
                    .unwrap()
                    .as_nanos();
                let dir = root.join(format!(
                    "native-string-export-{}-{unique}-{}",
                    std::process::id(),
                    case.native,
                ));
                std::fs::create_dir_all(&dir).unwrap();
                std::fs::write(
                    dir.join("NativeIrCase.lean"),
                    format!("module\npublic opaque compiled : {} := {}\n", case.ty, case.expression),
                ).unwrap();
                let generated = Command::new(&lean)
                    .current_dir(&dir)
                    .args(["-j", "1", "-o", "NativeIrCase.olean", "NativeIrCase.lean"])
                    .output()
                    .unwrap();
                std::fs::write(dir.join("compile.stdout"), &generated.stdout).unwrap();
                std::fs::write(dir.join("compile.stderr"), &generated.stderr).unwrap();
                assert!(generated.status.success(), "{source}: {} {}",
                    String::from_utf8_lossy(&generated.stdout),
                    String::from_utf8_lossy(&generated.stderr));
                let original = std::fs::read(dir.join("NativeIrCase.ir")).unwrap();
                std::fs::write(dir.join("original.ir"), &original).unwrap();
                // Heap input and the caller's retained alias exercise native
                // ownership, including passing the same String to append's
                // consuming first operand and borrowed second operand.
                std::fs::write(dir.join("heap-input.txt"), "fresh λ😀").unwrap();
                let probe = RuntimeProbe {
                    ty: case.ty,
                    application: case.application,
                    entry: "compiled",
                    check_meta: true,
                    higher_universe: false,
                    heap_call: Some("compiled saved"),
                };
                let expected = format!("{}\n{}\n{}", case.expected, case.expected, case.heap_expected);
                assert_probe(consume_ir(&lean, &dir, "string", &probe), &dir, "runtime-reference", &expected);
                let bytes = encode(&compiled.module, &original);
                std::fs::write(dir.join("native.ir"), &bytes).unwrap();
                std::fs::write(dir.join("NativeIrCase.ir"), &bytes).unwrap();
                assert_probe(consume_ir(&lean, &dir, "string", &probe), &dir, "runtime-native", &expected);

                if case.native == "String.length" {
                    // Change only the emitted call, retaining identical source
                    // companions. A runtime lookup must observe byte length,
                    // proving it consumed this physical native IR body.
                    let mut mutant = compiled.module.clone();
                    let mut switched = 0;
                    for declaration in &mut mutant.decls {
                        let IrDecl::Function { body, .. } = declaration else { continue };
                        for stmt in &mut body.stmts {
                            if let IrStmt::VDecl { expr: IrExpr::Fap { function, .. }, .. } = stmt {
                                if function == &native {
                                    *function = name("String.utf8ByteSize");
                                    switched += 1;
                                }
                            }
                        }
                    }
                    assert!(switched > 0, "the native-call mutation must not be vacuous");
                    std::fs::write(dir.join("NativeIrCase.ir"), encode(&mutant, &original)).unwrap();
                    assert_probe(consume_ir(&lean, &dir, "string", &probe), &dir,
                        "runtime-byte-size-mutant", "(0, 7, 3)\n(0, 7, 3)\n(12, \"fresh λ😀\")");
                    std::fs::write(dir.join("NativeIrCase.ir"), bytes).unwrap();
                }
            }
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn the_pin_calls_native_source_exports_directly_and_as_functions() {
    let Some(lean) = reference() else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "pinned Reference is required"
        );
        eprintln!("SKIP: source export consumer requires the pin");
        return;
    };
    let pin = include_str!("../../../SUITE.lock")
        .lines()
        .find(|s| s.starts_with("reference "))
        .unwrap()
        .split_whitespace()
        .find_map(|s| s.strip_prefix("commit="))
        .unwrap();
    let identity = Command::new(&lean).arg("--githash").output().unwrap();
    assert!(identity.status.success());
    assert_eq!(String::from_utf8(identity.stdout).unwrap().trim(), pin);
    let base = base();
    let options = KVMap::new();
    let original_root = base.logical_root(&options);
    let root = std::env::var_os("FLN_IR_REFERENCE_ARTIFACTS")
        .map(PathBuf::from)
        .unwrap_or_else(std::env::temp_dir);
    for (index, (ty, expression, application, result_type, expected, _)) in
        export_cases().into_iter().enumerate()
    {
        let source = format!("def compiled : {ty} := {expression}");
        let (declaration, checked) = checked_definition(&base, &source);
        let mut no_execution = limits();
        no_execution.vm.max_steps = 0;
        let compiled = ir::compile_source_definition(
            &base,
            declaration,
            &options,
            no_execution,
            CompileLimits::default(),
        )
        .unwrap_or_else(|e| panic!("{source}: {e:?}"))
        .into_complete()
        .unwrap();
        assert_eq!(
            compiled.admission.result_logical_root,
            checked.logical_root(&options)
        );
        let unique = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let dir = root.join(format!(
            "native-source-export-{}-{unique}-{index}",
            std::process::id()
        ));
        std::fs::create_dir_all(&dir).unwrap();
        // Only logical companions and envelope metadata come from the oracle.
        // Its IR declarations are replaced, never supplied to this compiler.
        std::fs::write(
            dir.join("NativeIrCase.lean"),
            format!("module\npublic opaque compiled : {ty} := {expression}\n"),
        )
        .unwrap();
        let generated = Command::new(&lean)
            .current_dir(&dir)
            .args(["-o", "NativeIrCase.olean", "NativeIrCase.lean"])
            .output()
            .unwrap();
        std::fs::write(dir.join("compile.stdout"), &generated.stdout).unwrap();
        std::fs::write(dir.join("compile.stderr"), &generated.stderr).unwrap();
        assert!(
            generated.status.success(),
            "{source}: {}",
            String::from_utf8_lossy(&generated.stderr)
        );
        let original = std::fs::read(dir.join("NativeIrCase.ir")).unwrap();
        std::fs::write(dir.join("original.ir"), &original).unwrap();
        let bytes = encode(&compiled.module, &original);
        std::fs::write(dir.join("NativeIrCase.ir"), &bytes).unwrap();
        std::fs::write(dir.join("native.ir"), &bytes).unwrap();
        let mut consumer = format!(
            "module\nmeta import NativeIrCase\n#eval ({application})\n#eval ({application})\n"
        );
        let mut expected_output = format!("{expected}\n{expected}");
        if index == 4 || index == 12 || index == 19 || index == 32 {
            // Effectful input prevents closed-term lifting from making the
            // alias a persistent literal. The caller keeps it across the call.
            std::fs::write(dir.join("heap-input.txt"), "fresh heap string").unwrap();
            let call = if index == 4 {
                "compiled saved"
            } else if index == 12 {
                "compiled 7 saved"
            } else if index == 32 {
                "compiled false saved"
            } else {
                "compiled Nat saved"
            };
            consumer.push_str(&format!("#eval do\n  let saved ← IO.FS.readFile \"heap-input.txt\"\n  let got := {call}\n  pure (got, saved)\n"));
            expected_output.push_str("\n(\"fresh heap string\", \"fresh heap string\")");
        }
        std::fs::write(dir.join("Consumer.lean"), consumer).unwrap();
        let result = consume(&lean, &dir);
        std::fs::write(dir.join("native.stdout"), &result.stdout).unwrap();
        std::fs::write(dir.join("native.stderr"), &result.stderr).unwrap();
        assert!(
            result.status.success(),
            "{source}: {:?}: {} {}",
            result.status,
            String::from_utf8_lossy(&result.stdout),
            String::from_utf8_lossy(&result.stderr)
        );
        assert_eq!(
            String::from_utf8(result.stdout).unwrap().trim(),
            expected_output
        );

        let full_probe = RuntimeProbe {
            ty,
            application,
            entry: "compiled",
            check_meta: true,
            higher_universe: matches!(index, 15 | 17 | 19 | 20 | 21 | 22 | 31),
            heap_call: match index {
                4 => Some("compiled saved"),
                12 => Some("compiled 7 saved"),
                19 => Some("compiled Nat saved"),
                32 => Some("compiled false saved"),
                _ => None,
            },
        };
        let reduced_probe = reduced_case(index).map(|(ty, application)| RuntimeProbe {
            ty,
            application,
            entry: "compiled._redArg",
            check_meta: false,
            higher_universe: false,
            heap_call: (index == 12 || index == 19 || index == 32).then_some("compiled saved"),
        });
        assert_eq!(
            compiled
                .module
                .decls
                .iter()
                .any(|d| d.name() == &name("compiled._redArg")),
            reduced_probe.is_some(),
            "the independently specified reduced-entry cases must actually exist",
        );
        // Check this evaluator against the pin's own IR with the same logical
        // companions and independently supplied types before judging our IR.
        std::fs::write(dir.join("NativeIrCase.ir"), &original).unwrap();
        assert_probe(
            consume_ir(&lean, &dir, "full", &full_probe),
            &dir,
            "runtime-reference",
            &expected_output,
        );
        if let Some(probe) = &reduced_probe {
            assert_probe(
                consume_ir(&lean, &dir, "reduced", probe),
                &dir,
                "runtime-reduced-reference",
                &expected_output,
            );
        }
        std::fs::write(dir.join("NativeIrCase.ir"), &bytes).unwrap();
        assert_probe(
            consume_ir(&lean, &dir, "full", &full_probe),
            &dir,
            "runtime-native",
            &expected_output,
        );
        if let Some(probe) = &reduced_probe {
            assert_probe(
                consume_ir(&lean, &dir, "reduced", probe),
                &dir,
                "runtime-reduced-native",
                &expected_output,
            );
        }

        // Alter only the source export, retaining every internal value body.
        let mut mutant = compiled.module.clone();
        let public = mutant
            .decls
            .iter_mut()
            .find(|d| d.name() == &name("compiled"))
            .unwrap();
        let IrDecl::Function { params, body, .. } = public else {
            panic!("source function entry")
        };
        if result_type == "Bool" {
            replace_boolean_result(params, body, IrType::UInt8, expected == "false");
        } else {
            replace_result(params, body, result_type);
        }
        assert_eq!(
            mutant
                .decls
                .iter()
                .filter(|d| d.name() != &name("compiled"))
                .collect::<Vec<_>>(),
            compiled
                .module
                .decls
                .iter()
                .filter(|d| d.name() != &name("compiled"))
                .collect::<Vec<_>>(),
        );
        let mutant_bytes = encode(&mutant, &original);
        std::fs::write(dir.join("export-mutant.ir"), &mutant_bytes).unwrap();
        std::fs::write(dir.join("NativeIrCase.ir"), mutant_bytes).unwrap();
        let result = consume(&lean, &dir);
        std::fs::write(dir.join("export-mutant.stdout"), &result.stdout).unwrap();
        std::fs::write(dir.join("export-mutant.stderr"), &result.stderr).unwrap();
        assert!(
            result.status.success(),
            "{source}: {:?}: {} {}",
            result.status,
            String::from_utf8_lossy(&result.stdout),
            String::from_utf8_lossy(&result.stderr)
        );
        let changed = if result_type == "Nat" {
            "99"
        } else if result_type == "Bool" {
            if expected == "true" { "false" } else { "true" }
        } else {
            "\"changed IR\""
        };
        let mut changed_output = format!("{changed}\n{changed}");
        if index == 4 || index == 12 || index == 19 || index == 32 {
            changed_output.push_str("\n(\"changed IR\", \"fresh heap string\")");
        }
        // Ordinary compilation may inline the logical companion's original
        // body. Retain its diagnostic output, but use direct interpreter calls
        // to require observation of this valid, deliberately changed IR.
        assert_probe(
            consume_ir(&lean, &dir, "full", &full_probe),
            &dir,
            "runtime-export-mutant",
            &changed_output,
        );
        if let Some(probe) = &reduced_probe {
            assert_probe(
                consume_ir(&lean, &dir, "reduced", probe),
                &dir,
                "runtime-reduced-mutant",
                &changed_output,
            );
        }
        if result_type == "Bool" && !boolean_positions(index).is_empty() {
            // Preserve the public entry and change only its boxed adapter.
            // Runtime lookup must execute that adapter, not merely an unused
            // wrapper included in the output module.
            let mut mutant = compiled.module.clone();
            let boxed = mutant
                .decls
                .iter_mut()
                .find(|d| d.name() == &name("compiled._boxed"))
                .unwrap();
            let IrDecl::Function { params, body, .. } = boxed else {
                panic!("source boxed function")
            };
            replace_boolean_result(params, body, IrType::Tagged, expected == "false");
            assert_eq!(
                mutant
                    .decls
                    .iter()
                    .filter(|d| d.name() != &name("compiled._boxed"))
                    .collect::<Vec<_>>(),
                compiled
                    .module
                    .decls
                    .iter()
                    .filter(|d| d.name() != &name("compiled._boxed"))
                    .collect::<Vec<_>>(),
            );
            let bytes = encode(&mutant, &original);
            std::fs::write(dir.join("boxed-export-mutant.ir"), &bytes).unwrap();
            std::fs::write(dir.join("NativeIrCase.ir"), &bytes).unwrap();
            assert_probe(
                consume_ir(&lean, &dir, "full", &full_probe),
                &dir,
                "runtime-boxed-export-mutant",
                &changed_output,
            );
        }
        std::fs::write(dir.join("NativeIrCase.ir"), bytes).unwrap();
        assert_eq!(base.logical_root(&options), original_root);
    }
}
