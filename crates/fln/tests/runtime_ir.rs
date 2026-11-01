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
        .filter(|p| !p.borrow)
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
