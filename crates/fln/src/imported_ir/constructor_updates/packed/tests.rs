use super::*;
use crate::imported_ir::{CompiledIr, EntryArgument, IrExecutionError, IrExecutionLimits, VerifiedPartition, compile};
use fln_comp::flbc;
use fln_core::{name::Name, outcome::Outcome};
use fln_hash::ir_graph::GraphArchiveLimits;
use fln_olean::ir::{IrAlt, IrArg, IrBody, IrCtorInfo, IrDecl, IrLit, IrModule, IrNat, IrParam, IrTerminal};
use fln_olean::ir_archive::CensusPartition;
use fln_vm::interpreter::{ExecutionLimits, VmExit, execute, nat_decimal};
use std::collections::BTreeSet;

fn name(text: &str) -> Name { Name::from_components(text.split('.')) }
fn var(x: u64) -> IrArg { IrArg::Var(x) }
fn body(stmts: Vec<IrStmt>, terminal: IrTerminal) -> IrBody {
    IrBody { stmts, terminal: Box::new(terminal) }
}
fn bind(x: u64, ty: IrType, expr: IrExpr) -> IrStmt { IrStmt::VDecl { x, ty, expr } }
fn param(x: u64, ty: IrType) -> IrParam { IrParam { x, ty, borrow: true } }
fn num(x: u64, n: u64) -> IrStmt {
    bind(x, IrType::TObject, IrExpr::Lit(IrLit::Num(IrNat::Small(n))))
}
fn call(x: u64, target: &str, args: Vec<IrArg>) -> IrStmt {
    bind(x, IrType::TObject, IrExpr::Fap { function: name(target), args })
}
fn function(text: &str, params: Vec<IrParam>, body: IrBody) -> IrDecl {
    IrDecl::Function { name: name(text), params, result: IrType::TObject, body, sorry_dep: None }
}
fn boolean(tag: u64, body: IrBody) -> IrAlt {
    IrAlt::Ctor {
        info: IrCtorInfo { name: name("Bool"), cidx: tag, size: 0, usize: 0, ssize: 0 },
        body,
    }
}

struct Layout {
    info: IrCtorInfo,
    fields: Vec<(IrType, u64)>,
    original: Vec<u64>,
}

impl Layout {
    fn integers(objects: bool) -> Self {
        Self {
            info: IrCtorInfo { name: name("PackedUpdates.Record"), cidx: 7, size: u64::from(objects), usize: 1, ssize: 15 },
            fields: vec![(IrType::USize, 0), (IrType::UInt64, 0), (IrType::UInt32, 8), (IrType::UInt16, 12), (IrType::UInt8, 14)],
            original: vec![13, (1 << 63) + 17, u32::MAX as u64 - 3, 65_530, 251],
        }
    }

    fn floats() -> Self {
        Self {
            info: IrCtorInfo { name: name("PackedUpdates.Floats"), cidx: 7, size: 1, usize: 0, ssize: 12 },
            fields: vec![(IrType::Float, 0), (IrType::Float32, 8)],
            original: vec![0x8000_0000_0000_0000, 0x7fa0_1234],
        }
    }

    fn projection(&self, index: usize, receiver: u64) -> IrExpr {
        let (ty, bytes) = &self.fields[index];
        if *ty == IrType::USize {
            IrExpr::UProj { i: self.info.size, x: receiver }
        } else {
            IrExpr::SProj { n: self.info.size + self.info.usize, offset: *bytes, x: receiver }
        }
    }

    fn store(&self, index: usize, receiver: u64, value: u64) -> IrStmt {
        let (ty, bytes) = &self.fields[index];
        if *ty == IrType::USize {
            IrStmt::USet { x: receiver, i: self.info.size, y: value }
        } else {
            IrStmt::SSet { x: receiver, i: self.info.size + self.info.usize, offset: *bytes, y: value, ty: ty.clone() }
        }
    }

    fn argument(&self, index: usize, bits: u64) -> EntryArgument {
        match self.fields[index].0 {
            IrType::Float => EntryArgument::FloatBits(bits),
            IrType::Float32 => EntryArgument::Float32Bits(u32::try_from(bits).unwrap()),
            _ => EntryArgument::Nat(IrNat::Small(bits)),
        }
    }

    fn module(&self, updated: usize) -> IrModule {
        let object_args = if self.info.size == 0 { vec![] } else { vec![var(3)] };
        let mut prefix = Vec::new();
        if self.info.size != 0 {
            prefix.push(bind(3, IrType::TObject, IrExpr::Proj { i: 0, x: 1 }));
        }
        for (index, (ty, _)) in self.fields.iter().enumerate() {
            prefix.push(bind(4 + index as u64, ty.clone(), self.projection(index, 1)));
        }
        prefix.push(bind(50, IrType::UInt8, IrExpr::IsShared { x: 1 }));
        let mut initialization = vec![bind(51, IrType::TObject, IrExpr::Ctor { info: self.info.clone(), args: object_args })];
        for index in 0..self.fields.len() {
            initialization.push(self.store(index, 51, if index == updated { 2 } else { 4 + index as u64 }));
        }
        let region = body(prefix, IrTerminal::Case {
            type_name: name("Bool"), x: 50, x_type: IrType::UInt8,
            alts: vec![
                boolean(0, body(vec![self.store(updated, 1, 2)], IrTerminal::Ret(var(1)))),
                boolean(1, body(initialization, IrTerminal::Ret(var(51)))),
            ],
        });
        let update = function("PackedUpdates.update", vec![param(1, IrType::TObject), param(2, self.fields[updated].0.clone())], body(vec![], IrTerminal::Case {
            type_name: self.info.name.clone(), x: 1, x_type: IrType::TObject,
            alts: vec![IrAlt::Ctor { info: self.info.clone(), body: region }],
        }));
        let mut params = vec![param(1, self.fields[updated].0.clone())];
        params.extend(self.fields.iter().enumerate().map(|(index, (ty, _))| param(index as u64 + 2, ty.clone())));
        let mut stmts = vec![num(20, 11), bind(31, IrType::TObject, IrExpr::Ctor {
            info: self.info.clone(), args: if self.info.size == 0 { vec![] } else { vec![var(20)] },
        })];
        for index in 0..self.fields.len() { stmts.push(self.store(index, 31, index as u64 + 2)); }
        stmts.push(call(32, "PackedUpdates.update", vec![var(31), var(1)]));
        stmts.push(num(50, 0));
        let mut sum = 50;
        let mut next = 51;
        // Read the result and then the still-shared original. Floating fields
        // are read as integer bytes here so NaN payloads cannot be normalized
        // by public Float.toBits before the assertion.
        for (index, receiver) in (0..self.fields.len()).map(|i| (i, 32)).chain([(updated, 31)]) {
            let (raw, converter) = match self.fields[index].0 {
                IrType::USize => (IrType::USize, "USize.toNat"),
                IrType::UInt64 | IrType::Float => (IrType::UInt64, "UInt64.toNat"),
                IrType::UInt32 | IrType::Float32 => (IrType::UInt32, "UInt32.toNat"),
                IrType::UInt16 => (IrType::UInt16, "UInt16.toNat"),
                IrType::UInt8 => (IrType::UInt8, "UInt8.toNat"),
                _ => unreachable!(),
            };
            stmts.push(bind(next, raw, self.projection(index, receiver)));
            stmts.push(call(next + 1, converter, vec![var(next)]));
            stmts.push(call(next + 2, "Nat.add", vec![var(sum), var(next + 1)]));
            sum = next + 2;
            next += 3;
        }
        if self.info.size != 0 {
            for receiver in [31, 32] {
                stmts.push(bind(next, IrType::TObject, IrExpr::Proj { i: 0, x: receiver }));
                stmts.push(call(next + 1, "Nat.add", vec![var(sum), var(next)]));
                sum = next + 1;
                next += 2;
            }
        }
        IrModule { decls: vec![update, function("PackedUpdates.main", params, body(stmts, IrTerminal::Ret(var(sum))))], ..IrModule::default() }
    }

    fn arguments(&self, updated: usize, replacement: u64) -> Vec<EntryArgument> {
        let mut args = vec![self.argument(updated, replacement)];
        args.extend(self.original.iter().enumerate().map(|(i, bits)| self.argument(i, *bits)));
        args
    }

    fn expected(&self, replacement: u64) -> String {
        (self.original.iter().copied().map(u128::from).sum::<u128>() + u128::from(replacement) + u128::from(self.info.size) * 22).to_string()
    }
}

fn compile_module(module: &IrModule, args: &[EntryArgument], limits: IrExecutionLimits) -> std::result::Result<CompiledIr, IrExecutionError> {
    let partition = VerifiedPartition { partition: CensusPartition::parse("constant_count\t0\n", GraphArchiveLimits::default()).unwrap() };
    let users = module.decls.iter().map(|decl| decl.name().clone()).collect::<BTreeSet<_>>();
    compile(std::slice::from_ref(module), &name("PackedUpdates.main"), args, &partition, &users, limits)
}

fn check(compiled: &CompiledIr, expected: &str) -> Vec<u8> {
    let bytes = flbc::encode_canonical(compiled.program.program(), flbc::CodecLimits::default()).unwrap();
    let replay = flbc::decode_canonical(&bytes, flbc::CodecLimits::default()).unwrap();
    assert_eq!(flbc::encode_canonical(&replay, flbc::CodecLimits::default()).unwrap(), bytes);
    for program in [compiled.program.program(), &replay] {
        let outcome = execute(program, ExecutionLimits::default(), None);
        let Outcome::Complete(VmExit::Returned(value)) = outcome else { panic!("{outcome:?}") };
        assert_eq!(nat_decimal(&value.value).as_deref(), Some(expected));
    }
    assert!(compiled.reference_functions().iter().all(|function| function.producer() == "reference"));
    bytes
}

fn region(module: &mut IrModule) -> &mut IrBody {
    let IrDecl::Function { body, .. } = &mut module.decls[0] else { panic!("update") };
    let IrTerminal::Case { alts, .. } = body.terminal.as_mut() else { panic!("shape case") };
    let IrAlt::Ctor { body, .. } = &mut alts[0] else { panic!("record") };
    body
}
fn arms(region: &mut IrBody) -> &mut Vec<IrAlt> {
    let IrTerminal::Case { alts, .. } = region.terminal.as_mut() else { panic!("guard") };
    alts
}
fn branch(region: &mut IrBody, index: usize) -> &mut IrBody {
    match &mut arms(region)[index] { IrAlt::Ctor { body, .. } | IrAlt::Default { body } => body }
}

#[test]
fn mixed_packed_updates_preserve_shared_originals_at_every_integer_width() {
    let layout = Layout::integers(true);
    for (updated, replacement) in [u64::MAX, (1 << 63) + 42, u32::MAX as u64, 65_535, 255].into_iter().enumerate() {
        let module = layout.module(updated);
        let compiled = compile_module(&module, &layout.arguments(updated, replacement), IrExecutionLimits::default()).unwrap();
        check(&compiled, &layout.expected(replacement));
    }
}

#[test]
fn scalar_only_updates_keep_the_full_payload_and_boolean_default() {
    let layout = Layout::integers(false);
    for fallback in [0, 1] {
        let mut module = layout.module(1);
        let alt = &mut arms(region(&mut module))[fallback];
        let IrAlt::Ctor { body, .. } = alt else { panic!("boolean") };
        let value = body.clone();
        *alt = IrAlt::Default { body: value };
        arms(region(&mut module)).reverse();
        let compiled = compile_module(&module, &layout.arguments(1, u64::MAX), IrExecutionLimits::default()).unwrap();
        check(&compiled, &layout.expected(u64::MAX));
    }
}

#[test]
fn floating_updates_preserve_nan_payloads_signed_zero_and_unchanged_fields() {
    let layout = Layout::floats();
    for (updated, replacement) in [(0, 0x7ff0_0000_0000_0042), (1, 0x8000_0000), (1, 0x7f80_0000)] {
        let compiled = compile_module(&layout.module(updated), &layout.arguments(updated, replacement), IrExecutionLimits::default()).unwrap();
        check(&compiled, &layout.expected(replacement));
    }
}

#[test]
fn expanded_reset_joins_remap_unchanged_packed_projections() {
    let layout = Layout::integers(true);
    let mut module = layout.module(1);
    let value = region(&mut module);
    let mut reuse = value.terminal.as_ref().clone();
    let IrTerminal::Case { x, alts, .. } = &mut reuse else { panic!("reuse") };
    *x = 61;
    let IrAlt::Ctor { body: exclusive, .. } = &mut alts[0] else { panic!("exclusive") };
    let IrStmt::SSet { x, .. } = &mut exclusive.stmts[0] else { panic!("store") };
    *x = 60;
    exclusive.terminal = Box::new(IrTerminal::Ret(var(60)));
    let join = IrStmt::JDecl { j: 70, params: vec![param(60, IrType::TObject), param(61, IrType::UInt8)], value: body(vec![], reuse) };
    value.stmts.insert(value.stmts.len() - 1, join);
    value.terminal = Box::new(IrTerminal::Case {
        type_name: name("Bool"), x: 50, x_type: IrType::UInt8,
        alts: vec![
            boolean(0, body(vec![], IrTerminal::Jmp { j: 70, args: vec![var(1), var(50)] })),
            boolean(1, body(vec![], IrTerminal::Jmp { j: 70, args: vec![IrArg::Erased, var(50)] })),
        ],
    });
    let compiled = compile_module(&module, &layout.arguments(1, u64::MAX), IrExecutionLimits::default()).unwrap();
    check(&compiled, &layout.expected(u64::MAX));
}

#[test]
fn malformed_packed_alternatives_cannot_hide_stores_or_change_layouts() {
    let layout = Layout::integers(true);
    for mutant in 0..9 {
        let mut module = layout.module(1);
        let value = region(&mut module);
        match mutant {
            0 => if let IrStmt::SSet { offset, .. } = &mut branch(value, 0).stmts[0] { *offset = u64::MAX; },
            1 => if let IrStmt::SSet { i, .. } = &mut branch(value, 0).stmts[0] { *i = 1; }, // word area
            2 => { let duplicate = branch(value, 0).stmts[0].clone(); branch(value, 0).stmts.push(duplicate); },
            3 => { branch(value, 1).stmts.pop(); }, // incomplete scalar payload
            4 => { let duplicate = branch(value, 1).stmts[1].clone(); branch(value, 1).stmts.push(duplicate); },
            5 => if let IrStmt::VDecl { expr: IrExpr::Ctor { info, .. }, .. } = &mut branch(value, 1).stmts[0] { info.ssize += 1; },
            6 => if let IrStmt::SSet { y, .. } = &mut branch(value, 0).stmts[0] { *y = 5; }, // different source
            7 => if let IrStmt::SSet { ty, .. } = &mut branch(value, 0).stmts[0] { *ty = IrType::Float; }, // same width, different carrier
            8 => { branch(value, 0).stmts.push(call(90, "Nat.succ", vec![var(3)])); },
            _ => unreachable!(),
        }
        assert!(compile_module(&module, &layout.arguments(1, 42), IrExecutionLimits::default()).is_err(), "mutant {mutant}");
    }
    let compiled = compile_module(&layout.module(1), &layout.arguments(1, 42), IrExecutionLimits::default()).unwrap();
    check(&compiled, &layout.expected(42));
}

#[test]
fn preserved_scalar_fields_require_the_exact_original_projection() {
    let layout = Layout::integers(true);
    for mutant in 0..3 {
        let mut module = layout.module(1);
        let value = region(&mut module);
        let IrStmt::VDecl { ty, expr, .. } = &mut value.stmts[3] else { panic!("UInt32 projection") };
        match mutant {
            0 => *expr = IrExpr::SProj { n: 2, offset: 9, x: 1 },
            1 => *ty = IrType::Float32,
            2 => *expr = IrExpr::Lit(IrLit::Num(IrNat::Small(7))),
            _ => unreachable!(),
        }
        assert!(compile_module(&module, &layout.arguments(1, 42), IrExecutionLimits::default()).is_err());
    }
}

#[test]
fn packed_update_preparation_is_bounded_failure_atomic_and_deterministic() {
    let layout = Layout::integers(true);
    let module = layout.module(1);
    let original = module.clone();
    let args = layout.arguments(1, u64::MAX);
    let mut limits = IrExecutionLimits::default();
    limits.ir.max_work = 1;
    assert!(compile_module(&module, &args, limits).unwrap_err().is_resource());
    assert_eq!(module, original);
    let expected = layout.expected(u64::MAX);
    let first = check(&compile_module(&module, &args, IrExecutionLimits::default()).unwrap(), &expected);
    let second = check(&compile_module(&module, &args, IrExecutionLimits::default()).unwrap(), &expected);
    assert_eq!(first, second);
}
