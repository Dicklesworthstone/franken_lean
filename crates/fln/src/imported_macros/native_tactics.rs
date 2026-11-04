//! Native counterparts for the pin's four registered `rfl` macros.
//!
//! These are individual registry candidates, not an aggregate reflexivity
//! tactic. Their checked owners and exact census names select native quotation
//! code; no Reference toolchain body is interpreted. User registrations and
//! recursive `expandMacro?` calls retain the ordinary candidate order.

use super::{
    MacroExecution, MacroInvocation, MacroLimits, StateBudget, SyntaxConversionError,
    VerifiedPartition, conversion_outcome, inject_state, layout, make_ctor, project_result, syntax,
};
use fln_comp::flbc::{
    self, ArgumentOwnership, CallableResultOwnership, Function, FunctionId, Instruction, Program,
    Register, ValidatedProgram,
};
use fln_core::name::{Name, hygiene::add_macro_scope};
use fln_core::outcome::Outcome;
use fln_hash::ir_graph::GraphClass;
use fln_rt::obj::Obj;
use fln_syntax::source::{BytePos, ByteSpan, SourceInfo};
use fln_syntax::tree::{Preresolved, RawIdentifier, Syntax};
use fln_vm::interpreter::{CancellationProbe, VmExit, execute_function};
use std::sync::{Arc, OnceLock};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum NativeTacticMacro {
    ApplyRfl,
    EqRefl,
    ExactHEq,
    ExactIff,
}

impl NativeTacticMacro {
    pub(super) fn identify(
        module: &Name,
        declaration: &Name,
        partition: &VerifiedPartition,
    ) -> Option<Self> {
        if partition.classify(declaration) != Some(GraphClass::ToolchainApi) {
            return None;
        }
        [Self::ApplyRfl, Self::EqRefl, Self::ExactHEq, Self::ExactIff]
            .into_iter()
            .find(|candidate| {
                *module == name(candidate.module()) && *declaration == name(candidate.declaration())
            })
    }

    fn module(self) -> &'static str {
        if self == Self::ExactIff {
            "Init.Core"
        } else {
            "Init.Tactics"
        }
    }

    fn declaration(self) -> &'static str {
        match self {
            Self::ApplyRfl => {
                "Lean.Parser.Tactic._aux_Init_Tactics___macroRules_Lean_Parser_Tactic_tacticRfl_1"
            }
            Self::EqRefl => {
                "Lean.Parser.Tactic._aux_Init_Tactics___macroRules_Lean_Parser_Tactic_tacticRfl_2"
            }
            Self::ExactHEq => {
                "Lean.Parser.Tactic._aux_Init_Tactics___macroRules_Lean_Parser_Tactic_tacticRfl_3"
            }
            Self::ExactIff => "_aux_Init_Core___macroRules_Lean_Parser_Tactic_tacticRfl_1",
        }
    }

    pub(super) fn id(self) -> &'static str {
        match self {
            Self::ApplyRfl => {
                "mirror:Lean.Parser.Tactic._aux_Init_Tactics___macroRules_Lean_Parser_Tactic_tacticRfl_1"
            }
            Self::EqRefl => {
                "mirror:Lean.Parser.Tactic._aux_Init_Tactics___macroRules_Lean_Parser_Tactic_tacticRfl_2"
            }
            Self::ExactHEq => {
                "mirror:Lean.Parser.Tactic._aux_Init_Tactics___macroRules_Lean_Parser_Tactic_tacticRfl_3"
            }
            Self::ExactIff => "mirror:_aux_Init_Core___macroRules_Lean_Parser_Tactic_tacticRfl_1",
        }
    }

    pub(super) fn execute(
        self,
        input: &Syntax,
        invocation: MacroInvocation<'_>,
        limits: MacroLimits,
        cancellation: Option<&dyn CancellationProbe>,
        reference: Option<&Syntax>,
    ) -> MacroExecution {
        let prepared = (|| {
            // Use the same bounded ABI crossings as interpreted user macros.
            // In particular, neither a bad source span nor a large untouched
            // state can bypass validation merely because this body is native.
            syntax::inject(input, invocation.source, limits.syntax)?;
            let reference = reference.unwrap_or(input);
            syntax::inject(reference, invocation.source, limits.syntax)?;
            let mut budget = StateBudget::new(limits.syntax);
            budget.inject_name(&invocation.context.quotation_context)?;
            let state = inject_state(invocation.state, &mut budget)?;
            if input.kind() != Some(&name("Lean.Parser.Tactic.tacticRfl")) {
                return Ok(make_ctor(
                    layout::RESULT_ERROR,
                    vec![Obj::mk_nat(layout::EXCEPTION_UNSUPPORTED_TAG), state],
                ));
            }
            // The pin checks only isOfKind. getArg 0 is read but its value and
            // even its presence are not tested by these four macro bodies.
            let info = info_from_reference(reference);
            let (kind, keyword, declaration) = match self {
                Self::ApplyRfl => ("applyRfl", "apply_rfl", None),
                Self::EqRefl => ("eqRefl", "eq_refl", None),
                Self::ExactHEq => ("exact", "exact", Some("HEq.rfl")),
                Self::ExactIff => ("exact", "exact", Some("Iff.rfl")),
            };
            let mut args = vec![Syntax::Atom {
                info,
                val: keyword.to_owned(),
            }];
            if let Some(declaration) = declaration {
                let constant = name(declaration);
                let value = add_macro_scope(
                    &invocation.context.quotation_context,
                    &constant,
                    invocation.context.current_macro_scope,
                )
                .map_err(|_| SyntaxConversionError::Malformed("native tactic quotation hygiene"))?;
                let raw = RawIdentifier::owned(
                    Arc::from(declaration),
                    ByteSpan::new(BytePos(0), BytePos(declaration.len()))
                        .expect("fixed native identifier range"),
                )
                .expect("fixed native identifier UTF-8 range");
                args.push(Syntax::Ident {
                    info,
                    raw_val: raw,
                    val: value,
                    preresolved: vec![Preresolved::Decl {
                        name: constant,
                        fields: Vec::new(),
                    }],
                });
            }
            let output = Syntax::Node {
                info,
                kind: Name::str(name("Lean.Parser.Tactic"), kind),
                args,
            };
            let output = syntax::inject(&output, invocation.source, limits.syntax)?;
            Ok::<_, SyntaxConversionError>(make_ctor(layout::RESULT_OK, vec![output, state]))
        })();
        let mut vm_usage = None;
        let outcome = match prepared {
            Err(error) => conversion_outcome(error),
            Ok(result) => match execute_function(
                return_thunk(),
                FunctionId::new(1),
                vec![result],
                limits.vm,
                cancellation,
            ) {
                Outcome::Complete(VmExit::Returned(result)) => {
                    vm_usage = Some(result.usage);
                    match project_result(&result.value, invocation.source, limits.syntax) {
                        Ok(result) => Outcome::Complete(Ok(result)),
                        Err(error) => conversion_outcome(error),
                    }
                }
                Outcome::Complete(VmExit::Refused { refusal, usage }) => {
                    vm_usage = Some(usage);
                    Outcome::Complete(Err(super::MacroExecutionError::Runtime(refusal)))
                }
                Outcome::Complete(VmExit::Panicked { message, usage }) => {
                    vm_usage = Some(usage);
                    Outcome::Complete(Err(super::MacroExecutionError::RuntimePanic(message)))
                }
                Outcome::Inconclusive(reason) => Outcome::Inconclusive(reason),
                Outcome::InternalFault(fault) => Outcome::InternalFault(fault),
            },
        };
        MacroExecution {
            outcome,
            vm_usage,
            reference_functions: Vec::new(),
            native_functions: vec![self.id().to_owned()],
        }
    }
}

fn name(text: &str) -> Name {
    Name::from_components(text.split('.'))
}

/// The pin's SourceInfo.fromRef with canonical=false. Its head traversal stops
/// at the first atom/identifier even if that leaf has no position; the tail
/// traversal skips positionless leaves. Input conversion already bounds this
/// tree, and these walks use an explicit stack rather than host recursion.
fn info_from_reference(reference: &Syntax) -> SourceInfo {
    let mut pending = vec![reference];
    let mut start = None;
    while let Some(current) = pending.pop() {
        match current {
            Syntax::Missing => {}
            Syntax::Node {
                info: SourceInfo::None,
                args,
                ..
            } => pending.extend(args.iter().rev()),
            other => {
                start = other.info().pos(false);
                break;
            }
        }
    }
    let Some(pos) = start else {
        return SourceInfo::None;
    };
    let mut pending = vec![reference];
    while let Some(current) = pending.pop() {
        if let Some(end_pos) = current.info().end_pos(false) {
            return SourceInfo::Synthetic {
                pos,
                end_pos,
                canonical: false,
            };
        }
        if let Syntax::Node { args, .. } = current {
            pending.extend(args);
        }
    }
    SourceInfo::None
}

/// Keep native quotations on the ordinary VM fuel, frame and cancellation
/// boundary. One real FLBC Return instruction transfers the prepared result;
/// its measured usage is never fabricated as a stand-in for native work.
fn return_thunk() -> &'static ValidatedProgram {
    static PROGRAM: OnceLock<ValidatedProgram> = OnceLock::new();
    PROGRAM.get_or_init(|| {
        let register = Register::new(0);
        flbc::validate(Program::new(
            FunctionId::new(0),
            vec![
                Function {
                    id: FunctionId::new(0),
                    arity: 0,
                    parameter_ownership: Vec::new(),
                    result_ownership: CallableResultOwnership::Scalar,
                    register_count: 1,
                    code: vec![
                        Instruction::Nat {
                            dst: register,
                            value: 0,
                        },
                        Instruction::Return { src: register },
                    ],
                },
                Function {
                    id: FunctionId::new(1),
                    arity: 1,
                    parameter_ownership: vec![ArgumentOwnership::Owned],
                    result_ownership: CallableResultOwnership::Owned,
                    register_count: 1,
                    code: vec![Instruction::Return { src: register }],
                },
            ],
        ))
        .expect("fixed native macro result thunk passes FLBC validation")
    })
}

#[cfg(test)]
#[path = "native_tactics/tests.rs"]
mod tests;
