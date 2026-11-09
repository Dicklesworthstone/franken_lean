//! Native counterparts for selected registered Init quotation macros.
//!
//! These are individual registry candidates, not an aggregate reflexivity
//! tactic. Their checked owners and exact census names select native quotation
//! code; no Reference toolchain body is interpreted. User registrations and
//! recursive `expandMacro?` calls retain the ordinary candidate order.
//! Applicative sequencing uses that same dispatch, including when a user macro
//! asks to expand a term before returning its result to the elaborator.

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
    Exfalso,
    InferInstance,
    Try,
    NoFun,
    Rwa,
    Rw,
    AndThen,
    TrivialAssumption,
    TrivialRfl,
    TrivialContradiction,
    TrivialDecide,
    TrivialTrue,
    TrivialAnd,
    Seq,
    SeqLeft,
    SeqRight,
}

impl NativeTacticMacro {
    // Exact registrations from REFERENCE_GRAMMAR_CENSUS.txt, not spellings
    // inferred from a caller's syntax kind. The partition and checked module
    // owner remain mandatory before any candidate receives native execution.
    const ALL: [Self; 20] = [
        Self::ApplyRfl,
        Self::EqRefl,
        Self::ExactHEq,
        Self::ExactIff,
        Self::Exfalso,
        Self::InferInstance,
        Self::Try,
        Self::NoFun,
        Self::Rwa,
        Self::Rw,
        Self::AndThen,
        Self::TrivialAssumption,
        Self::TrivialRfl,
        Self::TrivialContradiction,
        Self::TrivialDecide,
        Self::TrivialTrue,
        Self::TrivialAnd,
        Self::Seq,
        Self::SeqLeft,
        Self::SeqRight,
    ];

    pub(super) fn identify(
        module: &Name,
        declaration: &Name,
        partition: &VerifiedPartition,
    ) -> Option<Self> {
        if partition.classify(declaration) != Some(GraphClass::ToolchainApi) {
            return None;
        }
        Self::ALL.into_iter().find(|candidate| {
            *module == name(candidate.module()) && *declaration == name(candidate.declaration())
        })
    }

    fn module(self) -> &'static str {
        match self {
            Self::ExactIff => "Init.Core",
            Self::Seq | Self::SeqLeft | Self::SeqRight => "Init.Notation",
            _ => "Init.Tactics",
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
            Self::Exfalso => {
                "Lean.Parser.Tactic._aux_Init_Tactics___macroRules_Lean_Parser_Tactic_tacticExfalso_1"
            }
            Self::InferInstance => {
                "Lean.Parser.Tactic._aux_Init_Tactics___macroRules_Lean_Parser_Tactic_tacticInfer_instance_1"
            }
            Self::Try => {
                "Lean.Parser.Tactic._aux_Init_Tactics___macroRules_Lean_Parser_Tactic_tacticTry__1"
            }
            Self::NoFun => {
                "Lean.Parser.Tactic._aux_Init_Tactics___macroRules_Lean_Parser_Tactic_tacticNofun_1"
            }
            Self::Rwa => {
                "Lean.Parser.Tactic._aux_Init_Tactics___macroRules_Lean_Parser_Tactic_tacticRwa___1"
            }
            Self::Rw => {
                "Lean.Parser.Tactic._aux_Init_Tactics___macroRules_Lean_Parser_Tactic_rwSeq_1"
            }
            Self::AndThen => {
                "Lean.Parser.Tactic._aux_Init_Tactics___macroRules_Lean_Parser_Tactic_tactic_<;>__1"
            }
            Self::TrivialAssumption => {
                "Lean.Parser.Tactic._aux_Init_Tactics___macroRules_Lean_Parser_Tactic_tacticTrivial_1"
            }
            Self::TrivialRfl => {
                "Lean.Parser.Tactic._aux_Init_Tactics___macroRules_Lean_Parser_Tactic_tacticTrivial_2"
            }
            Self::TrivialContradiction => {
                "Lean.Parser.Tactic._aux_Init_Tactics___macroRules_Lean_Parser_Tactic_tacticTrivial_3"
            }
            Self::TrivialDecide => {
                "Lean.Parser.Tactic._aux_Init_Tactics___macroRules_Lean_Parser_Tactic_tacticTrivial_4"
            }
            Self::TrivialTrue => {
                "Lean.Parser.Tactic._aux_Init_Tactics___macroRules_Lean_Parser_Tactic_tacticTrivial_5"
            }
            Self::TrivialAnd => {
                "Lean.Parser.Tactic._aux_Init_Tactics___macroRules_Lean_Parser_Tactic_tacticTrivial_6"
            }
            Self::Seq => "_aux_Init_Notation___macroRules_term_<*>__1",
            Self::SeqLeft => "_aux_Init_Notation___macroRules_term_<*__1",
            Self::SeqRight => "_aux_Init_Notation___macroRules_term_*>__1",
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
            Self::Exfalso => {
                "mirror:Lean.Parser.Tactic._aux_Init_Tactics___macroRules_Lean_Parser_Tactic_tacticExfalso_1"
            }
            Self::InferInstance => {
                "mirror:Lean.Parser.Tactic._aux_Init_Tactics___macroRules_Lean_Parser_Tactic_tacticInfer_instance_1"
            }
            Self::Try => {
                "mirror:Lean.Parser.Tactic._aux_Init_Tactics___macroRules_Lean_Parser_Tactic_tacticTry__1"
            }
            Self::NoFun => {
                "mirror:Lean.Parser.Tactic._aux_Init_Tactics___macroRules_Lean_Parser_Tactic_tacticNofun_1"
            }
            Self::Rwa => {
                "mirror:Lean.Parser.Tactic._aux_Init_Tactics___macroRules_Lean_Parser_Tactic_tacticRwa___1"
            }
            Self::Rw => {
                "mirror:Lean.Parser.Tactic._aux_Init_Tactics___macroRules_Lean_Parser_Tactic_rwSeq_1"
            }
            Self::AndThen => {
                "mirror:Lean.Parser.Tactic._aux_Init_Tactics___macroRules_Lean_Parser_Tactic_tactic_<;>__1"
            }
            Self::TrivialAssumption => {
                "mirror:Lean.Parser.Tactic._aux_Init_Tactics___macroRules_Lean_Parser_Tactic_tacticTrivial_1"
            }
            Self::TrivialRfl => {
                "mirror:Lean.Parser.Tactic._aux_Init_Tactics___macroRules_Lean_Parser_Tactic_tacticTrivial_2"
            }
            Self::TrivialContradiction => {
                "mirror:Lean.Parser.Tactic._aux_Init_Tactics___macroRules_Lean_Parser_Tactic_tacticTrivial_3"
            }
            Self::TrivialDecide => {
                "mirror:Lean.Parser.Tactic._aux_Init_Tactics___macroRules_Lean_Parser_Tactic_tacticTrivial_4"
            }
            Self::TrivialTrue => {
                "mirror:Lean.Parser.Tactic._aux_Init_Tactics___macroRules_Lean_Parser_Tactic_tacticTrivial_5"
            }
            Self::TrivialAnd => {
                "mirror:Lean.Parser.Tactic._aux_Init_Tactics___macroRules_Lean_Parser_Tactic_tacticTrivial_6"
            }
            Self::Seq => "mirror:_aux_Init_Notation___macroRules_term_<*>__1",
            Self::SeqLeft => "mirror:_aux_Init_Notation___macroRules_term_<*__1",
            Self::SeqRight => "mirror:_aux_Init_Notation___macroRules_term_*>__1",
        }
    }

    fn input_kind(self) -> &'static str {
        match self {
            Self::ApplyRfl | Self::EqRefl | Self::ExactHEq | Self::ExactIff => "tacticRfl",
            Self::Exfalso => "tacticExfalso",
            Self::InferInstance => "tacticInfer_instance",
            Self::Try => "tacticTry_",
            Self::NoFun => "tacticNofun",
            Self::Rwa => "tacticRwa__",
            Self::Rw => "rwSeq",
            Self::AndThen => "tactic_<;>_",
            Self::TrivialAssumption
            | Self::TrivialRfl
            | Self::TrivialContradiction
            | Self::TrivialDecide
            | Self::TrivialTrue
            | Self::TrivialAnd => "tacticTrivial",
            Self::Seq => "term_<*>_",
            Self::SeqLeft => "term_<*_",
            Self::SeqRight => "term_*>_",
        }
    }

    fn syntax_kind(self) -> Name {
        match self {
            Self::Seq | Self::SeqLeft | Self::SeqRight => name(self.input_kind()),
            _ => Name::str(name("Lean.Parser.Tactic"), self.input_kind()),
        }
    }

    fn matches(self, input: &Syntax) -> bool {
        if input.kind() != Some(&self.syntax_kind()) {
            return false;
        }
        // rw's body performs a second quotation-pattern match on its rule
        // sequence; the other candidates only match their input node kind.
        self != Self::Rw || argument(input, 2).kind() == Some(&name("Lean.Parser.Tactic.rwRuleSeq"))
    }

    /// Quote the pin's RHS, preserving antiquotation children verbatim. The
    /// generated matcher checks the kind only: absent arguments are `missing`,
    /// and neither token spelling nor extra children are inspected. See
    /// Lean/Elab/Quotation.lean's `HeadCheck.shape` and `quoteSyntax`.
    fn quote(
        self,
        input: &Syntax,
        context: &super::MacroContext,
        info: SourceInfo,
    ) -> Result<Syntax, SyntaxConversionError> {
        let atom = |text: &str| Syntax::Atom {
            info,
            val: text.to_owned(),
        };
        let node = |kind: &str, args| Syntax::Node {
            info,
            kind: name(kind),
            args,
        };
        let tactic = |kind: &str, args| Syntax::Node {
            info,
            kind: Name::str(name("Lean.Parser.Tactic"), kind),
            args,
        };
        let sequence = |rows| {
            tactic(
                "tacticSeq",
                vec![tactic("tacticSeq1Indented", vec![node("null", rows)])],
            )
        };
        let parenthesized = |body| tactic("paren", vec![atom("("), body, atom(")")]);
        let optional = |capture: Syntax| {
            let args = match &capture {
                Syntax::Node { kind, args, .. } if *kind == name("null") && args.len() == 1 => {
                    args.clone()
                }
                _ => Vec::new(),
            };
            node("null", args)
        };
        let identifier = |declaration: &str| {
            let constant = name(declaration);
            let value = add_macro_scope(
                &context.quotation_context,
                &constant,
                context.current_macro_scope,
            )
            .map_err(|_| SyntaxConversionError::Malformed("native tactic quotation hygiene"))?;
            let raw = RawIdentifier::owned(
                Arc::from(declaration),
                ByteSpan::new(BytePos(0), BytePos(declaration.len()))
                    .expect("fixed native identifier range"),
            )
            .expect("fixed native identifier UTF-8 range");
            Ok::<_, SyntaxConversionError>(Syntax::Ident {
                info,
                raw_val: raw,
                val: value,
                preresolved: vec![Preresolved::Decl {
                    name: constant,
                    fields: Vec::new(),
                }],
            })
        };
        Ok(match self {
            Self::ApplyRfl => tactic("applyRfl", vec![atom("apply_rfl")]),
            Self::EqRefl => tactic("eqRefl", vec![atom("eq_refl")]),
            Self::ExactHEq => tactic("exact", vec![atom("exact"), identifier("HEq.rfl")?]),
            Self::ExactIff => tactic("exact", vec![atom("exact"), identifier("Iff.rfl")?]),
            Self::TrivialAssumption => tactic("assumption", vec![atom("assumption")]),
            Self::TrivialRfl => tactic("tacticRfl", vec![atom("rfl")]),
            Self::TrivialContradiction => tactic("contradiction", vec![atom("contradiction")]),
            Self::TrivialDecide => tactic(
                "decide",
                vec![
                    atom("decide"),
                    tactic("optConfig", vec![node("null", Vec::new())]),
                ],
            ),
            Self::TrivialTrue => tactic("apply", vec![atom("apply"), identifier("True.intro")?]),
            Self::TrivialAnd => tactic(
                "tactic_<;>_",
                vec![
                    tactic("apply", vec![atom("apply"), identifier("And.intro")?]),
                    atom("<;>"),
                    tactic("tacticTrivial", vec![atom("trivial")]),
                ],
            ),
            Self::InferInstance => {
                tactic("exact", vec![atom("exact"), identifier("inferInstance")?])
            }
            Self::NoFun => tactic(
                "exact",
                vec![
                    atom("exact"),
                    node("Lean.Parser.Term.nofun", vec![atom("nofun")]),
                ],
            ),
            Self::Exfalso => tactic(
                "refine",
                vec![
                    atom("refine"),
                    node(
                        "Lean.Parser.Term.app",
                        vec![
                            identifier("False.elim")?,
                            node(
                                "null",
                                vec![node(
                                    "Lean.Parser.Term.syntheticHole",
                                    vec![atom("?"), atom("_")],
                                )],
                            ),
                        ],
                    ),
                ],
            ),
            Self::Try => {
                let body = match input {
                    Syntax::Node { args, .. } => args.get(1).cloned().unwrap_or(Syntax::Missing),
                    _ => Syntax::Missing,
                };
                let skip = tactic(
                    "tacticSeq",
                    vec![tactic(
                        "tacticSeq1Indented",
                        vec![node("null", vec![tactic("skip", vec![atom("skip")])])],
                    )],
                );
                tactic(
                    "first",
                    vec![
                        atom("first"),
                        node(
                            "null",
                            vec![
                                node("group", vec![atom("|"), body]),
                                node("group", vec![atom("|"), skip]),
                            ],
                        ),
                    ],
                )
            }
            Self::Rwa => parenthesized(sequence(vec![
                tactic(
                    "rwSeq",
                    vec![
                        atom("rw"),
                        tactic("optConfig", vec![node("null", Vec::new())]),
                        argument(input, 1),
                        optional(argument(input, 2)),
                    ],
                ),
                atom(";"),
                tactic("assumption", vec![atom("assumption")]),
            ])),
            Self::Rw => {
                let rules = argument(input, 2);
                let entries = match &argument(&rules, 1) {
                    Syntax::Node { args, .. } => args.clone(),
                    _ => Vec::new(),
                };
                let close = parenthesized(sequence(vec![tactic(
                    "tacticTry_",
                    vec![
                        atom("try"),
                        sequence(vec![parenthesized(sequence(vec![tactic(
                            "withReducible",
                            vec![
                                atom("with_reducible"),
                                sequence(vec![tactic("tacticRfl", vec![atom("rfl")])]),
                            ],
                        )]))]),
                    ],
                )]));
                parenthesized(sequence(vec![
                    tactic(
                        "rewriteSeq",
                        vec![
                            atom("rewrite"),
                            argument(input, 1),
                            tactic(
                                "rwRuleSeq",
                                vec![atom("["), node("null", entries), atom("]")],
                            ),
                            optional(argument(input, 3)),
                        ],
                    ),
                    atom(";"),
                    tactic(
                        "withAnnotateState",
                        vec![atom("with_annotate_state"), argument(&rules, 2), close],
                    ),
                ]))
            }
            Self::AndThen => tactic(
                "focus",
                vec![
                    atom("focus"),
                    sequence(vec![
                        argument(input, 0),
                        node("null", Vec::new()),
                        tactic(
                            "withAnnotateState",
                            vec![
                                atom("with_annotate_state"),
                                argument(input, 1),
                                tactic("skip", vec![atom("skip")]),
                            ],
                        ),
                        node("null", Vec::new()),
                        tactic(
                            "allGoals",
                            vec![atom("all_goals"), sequence(vec![argument(input, 2)])],
                        ),
                    ]),
                ],
            ),
            Self::Seq | Self::SeqLeft | Self::SeqRight => {
                // Init/Notation.lean's registered macros quote an ordinary
                // application with a Unit thunk. Both constants are resolved
                // where the macro was declared, while each operand is kept
                // verbatim as an antiquotation. In particular, neither a
                // caller-local Unit nor SeqRight may capture the quotation.
                let function = match self {
                    Self::Seq => "Seq.seq",
                    Self::SeqLeft => "SeqLeft.seqLeft",
                    Self::SeqRight => "SeqRight.seqRight",
                    _ => unreachable!("matched sequencing quotation"),
                };
                let mut unit = identifier("Unit")?;
                // Unit is both a declaration and a namespace at the macro's
                // declaration site. Quotation records both resolution paths.
                if let Syntax::Ident { preresolved, .. } = &mut unit {
                    preresolved.push(Preresolved::Namespace { ns: name("Unit") });
                }
                let thunk = node(
                    "Lean.Parser.Term.fun",
                    vec![
                        atom("fun"),
                        node(
                            "Lean.Parser.Term.basicFun",
                            vec![
                                node("null", vec![node("Lean.Parser.Term.hole", vec![atom("_")])]),
                                node(
                                    "null",
                                    vec![node("Lean.Parser.Term.typeSpec", vec![atom(":"), unit])],
                                ),
                                atom("=>"),
                                argument(input, 2),
                            ],
                        ),
                    ],
                );
                node(
                    "Lean.Parser.Term.app",
                    vec![
                        identifier(function)?,
                        node("null", vec![argument(input, 0), thunk]),
                    ],
                )
            }
        })
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
            if !self.matches(input) {
                return Ok(make_ctor(
                    layout::RESULT_ERROR,
                    vec![Obj::mk_nat(layout::EXCEPTION_UNSUPPORTED_TAG), state],
                ));
            }
            let info = info_from_reference(reference);
            let output = self.quote(input, invocation.context, info)?;
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

/// Syntax.getArg returns `missing` for absent children and non-node syntax.
fn argument(syntax: &Syntax, index: usize) -> Syntax {
    match syntax {
        Syntax::Node { args, .. } => args.get(index).cloned().unwrap_or(Syntax::Missing),
        _ => Syntax::Missing,
    }
}

fn name(text: &str) -> Name {
    Name::from_components(text.split('.'))
}

/// The pin's SourceInfo.fromRef with canonical=false. Its head traversal stops
/// at the first atom/identifier even if that leaf has no position; the tail
/// traversal skips positionless leaves. Input conversion already bounds this
/// tree, and these walks use an explicit stack rather than host recursion.
pub(super) fn info_from_reference(reference: &Syntax) -> SourceInfo {
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
