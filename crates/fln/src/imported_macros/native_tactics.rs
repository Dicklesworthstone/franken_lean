//! Native counterparts for selected registered Init quotation macros.
//!
//! These are individual registry candidates, not an aggregate reflexivity
//! tactic. Their checked owners and exact census names select native quotation
//! code; no Reference toolchain body is interpreted. User registrations and
//! recursive `expandMacro?` calls retain the ordinary candidate order.
//! Applicative sequencing uses that same dispatch, including when a user macro
//! asks to expand a term before returning its result to the elaborator.

use super::{
    MacroExecution, MacroInvocation, MacroLimits, StateBudget, SyntaxConversionError, SyntaxLimits,
    VerifiedPartition, conversion_outcome, inject_state, layout, make_ctor, project_result, syntax,
};
use fln_comp::flbc::{
    self, ArgumentOwnership, CallableResultOwnership, Function, FunctionId, Instruction, Program,
    Register, ValidatedProgram,
};
use fln_core::name::{
    Name,
    hygiene::{RESERVED_MACRO_SCOPE, add_macro_scope},
};
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
    BoolIf,
    IfLet,
    BitOr,
    BitXor,
    BitAnd,
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Pow,
    Append,
    Neg,
    SMul,
    GeAscii,
    LeAscii,
    Le,
    Lt,
    Gt,
    Ge,
    Eq,
    BEq,
    Exists,
    ExistsAscii,
    Sigma,
    PSigma,
    DependentPair,
    DependentPairSort,
}

enum NativeQuotation {
    Expanded(Syntax),
    Error(&'static str),
}

impl NativeTacticMacro {
    // Exact registrations from REFERENCE_GRAMMAR_CENSUS.txt, not spellings
    // inferred from a caller's syntax kind. The partition and checked module
    // owner remain mandatory before any candidate receives native execution.
    const ALL: [Self; 48] = [
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
        Self::BoolIf,
        Self::IfLet,
        Self::BitOr,
        Self::BitXor,
        Self::BitAnd,
        Self::Add,
        Self::Sub,
        Self::Mul,
        Self::Div,
        Self::Mod,
        Self::Pow,
        Self::Append,
        Self::Neg,
        Self::SMul,
        Self::GeAscii,
        Self::LeAscii,
        Self::Le,
        Self::Lt,
        Self::Gt,
        Self::Ge,
        Self::Eq,
        Self::BEq,
        Self::Exists,
        Self::ExistsAscii,
        Self::Sigma,
        Self::PSigma,
        Self::DependentPair,
        Self::DependentPairSort,
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
            Self::Seq
            | Self::SeqLeft
            | Self::SeqRight
            | Self::BoolIf
            | Self::IfLet
            | Self::BitOr
            | Self::BitXor
            | Self::BitAnd
            | Self::Add
            | Self::Sub
            | Self::Mul
            | Self::Div
            | Self::Mod
            | Self::Pow
            | Self::Append
            | Self::Neg
            | Self::SMul
            | Self::GeAscii
            | Self::LeAscii
            | Self::Le
            | Self::Lt
            | Self::Gt
            | Self::Ge
            | Self::Eq
            | Self::BEq => "Init.Notation",
            Self::Exists
            | Self::ExistsAscii
            | Self::Sigma
            | Self::PSigma
            | Self::DependentPair
            | Self::DependentPairSort => "Init.NotationExtra",
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
            Self::BoolIf => "_aux_Init_Notation___macroRules_boolIfThenElse_1",
            Self::IfLet => "_aux_Init_Notation___macroRules_termIfLet_1",
            Self::BitOr => "_aux_Init_Notation___macroRules_term_|||__2",
            Self::BitXor => "_aux_Init_Notation___macroRules_term_^^^__2",
            Self::BitAnd => "_aux_Init_Notation___macroRules_term_&&&__2",
            Self::Add => "_aux_Init_Notation___macroRules_term_+__2",
            Self::Sub => "_aux_Init_Notation___macroRules_term_-__2",
            Self::Mul => "_aux_Init_Notation___macroRules_term_*__2",
            Self::Div => "_aux_Init_Notation___macroRules_term_/__2",
            Self::Mod => "_aux_Init_Notation___macroRules_term_%__2",
            Self::Pow => "_aux_Init_Notation___macroRules_term_^__2",
            Self::Append => "_aux_Init_Notation___macroRules_term_++__2",
            Self::Neg => "_aux_Init_Notation___macroRules_term-__2",
            Self::SMul => "_aux_Init_Notation___macroRules_term_•__2",
            Self::GeAscii => "_aux_Init_Notation___macroRules_term_>=__2",
            Self::LeAscii => "_aux_Init_Notation___macroRules_term_<=__2",
            Self::Le => "_aux_Init_Notation___macroRules_term_≤__2",
            Self::Lt => "_aux_Init_Notation___macroRules_term_<__2",
            Self::Gt => "_aux_Init_Notation___macroRules_term_>__2",
            Self::Ge => "_aux_Init_Notation___macroRules_term_≥__2",
            Self::Eq => "_aux_Init_Notation___macroRules_term_=__2",
            Self::BEq => "_aux_Init_Notation___macroRules_term_==__2",
            Self::Exists => "_aux_Init_NotationExtra___macroRules_term∃_,__1",
            Self::ExistsAscii => "_aux_Init_NotationExtra___macroRules_termExists_,__1",
            Self::Sigma => "_aux_Init_NotationExtra___macroRules_termΣ_,__1",
            Self::PSigma => "_aux_Init_NotationExtra___macroRules_termΣ'_,__1",
            Self::DependentPair => "_aux_Init_NotationExtra___macroRules_term_×__1_1",
            Self::DependentPairSort => "_aux_Init_NotationExtra___macroRules_term_×'__1_1",
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
            Self::BoolIf => "mirror:_aux_Init_Notation___macroRules_boolIfThenElse_1",
            Self::IfLet => "mirror:_aux_Init_Notation___macroRules_termIfLet_1",
            Self::BitOr => "mirror:_aux_Init_Notation___macroRules_term_|||__2",
            Self::BitXor => "mirror:_aux_Init_Notation___macroRules_term_^^^__2",
            Self::BitAnd => "mirror:_aux_Init_Notation___macroRules_term_&&&__2",
            Self::Add => "mirror:_aux_Init_Notation___macroRules_term_+__2",
            Self::Sub => "mirror:_aux_Init_Notation___macroRules_term_-__2",
            Self::Mul => "mirror:_aux_Init_Notation___macroRules_term_*__2",
            Self::Div => "mirror:_aux_Init_Notation___macroRules_term_/__2",
            Self::Mod => "mirror:_aux_Init_Notation___macroRules_term_%__2",
            Self::Pow => "mirror:_aux_Init_Notation___macroRules_term_^__2",
            Self::Append => "mirror:_aux_Init_Notation___macroRules_term_++__2",
            Self::Neg => "mirror:_aux_Init_Notation___macroRules_term-__2",
            Self::SMul => "mirror:_aux_Init_Notation___macroRules_term_•__2",
            Self::GeAscii => "mirror:_aux_Init_Notation___macroRules_term_>=__2",
            Self::LeAscii => "mirror:_aux_Init_Notation___macroRules_term_<=__2",
            Self::Le => "mirror:_aux_Init_Notation___macroRules_term_≤__2",
            Self::Lt => "mirror:_aux_Init_Notation___macroRules_term_<__2",
            Self::Gt => "mirror:_aux_Init_Notation___macroRules_term_>__2",
            Self::Ge => "mirror:_aux_Init_Notation___macroRules_term_≥__2",
            Self::Eq => "mirror:_aux_Init_Notation___macroRules_term_=__2",
            Self::BEq => "mirror:_aux_Init_Notation___macroRules_term_==__2",
            Self::Exists => "mirror:_aux_Init_NotationExtra___macroRules_term∃_,__1",
            Self::ExistsAscii => "mirror:_aux_Init_NotationExtra___macroRules_termExists_,__1",
            Self::Sigma => "mirror:_aux_Init_NotationExtra___macroRules_termΣ_,__1",
            Self::PSigma => "mirror:_aux_Init_NotationExtra___macroRules_termΣ'_,__1",
            Self::DependentPair => "mirror:_aux_Init_NotationExtra___macroRules_term_×__1_1",
            Self::DependentPairSort => "mirror:_aux_Init_NotationExtra___macroRules_term_×'__1_1",
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
            Self::BoolIf => "boolIfThenElse",
            Self::IfLet => "termIfLet",
            Self::BitOr => "term_|||_",
            Self::BitXor => "term_^^^_",
            Self::BitAnd => "term_&&&_",
            Self::Add => "term_+_",
            Self::Sub => "term_-_",
            Self::Mul => "term_*_",
            Self::Div => "term_/_",
            Self::Mod => "term_%_",
            Self::Pow => "term_^_",
            Self::Append => "term_++_",
            Self::Neg => "term-_",
            Self::SMul => "term_•_",
            Self::GeAscii => "term_>=_",
            Self::LeAscii => "term_<=_",
            Self::Le => "term_≤_",
            Self::Lt => "term_<_",
            Self::Gt => "term_>_",
            Self::Ge => "term_≥_",
            Self::Eq => "term_=_",
            Self::BEq => "term_==_",
            Self::Exists => "term∃_,_",
            Self::ExistsAscii => "termExists_,_",
            Self::Sigma => "termΣ_,_",
            Self::PSigma => "termΣ'_,_",
            Self::DependentPair => "term_×__1",
            Self::DependentPairSort => "term_×'__1",
        }
    }

    fn syntax_kind(self) -> Name {
        if matches!(self.module(), "Init.Notation" | "Init.NotationExtra") {
            name(self.input_kind())
        } else {
            Name::str(name("Lean.Parser.Tactic"), self.input_kind())
        }
    }

    fn matches(self, input: &Syntax) -> bool {
        if !is_of_kind(input, &self.syntax_kind()) {
            return false;
        }
        // rw's body performs a second quotation-pattern match on its rule
        // sequence; the other candidates only match their input node kind.
        self != Self::Rw
            || is_of_kind(
                argument_ref(input, 2),
                &name("Lean.Parser.Tactic.rwRuleSeq"),
            )
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
        limits: SyntaxLimits,
    ) -> Result<NativeQuotation, SyntaxConversionError> {
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
        Ok(NativeQuotation::Expanded(match self {
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
            Self::BoolIf => {
                let mut function = identifier("cond")?;
                // cond is both a declaration and a namespace at the macro's
                // declaration site, so the quotation records both targets.
                if let Syntax::Ident { preresolved, .. } = &mut function {
                    preresolved.push(Preresolved::Namespace { ns: name("cond") });
                }
                node(
                    "Lean.Parser.Term.app",
                    vec![
                        function,
                        node(
                            "null",
                            vec![argument(input, 1), argument(input, 3), argument(input, 5)],
                        ),
                    ],
                )
            }
            Self::IfLet => {
                // Init.Notation's pattern conditional is a match quotation,
                // not a Boolean test: the first branch keeps the captured
                // pattern's binders, and the fallback has its own wildcard.
                let alternative = |pattern, body| {
                    node(
                        "Lean.Parser.Term.matchAlt",
                        vec![
                            atom("|"),
                            node("null", vec![node("null", vec![pattern])]),
                            atom("=>"),
                            body,
                        ],
                    )
                };
                node(
                    "Lean.Parser.Term.match",
                    vec![
                        atom("match"),
                        node("null", Vec::new()),
                        node("null", Vec::new()),
                        node(
                            "null",
                            vec![node(
                                "Lean.Parser.Term.matchDiscr",
                                vec![node("null", Vec::new()), argument(input, 4)],
                            )],
                        ),
                        atom("with"),
                        node(
                            "Lean.Parser.Term.matchAlts",
                            vec![node(
                                "null",
                                vec![
                                    alternative(argument(input, 2), argument(input, 6)),
                                    alternative(
                                        node("Lean.Parser.Term.hole", vec![atom("_")]),
                                        argument(input, 8),
                                    ),
                                ],
                            )],
                        ),
                    ],
                )
            }
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
            Self::BitOr
            | Self::BitXor
            | Self::BitAnd
            | Self::Add
            | Self::Sub
            | Self::Mul
            | Self::Div
            | Self::Mod
            | Self::Pow
            | Self::Append
            | Self::Neg
            | Self::SMul
            | Self::GeAscii
            | Self::LeAscii
            | Self::Le
            | Self::Lt
            | Self::Gt
            | Self::Ge
            | Self::Eq
            | Self::BEq => {
                // Init.Notation replaces the earlier infix-generated macro
                // with an expression-tree quotation. The helper kind matters:
                // it controls coercion propagation and relation elaboration.
                let (helper, constant) = match self {
                    Self::BitOr => ("binop", "HOr.hOr"),
                    Self::BitXor => ("binop", "HXor.hXor"),
                    Self::BitAnd => ("binop", "HAnd.hAnd"),
                    Self::Add => ("binop", "HAdd.hAdd"),
                    Self::Sub => ("binop", "HSub.hSub"),
                    Self::Mul => ("binop", "HMul.hMul"),
                    Self::Div => ("binop", "HDiv.hDiv"),
                    Self::Mod => ("binop", "HMod.hMod"),
                    Self::Pow => ("rightact", "HPow.hPow"),
                    Self::Append => ("binop", "HAppend.hAppend"),
                    Self::Neg => ("unop", "Neg.neg"),
                    Self::SMul => ("leftact", "HSMul.hSMul"),
                    Self::GeAscii | Self::Ge => ("binrel", "GE.ge"),
                    Self::LeAscii | Self::Le => ("binrel", "LE.le"),
                    Self::Lt => ("binrel", "LT.lt"),
                    Self::Gt => ("binrel", "GT.gt"),
                    Self::Eq => ("binrel", "Eq"),
                    Self::BEq => ("binrel_no_prop", "BEq.beq"),
                    _ => unreachable!("matched operator quotation"),
                };
                let mut function = identifier(constant)?;
                if self == Self::Eq {
                    // Like Unit, Eq resolves both as a declaration and as the
                    // namespace containing its constructors and eliminators.
                    if let Syntax::Ident { preresolved, .. } = &mut function {
                        preresolved.push(Preresolved::Namespace { ns: name("Eq") });
                    }
                }
                let mut args = vec![atom(&format!("{helper}%")), function];
                if self == Self::Neg {
                    args.push(argument(input, 1));
                } else {
                    args.extend([argument(input, 0), argument(input, 2)]);
                }
                node(&format!("Lean.Parser.Term.{helper}"), args)
            }
            Self::Exists
            | Self::ExistsAscii
            | Self::Sigma
            | Self::PSigma
            | Self::DependentPair
            | Self::DependentPairSort => return self.quote_binders(input, info, limits),
        }))
    }

    fn quote_binders(
        self,
        input: &Syntax,
        info: SourceInfo,
        limits: SyntaxLimits,
    ) -> Result<NativeQuotation, SyntaxConversionError> {
        // Init/NotationExtra.lean:26–62. These macros share the pin's binder
        // fold, including its behavior on partial trees: getArg supplies
        // missing, getArgs supplies an empty array, and non-ident binders
        // become freshly quoted holes rather than spliced source holes.
        let (constant, bracketed) = match self {
            Self::Exists | Self::ExistsAscii => ("Exists", false),
            Self::Sigma => ("Sigma", false),
            Self::PSigma => ("PSigma", false),
            Self::DependentPair => ("Sigma", true),
            Self::DependentPairSort => ("PSigma", true),
            _ => unreachable!("only the binder family uses this quotation"),
        };
        let binders = argument_ref(input, usize::from(!bracketed));
        let body = argument_ref(input, if bracketed { 2 } else { 3 });
        let inner = argument_ref(binders, 0);
        let unbracketed =
            !bracketed && inner.kind() == Some(&name("Lean.unbracketedExplicitBinders"));
        if !bracketed
            && !unbracketed
            && !arguments(inner)
                .iter()
                .all(|group| group.kind() == Some(&name("Lean.bracketedExplicitBinders")))
        {
            return Ok(NativeQuotation::Error("unexpected explicit binder"));
        }

        // mkCIdentFrom uses the reserved scope, not the caller's quotation
        // scope, and retains only its explicit declaration resolution.
        let declaration = name(constant);
        let value = add_macro_scope(&name("_internal"), &declaration, RESERVED_MACRO_SCOPE)
            .map_err(|_| SyntaxConversionError::Malformed("native binder constant hygiene"))?;
        let text = fln_core::name::identifier::to_identifier_string(&value, 4096)
            .map_err(|_| SyntaxConversionError::Malformed("native binder constant spelling"))?;
        let raw = RawIdentifier::owned(
            Arc::from(text.as_str()),
            ByteSpan::new(BytePos(0), BytePos(text.len())).expect("fixed binder constant range"),
        )
        .expect("fixed binder constant UTF-8 range");
        let mut quotation = BinderQuotation {
            info,
            constant: Syntax::Ident {
                info,
                raw_val: raw,
                val: value,
                preresolved: vec![Preresolved::Decl {
                    name: declaration,
                    fields: Vec::new(),
                }],
            },
            limits,
            nodes: 0,
            bytes: 0,
        };
        quotation.capture(body)?;
        let mut result = body.clone();
        if unbracketed {
            let annotation = argument_ref(inner, 1);
            let domain = match annotation {
                Syntax::Missing => None,
                Syntax::Node { kind, args, .. } if *kind == name("null") && args.is_empty() => None,
                _ => Some(argument_ref(annotation, 1)),
            };
            result = quotation.binders(arguments(argument_ref(inner, 0)), domain, result)?;
        } else if bracketed {
            result = quotation.binders(
                arguments(argument_ref(binders, 1)),
                Some(argument_ref(binders, 3)),
                result,
            )?;
        } else {
            for group in arguments(inner).iter().rev() {
                result = quotation.binders(
                    arguments(argument_ref(group, 1)),
                    Some(argument_ref(group, 3)),
                    result,
                )?;
            }
        }
        Ok(NativeQuotation::Expanded(result))
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
            let reference_object = syntax::inject(reference, invocation.source, limits.syntax)?;
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
            match self.quote(input, invocation.context, info, limits.syntax)? {
                NativeQuotation::Expanded(output) => {
                    let output = syntax::inject(&output, invocation.source, limits.syntax)?;
                    Ok(make_ctor(layout::RESULT_OK, vec![output, state]))
                }
                NativeQuotation::Error(message) => {
                    let error = make_ctor(
                        layout::EXCEPTION_ERROR,
                        vec![reference_object, Obj::mk_string(message)],
                    );
                    Ok(make_ctor(layout::RESULT_ERROR, vec![error, state]))
                }
            }
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

/// Bound construction before a shared binder type is copied once per name.
/// These are lower bounds on the existing ABI conversion's node/text charges;
/// the complete conversion still checks names, source ranges and pre-resolution.
/// Thus the guard cannot narrow a result that would fit that same allowance.
struct BinderQuotation {
    info: SourceInfo,
    constant: Syntax,
    limits: SyntaxLimits,
    nodes: usize,
    bytes: usize,
}

impl BinderQuotation {
    fn charge(&mut self, nodes: usize, bytes: usize) -> Result<(), SyntaxConversionError> {
        for (total, count, limit, resource) in [
            (
                &mut self.nodes,
                nodes,
                self.limits.max_nodes,
                "native binder quotation nodes",
            ),
            (
                &mut self.bytes,
                bytes,
                self.limits.max_bytes,
                "native binder quotation text bytes",
            ),
        ] {
            *total = total
                .checked_add(count)
                .ok_or(SyntaxConversionError::Limit {
                    resource,
                    limit,
                    observed: usize::MAX,
                })?;
            if *total > limit {
                return Err(SyntaxConversionError::Limit {
                    resource,
                    limit,
                    observed: *total,
                });
            }
        }
        Ok(())
    }

    fn capture(&mut self, syntax: &Syntax) -> Result<(), SyntaxConversionError> {
        let mut pending = vec![syntax];
        while let Some(current) = pending.pop() {
            self.charge(1, 0)?;
            match current {
                Syntax::Node { args, .. } => pending.extend(args),
                Syntax::Atom { val, .. } => self.charge(0, val.len())?,
                Syntax::Ident {
                    raw_val,
                    preresolved,
                    ..
                } => {
                    if let Some(backing) = raw_val.owned_backing() {
                        self.charge(0, backing.len())?;
                    }
                    for target in preresolved {
                        if let Preresolved::Decl { fields, .. } = target {
                            for field in fields {
                                self.charge(0, field.len())?;
                            }
                        }
                    }
                }
                Syntax::Missing => {}
            }
        }
        Ok(())
    }

    fn binders(
        &mut self,
        binders: &[Syntax],
        domain: Option<&Syntax>,
        mut body: Syntax,
    ) -> Result<Syntax, SyntaxConversionError> {
        for binder in binders.iter().rev() {
            let binder = argument_ref(binder, 0);
            let named = matches!(binder, Syntax::Ident { .. });
            // app/null/fun/basicFun/binder-list/type-list and fun/=> atoms;
            // typed binders add typeSpec/:, anonymous ones add hole/_ syntax.
            self.charge(
                8 + 2 * usize::from(domain.is_some()) + 2 * usize::from(!named),
                5 + usize::from(domain.is_some()) + usize::from(!named),
            )?;
            let constant = self.constant.clone();
            self.capture(&constant)?;
            if named {
                self.capture(binder)?;
            }
            if let Some(domain) = domain {
                self.capture(domain)?;
            }
            let atom = |text: &str| Syntax::Atom {
                info: self.info,
                val: text.to_owned(),
            };
            let node = |kind: &str, args| Syntax::Node {
                info: self.info,
                kind: name(kind),
                args,
            };
            let binder = if named {
                binder.clone()
            } else {
                node("Lean.Parser.Term.hole", vec![atom("_")])
            };
            let annotation = domain.map_or_else(Vec::new, |domain| {
                vec![node(
                    "Lean.Parser.Term.typeSpec",
                    vec![atom(":"), domain.clone()],
                )]
            });
            let lambda = node(
                "Lean.Parser.Term.fun",
                vec![
                    atom("fun"),
                    node(
                        "Lean.Parser.Term.basicFun",
                        vec![
                            node("null", vec![binder]),
                            node("null", annotation),
                            atom("=>"),
                            body,
                        ],
                    ),
                ],
            );
            body = node(
                "Lean.Parser.Term.app",
                vec![constant, node("null", vec![lambda])],
            );
        }
        Ok(body)
    }
}

fn arguments(syntax: &Syntax) -> &[Syntax] {
    match syntax {
        Syntax::Node { args, .. } => args,
        _ => &[],
    }
}

/// Syntax.isOfKind includes pseudo-kinds. In particular an atom can match a
/// root-level notation kind, but a dotted atom remains one Name component.
fn is_of_kind(syntax: &Syntax, expected: &Name) -> bool {
    match syntax {
        Syntax::Node { kind, .. } => kind == expected,
        Syntax::Atom { val, .. } => Name::str(Name::anonymous(), val) == *expected,
        Syntax::Ident { .. } => name("ident") == *expected,
        Syntax::Missing => name("missing") == *expected,
    }
}

fn argument_ref(syntax: &Syntax, index: usize) -> &Syntax {
    static MISSING: Syntax = Syntax::Missing;
    arguments(syntax).get(index).unwrap_or(&MISSING)
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
