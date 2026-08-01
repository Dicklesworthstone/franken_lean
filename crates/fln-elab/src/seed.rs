//! The elaboration seam, seeded: parsed syntax in, a KERNEL-ACCEPTED constant out
//! (bead `fln-5720`, filed from the 2026-07-31 reality check; plan §10, §4.3).
//!
//! # What this is, stated so nobody mistakes it for the elaborator
//!
//! This is the SMALLEST end-to-end slice that makes FrankenLean a toolchain
//! rather than an apparatus: for `def <ident> := <nat-literal>`, walk Vellum's
//! command tree, build the `Declaration` the kernel's one authority accepts, and
//! run `fln_kernel::check`. No unifier, no instance search, no tactics, no
//! macros, no type inference — the type is the literal's own `Nat`. Everything
//! it does not do is a bead, not a silence (see the module's residue list at the
//! bottom of this doc comment).
//!
//! It is a SUBSET of Athanor, never a substitute (the plan's subset rule): the
//! monadic tower, the approximation ladder, Synod, match compilation and the
//! deterministic scheduler all arrive with their workstream beads. What this
//! establishes is that the seam CLOSES — that Vellum's output and the kernel's
//! input are joinable today, with a real acceptance at the end.
//!
//! # The residue, named
//!
//! Not implemented here, each already owned or filed: type INFERENCE (the seed
//! reads the literal's type directly), non-literal bodies, binders and
//! telescopes, universe polymorphism (the seed is level-monomorphic),
//! definitional unfolding hints beyond `Abbrev`, `theorem`/`inductive`/
//! `mutual` forms, and every effect of elaboration order. A body outside the
//! seed grammar REFUSES typed — it is never guessed at.

use fln_core::expr::{Expr, Literal, NatLit};
use fln_core::level::Level;
use fln_core::name::Name;
use fln_core::outcome::Outcome;
use fln_env::constants::AxiomVal;
use fln_env::constants::{ConstantVal, DefinitionSafety, DefinitionVal, ReducibilityHints};
use fln_env::environment::Environment;
use fln_env::environment::{DeclarationBudget, DeclarationCommitted};
use fln_env::pmap::CollisionBudget;
use fln_kernel::capability::{Published, admit};
use fln_kernel::council::{Council, CouncilOutcome, convene};
use fln_kernel::verdict::{Budget, Verdict};
use fln_kernel::{Declaration, check};
use fln_parse::{ParsedNatDefinition, parse_nat_definition};
use fln_syntax::tree::Syntax;

/// Why the seed refused. Every arm is a REFUSAL, never a rejection of the
/// source: outside-the-seed-grammar means "this elaborator cannot see it yet",
/// which is the honest thing a subset can say (FL-INV-07's shape one layer up).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SeedError {
    /// Vellum refused the bytes; the parser's own diagnostic is carried.
    Parse(String),
    /// The command tree parsed but its shape is outside what the seed reads.
    OutsideSeedShape(&'static str),
    /// The kernel did not accept, or did not answer. Carries its own words.
    Kernel(String),
}

impl core::fmt::Display for SeedError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            SeedError::Parse(d) => write!(f, "parse refused: {d}"),
            SeedError::OutsideSeedShape(w) => write!(f, "outside the seed shape: {w}"),
            SeedError::Kernel(w) => write!(f, "kernel: {w}"),
        }
    }
}

impl std::error::Error for SeedError {}

/// One elaborated declaration and the verdict the kernel gave it.
#[derive(Debug, Clone)]
pub struct Elaborated {
    pub declaration: Declaration,
    pub verdict: Verdict,
}

/// Read the identifier and the natural literal out of Vellum's command tree.
/// Returns `None` for any shape the seed does not recognise — the caller turns
/// that into a typed refusal rather than a guess.
fn read_def_shape(syntax: &Syntax) -> Option<(Name, u64)> {
    let mut ident: Option<Name> = None;
    let mut literal: Option<u64> = None;
    let mut stack = vec![syntax];
    while let Some(node) = stack.pop() {
        match node {
            Syntax::Atom { val, .. } => {
                if let Ok(n) = val.parse::<u64>() {
                    // The seed grammar admits exactly one literal; a second
                    // would already have been refused upstream by the parser.
                    if literal.is_none() {
                        literal = Some(n);
                    }
                }
            }
            Syntax::Ident { val, .. } => {
                if ident.is_none() {
                    ident = Some(val.clone());
                }
            }
            Syntax::Node { args, .. } => stack.extend(args.iter().rev()),
            Syntax::Missing => {}
        }
    }
    match (ident, literal) {
        (Some(i), Some(l)) => Some((i, l)),
        _ => None,
    }
}

/// The seed's PRELUDE, and why it needs one at all: the kernel refuses a
/// definition whose type names a constant the environment does not hold —
/// `unknown constant Nat`, measured on the first run of the seam. That refusal
/// is the kernel doing its job (FL-INV-02: nothing admits a constant but the
/// kernel), so the seed builds its environment the only legal way — through the
/// kernel's own admission and publication path.
///
/// `Nat` enters as an AXIOM of type `Sort 1`, which is a deliberate subset, not
/// a lie: the real `Nat` is an inductive with constructors and a recursor, and
/// admitting that whole block is the inductive-elaboration bead, not this seam.
/// A definition checked against this prelude is checked against an OPAQUE `Nat`
/// — enough for a literal's type to resolve, not enough to compute with, and
/// the residue says so.
fn prelude_with_nat() -> Result<Environment, SeedError> {
    let env = Environment::new();
    let nat_axiom = Declaration::Axiom(AxiomVal {
        base: ConstantVal {
            name: Name::from_components(["Nat"]),
            level_params: Vec::new(),
            type_: Expr::sort(Level::one()),
        },
        is_unsafe: false,
    });
    let budget = Budget::for_stack_bytes(Budget::MIN_STACK_BYTES);
    // A Reviewable has no `publish` and no route to a CheckedDecl outside the
    // kernel: admission runs through a COUNCIL by construction. The empty
    // council is the honest answer for a seed prelude — spelled, never skipped,
    // and it is exactly what makes this a subset rather than a bypass.
    let checked = match admit(&env, nat_axiom, budget) {
        Outcome::Complete(admitted) => match convene(&Council::nobody_was_asked(), admitted) {
            CouncilOutcome::Agreed(checked) => checked,
            CouncilOutcome::KernelRejected { class, .. } => {
                return Err(SeedError::Kernel(format!("prelude rejected: {class:?}")));
            }
            _ => {
                return Err(SeedError::Kernel(
                    "prelude council did not agree".to_string(),
                ));
            }
        },
        Outcome::Inconclusive(i) => {
            return Err(SeedError::Kernel(format!(
                "prelude inconclusive: {:?}",
                i.cause
            )));
        }
        Outcome::InternalFault(f) => {
            return Err(SeedError::Kernel(format!("prelude fault: {f:?}")));
        }
    };
    match checked.publish(
        DeclarationBudget::default(),
        CollisionBudget::default(),
        None,
    ) {
        Outcome::Complete(Published::Committed(committed)) => match committed {
            DeclarationCommitted::Published(p) => Ok(p.environment),
            _ => Err(SeedError::Kernel("prelude did not commit".to_string())),
        },
        Outcome::Complete(_) => Err(SeedError::Kernel("prelude publish refused".to_string())),
        Outcome::Inconclusive(i) => Err(SeedError::Kernel(format!(
            "prelude publish inconclusive: {:?}",
            i.cause
        ))),
        Outcome::InternalFault(f) => {
            Err(SeedError::Kernel(format!("prelude publish fault: {f:?}")))
        }
    }
}

/// The seam: source bytes in, a kernel-accepted constant out.
pub fn elaborate_nat_definition(source: &[u8]) -> Result<Elaborated, SeedError> {
    let parsed: ParsedNatDefinition =
        parse_nat_definition(source).map_err(|e| SeedError::Parse(format!("{e:?}")))?;
    let (ident, value) = read_def_shape(parsed.syntax()).ok_or(SeedError::OutsideSeedShape(
        "expected one identifier and one Nat literal",
    ))?;

    // The seed's whole type story: a Nat literal has type Nat. Inference is a
    // later bead; reading the type off the literal is a subset, not a stand-in
    // for the algorithm.
    let nat = Name::from_components(["Nat"]);
    let ty = Expr::const_(nat, Vec::<Level>::new());
    let body = Expr::lit(Literal::Nat(NatLit::from_u64(value)));

    let decl = Declaration::Defn(DefinitionVal {
        base: ConstantVal {
            name: ident,
            level_params: Vec::new(),
            type_: ty,
        },
        value: body,
        hints: ReducibilityHints::Abbrev,
        safety: DefinitionSafety::Safe,
        all: Vec::new(),
    });

    let env = prelude_with_nat()?;
    match check(
        &env,
        &decl,
        Budget::for_stack_bytes(Budget::MIN_STACK_BYTES),
    ) {
        Outcome::Complete(verdict @ Verdict::Accepted { .. }) => Ok(Elaborated {
            declaration: decl,
            verdict,
        }),
        Outcome::Complete(verdict) => Err(SeedError::Kernel(format!("{verdict:?}"))),
        // FL-INV-07's two non-answers stay DISTINCT from each other and from a
        // rejection: neither is ever rendered as acceptance, and the compiler
        // itself insisted on this arm.
        Outcome::Inconclusive(i) => Err(SeedError::Kernel(format!("inconclusive: {:?}", i.cause))),
        Outcome::InternalFault(f) => Err(SeedError::Kernel(format!("internal fault: {f:?}"))),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn one_definition_goes_from_source_text_to_a_kernel_accepted_constant() {
        let elaborated =
            elaborate_nat_definition(b"def seven := 7\n").expect("the seam closes end to end");
        assert!(matches!(elaborated.verdict, Verdict::Accepted { .. }));
        match &elaborated.declaration {
            Declaration::Defn(d) => {
                assert_eq!(d.base.name, Name::from_components(["seven"]));
                assert!(
                    d.base.level_params.is_empty(),
                    "the seed is level-monomorphic"
                );
            }
            other => panic!("expected a definition, got {other:?}"),
        }
    }

    #[test]
    fn source_outside_the_seed_grammar_refuses_typed_never_guesses() {
        for bytes in [
            &b"theorem t : True := trivial\n"[..],
            &b"def missing_value\n"[..],
            &b""[..],
            &b"\xff\xfe not utf8"[..],
        ] {
            let err = elaborate_nat_definition(bytes).expect_err("must refuse");
            assert!(
                matches!(err, SeedError::Parse(_) | SeedError::OutsideSeedShape(_)),
                "refusal must be typed, got {err:?}"
            );
        }
    }
}
