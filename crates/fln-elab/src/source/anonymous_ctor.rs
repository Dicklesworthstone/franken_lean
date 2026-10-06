//! `⟨a, b, …⟩`: the pin's `elabAnonymousCtor` (`Lean/Elab/BuiltinNotation.lean:43`), bead
//! `franken_lean-z8j.1.10`.
//!
//! The pin expands the notation to an application of the expected type's only constructor:
//!
//! 1. the expected type must be known; it is reduced to weak head normal form, and a
//!    metavariable head is "could not be determined";
//! 2. its head must be an inductive type with exactly one constructor;
//! 3. with `n` the number of the constructor's *explicit* fields (binders after its
//!    parameters), `⟨a₁, …, aₙ⟩` becomes `C a₁ … aₙ`, elaborated against the expected type.
//!
//! Fewer than `n` arguments is the pin's "Insufficient number of fields" error (the pin then
//! fills sorries under `errToSorry`; an error is an error here). More than `n` arguments nest
//! the extra ones into a `⟨…⟩` for the last field ([`nest_fields`]), as at the pin, so
//! `⟨1, 2, rfl⟩ : ∃ x y, x + y = 3` is `⟨1, ⟨2, rfl⟩⟩`. The pin postpones elaboration while the expected type is
//! unknown or a metavariable (`tryPostponeIfNoneOrMVar`); this elaborator has no postponement
//! here, so it refuses where the pin would wait, which can refuse a program the pin accepts
//! but never accepts one it rejects.
use super::*;
use fln_env::constants::{ConstantInfo, ConstructorVal};

/// Why `⟨…⟩` was refused. The first five are the pin's own errors, in its words.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AnonymousCtorError {
    ExpectedTypeUnknown,
    NotInductive,
    NoConstructors,
    ManyConstructors,
    InsufficientFields {
        ctor: Name,
        explicit: usize,
        provided: usize,
    },
    NoExplicitFields {
        ctor: Name,
        provided: usize,
    },
    /// More arguments than explicit fields: the pin nests the rest into the last field.
    NestedFieldsUnsupported {
        ctor: Name,
        explicit: usize,
        provided: usize,
    },
}

impl std::fmt::Display for AnonymousCtorError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        const PREFIX: &str = "Invalid `⟨...⟩` notation: ";
        match self {
            Self::ExpectedTypeUnknown => write!(
                f,
                "{PREFIX}The expected type of this term could not be determined"
            ),
            Self::NotInductive => write!(f, "{PREFIX}The expected type is not an inductive type"),
            Self::NoConstructors => write!(f, "{PREFIX}The expected type has no constructors"),
            Self::ManyConstructors => {
                write!(f, "{PREFIX}The expected type has more than one constructor")
            }
            Self::InsufficientFields {
                ctor,
                explicit,
                provided,
            } => {
                // The pin's wording, including its "fields"/"field" choice.
                let fields = if *explicit == 1 { "fields" } else { "field" };
                let provided = match provided {
                    0 => "none were".to_string(),
                    1 => "only 1 was".to_string(),
                    n => format!("only {n} were"),
                };
                write!(
                    f,
                    "Insufficient number of fields for `⟨...⟩` constructor: Constructor `{}` has {explicit} explicit {fields}, but {provided} provided",
                    ctor.to_display_string()
                )
            }
            Self::NoExplicitFields { ctor, provided } => write!(
                f,
                "Insufficient number of fields for `⟨...⟩` constructor: Constructor `{}` does not have explicit fields, but {provided} {} provided",
                ctor.to_display_string(),
                if *provided == 1 { "was" } else { "were" }
            ),
            Self::NestedFieldsUnsupported {
                ctor,
                explicit,
                provided,
            } => write!(
                f,
                "`⟨...⟩` with {provided} arguments for constructor `{}` ({explicit} explicit fields) nests the extra arguments into the last field, which is not implemented",
                ctor.to_display_string()
            ),
        }
    }
}

fn refuse(error: AnonymousCtorError) -> NatDefinitionElabError {
    failure(SourceInferenceError::AnonymousCtor(error))
}

impl Context {
    /// The constructor `⟨…⟩` with `provided` arguments stands for under `expected`, as a typed
    /// constant ready to be applied to exactly those arguments.
    pub(super) fn anonymous_constructor(
        &mut self,
        expected: Option<&Expr>,
        provided: usize,
    ) -> Result<Typed, NatDefinitionElabError> {
        let Some(expected) = expected else {
            return Err(refuse(AnonymousCtorError::ExpectedTypeUnknown));
        };
        let expected = self.instantiate(expected)?;
        let expected = self.whnf(&expected)?;
        let mut head = &expected;
        while let ExprNode::App { f, .. } = head.node() {
            head = f;
        }
        let name = match head.node() {
            ExprNode::MVar { .. } => return Err(refuse(AnonymousCtorError::ExpectedTypeUnknown)),
            ExprNode::Const { name, .. } => name.clone(),
            _ => return Err(refuse(AnonymousCtorError::NotInductive)),
        };
        let Some(ConstantInfo::Induct(inductive)) = self.txn.env.find(&name).cloned() else {
            return Err(refuse(AnonymousCtorError::NotInductive));
        };
        let ctor = match inductive.ctors.as_slice() {
            [ctor] => ctor.clone(),
            [] => return Err(refuse(AnonymousCtorError::NoConstructors)),
            _ => return Err(refuse(AnonymousCtorError::ManyConstructors)),
        };
        let Some(ConstantInfo::Ctor(info)) = self.txn.env.find(&ctor).cloned() else {
            return Err(failure(SourceInferenceError::Scope));
        };
        let explicit = explicit_fields(&info)?;
        if provided < explicit {
            return Err(refuse(AnonymousCtorError::InsufficientFields {
                ctor,
                explicit,
                provided,
            }));
        }
        if provided > explicit {
            return Err(refuse(if explicit == 0 {
                AnonymousCtorError::NoExplicitFields { ctor, provided }
            } else {
                AnonymousCtorError::NestedFieldsUnsupported {
                    ctor,
                    explicit,
                    provided,
                }
            }));
        }
        self.constant(&ctor)
    }
}

/// The pin's nesting rewrite (`elabAnonymousCtor`, `BuiltinNotation.lean:62`): with `explicit`
/// explicit fields and more `elements` (separators interleaved), the first `explicit - 1`
/// stay and the rest become one `⟨…⟩` in the last field's place. `explicit` is at least 1.
pub(super) fn nest_fields(elements: &[Syntax], explicit: usize) -> Syntax {
    let keep = (explicit.saturating_sub(1)) * 2;
    let atom = |text: &str| Syntax::atom(fln_syntax::source::SourceInfo::None, text);
    let ctor = |fields: Vec<Syntax>| {
        Syntax::node(
            parser_kind(&["Term", "anonymousCtor"]),
            vec![
                atom("⟨"),
                Syntax::node(Name::from_components(["null"]), fields),
                atom("⟩"),
            ],
        )
    };
    let mut outer: Vec<Syntax> = elements[..keep].to_vec();
    outer.push(ctor(elements[keep..].to_vec()));
    ctor(outer)
}

/// The number of explicit binders among a constructor's fields: the binders after its
/// parameters (`forallTelescopeReducing cinfo.type`, counting `isExplicit` from `numParams`).
/// A constructor type is a syntactic telescope of exactly `num_params + num_fields` binders.
fn explicit_fields(info: &ConstructorVal) -> Result<usize, NatDefinitionElabError> {
    let mut type_ = &info.base.type_;
    let mut explicit = 0;
    for index in 0..(info.num_params as usize + info.num_fields as usize) {
        let ExprNode::ForallE {
            body, binder_info, ..
        } = type_.node()
        else {
            return Err(failure(SourceInferenceError::Scope));
        };
        if index >= info.num_params as usize && matches!(binder_info, BinderInfo::Default) {
            explicit += 1;
        }
        type_ = body;
    }
    Ok(explicit)
}
