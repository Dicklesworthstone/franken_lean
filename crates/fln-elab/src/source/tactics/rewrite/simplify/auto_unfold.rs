//! The pin's `Simp.unfold?` auto branch: choose a match alternative without assigning its
//! discriminants, or use an admitted structural definition's smart-unfolding body. Ordinary
//! definitions, partial applications, erased names and irreducible definitions stay folded.
//!
//! Source matches compile directly to recursors here. Their equation journal retains the
//! original alternatives, so an outer match can select its branch without confusing a stuck
//! nested match in that branch with a stuck outer discriminant. The journal selects reductions;
//! the expression returned is always the admitted definition's actual body, never journal RHSs.
use super::*;
use crate::source::equation_theorems::journal::{self, Record};
use fln_core::expr::Literal;
use fln_env::constants::{ConstantInfo, DefinitionVal};

pub(in crate::source) struct AutoUnfold {
    erased: HashSet<Name>,
    matches: HashMap<Name, Record>,
    reducibility: Arc<crate::reducibility::ReducibilityTable>,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Match {
    Yes,
    No,
    Stuck,
}

impl Context {
    pub(super) fn simp_auto_unfold(
        &mut self,
        erased: HashSet<Name>,
    ) -> Result<AutoUnfold, NatDefinitionElabError> {
        let environment = self.txn.env.clone();
        // Decoding is bounded by the journal's own limits and charged before allocating its
        // expression trees. Read it once per call, never once per occurrence or definition.
        if let Some(state) = environment.extension(&journal::journal_name()) {
            for entry in state.entries() {
                for _ in entry.payload.chunks(64) {
                    self.tick()?;
                }
            }
        }
        let matches = journal::read(&environment)?
            .into_iter()
            .map(|record| (record.declaration.clone(), record))
            .collect();
        let reducibility = crate::reducibility::table(&environment).map_err(|e| {
            failure(SourceInferenceError::Unification(Box::new(
                UnificationError::Reducibility(e),
            )))
        })?;
        Ok(AutoUnfold {
            erased,
            matches,
            reducibility,
        })
    }

    pub(super) fn simp_auto_unfold_head(
        &mut self,
        term: &Expr,
        policy: &AutoUnfold,
    ) -> Result<Expr, NatDefinitionElabError> {
        let (head, arguments) = self.dsimp_spine(term)?;
        let ExprNode::Const { name, levels } = head.node() else {
            return Ok(term.clone());
        };
        if policy.erased.contains(name)
            || policy.reducibility.status(name) == crate::reducibility::Reducibility::Irreducible
        {
            return Ok(term.clone());
        }
        let Some(ConstantInfo::Defn(definition)) = self.txn.env.find(name).cloned() else {
            return Ok(term.clone());
        };
        if definition.safety != DefinitionSafety::Safe {
            return Ok(term.clone());
        }
        let selected = match policy.matches.get(name) {
            Some(record) => self.simp_auto_match(&definition, levels, &arguments, record)?,
            None => {
                if self.simp_auto_requires_matcher_metadata(&definition, arguments.len())? {
                    return Err(error(TacticError::SimprocUnsupported(
                        "automatic unfolding without imported matcher metadata",
                    )));
                }
                false
            }
        };
        self.unfold_auto_definition(term, &definition, selected)
    }

    /// A saturated call through a conventional imported matcher helper cannot be treated as
    /// an ordinary nonmatch when its matcher metadata is absent. Its spelling only selects
    /// this capability refusal; it never authorizes an unfolding. User-authored lookalikes
    /// deliberately have the same conservative boundary.
    fn simp_auto_requires_matcher_metadata(
        &mut self,
        definition: &DefinitionVal,
        arguments: usize,
    ) -> Result<bool, NatDefinitionElabError> {
        if matches!(
            self.txn
                .env
                .find(&Name::str(definition.base.name.clone(), "_sunfold")),
            Some(ConstantInfo::Defn(_))
        ) {
            return Ok(false);
        }
        let mut body = &definition.value;
        let mut arity = 0usize;
        while let ExprNode::Lam { body: inner, .. } = body.node() {
            self.tick()?;
            arity = arity
                .checked_add(1)
                .ok_or_else(|| failure(SourceInferenceError::ResourceLimit))?;
            body = inner;
        }
        if arguments < arity {
            return Ok(false);
        }
        while let ExprNode::App { f, .. } = body.node() {
            self.tick()?;
            body = f;
        }
        let ExprNode::Const { name, .. } = body.node() else {
            return Ok(false);
        };
        let LeafView::Str(component) = name.leaf_view() else {
            return Ok(false);
        };
        let Some(index) = component.strip_prefix("match_") else {
            return Ok(false);
        };
        if index.is_empty() {
            return Ok(false);
        }
        for byte in index.bytes() {
            self.tick()?;
            if !byte.is_ascii_digit() {
                return Ok(false);
            }
        }
        Ok(matches!(
            self.txn.env.find(name),
            Some(ConstantInfo::Defn(helper)) if helper.safety == DefinitionSafety::Safe
        ))
    }

    /// Whether the original match has selected an alternative. No expression or universe hole
    /// in the target may be assigned to make a constructor fit. Earlier undecided rows block
    /// later catch-alls; a definite mismatch in any column rules the earlier row out.
    fn simp_auto_match(
        &mut self,
        definition: &DefinitionVal,
        levels: &[Level],
        arguments: &[Expr],
        record: &Record,
    ) -> Result<bool, NatDefinitionElabError> {
        if arguments.len() < record.arity {
            return Ok(false);
        }
        if definition.base.level_params.len() != levels.len()
            || record
                .discriminants
                .iter()
                .any(|&index| index >= record.arity)
        {
            return Err(failure(SourceInferenceError::Scope));
        }
        for alternative in &record.alternatives {
            self.tick()?;
            let mut body =
                self.instantiate_params(alternative, &definition.base.level_params, levels)?;
            for argument in arguments.iter().take(record.arity) {
                self.tick()?;
                let ExprNode::Lam { body: inner, .. } = body.node() else {
                    return Err(failure(SourceInferenceError::Scope));
                };
                body = self.substitute(inner, argument)?;
            }
            let mut fields = HashSet::new();
            while let ExprNode::Lam { body: inner, .. } = body.node() {
                self.tick()?;
                let id = FVarId(self.fresh_name()?);
                body = self.substitute(inner, &Expr::fvar(id.clone()))?;
                fields.insert(id);
            }
            let parts =
                journal::unpack(&body).ok_or_else(|| failure(SourceInferenceError::Scope))?;
            if parts.len() != record.discriminants.len() + 1 {
                return Err(failure(SourceInferenceError::Scope));
            }
            let mut bindings = HashMap::new();
            let mut verdict = Match::Yes;
            for (pattern, &index) in parts.iter().zip(&record.discriminants) {
                match self.simp_auto_pattern(pattern, &arguments[index], &fields, &mut bindings)? {
                    Match::No => {
                        verdict = Match::No;
                        break;
                    }
                    Match::Stuck => verdict = Match::Stuck,
                    Match::Yes => {}
                }
            }
            match verdict {
                Match::Yes => return Ok(true),
                Match::Stuck => return Ok(false),
                Match::No => {}
            }
        }
        Ok(false)
    }

    fn simp_auto_pattern(
        &mut self,
        pattern: &Expr,
        actual: &Expr,
        fields: &HashSet<FVarId>,
        bindings: &mut HashMap<FVarId, Expr>,
    ) -> Result<Match, NatDefinitionElabError> {
        let mut work = vec![(pattern.clone(), actual.clone())];
        let mut verdict = Match::Yes;
        while let Some((pattern, actual)) = work.pop() {
            self.tick()?;
            if let ExprNode::FVar { id } = pattern.node()
                && fields.contains(id)
            {
                if let Some(previous) = bindings.get(id) {
                    if !self.rewrite_same(previous, &actual)? {
                        verdict = Match::Stuck;
                    }
                } else {
                    bindings.insert(id.clone(), actual);
                }
                continue;
            }
            let pattern = self.simp_auto_discriminant(&pattern)?;
            let actual = self.simp_auto_discriminant(&actual)?;
            if self.rewrite_same(&pattern, &actual)? {
                continue;
            }
            if let (
                ExprNode::Lit {
                    literal: Literal::Nat(left),
                },
                ExprNode::Lit {
                    literal: Literal::Nat(right),
                },
            ) = (pattern.node(), actual.node())
            {
                if left != right {
                    return Ok(Match::No);
                }
                continue;
            }
            match (
                self.simp_auto_constructor(&pattern)?,
                self.simp_auto_constructor(&actual)?,
            ) {
                (Some((left, patterns)), Some((right, values))) => {
                    if left != right {
                        return Ok(Match::No);
                    }
                    if patterns.len() != values.len() {
                        return Err(failure(SourceInferenceError::Scope));
                    }
                    work.extend(patterns.into_iter().zip(values));
                }
                _ => verdict = Match::Stuck,
            }
        }
        Ok(verdict)
    }

    fn simp_auto_discriminant(&mut self, term: &Expr) -> Result<Expr, NatDefinitionElabError> {
        if let Some(major) = crate::source::pattern_typing::offset_major(term) {
            return Ok(major);
        }
        let term =
            self.whnf_with_transparency(term, UnificationTransparency::Abbreviations, false)?;
        Ok(crate::source::pattern_typing::offset_major(&term).unwrap_or(term))
    }

    /// Constructor fields only: parameters are fixed by the admitted discriminant type.
    /// Nat literals are exposed one successor at a time, so large values cost work only when
    /// the pattern actually inspects those constructors.
    fn simp_auto_constructor(
        &mut self,
        term: &Expr,
    ) -> Result<Option<(Name, Vec<Expr>)>, NatDefinitionElabError> {
        self.tick()?;
        if let ExprNode::Lit {
            literal: Literal::Nat(value),
        } = term.node()
        {
            if value.limbs_le().is_empty() {
                return Ok(Some((Name::from_components(["Nat", "zero"]), Vec::new())));
            }
            for _ in value.limbs_le() {
                self.tick()?;
            }
            let predecessor = fln_bignum::nat::BigNatView::from_limbs_le(value.limbs_le())
                .sub(fln_bignum::nat::BigNatView::from_limbs_le(&[1]));
            return Ok(Some((
                Name::from_components(["Nat", "succ"]),
                vec![Expr::lit(Literal::Nat(
                    fln_bignum::interop::literal_from_bignat(&predecessor),
                ))],
            )));
        }
        let (head, arguments) = self.dsimp_spine(term)?;
        let ExprNode::Const { name, .. } = head.node() else {
            return Ok(None);
        };
        let Some(ConstantInfo::Ctor(ctor)) = self.txn.env.find(name) else {
            return Ok(None);
        };
        let parameters = ctor.num_params as usize;
        if ctor.is_unsafe || arguments.len() != parameters + ctor.num_fields as usize {
            return Ok(None);
        }
        Ok(Some((name.clone(), arguments[parameters..].to_vec())))
    }
}
