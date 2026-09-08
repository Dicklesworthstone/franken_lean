#!/usr/bin/env python3
"""Apply the source equality increment; refuse changed anchors before any write."""
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
updates = {}
def edit(path, old, new):
    text = updates.get(path, (ROOT / path).read_text())
    if text.count(old) != 1:
        raise SystemExit(f'changed or ambiguous implementation anchor: {path}: {old[:70]}')
    updates[path] = text.replace(old, new, 1)

def main():
    edit('crates/fln-elab/src/seed.rs', 'use fln_core::expr::{BinderInfo, Expr};', 'pub mod equality;\npub use equality::{eq_seed_declaration, rfl_seed_declaration};\n\nuse fln_core::expr::{BinderInfo, Expr};')
    edit('crates/fln-elab/src/seed.rs', 'source_seed_declarations() -> [Declaration; 25]', 'source_seed_declarations() -> [Declaration; 27]')
    edit('crates/fln-elab/src/seed.rs', '        string_dec_eq_seed_declaration(),\n    ]', '        string_dec_eq_seed_declaration(),\n        eq_seed_declaration(),\n        rfl_seed_declaration(),\n    ]')
    edit('crates/fln-elab/src/seed.rs', '        assert_eq!(declarations[24], string_dec_eq_seed_declaration());', '        assert_eq!(declarations[24], string_dec_eq_seed_declaration());\n        assert_eq!(declarations[25], eq_seed_declaration());\n        assert_eq!(declarations[26], rfl_seed_declaration());')
    edit('crates/fln-elab/src/seed/equality.rs', '#[cfg(test)]', RFL_SEED + '\n#[cfg(test)]')
    edit('crates/fln-parse/src/lib.rs', 'enum BoundedInfix {\n    Arrow,', 'enum BoundedInfix {\n    Arrow,\n    Equality,')
    edit('crates/fln-parse/src/lib.rs', '            Self::Arrow => "->",', '            Self::Arrow => "->",\n            Self::Equality => "=",')
    edit('crates/fln-parse/src/lib.rs', '            Self::ScalarBeq => 50,', '            Self::ScalarBeq | Self::Equality => 50,')
    edit('crates/fln-parse/src/lib.rs', 'matches!(self, Self::ScalarBeq)', 'matches!(self, Self::ScalarBeq | Self::Equality)')
    path = 'crates/fln-parse/src/lib.rs'
    assert updates[path].count('\":=\", \";\", \"==\"') == 2
    updates[path] = updates[path].replace('\":=\", \";\", \"==\"', '\":=\", \";\", \"=\", \"==\"')
    edit(path, '        "==" if grammar == DefinitionGrammar::Scalar => Some(BoundedInfix::ScalarBeq),', '        "==" if grammar == DefinitionGrammar::Scalar => Some(BoundedInfix::ScalarBeq),\n        "=" if grammar == DefinitionGrammar::Scalar => Some(BoundedInfix::Equality),')
    edit('crates/fln-elab/src/lib.rs', 'fn bounded_infix_intrinsic(kind: &Name, allow_string: bool) -> Option<BoundedInfixIntrinsic> {', 'fn bounded_infix_intrinsic(kind: &Name, allow_string: bool) -> Option<BoundedInfixIntrinsic> {\n    if allow_string && kind == &Name::str(Name::anonymous(), "term_=_") {\n        return Some(BoundedInfixIntrinsic::Fixed { spelling: "=", intrinsic: Name::from_components(["Eq"]) });\n    }')
    edit('crates/fln-parse/src/proofs.rs', '["intro", "exact", "assumption", "apply"]', '["intro", "exact", "assumption", "apply", "rfl"]')
    edit('crates/fln-parse/src/proofs.rs', '        "assumption" if range.end == start + 1 => {}', '        "assumption" | "rfl" if range.end == start + 1 => {}')
    edit('crates/fln-elab/src/source/tactics.rs', '            } else if kind == &parser_kind(&["Tactic", "assumption"]) {', RFL_TACTIC + '            } else if kind == &parser_kind(&["Tactic", "assumption"]) {')
    updates['crates/fln-elab/src/source/tactics.rs'] += EQ_TARGET
    edit('crates/fln/src/lib.rs', 'assert_eq!(engine.environment().len(), 28);', 'assert_eq!(engine.environment().len(), 32);')
    edit('crates/fln/src/lib.rs', 'assert_eq!(completed.engine.environment().len(), 30);', 'assert_eq!(completed.engine.environment().len(), engine.environment().len() + 2);')
    anchor = '    /// Parse, elaborate, admit, publish, compile, canonically encode/decode,\n    /// and execute one bounded Nat-valued definition command.'
    edit('crates/fln/src/lib.rs', anchor, ADMISSION + anchor)
    for path, text in updates.items():
        (ROOT / path).write_text(text)

RFL_SEED = '''/// The ordinary polymorphic `rfl` term, with both arguments inferred.
pub fn rfl_seed_declaration() -> Declaration {
    let name = Name::from_components(["rfl"]);
    let u_name = Name::from_components(["u"]);
    let u = Level::param(u_name.clone());
    let a = Name::from_components(["a"]);
    let alpha = Name::from_components(["α"]);
    let bv = |i| Expr::bvar(i).expect("fixed reflexivity telescope index");
    let relation = Expr::app(Expr::app(Expr::app(
        Expr::const_(Name::from_components(["Eq"]), vec![u.clone()]), bv(1)), bv(0)), bv(0));
    let type_ = Expr::forall_e(alpha.clone(), Expr::sort(u.clone()),
        Expr::forall_e(a.clone(), bv(0), relation, BinderInfo::Implicit), BinderInfo::Implicit);
    let value = Expr::lam(alpha, Expr::sort(u.clone()),
        Expr::lam(a, bv(0), Expr::app(Expr::app(
            Expr::const_(Name::from_components(["Eq", "refl"]), vec![u]), bv(1)), bv(0)),
            BinderInfo::Implicit), BinderInfo::Implicit);
    Declaration::Defn(fln_env::constants::DefinitionVal {
        base: ConstantVal { name: name.clone(), level_params: vec![u_name], type_ },
        value, hints: fln_env::constants::ReducibilityHints::Abbrev,
        safety: fln_env::constants::DefinitionSafety::Safe, all: vec![name],
    })
}
'''
RFL_TACTIC = '''            } else if kind == &parser_kind(&["Tactic", "rfl"]) {
                let [keyword] = args.as_slice() else { return Err(error(TacticError::MalformedScript)); };
                expect_atom(keyword, "rfl", "reflexivity tactic")?;
                let target = self.whnf(&goal.target)?;
                let (level, alpha, left, right) = equality_target(&target).ok_or_else(|| error(TacticError::ApplyMismatch))?;
                self.constrain(&left, &right)?;
                let value = Expr::app(Expr::app(Expr::const_(Name::from_components(["Eq", "refl"]), vec![level]), alpha), left);
                self.close_proof_goal(goal, value)?;
'''
EQ_TARGET = '''
/// Decode only the ordinary homogeneous equality head; no lookalike names or
/// Boolean comparisons count as equality propositions.
fn equality_target(target: &Expr) -> Option<(Level, Expr, Expr, Expr)> {
    let ExprNode::App { f, a: right } = target.node() else { return None; };
    let ExprNode::App { f, a: left } = f.node() else { return None; };
    let ExprNode::App { f, a: alpha } = f.node() else { return None; };
    let ExprNode::Const { name, levels } = f.node() else { return None; };
    if name != &Name::from_components(["Eq"]) { return None; }
    let [level] = levels.as_slice() else { return None; };
    Some((level.clone(), alpha.clone(), left.clone(), right.clone()))
}
'''
ADMISSION = '''    /// Parse, elaborate and dual-check one source definition or theorem without
    /// attempting to compile or execute a proof. Publication remains the same
    /// immutable K1-plus-independent-checker transition as `admit_declaration`.
    pub fn admit_source_declaration(
        &self,
        source: &[u8],
        options: &KVMap,
        limits: EngineAdmissionLimits,
    ) -> Result<Outcome<DeclarationAdmission>, EngineExecutionError> {
        let parsed = fln_parse::parse_definition(source)
            .map_err(DefinitionFrontendError::Parse)
            .map_err(EngineExecutionError::Frontend)?;
        let declaration = fln_elab::elaborate_definition_in_with_budget(
            parsed.syntax(), self.environment(), limits.kernel,
        ).map_err(DefinitionFrontendError::Elaborate)
            .map_err(EngineExecutionError::Frontend)?;
        self.admit_declaration(declaration, options, limits)
            .map_err(EngineExecutionError::from)
    }

'''
if __name__ == '__main__': main()
