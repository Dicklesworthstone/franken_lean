#!/usr/bin/env python3
"""Wire native rewriting using exact anchors, preserving concurrent edits."""
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
updates = {}
def edit(path, old, new):
    text = updates.get(path, (ROOT / path).read_text())
    if text.count(old) != 1:
        raise SystemExit(f'changed or ambiguous anchor: {path}: {old[:60]}')
    updates[path] = text.replace(old, new, 1)
def main():
    path = 'crates/fln-parse/src/lib.rs'
    text = (ROOT / path).read_text()
    assert text.count('"theorem", "by",') == 2
    updates[path] = text.replace('"theorem", "by",', '"theorem", "by", "[", "]", ",", "←", "<-",')
    path = 'crates/fln-parse/src/proofs.rs'
    edit(path, '["intro", "exact", "assumption", "apply", "rfl"]', '["intro", "exact", "assumption", "apply", "rfl", "rw", "rewrite"]')
    edit(path, '    match keyword {', '    if keyword == "rw" || keyword == "rewrite" {\n        return rewrite(leaves, view, tokens, range, args.remove(0), keyword == "rw");\n    }\n    match keyword {')
    updates[path] = updates[path].replace('if symbol == "(" => depth += 1,', 'if symbol == "(" || symbol == "[" => depth += 1,').replace('if symbol == ")" => {', 'if symbol == ")" || symbol == "]" => {').replace('if symbol == ")" => depth -= 1,', 'if symbol == ")" || symbol == "]" => depth -= 1,')
    updates[path] += PARSER
    path = 'crates/fln-elab/src/source/tactics.rs'
    edit(path, 'use super::*;', 'use super::*;\nmod rewrite;')
    edit(path, '    MalformedScript,', '    MalformedScript,\n    ExpectedEquality,\n    RewriteNoMatch,')
    edit(path, '            Self::MalformedScript =>', '            Self::ExpectedEquality => write!(f, "rewrite requires an instantiated equality proof"),\n            Self::RewriteNoMatch => write!(f, "rewrite found no matching occurrence in the goal"),\n            Self::MalformedScript =>')
    edit(path, 'enum Work {', "enum Work<'a> {\n    Rewrite(ProofGoal, std::collections::VecDeque<RewriteRule<'a>>, bool),")
    edit(path, '    work: Vec<Work>,', "    work: Vec<Work<'a>>,")
    edit(path, "pub(super) enum ProofAction<'a> {", "pub(super) struct RewriteRule<'a> {\n    pub(super) syntax: &'a Syntax,\n    pub(super) reverse: bool,\n}\n\npub(super) enum ProofAction<'a> {\n    Rewrite { goal: ProofGoal, rule: RewriteRule<'a>, remaining: std::collections::VecDeque<RewriteRule<'a>>, close: bool },")
    edit(path, '            let mut goal = match work {', '            let mut goal = match work {\n                Work::Rewrite(goal, mut remaining, close) => {\n                    self.txn.lctx = goal.lctx.clone();\n                    if let Some(rule) = remaining.pop_front() {\n                        return Ok(ProofAction::Rewrite { goal, rule, remaining, close });\n                    }\n                    if close && self.rewrite_reflexivity(&goal)? { continue; }\n                    goal\n                },')
    edit(path, '            if kind == &parser_kind(&["Tactic", "intro"]) {', '            if kind == &parser_kind(&["Tactic", "rwSeq"]) || kind == &parser_kind(&["Tactic", "rewriteSeq"]) {\n                let close = kind == &parser_kind(&["Tactic", "rwSeq"]);\n                let rules = self.rewrite_rules(args, close)?;\n                proof.work.push(Work::Rewrite(goal, rules, close));\n            } else if kind == &parser_kind(&["Tactic", "intro"]) {')
    path = 'crates/fln-elab/src/source.rs'
    edit(path, "            Proof(tactics::ProofState<'a>),", "            RewriteTerm(tactics::ProofState<'a>, tactics::ProofGoal, bool, std::collections::VecDeque<tactics::RewriteRule<'a>>, bool),\n            Proof(tactics::ProofState<'a>),")
    edit(path, '                Task::Proof(mut proof) => match self.advance_proof(&mut proof)? {', '                Task::Proof(mut proof) => match self.advance_proof(&mut proof)? {\n                    tactics::ProofAction::Rewrite { goal, rule, remaining, close } => {\n                        self.txn.lctx = goal.lctx.clone();\n                        tasks.push(Task::RewriteTerm(proof, goal, rule.reverse, remaining, close));\n                        tasks.push(Task::Visit(rule.syntax, None, true));\n                    }')
    edit(path, '                Task::ProofTerm(mut proof, goal, apply) => {', '                Task::RewriteTerm(mut proof, goal, reverse, remaining, close) => {\n                    let term = values.pop().expect("rewrite rule visit");\n                    self.rewrite_proof_term(&mut proof, goal, term, reverse, remaining, close)?;\n                    tasks.push(Task::Proof(proof));\n                }\n                Task::ProofTerm(mut proof, goal, apply) => {')
    test = ROOT / 'crates/fln/tests/source_rewriting.rs'
    if test.exists():
        raise SystemExit('test target already exists; reconcile before changing it')
    for path, text in updates.items(): (ROOT / path).write_text(text)
    test.write_text(TESTS)
PARSER = '''
fn rewrite(leaves: &Leaves, view: &SourceView, tokens: &[LexedToken], range: Range<usize>, keyword: Syntax, close: bool) -> Result<Syntax, NatDefinitionParseError> {
    let is = |at: usize, text: &str| matches!(tokens.get(at).map(|t| &t.kind), Some(TokenKind::Symbol(s)) if s == text);
    if range.len() < 4 || !is(range.start + 1, "[") || !is(range.end - 1, "]") { return Err(refusal(view, tokens, range.start)); }
    let mut rows = Vec::new();
    let mut start = range.start + 2;
    let mut depth = 0_usize;
    for at in (range.start + 2)..range.end {
        let end = at == range.end - 1;
        if end || (depth == 0 && is(at, ",")) {
            if at == start { if end && !rows.is_empty() { break; } return Err(refusal(view, tokens, at)); }
            let reverse = is(start, "←") || is(start, "<-");
            let term_start = start + usize::from(reverse);
            let direction = if reverse { null_node(vec![leaves.leaf(start)?]) } else { null_node(Vec::new()) };
            let term = bounded_term(leaves, view, tokens, term_start..at, DefinitionGrammar::Scalar)?;
            rows.push(Syntax::node(parser_kind(&["Tactic", "rwRule"]), vec![direction, term]));
            if !end { rows.push(leaves.leaf(at)?); }
            start = at + 1;
        } else if is(at, "(") { depth += 1; }
        else if is(at, ")") { depth = depth.checked_sub(1).ok_or_else(|| refusal(view, tokens, at))?; }
    }
    if depth != 0 { return Err(refusal(view, tokens, range.end)); }
    let rules = Syntax::node(parser_kind(&["Tactic", "rwRuleSeq"]), vec![leaves.leaf(range.start + 1)?, null_node(rows), leaves.leaf(range.end - 1)?]);
    Ok(Syntax::node(parser_kind(&["Tactic", if close { "rwSeq" } else { "rewriteSeq" }]), vec![keyword, null_node(Vec::new()), rules, null_node(Vec::new())]))
}
'''
TESTS = r'''//! Proof-producing rewriting through the production engine council.
#![forbid(unsafe_code)]
use fln::{Engine, EngineAdmissionLimits};
use fln_core::{name::Name, options::KVMap};
use fln_kernel::verdict::Budget;
fn limits() -> EngineAdmissionLimits { EngineAdmissionLimits::new(Budget::for_stack_bytes(2*1024*1024)) }
fn engine() -> Engine { Engine::with_source_seed(limits()).unwrap().into_complete().unwrap() }
fn prove(source: &str) {
    let base=engine();
    let admitted=base.admit_source_declaration(source.as_bytes(), &KVMap::new(), limits()).unwrap_or_else(|e|panic!("{source}\n{e:?}")).into_complete().unwrap();
    assert!(admitted.engine.environment().len()>base.environment().len());
}
#[test]
fn equality_symmetry_and_congruence_have_checked_eliminator_proofs() {
    prove("theorem symm (x y : Nat) (h : x = y) : y = x := by rw [h]");
    prove("theorem cong (f : Nat -> Nat) (x y : Nat) (h : x = y) : f x = f y := by rw [h]");
    prove("theorem cong (f : Nat -> Nat) (x y : Nat) (h : x = y) : f x = f y := by rw [<- h]");
    prove("theorem cong (f : Nat -> Nat) (x y : Nat) (h : x = y) : f x = f y := by rw [← h]");
}
#[test]
fn rewriting_transports_proofs_in_both_directions() {
    prove("theorem transport (P : Nat -> Prop) (x y : Nat) (h : x = y) (hy : P y) : P x := by rw [h]; exact hy");
    prove("theorem transport (P : Nat -> Prop) (x y : Nat) (h : x = y) (hx : P x) : P y := by rw [← h]; exact hx");
}
#[test]
fn rewriting_preserves_introduced_and_dependent_local_scopes() {
    prove("theorem arrow (P : Nat -> Prop) (x y : Nat) (h : x = y) : P x -> P y := by rw [h]; intro p; exact p");
    prove("theorem transport (P : Nat -> Prop) (x y : Nat) (h : x = y) : P x -> P y := by intro hx; rw [← h]; exact hx");
    prove("theorem transport (P : Nat -> Prop) (x y : Nat) : x = y -> P x -> P y := by intro h hx; rw [← h]; exact hx");
}
#[test]
fn explicit_rewrite_leaves_its_goal_while_rw_tries_reflexivity() {
    prove("theorem symm (x y : Nat) (h : x = y) : y = x := by rewrite [h]; rfl");
    assert!(engine().admit_source_declaration(b"theorem symm (x y : Nat) (h : x = y) : y = x := by rewrite [h]",&KVMap::new(),limits()).is_err());
}
#[test]
fn rule_lists_apply_in_source_order_with_comments_and_newlines() {
    let source="theorem trans (x y z : Nat) (h : x = y) (k : y = z) : x = z := by\r\n  rw [\r\n    h, -- first rewrite\r\n    k,\r\n  ]\r\n";
    let parsed=fln_parse::parse_definition(source.as_bytes()).unwrap();
    assert_eq!(parsed.reconstruct_original(),source.as_bytes());
    prove(source);
}
#[test]
fn rewrite_arguments_use_normal_source_elaboration() {
    prove("theorem use (x y : Nat) (f : Nat -> x = y) : y = x := by rw [f 0]");
}
#[test]
fn rewrite_universes_are_not_hardcoded_to_nat_or_prop() {
    prove("theorem symm {A : Type} (x y : A) (h : x = y) : y = x := by rw [h]");
    let source=b"def transport (A B : Type) (h : A = B) (b : B) : A := by rw [h]; exact b";
    engine().admit_source_declaration(source,&KVMap::new(),limits()).unwrap().into_complete().unwrap();
}
#[test]
fn missing_matches_invalid_rules_and_unproved_transports_do_not_publish() {
    let base=engine();let options=KVMap::new();let root=base.logical_root(&options);
    for source in [
        "theorem bad (x y : Nat) (h : x = y) : 0 = 1 := by rw [h]",
        "theorem bad (n : Nat) : 0 = 0 := by rw [n]",
        "theorem bad (x y : Nat) (h : x = y) : x = 0 := by rw [h]; rfl",
        "theorem bad (x y : Nat) (h : x = y) : x = y := by rw [h] at h",
        "theorem bad (x y : Nat) (h : x = y) : x = y := by rw []",
        "theorem bad (x y : Nat) (h : x = y) : x = y := by rw [,h]",
    ] { assert!(base.admit_source_declaration(source.as_bytes(),&options,limits()).is_err(),"{source}"); }
    assert_eq!(base.logical_root(&options),root);
    assert!(!base.environment().contains(&Name::from_components(["bad"])));
}
'''
if __name__ == '__main__': main()
