#!/usr/bin/env python3
"""Apply the native simp-only implementation with fail-closed source anchors."""
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]

def replace_once(text, old, new):
    if text.count(old) != 1:
        raise SystemExit(f'Expected exactly one source anchor: {old[:100]!r}')
    return text.replace(old, new, 1)

def regex_once(text, pattern, replacement):
    changed, count = re.subn(pattern, replacement, text, count=0, flags=re.S)
    if count != 1:
        raise SystemExit(f'Expected exactly one source pattern: {pattern[:100]!r}; got {count}')
    return changed

def main():
    paths = {
        'rewrite': 'crates/fln-elab/src/source/tactics/rewrite.rs',
        'matching': 'crates/fln-elab/src/source/tactics/rewrite/matching.rs',
        'tactics': 'crates/fln-elab/src/source/tactics.rs',
        'parser': 'crates/fln-parse/src/proofs.rs',
    }
    sources = {key: (ROOT / path).read_text() for key, path in paths.items()}
    module = ROOT / 'crates/fln-elab/src/source/tactics/rewrite/simplify.rs'
    tests = ROOT / 'crates/fln/tests/source_simplification.rs'
    if module.exists() or tests.exists() or 'SimplificationNoProgress' in sources['tactics']:
        raise SystemExit('Simplification implementation already exists; review current code instead of overwriting it')
    if subprocess.run(['git', 'diff', '--quiet', '--', *paths.values()], cwd=ROOT).returncode:
        raise SystemExit('Source paths have local changes')

    matching = sources['matching']
    for method in ('rewrite_trial', 'charge_rewrite_trial', 'rewrite_nonmatch'):
        matching = replace_once(matching, f'    fn {method}(', f'    pub(super) fn {method}(')
    matching = regex_once(matching,
        r'Ok\(Some\(\(Typed\s*\{\s*value,\s*type_\s*\},\s*trial\.instantiate\(term\)\?\)\)\)',
        '''let occurrence = trial.instantiate(term)?;
                if inside_out {
                    let (_, _, from, to) = equality_target(&type_)
                        .expect("instantiated equality retains its shape");
                    let replacement = if reverse { from } else { to };
                    if trial.rewrite_same(&occurrence, &replacement)? {
                        return Ok(None);
                    }
                }
                Ok(Some((Typed { value, type_ }, occurrence)))''')
    sources['matching'] = matching

    rewrite = replace_once(sources['rewrite'], 'mod matching;', 'mod matching;\nmod simplify;')
    start = rewrite.index("    pub(in crate::source) fn rewrite_proof_term<'a>(")
    end = rewrite.index('    /// Allocation-memoized replacement', start)
    function = rewrite[start:end]
    split = function.index('        let rule_type = self.whnf(&rule.type_)?;')
    prefix = function[:split]
    body = function[split:]
    body = regex_once(body,
        r'proof\.work\.push\(Work::Close\(goal, child\)\);\s*proof\.work\.push\(Work::Rewrite\(next_goal, remaining, close\)\);\s*return Ok\(\(\)\);',
        'return Ok((next_goal, child));')
    body = regex_once(body,
        r'proof\.work\.push\(Work::Close\(goal, value\)\);\s*proof\.work\.push\(Work::Rewrite\(next_goal, remaining, close\)\);\s*Ok\(\(\)\)',
        'Ok((next_goal, value))')
    body = body.replace('let pattern = &occurrence;', 'let pattern = occurrence;')
    wrapper = prefix + '''        let (next_goal, value) = self.rewrite_transport(&goal, rule, &occurrence, reverse)?;
        proof.work.push(Work::Close(goal, value));
        proof.work.push(Work::Rewrite(next_goal, remaining, close));
        Ok(())
    }

    fn rewrite_transport(
        &mut self,
        goal: &ProofGoal,
        rule: Typed,
        occurrence: &Expr,
        reverse: bool,
    ) -> Result<(ProofGoal, Expr), NatDefinitionElabError> {
        let target = self.instantiate(&goal.target)?;
''' + body
    sources['rewrite'] = rewrite[:start] + wrapper + rewrite[end:]

    tactics = replace_once(sources['tactics'], 'pub enum TacticError {',
        'pub enum TacticError {\n    SimplificationNoProgress,\n    SimplificationCycle,')
    at = tactics.index('impl std::fmt::Display for TacticError')
    position = tactics.index('        match self {', at) + len('        match self {')
    tactics = tactics[:position] + '''
            Self::SimplificationNoProgress => write!(f, "simp only made no progress"),
            Self::SimplificationCycle => write!(f, "simp only encountered a rewrite cycle"),''' + tactics[position:]
    tactics = regex_once(tactics,
        r'if kind == &parser_kind\(&\["Tactic", "rwSeq"\]\)',
        '''if kind == &parser_kind(&["Tactic", "simp"]) {
                self.simplify_proof_goal(proof, goal, args)?;
            } else if kind == &parser_kind(&["Tactic", "rwSeq"])''')
    sources['tactics'] = tactics

    parser = sources['parser']
    start = parser.index('let keyword = match &tokens[start].kind')
    array_start = parser.index('TokenKind::Ident(name) => [', start)
    array_end = parser.index(']', array_start)
    parser = parser[:array_end] + ', "simp"' + parser[array_end:]
    parser = replace_once(parser, '    match keyword {', '''    if keyword == "simp" {
        return simplify(leaves, view, tokens, range, args.remove(0));
    }
    match keyword {''')
    parser += PARSER
    sources['parser'] = parser

    for key, content in sources.items():
        (ROOT / paths[key]).write_text(content)
    module.write_text(SIMPLIFY)
    tests.write_text(TESTS)
    print('Applied native simp-only implementation and engine regressions')

PARSER = r'''

fn simplify(
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    range: Range<usize>,
    keyword: Syntax,
) -> Result<Syntax, NatDefinitionParseError> {
    let only = range.start + 1;
    if !matches!(tokens.get(only).map(|token| &token.kind),
        Some(TokenKind::Ident(name)) if name == &Name::from_components(["only"]))
    {
        return Err(refusal(view, tokens, only));
    }
    let only_leaf = leaves.leaf(only)?;
    let only = null_node(vec![Syntax::Atom {
        info: only_leaf.info(),
        val: "only".to_string(),
    }]);
    let open = range.start + 2;
    let is = |at: usize, text: &str| matches!(tokens.get(at).map(|token| &token.kind),
        Some(TokenKind::Symbol(symbol)) if symbol == text);
    let arguments = if open == range.end {
        null_node(Vec::new())
    } else {
        if range.end < open + 2 || !is(open, "[") || !is(range.end - 1, "]") {
            return Err(refusal(view, tokens, open));
        }
        let mut rows = Vec::new();
        let mut start = open + 1;
        let mut depth = 0_usize;
        for at in open + 1..range.end {
            let end = at == range.end - 1;
            if end || depth == 0 && is(at, ",") {
                if at == start {
                    if end && (start == open + 1 || !rows.is_empty()) {
                        break;
                    }
                    return Err(refusal(view, tokens, at));
                }
                let reverse = is(start, "←") || is(start, "<-");
                let direction = if reverse {
                    null_node(vec![leaves.leaf(start)?])
                } else {
                    null_node(Vec::new())
                };
                let term = bounded_term(leaves, view, tokens,
                    start + usize::from(reverse)..at, DefinitionGrammar::Scalar)?;
                rows.push(Syntax::node(parser_kind(&["Tactic", "simpLemma"]),
                    vec![null_node(Vec::new()), direction, term]));
                if !end {
                    rows.push(leaves.leaf(at)?);
                }
                start = at + 1;
            } else if is(at, "(") {
                depth += 1;
            } else if is(at, ")") {
                depth = depth.checked_sub(1).ok_or_else(|| refusal(view, tokens, at))?;
            }
        }
        if depth != 0 {
            return Err(refusal(view, tokens, range.end));
        }
        null_node(vec![leaves.leaf(open)?, null_node(rows), leaves.leaf(range.end - 1)?])
    };
    Ok(Syntax::node(parser_kind(&["Tactic", "simp"]), vec![
        keyword, null_node(Vec::new()), null_node(Vec::new()), only,
        arguments, null_node(Vec::new()),
    ]))
}
'''

SIMPLIFY = r'''//! Explicit-set, proof-producing simplification. There is no ambient simp set.
//! Rules are re-instantiated deterministically for every productive application.
//! Failed alternatives restore semantic state while retaining spent work.
use super::*;

const MAX_SIMPLIFICATION_STEPS: usize = 256;

impl Context {
    fn simp_rules<'a>(&mut self, args: &'a [Syntax]) -> Result<Vec<RewriteRule<'a>>, NatDefinitionElabError> {
        let [keyword, config, discharger, only, arguments, location] = args else {
            return Err(error(TacticError::MalformedScript));
        };
        expect_atom(keyword, "simp", "simplification keyword")?;
        expect_empty_null(config, "default simplification configuration")?;
        expect_empty_null(discharger, "default simplification discharger")?;
        expect_empty_null(location, "goal-only simplification")?;
        let [only] = expect_null_args(only, "explicit simp set")? else {
            return Err(error(TacticError::MalformedScript));
        };
        expect_atom(only, "only", "explicit-set simplification")?;
        let arguments = expect_null_args(arguments, "optional simp rule list")?;
        if arguments.is_empty() {
            return Ok(Vec::new());
        }
        let [open, rows, close] = arguments else {
            return Err(error(TacticError::MalformedScript));
        };
        expect_atom(open, "[", "simp rule opener")?;
        expect_atom(close, "]", "simp rule closer")?;
        let rows = expect_null_args(rows, "simp rules")?;
        let mut rules = Vec::new();
        for (index, row) in rows.iter().enumerate() {
            self.tick()?;
            if index % 2 == 1 {
                expect_atom(row, ",", "simp rule separator")?;
                continue;
            }
            let parts = expect_node(row, &parser_kind(&["Tactic", "simpLemma"]), 3, "simp lemma")?;
            expect_empty_null(&parts[0], "default post-order simp rule")?;
            let reverse = match expect_null_args(&parts[1], "simp direction")? {
                [] => false,
                [Syntax::Atom { val, .. }] if val == "←" || val == "<-" => true,
                _ => return Err(error(TacticError::MalformedScript)),
            };
            let mut pending = vec![&parts[2]];
            while let Some(term) = pending.pop() {
                self.tick()?;
                if let Syntax::Node { kind, args, .. } = term {
                    if kind == &parser_kind(&["Term", "byTactic"]) {
                        return Err(error(TacticError::MalformedScript));
                    }
                    pending.extend(args);
                }
            }
            rules.push(RewriteRule { syntax: &parts[2], reverse });
        }
        Ok(rules)
    }

    fn restore_simp_trial(&mut self, mut original: Self) {
        original.txn.budget.heartbeats_consumed = self.txn.budget.heartbeats_consumed;
        *self = original;
    }

    fn simp_reflexivity(&mut self, goal: &ProofGoal) -> Result<Option<Expr>, NatDefinitionElabError> {
        let target = self.whnf(&goal.target)?;
        let Some((level, alpha, left, _)) = equality_target(&target) else {
            return Ok(None);
        };
        let mut trial = self.rewrite_trial();
        let candidate = app(Expr::const_(Name::from_components(["Eq", "refl"]), vec![level]), [alpha, left]);
        let hole = trial.hole(target)?;
        let result = trial.txn.unify(&hole, &candidate, UnificationBudget::new(trial.kernel));
        self.charge_rewrite_trial(&trial);
        match result {
            Ok(report) => {
                assert!(report.awakened.is_empty(), "private source queue");
                let candidate = trial.instantiate(&candidate)?;
                *self = trial;
                Ok(Some(candidate))
            }
            Err(error) => {
                let error = failure(SourceInferenceError::Unification(Box::new(error)));
                if Self::rewrite_nonmatch(&error) { Ok(None) } else { Err(error) }
            }
        }
    }

    pub(in crate::source) fn simplify_proof_goal(
        &mut self,
        proof: &mut ProofState<'_>,
        mut goal: ProofGoal,
        args: &[Syntax],
    ) -> Result<(), NatDefinitionElabError> {
        let rules = self.simp_rules(args)?;
        let mut history = vec![self.instantiate(&goal.target)?];
        let mut steps = 0;
        loop {
            self.tick()?;
            self.txn.lctx = goal.lctx.clone();
            let target = self.instantiate(&goal.target)?;
            let mut advanced = false;
            for rule in &rules {
                self.tick()?;
                let original = self.rewrite_trial();
                let term = self.term(rule.syntax, None)?;
                let Some((term, occurrence)) = self.instantiate_rewrite_rule(term, &target, rule.reverse, true)? else {
                    self.restore_simp_trial(original);
                    continue;
                };
                if steps >= MAX_SIMPLIFICATION_STEPS {
                    return Err(failure(SourceInferenceError::ResourceLimit));
                }
                let (next_goal, value) = self.rewrite_transport(&goal, term, &occurrence, rule.reverse)?;
                let next_target = self.instantiate(&next_goal.target)?;
                for previous in &history {
                    self.tick()?;
                    if self.rewrite_same(previous, &next_target)? {
                        return Err(error(TacticError::SimplificationCycle));
                    }
                }
                history.push(next_target);
                proof.work.push(Work::Close(goal, value));
                goal = next_goal;
                steps += 1;
                advanced = true;
                break;
            }
            if advanced { continue; }
            if let Some(value) = self.simp_reflexivity(&goal)? {
                self.close_proof_goal(goal, value)?;
            } else if steps > 0 {
                proof.work.push(Work::Goal(goal));
            } else {
                return Err(error(TacticError::SimplificationNoProgress));
            }
            return Ok(());
        }
    }
}
'''

TESTS = r'''//! Native source simplification tested through the ordinary dual-checker engine.
#![forbid(unsafe_code)]
use fln::{Engine, EngineAdmissionLimits};
use fln_core::options::KVMap;
use fln_kernel::verdict::Budget;

fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}
fn engine() -> Engine {
    Engine::with_source_seed(limits()).unwrap().into_complete().unwrap()
}
fn admit(base: &Engine, source: &str) -> Engine {
    base.admit_source_declaration(source.as_bytes(), &KVMap::new(), limits())
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete().expect("the ordinary council must complete").engine
}

#[test]
fn simplification_repeats_inside_out_with_actual_transport_proofs() {
    admit(&engine(), "theorem nested (f : Nat -> Nat) (x : Nat) (h : f x = x) : f (f (f x)) = x := by simp only [h]");
}

#[test]
fn quantified_rules_are_reinstantiated_and_local_premises_discharged() {
    let base = admit(&engine(), "theorem contract (f : Nat -> Nat) (x : Nat) (h : f x = x) : f x = x := h");
    admit(&base, "theorem nested (f : Nat -> Nat) (x : Nat) (h : f x = x) : f (f x) = x := by simp only [contract f]");
}

#[test]
fn empty_explicit_sets_use_kernel_conversion_not_an_equality_guess() {
    let base = engine();
    admit(&base, "theorem reflexive (x : Nat) : x = x := by simp only");
    admit(&base, "theorem arithmetic : 2 + 3 = 5 := by simp only []");
    assert!(base.admit_source_declaration(b"theorem false_equality : 1 = 2 := by simp only []", &KVMap::new(), limits()).is_err());
}

#[test]
fn introduced_scopes_and_unsolved_transported_goals_are_preserved() {
    let base = engine();
    admit(&base, "theorem symmetry (x y : Nat) : (x = y) -> (y = x) := by intro h; simp only [h]");
    admit(&base, "theorem transport (P : Nat -> Prop) (x y : Nat) (h : x = y) (hy : P y) : P x := by simp only [h]; exact hy");
}

#[test]
fn unused_rules_do_not_leak_parameters_into_later_successful_rules() {
    admit(&engine(), "theorem select (f : Nat -> Nat) (x y : Nat) (unused : f y = y) (h : f x = x) : f (f x) = x := by simp only [unused, h]");
}

#[test]
fn reflexive_rules_are_noops_and_cycles_are_visible_refusals() {
    let base = engine();
    admit(&base, "theorem noop (x : Nat) (h : x = x) : x = x := by simp only [h]");
    let result = base.admit_source_declaration(b"theorem cycle (P : Nat -> Prop) (x y : Nat) (h : x = y) (k : y = x) : P x := by simp only [h, k]", &KVMap::new(), limits());
    let error = match result { Err(error) => error, Ok(_) => panic!("cycle must not produce a checked declaration") };
    assert!(format!("{error:?}").contains("SimplificationCycle"));
}

#[test]
fn reverse_rules_repeat_and_unsupported_simp_forms_are_not_ignored() {
    let base = engine();
    admit(&base, "theorem reverse (f : Nat -> Nat) (x : Nat) (h : x = f x) : f (f x) = x := by simp only [<- h]");
    for script in ["simp", "simp [h]", "simp only [h] at h", "simp only [*]", "simp only [,h]", "simp only [h,,h]", "simp only [<-]", "simp only [missing]"] {
        let source = format!("theorem bad (x : Nat) (h : x = x) : x = x := by {script}");
        assert!(base.admit_source_declaration(source.as_bytes(), &KVMap::new(), limits()).is_err(), "{source}");
    }
}
'''

if __name__ == '__main__':
    main()
