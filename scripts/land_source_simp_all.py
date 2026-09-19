#!/usr/bin/env python3
"""Apply the reviewed simp_all increment; the companion job tests before push."""
from pathlib import Path
import hashlib


def replace_once(path, old, new):
    target = Path(path)
    source = target.read_text(encoding="utf-8")
    if new in source:
        return
    if source.count(old) != 1:
        raise SystemExit(f"source anchor changed: {path}")
    target.write_text(source.replace(old, new, 1), encoding="utf-8")


def publish_new(path, content):
    target = Path(path)
    if target.exists() and target.read_text(encoding="utf-8") != content:
        raise SystemExit(f"refusing to overwrite unexpected file: {path}")
    target.write_text(content, encoding="utf-8")


LOCATIONS = r'''//! Simplification of local types retains every transport and selected proof.
//! Whole-context saturation shares its productive budget with goal simplification.
use super::*;

impl Context {
    pub(super) fn simp_hypothesis_step(
        &mut self,
        local: &LocalDecl,
        rule: &SimpRule<'_>,
        rules: &[SimpRule<'_>],
    ) -> Result<Option<Typed>, NatDefinitionElabError> {
        let target = self.instantiate(&local.type_)?;
        match self.unfold_simp_rule(rule, &target)? {
            UnfoldResult::Unchanged => Ok(None),
            UnfoldResult::Changed(type_) => Ok(Some(Typed {
                value: Expr::fvar(local.id.clone()),
                type_,
            })),
            UnfoldResult::NotDefinition => {
                let mut term = self.selected_simp_term(rule)?;
                term.type_ = self.simp_premise_target(&term.type_, rules)?;
                let Some(RewriteMatch {
                    rule: term,
                    occurrence,
                    premises,
                }) = self.instantiate_rewrite_rule(term, &target, rule.reverse(), true, rules)?
                else {
                    return Ok(None);
                };
                assert!(premises.is_empty(), "simp discharges its own premises");
                self.rewrite_hypothesis_value(local, term, &occurrence, rule.reverse())
                    .map(Some)
            }
        }
    }

    /// `simp_all` selects the current propositional evidence and revisits
    /// earlier hypotheses whenever a later one changes. This is not a loop of
    /// independent `simp` calls: identities, cycle history and spent work survive
    /// every round, and the goal consumes the same productive-step budget.
    pub(in crate::source) fn simplify_all_proof_goal(
        &mut self,
        proof: &mut ProofState<'_>,
        initial: ProofGoal,
        args: &[Syntax],
    ) -> Result<(), NatDefinitionElabError> {
        let [keyword, config, discharger, only, arguments] = args else {
            return Err(error(TacticError::MalformedScript));
        };
        expect_atom(keyword, "simp_all", "whole-context simplification keyword")?;
        expect_empty_null(config, "default simplification configuration")?;
        // Reuse the ordinary set parser without reparsing source or changing
        // the persistent registry. Its location slot is an empty null node.
        let selection = [
            Syntax::Atom {
                info: keyword.info(),
                val: "simp".to_string(),
            },
            config.clone(),
            discharger.clone(),
            only.clone(),
            arguments.clone(),
            config.clone(),
        ];
        self.txn.lctx = initial.lctx.clone();
        let mut rules = self.simp_rules(&selection)?;
        let mut hypotheses = Vec::new();
        let mut selected = HashSet::new();
        for rule in &rules {
            self.tick()?;
            if let SimpRule::Local(id) = rule {
                selected.insert(id.clone());
            }
        }
        for local in initial.lctx.decls() {
            self.tick()?;
            if self.is_matrix_hypothesis(local) {
                continue;
            }
            let type_ = self.instantiate(&local.type_)?;
            let Some(sort) = self.known_type(&type_)? else {
                continue;
            };
            let sort = self.whnf(&sort)?;
            if sort.has_expr_mvar()
                || sort.has_level_mvar()
                || !self.proof_types_match(&sort, &Expr::sort(Level::zero()))?
            {
                continue;
            }
            if selected.insert(local.id.clone()) {
                rules.push(SimpRule::Local(local.id.clone()));
            }
            // Shadowed and inaccessible locals may provide evidence by ID,
            // but must never redirect a source-visible simplification location.
            if !local.user_name.is_anonymous()
                && scope::components(&local.user_name).is_ok()
                && initial
                    .lctx
                    .find_by_user_name(&local.user_name)
                    .is_some_and(|visible| visible.id == local.id)
            {
                hypotheses.push(local.user_name.clone());
            }
        }
        let locations = super::super::locations::RewriteLocations {
            hypotheses,
            target: true,
            all: true,
        };
        self.simplify_location_rules(proof, &initial, locations, rules, true)
    }

    pub(super) fn simplify_at_locations(
        &mut self,
        proof: &mut ProofState<'_>,
        initial: &ProofGoal,
        args: &[Syntax],
    ) -> Result<bool, NatDefinitionElabError> {
        let [_, _, _, _, _, location] = args else {
            return Err(error(TacticError::MalformedScript));
        };
        self.txn.lctx = initial.lctx.clone();
        let Some(locations) = self.rewrite_locations(location)? else {
            return Ok(false);
        };
        let rules = self.simp_rules(args)?;
        self.simplify_location_rules(proof, initial, locations, rules, false)?;
        Ok(true)
    }

    fn simplify_location_rules(
        &mut self,
        proof: &mut ProofState<'_>,
        initial: &ProofGoal,
        locations: super::super::locations::RewriteLocations,
        mut rules: Vec<SimpRule<'_>>,
        saturate: bool,
    ) -> Result<(), NatDefinitionElabError> {
        let mut protected = HashSet::new();
        if locations.all {
            // Preserve explicitly selected evidence for the entire traversal.
            // Automatically selected locals are remapped after each transport.
            for rule in &rules {
                self.tick()?;
                if !matches!(rule, SimpRule::Explicit(_)) {
                    continue;
                }
                let mut trial = self.rewrite_trial();
                let inspected = (|| {
                    let term = trial.selected_simp_term(rule)?;
                    trial.flush(false)?;
                    trial.wildcard_rule_dependencies(&term)
                })();
                self.txn.budget.heartbeats_consumed = trial.txn.budget.heartbeats_consumed;
                protected.extend(inspected?);
            }
        }
        let mut histories = Vec::new();
        for name in &locations.hypotheses {
            self.tick()?;
            let local = initial
                .lctx
                .find_by_user_name(name)
                .ok_or_else(|| error(TacticError::RewriteLocation))?;
            histories.push(vec![self.instantiate(&local.type_)?]);
        }
        let mut goal = initial.clone();
        let mut steps = 0;
        loop {
            let previous_steps = steps;
            for (name, history) in locations.hypotheses.iter().zip(&mut histories) {
                self.txn.lctx = goal.lctx.clone();
                let local = goal
                    .lctx
                    .find_by_user_name(name)
                    .cloned()
                    .ok_or_else(|| error(TacticError::RewriteLocation))?;
                if protected.contains(&local.id) {
                    continue;
                }
                loop {
                    self.tick()?;
                    self.txn.lctx = goal.lctx.clone();
                    let local = goal
                        .lctx
                        .find_by_user_name(name)
                        .cloned()
                        .ok_or_else(|| error(TacticError::RewriteLocation))?;
                    let mut advanced = false;
                    // Self evidence is also unavailable for premise discharge.
                    let active: Vec<_> = rules
                        .iter()
                        .filter(|rule| !matches!(rule, SimpRule::Local(id) if id == &local.id))
                        .cloned()
                        .collect();
                    for rule in &active {
                        self.tick()?;
                        let original = self.rewrite_trial();
                        let Some(replacement) = self.simp_hypothesis_step(&local, rule, &active)?
                        else {
                            self.restore_simp_trial(original);
                            continue;
                        };
                        if steps >= MAX_SIMPLIFICATION_STEPS {
                            return Err(failure(SourceInferenceError::ResourceLimit));
                        }
                        let target = self.instantiate(&replacement.type_)?;
                        for previous in history.iter() {
                            self.tick()?;
                            if self.rewrite_same(previous, &target)? {
                                return Err(error(TacticError::SimplificationCycle));
                            }
                        }
                        history.push(target);
                        let (next, parent, value) =
                            self.replace_rewritten_hypothesis(goal, &local, replacement)?;
                        let replacement_id = next
                            .lctx
                            .find_by_user_name(name)
                            .ok_or_else(|| failure(SourceInferenceError::Scope))?
                            .id
                            .clone();
                        for rule in &mut rules {
                            self.tick()?;
                            if let SimpRule::Local(id) = rule
                                && id == &local.id
                            {
                                *id = replacement_id.clone();
                            }
                        }
                        proof.work.push(Work::Close(parent, value));
                        goal = next;
                        steps += 1;
                        advanced = true;
                        break;
                    }
                    if !advanced {
                        break;
                    }
                }
            }
            if !saturate || steps == previous_steps {
                break;
            }
        }
        if locations.target {
            return self.simplify_goal_with_rules(proof, goal, &rules, steps, None);
        }
        if steps == 0 {
            return Err(error(TacticError::SimplificationNoProgress));
        }
        proof.work.push(Work::Goal(goal));
        Ok(())
    }
}
'''

TESTS = r'''//! Whole-context simplification must produce closed, kernel-checked terms.
#![forbid(unsafe_code)]

use fln_core::outcome::Outcome;
use fln_elab::{check_definition_source, seed::source_seed_declarations};
use fln_env::{
    environment::{DeclarationBudget, DeclarationCommitted, Environment},
    pmap::CollisionBudget,
};
use fln_kernel::{
    Declaration,
    capability::{Published, admit},
    council::{Council, CouncilOutcome, convene},
    verdict::{Budget, Verdict},
};

fn budget() -> Budget {
    Budget::for_stack_bytes(2 * 1024 * 1024)
}

fn environment() -> Environment {
    let mut env = Environment::new();
    for declaration in source_seed_declarations() {
        let Outcome::Complete(admitted) = admit(&env, declaration, budget()) else {
            panic!("seed nonanswer");
        };
        let CouncilOutcome::Agreed(checked) = convene(&Council::nobody_was_asked(), admitted)
        else {
            panic!("seed rejected");
        };
        env = match checked.publish(
            DeclarationBudget::default(),
            CollisionBudget::default(),
            None,
        ) {
            Outcome::Complete(Published::Committed(DeclarationCommitted::Published(result))) => {
                result.environment
            }
            Outcome::Complete(Published::BlockCommitted(result)) => result.environment,
            other => panic!("seed publication {other:?}"),
        };
    }
    env
}

fn accepted(source: &str) {
    let result = check_definition_source(source.as_bytes(), &environment(), budget())
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"));
    assert!(
        matches!(result.outcome, Outcome::Complete(Verdict::Accepted { .. })),
        "{source}\n{:?}",
        result.outcome
    );
    let Declaration::Thm(proof) = result.declaration else {
        panic!("expected an actual theorem");
    };
    assert!(!proof.value.has_expr_mvar());
    assert!(!proof.value.has_level_mvar());
    assert!(!proof.value.has_fvar());
}

fn refused(source: &str) {
    if let Ok(result) = check_definition_source(source.as_bytes(), &environment(), budget()) {
        assert!(
            !matches!(result.outcome, Outcome::Complete(Verdict::Accepted { .. })),
            "unexpected theorem: {source}"
        );
    }
}

#[test]
fn simp_all_selects_local_proofs_with_and_without_defaults() {
    for tactic in ["simp_all", "simp_all only", "simp_all only []", "simp_all only [*, *]"] {
        accepted(&format!("theorem t (P : Prop) (h : P) : P := by {tactic}"));
    }
    accepted("theorem t : 2 + 3 = 5 := by simp_all only");
}

#[test]
fn simp_all_revisits_earlier_hypotheses_after_later_equalities_change() {
    accepted(
        "theorem t (P : Nat -> Prop) (f : Nat -> Nat) (x y z : Nat) (hp : P (f y)) (he : f x = z) (hxy : x = y) : P z := by simp_all only",
    );
}

#[test]
fn simp_all_reaches_the_same_result_with_reordered_hypotheses() {
    accepted(
        "theorem t (P : Nat -> Prop) (f : Nat -> Nat) (x y z : Nat) (hxy : x = y) (he : f x = z) (hp : P (f y)) : P z := by simp_all only",
    );
}

#[test]
fn simp_all_preserves_explicit_evidence_and_uses_checked_transports() {
    accepted(
        "theorem t (P : Nat -> Prop) (x y : Nat) (h : x = y) (hx : P x) : P y := by simp_all only [h]",
    );
    accepted(
        "theorem t.{u} (A : Sort u) (P : A -> Prop) (x y : A) (h : x = y) (hx : P x) : P y := by simp_all only",
    );
}

#[test]
fn simp_all_handles_local_proof_bindings_and_introduced_contexts() {
    accepted("theorem t (P : Prop) : P -> P := by intro h; simp_all only");
    accepted(
        "theorem t (P : Prop) (h : P) : P := by have hp : P := h; simp_all only",
    );
}

#[test]
fn failed_simp_all_alternative_restores_context_and_pending_transports() {
    accepted(
        "theorem t (P : Nat -> Prop) (Q : Prop) (x y : Nat) (h : x = y) (hx : P x) (hq : Q) : Q := by\n try (simp_all only [h]; fail)\n rewrite [h] at hx\n exact hq",
    );
}

#[test]
fn simp_all_does_not_assume_a_missing_conditional_premise() {
    refused(
        "theorem t (P : Nat -> Prop) (Q : Prop) (x y : Nat) (h : Q -> x = y) (hx : P x) : P y := by simp_all only",
    );
}

#[test]
fn simp_all_does_not_accept_false_or_unfinished_proofs() {
    for source in [
        "theorem t : 1 = 2 := by simp_all only",
        "theorem t (P Q : Prop) (h : P) : Q := by simp_all only",
        "theorem t : 0 = 0 := by simp_all only [missing]",
        "theorem t (x y : Nat) (h : x = y) (k : y = x) : x = x := by simp_all only [h, k]",
    ] {
        refused(source);
    }
}
'''

PARSER_TESTS = r'''

#[cfg(test)]
mod simp_all_tests {
    use super::*;

    #[test]
    fn simp_all_has_its_own_lossless_syntax_and_is_contextual() {
        for tactic in ["simp_all", "simp_all only", "simp_all only [h, <- k,]", "simp_all [*, -N.rule]"] {
            let source = format!("theorem t : True := by\r\n  /- 🦀 -/ {tactic}\r\n");
            let parsed = parse_source_command(source.as_bytes()).unwrap();
            assert_eq!(parsed.reconstruct_original(), source.as_bytes());
            assert_eq!(parsed.reconstruct_normalized().unwrap(), source.replace("\r\n", "\n").as_bytes());
            let mut pending = vec![parsed.syntax()];
            let mut count = 0;
            while let Some(syntax) = pending.pop() {
                if let Syntax::Node { kind, args, .. } = syntax {
                    if kind == &parser_kind(&["Tactic", "simpAll"]) {
                        assert_eq!(args.len(), 5);
                        assert!(matches!(&args[0], Syntax::Atom { val, .. } if val == "simp_all"));
                        count += 1;
                    }
                    pending.extend(args);
                }
            }
            assert_eq!(count, 1);
        }
        assert!(parse_definition(b"def simp_all (n : Nat) := n").is_ok());
    }

    #[test]
    fn unsupported_simp_all_arguments_do_not_disappear() {
        for tactic in ["simp_all at *", "simp_all only at h", "simp_all [] using h", "simp_all only [by rfl]", "simp_all [h,,k]"] {
            let source = format!("theorem t : True := by {tactic}");
            assert!(parse_source_command(source.as_bytes()).is_err(), "{source}");
        }
    }
}
'''

WRAPPER = r'''
/// Whole-context simplification shares rule syntax with simp, but has no
/// location suffix. Retain the original keyword and all source attachments.
#[inline(never)]
fn simplify_all(
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    range: Range<usize>,
    keyword: Syntax,
) -> Result<Syntax, NatDefinitionParseError> {
    let end = range.end;
    let mut parsed = simplify(leaves, view, tokens, range, keyword)?;
    let Syntax::Node { kind, args, .. } = &mut parsed else {
        unreachable!("simplify builds a tactic node");
    };
    if !matches!(&args[5], Syntax::Node { args, .. } if args.is_empty()) {
        return Err(refusal(view, tokens, end));
    }
    *kind = parser_kind(&["Tactic", "simpAll"]);
    args.pop();
    Ok(parsed)
}

'''

EXAMPLE = '''-- Native fixed-point context simplification; no imports or runtime execution.
theorem localEvidence (P : Prop) (h : P) : P := by simp_all

theorem transported (P : Nat -> Prop) (x y : Nat) (h : x = y) (hx : P x) : P y := by
  simp_all only

theorem fixedPoint (P : Nat -> Prop) (f : Nat -> Nat) (x y z : Nat)
    (hp : P (f y)) (he : f x = z) (hxy : x = y) : P z := by
  simp_all only

theorem introduced (P : Prop) : P -> P := by
  intro h
  simp_all only

theorem computed : 2 + 3 = 5 := by simp_all only
'''

DOCUMENTATION = '''# Native whole-context simplification

`simp_all`, `simp_all [rules]`, and `simp_all only [rules]` select the current
propositional hypotheses and simplify their types repeatedly until no hypothesis
changes. Unlike a single `simp [*] at *` traversal, a later transformed equality
can simplify an earlier hypothesis on the next pass. The final goal uses the
same selected evidence and the same productive-step budget.

```lean
theorem fixedPoint (P : Nat -> Prop) (f : Nat -> Nat) (x y z : Nat)
    (hp : P (f y)) (he : f x = z) (hxy : x = y) : P z := by
  simp_all only
```

Each transformation constructs the existing checked transport and introduces a
fresh local identity. Dependent uses retain the original well-typed identity;
local types are never retagged in place. A hypothesis cannot serve as its own
rewrite evidence or discharge its own conditional premise. Explicitly selected
proofs and their dependency telescopes are preserved while automatic selections
follow replacement identities. Backtracking restores semantic state and pending
closures without refunding consumed work.

Ordinary `simp_all` reads the immutable registered simp set; `only` does not.
Explicit selections, global exclusions, priorities, and selected unfolding use
the existing simp rule machinery. Rule ordering is deterministic. All rounds
share the 256 productive-step limit, source heartbeat budget, and per-location
cycle histories. A cycle is a typed tactic failure; resource and internal
nonanswers do not become successful tactic alternatives.

Run the real source-checking path, including both declaration checkers:

```bash
cargo run --locked -p fln-cli --bin fln -- check-source --json examples/native_simp_all.lean
```

This is a bounded native tactic, not complete upstream `simp_all` parity.
Only source-visible propositional hypotheses are simplification locations;
shadowed proof hypotheses remain selectable evidence by identity. Data-valued
local types are not rewritten by this tactic. Custom configurations, dischargers,
locations, local-rule erasure, automatic rule orientation, and general
binder-opening congruence remain unsupported. Productive simplification can
leave a genuine goal for subsequent tactics; it never admits an unfinished proof.
'''

replace_once("crates/fln-parse/src/proofs.rs", '            "simp",\n            "simpa",', '            "simp",\n            "simp_all",\n            "simpa",')
replace_once("crates/fln-parse/src/proofs.rs", '        "simp" => simplify(leaves, view, tokens, range, atom),', '        "simp" => simplify(leaves, view, tokens, range, atom),\n        "simp_all" => simplify_all(leaves, view, tokens, range, atom),')
replace_once("crates/fln-parse/src/proofs.rs", '/// Separate a top-level evidence clause without splitting identifiers inside', WRAPPER + '/// Separate a top-level evidence clause without splitting identifiers inside')
parser = Path("crates/fln-parse/src/proofs.rs")
source = parser.read_text(encoding="utf-8")
if "mod simp_all_tests" not in source:
    parser.write_text(source + PARSER_TESTS, encoding="utf-8")
replace_once("crates/fln-elab/src/source/tactics.rs", '            } else if kind == &parser_kind(&["Tactic", "simp"]) {\n                self.simplify_proof_goal(proof, goal, args)?;', '            } else if kind == &parser_kind(&["Tactic", "simpAll"]) {\n                self.simplify_all_proof_goal(proof, goal, args)?;\n            } else if kind == &parser_kind(&["Tactic", "simp"]) {\n                self.simplify_proof_goal(proof, goal, args)?;')
location = Path("crates/fln-elab/src/source/tactics/rewrite/simplify/locations.rs")
old = location.read_bytes()
identity = hashlib.sha1(b"blob " + str(len(old)).encode() + b"\0" + old).hexdigest()
if identity != "8f785fef895c8714b558c2ef0505a0fcdd61651b" and old != LOCATIONS.encode():
    raise SystemExit("hypothesis simplification changed; reconcile before applying")
location.write_text(LOCATIONS, encoding="utf-8")
publish_new("crates/fln-elab/tests/source_simp_all.rs", TESTS)
publish_new("examples/native_simp_all.lean", EXAMPLE)
publish_new("docs/NATIVE_SIMP_ALL.md", DOCUMENTATION)
