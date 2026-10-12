"""Extend empty-matrix leaves with selected-evidence contradiction proofs."""
from pathlib import Path
import shutil
import sys

PAYLOAD = Path(__file__).resolve().parent


def replace(text, old, new, count=1):
    actual = text.count(old)
    if actual != count:
        raise RuntimeError(f'expected {count} anchors, found {actual}: {old[:140]!r}')
    return text.replace(old, new)


def tests():
    test = Path('crates/fln/tests/source_empty_contradictions.rs')
    fixture = Path('crates/fln/tests/fixtures/empty_contradictions.tsv')
    if test.exists() or fixture.exists():
        raise RuntimeError('new test destinations already exist')
    text = Path('crates/fln/tests/source_empty_matrices.rs').read_text()
    text = replace(text, 'assert_eq!(counts, [18, 10]);', 'assert_eq!(counts, [16, 10]);')
    text = text.replace('empty_matrices', 'empty_contradictions').replace('EMPTY_MATRIX', 'EMPTY_CONTRADICTION')
    test.write_text(text)
    shutil.copyfile(PAYLOAD / 'cases.tsv', fixture)


def implementation():
    path = Path('crates/fln-elab/src/source/tactics/constructors.rs')
    text = path.read_text()
    anchor = '''            .collect();
        // The pin's `contradictionCore`'''
    text = replace(text, anchor, '''            .collect();
        self.contradict_evidence_goal(goal, original)
    }

    /// Contradiction from an explicit set of checked evidence. Empty matches
    /// pass only their discriminants and exposed constructor fields: the pin's
    /// matcher closure does not capture unrelated ambient hypotheses.
    pub(super) fn contradict_evidence_goal(
        &mut self,
        goal: ProofGoal,
        original: Vec<Typed>,
    ) -> Result<(), NatDefinitionElabError> {
        self.txn.lctx = goal.lctx.clone();
        self.resolve_instances(false)?;
        self.flush(false)?;
        // The pin's `contradictionCore`''')
    path.write_text(text)

    path = Path('crates/fln-elab/src/source/tactics/empty.rs')
    text = path.read_text()
    text = replace(text, 'Split(ProofGoal, VecDeque<Name>),', 'Split(ProofGoal, VecDeque<Name>, Vec<Name>),')
    text = replace(text, 'EmptyTask::Split(child, columns.iter().cloned().collect()),',
                   'EmptyTask::Split(child, columns.iter().cloned().collect(), columns.to_vec()),')
    text = replace(text, 'let (goal, mut remaining) = match task {',
                   'let (goal, mut remaining, evidence) = match task {')
    text = replace(text, 'EmptyTask::Split(goal, remaining) => (goal, remaining),',
                   'EmptyTask::Split(goal, remaining, evidence) => (goal, remaining, evidence),')
    text = replace(text, '''            let Some(column) = remaining.pop_front() else {
                return Err(error(TacticError::EliminationCoverage));
            };''', '''            let Some(column) = remaining.pop_front() else {
                let mut selected = Vec::new();
                for name in evidence {
                    self.tick()?;
                    if let Some(local) = goal.lctx.find_by_user_name(&name) {
                        selected.push(Typed {
                            value: Expr::fvar(local.id.clone()),
                            type_: local.type_.clone(),
                        });
                    }
                }
                match self.contradict_evidence_goal(goal, selected) {
                    Ok(()) => continue,
                    Err(NatDefinitionElabError::Inference(SourceInferenceError::Tactic(
                        TacticError::NoContradiction,
                    ))) => return Err(error(TacticError::EliminationCoverage)),
                    Err(error) => return Err(error),
                }
            };''')
    text = replace(text, 'pending.push(EmptyTask::Split(goal, remaining));',
                   'pending.push(EmptyTask::Split(goal, remaining, evidence));')
    text = replace(text, '''                    original.expect("recursive case snapshot"),
                    remaining,
''', '''                    original.expect("recursive case snapshot"),
                    remaining,
                    evidence,
''')
    text = replace(text, '''                        let mut columns = remaining.clone();
''', '''                        let mut columns = remaining.clone();
                        let mut evidence = evidence.clone();
''')
    text = replace(text, '''                                columns.push_front(name.clone());
''', '''                                columns.push_front(name.clone());
                                evidence.push(name.clone());
''')
    text = replace(text, 'EmptyTask::Split(child, columns)', 'EmptyTask::Split(child, columns, evidence)')
    text = text.replace('//! computationally irrelevant. No ambient assumption search supplies a result.',
                        '//! computationally irrelevant. Leaves use only selected evidence, never an\n//! unrelated ambient hypothesis, to construct a checked contradiction proof.')
    path.write_text(text)


if __name__ == '__main__':
    {'tests': tests, 'implementation': implementation}[sys.argv[1]]()
