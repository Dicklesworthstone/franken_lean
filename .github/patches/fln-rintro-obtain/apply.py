from pathlib import Path
import sys

PAYLOAD = Path(__file__).resolve().parent

def replace(text, old, new):
    if text.count(old) != 1:
        raise RuntimeError(f'changed source anchor: {old[:140]!r} ({text.count(old)})')
    return text.replace(old, new)

def tests():
    destination = Path('crates/fln/tests/source_rintro_obtain.rs')
    fixture = Path('crates/fln/tests/fixtures/rintro_obtain.tsv')
    if destination.exists() or fixture.exists():
        raise RuntimeError('rintro/obtain test destinations already exist')
    text = Path('crates/fln/tests/source_rcases.rs').read_text()
    text = replace(text, 'assert_eq!(counts, [16, 11]);', 'assert_eq!(counts, [36, 25]);')
    text = replace(text, 'const FIXTURES: &str = include_str!("fixtures/rcases.tsv");',
        'const FIXTURES: &str = concat!(include_str!("fixtures/rcases.tsv"), "\\n", include_str!("fixtures/rintro_obtain.tsv"));')
    text = text.replace('rcases_and_functions_pass_both_checkers', 'recursive_introductions_and_obtained_witnesses_pass_both_checkers')
    text = text.replace('actual_imported_core_checks_the_same_rcases', 'actual_imported_rcases_checks_introductions_and_obtained_witnesses')
    text = text.replace('RCASES', 'RINTRO_OBTAIN')
    text = replace(text, '    verify(&engine, STACK);', '''    // The bounded seed intentionally has no Exists. Admit its ordinary
    // polymorphic declaration for these source fixtures; imported testing
    // below still uses the actual Reference declaration and full metadata.
    assert!(!engine.environment().contains(&fln::Name::from_components(["Exists"])));
    let initialized = engine.check_source_files(
        &[b"inductive Exists.{u} {A : Sort u} (P : A -> Prop) : Prop where | intro (w : A) (h : P w)"],
        &KVMap::new(),
        SourceCheckLimits::new(EngineAdmissionLimits::new(Budget::for_stack_bytes(STACK))),
    ).expect("source existential fixture admitted by both checkers")
        .into_complete().expect("source existential fixture completes");
    verify(&initialized.engine, STACK);''')
    destination.write_text(text)
    cases = (PAYLOAD / 'cases.tsv').read_text()
    # Run 38306613816 shows h/this with inaccessible dagger names, while
    # destructured hp/hq are accessible. Preserve both exact rejected sources.
    cases = replace(cases, 'obtain_typed_hole\taccept\t', 'obtain_typed_hole\treject\t')
    cases = replace(cases, 'obtain_default_this\taccept\t', 'obtain_default_this\treject\t')
    cases += 'obtain_opaque_witness\taccept\ttheorem f : True := by obtain h : True; exact True.intro; assumption\n'
    cases += 'obtain_opaque_default_witness\taccept\ttheorem f : True := by obtain : True; exact True.intro; assumption\n'
    fixture.write_text(cases)

def implementation():
    destination = Path('crates/fln-elab/src/source/tactics/rcases/derived.rs')
    if destination.exists():
        raise RuntimeError('rintro/obtain implementation already exists')
    destination.parent.mkdir(exist_ok=True)
    text = (PAYLOAD / 'derived.rs').read_text()
    text = replace(text,
        '                self.run_rcases_patterns(proof, goal, arena, vec![Subject { name, pattern, rename: true }])?;',
        '''                // The pin's assert/intro1 leaves the whole witness inaccessible.
                // Named tuple/alternative fields become visible only after cases.
                self.run_rcases_patterns(proof, goal, arena, vec![Subject { name, pattern, rename: false }])?;''')
    destination.write_text(text)
    path = Path('crates/fln-elab/src/source/tactics/rcases.rs')
    text = path.read_text()
    text = replace(text, 'use std::collections::HashMap;\n', 'use std::collections::HashMap;\nmod derived;\n')
    text = replace(text, "        args: &'a [Syntax],", '        args: &[Syntax],')
    text = replace(text, "        mut arena: Vec<Pattern<'a>>,", "        mut arena: Vec<Pattern<'_>>,")
    path.write_text(text)
    path = Path('crates/fln-elab/src/source/tactics.rs')
    text = path.read_text()
    anchor = '            } else if kind == &parser_kind(&["Tactic", "rcases"]) {'
    text = replace(text, anchor, '''            } else if kind == &parser_kind(&["Tactic", "rintro"]) {
                self.rintro_proof_goal(proof, goal, args)?;
            } else if kind == &parser_kind(&["Tactic", "obtain"]) {
                self.obtain_proof_goal(proof, goal, args)?;
''' + anchor)
    path.write_text(text)

{'tests': tests, 'implementation': implementation}[sys.argv[1]]()
