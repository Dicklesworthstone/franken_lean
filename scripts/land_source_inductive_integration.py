#!/usr/bin/env python3
"""Connect the native constructor-family modules at guarded integration points."""
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
CHANGED = []


def lex(text):
    pattern = re.compile(r'//[^\n]*|/\*.*?\*/|r(#+)".*?"\1|r"[^"]*"|"(?:\\.|[^"\\])*"|\'(?:\\.|[^\'\\])\'|[A-Za-z_][A-Za-z_0-9]*|::|[^\s]', re.S)
    return [(m.group(), m.start(), m.end()) for m in pattern.finditer(text)
            if not m.group().startswith(('//', '/*'))]


def function(text, name):
    tokens = lex(text)
    for i, (value, _, _) in enumerate(tokens[:-1]):
        if value == 'fn' and tokens[i + 1][0] == name:
            opening = next(j for j in range(i + 2, len(tokens)) if tokens[j][0] == '{')
            depth = 1
            for j in range(opening + 1, len(tokens)):
                depth += (tokens[j][0] == '{') - (tokens[j][0] == '}')
                if depth == 0:
                    return tokens[opening][2], tokens[j][1]
    raise RuntimeError('Missing function: ' + name)


def edit(path, operation):
    file = ROOT / path
    before = file.read_text()
    after = operation(before)
    if after != before:
        file.write_text(after)
        CHANGED.append(path)


def once(text, old, new):
    if new in text:
        return text
    if text.count(old) != 1:
        raise RuntimeError('Integration anchor is not unique: ' + old[:90])
    return text.replace(old, new, 1)


def parser(text):
    if 'mod inductive;' not in text:
        text = once(text, 'mod records;', 'mod records;\nmod inductive;')
    if '    InductiveConstructor,' not in text:
        text = once(text, 'pub enum NatDefinitionExpectation {', 'pub enum NatDefinitionExpectation {\n    InductiveConstructor,')
    for name in ('nat_definition_token_table', 'source_module_token_table'):
        start, end = function(text, name)
        body = text[start:end]
        additions = [value for value in ('"inductive"', '"|"') if value not in body]
        if additions:
            if '"structure",' not in body:
                raise RuntimeError('Missing structure token in ' + name)
            body = body.replace('"structure",', '"structure", ' + ', '.join(additions) + ',', 1)
            text = text[:start] + body + text[end:]
    start, end = function(text, 'parse_definition_with_grammar')
    body = text[start:end]
    if 'inductive::parse' not in body:
        target = body.find('records::parse')
        if target < 0:
            raise RuntimeError('Missing record dispatch')
        depth = 0
        anchor = None
        for value, pos, _ in lex(body[:target]):
            if value == 'if' and depth == 0:
                anchor = pos
            depth += (value in ('{', '(', '[')) - (value in ('}', ')', ']'))
        if anchor is None:
            raise RuntimeError('Record dispatch is not a top-level conditional')
        line = body.rfind('\n', 0, anchor) + 1
        insertion = '''    if grammar == DefinitionGrammar::Scalar
        && matches!(tokens.first().map(|token| &token.kind),
            Some(TokenKind::Symbol(symbol)) if symbol == "inductive")
    {
        return inductive::parse(view, tokens);
    }
'''
        body = body[:line] + insertion + body[line:]
        text = text[:start] + body + text[end:]
    text = re.sub(r'"structure"\s*\|\s*"class"(?!\s*\|\s*"inductive")',
                  '"structure" | "class" | "inductive"', text)
    return text


def records(text):
    for name in ('modifiers', 'optional_type'):
        text = re.sub(r'(?m)^fn ' + name + r'\(', 'pub(super) fn ' + name + '(', text)
    return text


def elaborator(text):
    if 'mod inductive;' not in text:
        text = once(text, 'mod infer;', 'mod infer;\nmod inductive;')
    if 'Inductive(crate::inductive::InductiveError)' not in text:
        text = once(text, 'pub enum SourceInferenceError {',
                    'pub enum SourceInferenceError {\n    Inductive(crate::inductive::InductiveError),')
    if 'Self::Inductive(error)' not in text:
        begin = text.index('impl std::fmt::Display for SourceInferenceError')
        pos = text.index('match self {', begin) + len('match self {')
        text = text[:pos] + '\n            Self::Inductive(error) => write!(f, "{error}"),' + text[pos:]
    if 'pub use inductive::' not in text:
        text += '\npub use inductive::{elaborate_inductive, is_inductive};\n'
    return text


def invocation(text, name):
    match = re.search(r'((?:[A-Za-z_][A-Za-z_0-9]*::)*)' + name + r'\s*\(', text)
    if match is None:
        raise RuntimeError('Missing call: ' + name)
    opening = match.end() - 1
    depth = 1
    for value, start, end in lex(text[opening + 1:]):
        depth += (value == '(') - (value == ')')
        if depth == 0:
            return match.group(1), text[opening + 1:opening + 1 + start], match.start()
    raise RuntimeError('Unclosed call: ' + name)


def engine(text):
    if 'is_inductive(' in text:
        return text
    predicate_prefix, syntax, call = invocation(text, 'is_record')
    builder_prefix, arguments, _ = invocation(text, 'elaborate_record')
    line = text.rfind('\n', 0, call) + 1
    if not text[line:call].strip().startswith('if !'):
        raise RuntimeError('Record predicate is not the expected command fallback')
    predicate_prefix = predicate_prefix or 'fln_elab::source::'
    builder_prefix = builder_prefix or 'fln_elab::source::'
    insertion = f'''        if {predicate_prefix}is_inductive({syntax}) {{
            let candidate = {builder_prefix}elaborate_inductive({arguments})
                .map_err(DefinitionFrontendError::Elaborate)
                .map_err(EngineExecutionError::Frontend)?;
            return self.admit_declarations(&[candidate], options, limits)
                .map_err(EngineExecutionError::from);
        }}
'''
    return text[:line] + insertion + text[line:]


def main():
    for path in ('crates/fln-parse/src/inductive.rs', 'crates/fln-elab/src/source/inductive.rs',
                 'crates/fln/tests/source_inductive.rs'):
        if not (ROOT / path).is_file():
            raise RuntimeError('Missing already committed implementation: ' + path)
    edit('crates/fln-parse/src/lib.rs', parser)
    edit('crates/fln-parse/src/records.rs', records)
    edit('crates/fln-elab/src/source.rs', elaborator)
    edit('crates/fln/src/source_records.rs', engine)
    edit('crates/fln/src/source_check.rs', lambda text: once(
        text,
        '            | SourceInferenceError::Record(fln_elab::records::RecordError::ResourceLimit)',
        '            | SourceInferenceError::Record(fln_elab::records::RecordError::ResourceLimit)\n'
        '            | SourceInferenceError::Inductive(fln_elab::inductive::InductiveError::ResourceLimit)',
    ))
    output = ROOT / 'target' / 'source-inductive-integration'
    output.mkdir(parents=True, exist_ok=True)
    paths = CHANGED + ['crates/fln-parse/src/inductive.rs',
                       'crates/fln-elab/src/source/inductive.rs',
                       'crates/fln/tests/source_inductive.rs']
    (output / 'paths.json').write_text(json.dumps(paths))
    print('\n'.join(paths))


if __name__ == '__main__':
    main()
