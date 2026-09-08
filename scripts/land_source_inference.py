#!/usr/bin/env python3
"""Apply the source inference seam without rewriting unrelated declarations."""
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LIB = ROOT / "crates/fln-elab/src/lib.rs"


def replace_function(source, name, replacement):
    start = source.index(f"pub fn {name}(")
    end = source.index("\n}\n", start) + 3
    return source[:start] + replacement + source[end:]


def main():
    module = ROOT / "crates/fln-elab/src/source.rs"
    levels = ROOT / "crates/fln-elab/src/source/levels.rs"
    if not module.is_file() or not levels.is_file():
        raise SystemExit("source inference implementation files must be present first")
    text = LIB.read_text()
    if "pub mod source;" in text:
        raise SystemExit("source inference is already registered; reconcile rather than replay")
    text = text.replace("pub mod seed;", "pub mod seed;\npub mod source;", 1)
    text = text.replace("pub enum NatDefinitionElabError {", "pub enum NatDefinitionElabError {\n    Inference(source::SourceInferenceError),", 1)
    old = "match self {\n            Self::UnexpectedSyntax"
    new = 'match self {\n            Self::Inference(error) => write!(formatter, "{error}"),\n            Self::UnexpectedSyntax'
    if old not in text:
        raise SystemExit("elaboration error display changed; reconcile before landing")
    text = text.replace(old, new, 1)
    text = replace_function(text, "elaborate_definition_in", '''pub fn elaborate_definition_in(syntax: &Syntax, environment: &Environment) -> Result<Declaration, NatDefinitionElabError> {
    elaborate_definition_in_with_budget(syntax, environment, Budget::DEFAULT)
}

/// Infer source arguments using the caller's kernel budget for assignments.
pub fn elaborate_definition_in_with_budget(syntax: &Syntax, environment: &Environment, budget: Budget) -> Result<Declaration, NatDefinitionElabError> {
    source::definition(syntax, environment, budget)
}
''')
    for name, evaluate in (("elaborate_evaluation_in", "true"), ("elaborate_check_in", "false")):
        text = replace_function(text, name, f'''pub fn {name}(syntax: &Syntax, generated_name: Name, environment: &Environment) -> Result<Declaration, NatDefinitionElabError> {{
    {name}_with_budget(syntax, generated_name, environment, Budget::DEFAULT)
}}

/// Infer the query directly; no fabricated definition source is reparsed.
pub fn {name}_with_budget(syntax: &Syntax, generated_name: Name, environment: &Environment, budget: Budget) -> Result<Declaration, NatDefinitionElabError> {{
    source::query(syntax, generated_name, environment, budget, {evaluate})
}}
''')
    old = "let declaration = elaborate_definition_in(parsed.syntax(), environment)?;"
    if text.count(old) != 1:
        raise SystemExit("source-check seam changed; reconcile before landing")
    text = text.replace(old, "let declaration = elaborate_definition_in_with_budget(parsed.syntax(), environment, budget)?;")
    unifier = ROOT / "crates/fln-elab/src/constraint/unify.rs"
    unify = unifier.read_text()
    old = "#[derive(Debug)]\npub enum UnificationError"
    if old in unify:
        unify = unify.replace(old, "#[derive(Debug, Clone, PartialEq, Eq)]\npub enum UnificationError", 1)
    elif "#[derive(Debug, Clone, PartialEq, Eq)]\npub enum UnificationError" not in unify:
        raise SystemExit("unifier error traits changed; reconcile before landing")
    LIB.write_text(text)
    unifier.write_text(unify)


if __name__ == "__main__":
    main()
