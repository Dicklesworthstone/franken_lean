#!/usr/bin/env python3
"""Register the admission-only source checker using guarded source anchors."""
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
updates = {}
def edit(path, old, new):
    text=updates.get(path,(ROOT/path).read_text())
    if text.count(old)!=1:
        raise SystemExit(f'changed or ambiguous source anchor: {path}: {old[:60]}')
    updates[path]=text.replace(old,new,1)
def main():
    edit('crates/fln/src/lib.rs','#![forbid(unsafe_code)]','#![forbid(unsafe_code)]\n\npub mod source_check;\npub use source_check::{SourceFileCheck, SourceCheckError, SourceCheckLimits};')
    path='crates/fln-cli/src/lib.rs'
    edit(path,'#![forbid(unsafe_code)]','#![forbid(unsafe_code)]\n\nmod source_check;')
    edit(path,'enum MultiplexerCommand {','enum MultiplexerCommand {\n    SourceCheck { paths: Vec<PathBuf>, max_bytes: usize, json: bool },')
    edit(path,'    if command == "run" {','    if command == "check-source" {\n        return source_check::parse(arguments.collect());\n    }\n    if command == "run" {')
    edit(path,'        Ok(MultiplexerCommand::SourceRun {','        Ok(MultiplexerCommand::SourceCheck { paths, max_bytes, json }) => source_check::run(paths, max_bytes, json),\n        Ok(MultiplexerCommand::SourceRun {')
    anchor='    "  fln check-olean [--json] [--receipts PATH] [--max-bytes BYTES] PATH\\n",\n'
    edit(path,anchor,anchor+'    "  fln check-source [--json] [--max-bytes BYTES] PATH...\\n",\n    "    Check import-free definitions and theorems without executing code.\\n",\n')
    for path,text in updates.items(): (ROOT/path).write_text(text)
if __name__=='__main__': main()
