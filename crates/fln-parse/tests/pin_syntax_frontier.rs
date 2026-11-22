//! Frontier A of the pin syntax corpus (bead `fln-pin-syntax-corpus-7b5b`, item 4; the metric
//! `franken_lean-z8j.1.10` asks for over a real denominator): FrankenLean's production parser on
//! every vendored `Init` and `Std` file, command by command, against the tree the pinned frontend
//! produced for the same bytes.
//!
//! The pin's trees are read from the corpus cache that `fln-syntax`'s
//! `pin_syntax_corpus_against_the_pin` fills (see `fln_syntax::pin_syntax::cache_root`); with no
//! cache the lane is a typed SKIP. The production parser is the drop-in's: the header parser,
//! then `command_scope::partition` over the body, then each command through
//! `command_scope::parse` (scope commands) or `parse_source_command`. A scope command's tree is
//! the one `command_scope::trees` builds for it. Each command is parsed under its file's grammar
//! (`fln_parse::extensions`): the syntax the header's imports declare, with the scoped syntax the
//! namespaces and `open`s before it have activated.
//!
//! Each pin command lands in exactly one class:
//! - `identical`: the same tree, every leaf at the same file position;
//! - `positions`: the same tree shape, some leaf elsewhere;
//! - `tree`: FrankenLean built a different tree (the first differing node's kind is named);
//! - `refused:<what>`: FrankenLean's parser refused the command;
//! - `no-tree`: FrankenLean reads the command as a scope command and builds no syntax tree for
//!   it;
//! - `boundary`: FrankenLean's partition starts no command where the pin's does;
//! - `file:<what>`: the file failed before its commands were partitioned.
//!
//! It is a measurement and fails only on a broken scan. Its ratchet, a checked-in per-file table
//! of identical commands, comes once the count is above zero.
#![forbid(unsafe_code)]

use fln_core::name::Name;
use fln_parse::command_scope::imports::parse_source_header;
use fln_parse::command_scope::{self, ScopeCommand};
use fln_parse::extensions::{FileGrammar, SyntaxDecl, extension_census, with_grammar};
use fln_parse::{NatDefinitionParseError, parse_source_command};
use fln_syntax::pin_syntax::{self, cache_root, fnv1a};
use fln_syntax::source::{BytePos, ByteSpan, SourceInfo};
use fln_syntax::tree::Syntax;
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

const SOURCES: &str = "vendor/lean4-src/src";
const MANIFEST: &str = "crates/fln-syntax/tests/corpus/pin_syntax_manifest.tsv";
const PRODUCER: &str = "scripts/extract/dump_command_syntax.lean";

fn workspace_root() -> PathBuf {
    // The tree this run was launched from, refused if the binary was compiled in
    // another checkout (bead fln-cross-tree-baked-root-k60n).
    fln_core::checked_workspace_root!()
}

fn pin_commit(root: &Path) -> String {
    let lock = std::fs::read_to_string(root.join("SUITE.lock")).expect("read SUITE.lock");
    lock.lines()
        .find(|line| line.starts_with("reference leanprover/lean4 "))
        .and_then(|line| {
            line.split_whitespace()
                .find_map(|part| part.strip_prefix("commit="))
        })
        .expect("SUITE.lock names the reference commit")
        .to_owned()
}

/// The first original position in a tree: where its command begins.
fn first_position(root: &Syntax) -> Option<usize> {
    let mut stack = vec![root];
    while let Some(syntax) = stack.pop() {
        match syntax {
            Syntax::Atom {
                info: SourceInfo::Original { pos, .. },
                ..
            }
            | Syntax::Ident {
                info: SourceInfo::Original { pos, .. },
                ..
            } => return Some(pos.0),
            Syntax::Node { args, .. } => stack.extend(args.iter().rev()),
            _ => {}
        }
    }
    None
}

fn kind_of(syntax: &Syntax) -> String {
    match syntax {
        Syntax::Missing => "<missing>".to_owned(),
        Syntax::Atom { val, .. } => format!("{val:?}"),
        Syntax::Ident { val, .. } => format!("`{}", val.to_display_string()),
        Syntax::Node { kind, .. } => kind.to_display_string(),
    }
}

/// The leaf's file span: the pin's are file positions already, ours are positions in the
/// command's own bytes and move by `offset`.
fn leaf_span(info: &SourceInfo, offset: usize) -> Option<(usize, usize)> {
    match info {
        SourceInfo::Original { pos, end_pos, .. } => Some((pos.0 + offset, end_pos.0 + offset)),
        _ => None,
    }
}

/// `Ok(None)` identical, `Ok(Some(leaf))` the same shape with a leaf elsewhere (the first such
/// leaf, with both spans), `Err(kind)` a different tree, naming the pin's node where they part.
fn compare(pin: &Syntax, ours: &Syntax, offset: usize) -> Result<Option<String>, String> {
    let mut misplaced = None;
    let mut stack = vec![(pin, ours)];
    let mut place = |pin_leaf: &Syntax, a: &SourceInfo, b: &SourceInfo| {
        let (theirs, mine) = (leaf_span(a, 0), leaf_span(b, offset));
        if misplaced.is_none() && theirs != mine {
            misplaced = Some(format!(
                "{} pin {theirs:?} ours {mine:?}",
                kind_of(pin_leaf)
            ));
        }
    };
    while let Some((pin, ours)) = stack.pop() {
        match (pin, ours) {
            (Syntax::Missing, Syntax::Missing) => {}
            (Syntax::Atom { info: a, val: x }, Syntax::Atom { info: b, val: y }) if x == y => {
                place(pin, a, b);
            }
            (
                Syntax::Ident {
                    info: a, val: x, ..
                },
                Syntax::Ident {
                    info: b, val: y, ..
                },
            ) if x == y => {
                place(pin, a, b);
            }
            (
                Syntax::Node {
                    kind: k, args: xs, ..
                },
                Syntax::Node {
                    kind: l, args: ys, ..
                },
            ) if k == l && xs.len() == ys.len() => {
                stack.extend(xs.iter().zip(ys).rev());
            }
            (pin, _) => return Err(kind_of(pin)),
        }
    }
    Ok(misplaced)
}

fn refusal_class(error: &NatDefinitionParseError) -> String {
    match error {
        NatDefinitionParseError::Lexical { .. } => "lexer".to_owned(),
        NatDefinitionParseError::OutsideSeedGrammar { expected, .. } => format!("{expected:?}"),
        NatDefinitionParseError::ModuleHeader { reason, .. } => format!("header:{reason:?}"),
        NatDefinitionParseError::GeneratedParser { error, .. } => format!("generated:{error:?}"),
        NatDefinitionParseError::Source(_) => "source".to_owned(),
        NatDefinitionParseError::Build(_) => "build".to_owned(),
    }
}

fn scope_name(command: &ScopeCommand) -> &'static str {
    match command {
        ScopeCommand::Namespace(_) => "namespace",
        ScopeCommand::Section(_) | ScopeCommand::SectionWithModifiers { .. } => "section",
        ScopeCommand::End(_) => "end",
        ScopeCommand::Open(_)
        | ScopeCommand::OpenScoped(_)
        | ScopeCommand::OpenIn { .. }
        | ScopeCommand::OpenExplicit { .. } => "open",
        ScopeCommand::Export { .. } => "export",
        ScopeCommand::Universe(_) => "universe",
        ScopeCommand::Variable(_) => "variable",
        ScopeCommand::Include(_) | ScopeCommand::Omit(_) => "include-omit",
        ScopeCommand::SetOption { .. } | ScopeCommand::SetOptionIn { .. } => "set_option",
        ScopeCommand::GuardMsgs { .. } => "guard_msgs",
        ScopeCommand::In { .. } => "in",
        ScopeCommand::Simp(_)
        | ScopeCommand::Instance(_)
        | ScopeCommand::Reducibility(_)
        | ScopeCommand::Executable(_) => "attribute",
        ScopeCommand::Trivia => "trivia",
        ScopeCommand::Exit => "exit",
    }
}

/// One pin command's class, where it starts, and for `positions` the first misplaced leaf.
struct Outcome {
    class: String,
    start: usize,
    detail: String,
}

/// The class of every pin command of one file.
/// How the syntax declarations a file makes compare with the census rows of its module: the
/// translation `FileGrammar::declare` does is checked against the pin's own.
#[derive(Default)]
struct DeclarationCheck {
    census: usize,
    registered: usize,
    identical: usize,
    differing: Vec<String>,
    unnamed: Vec<String>,
    refused: BTreeMap<&'static str, usize>,
    refused_examples: BTreeMap<&'static str, Vec<String>>,
}

fn check_declarations(
    module: &Name,
    declared: &[std::sync::Arc<SyntaxDecl>],
    check: &mut DeclarationCheck,
) {
    let census: BTreeMap<&Name, &SyntaxDecl> = extension_census()
        .decls()
        .iter()
        .filter(|decl| decl.module == *module)
        .map(|decl| (&decl.decl, decl.as_ref()))
        .collect();
    check.census += census.len();
    for decl in declared {
        check.registered += 1;
        match census.get(&decl.decl) {
            Some(expected) if **expected == **decl => check.identical += 1,
            // A `local` entry is not exported, so its census row has no category or scope: only
            // its description is the pin's to compare.
            Some(expected) if expected.category.is_none() && expected.descr == decl.descr => {
                check.identical += 1
            }
            Some(expected) => check.differing.push(format!(
                "{} cat={:?} scope={:?} prio={}\n     pin  {}\n     ours {} cat={:?} scope={:?} prio={}",
                decl.decl.to_display_string(),
                expected.category.as_ref().map(Name::to_display_string),
                expected.scope.as_ref().map(Name::to_display_string),
                expected.priority,
                expected.descr,
                decl.descr,
                decl.category.as_ref().map(Name::to_display_string),
                decl.scope.as_ref().map(Name::to_display_string),
                decl.priority,
            )),
            None => check.unnamed.push(format!("{}: {}", module.to_display_string(), decl.decl.to_display_string())),
        }
    }
}

fn classify_file(
    source: &[u8],
    trees: &pin_syntax::PinTrees,
    module: Option<Name>,
    check: &mut DeclarationCheck,
) -> Vec<Outcome> {
    let commands: Vec<&Syntax> = trees
        .commands
        .iter()
        .filter(|tree| !matches!(tree, Syntax::Node { kind, .. } if kind.to_display_string() == "Lean.Parser.Command.eoi"))
        .collect();
    let outcome = |class: String, start: usize| Outcome {
        class,
        start,
        detail: String::new(),
    };
    let whole = |class: String| {
        commands
            .iter()
            .map(|pin| outcome(class.clone(), first_position(pin).unwrap_or(0)))
            .collect::<Vec<_>>()
    };
    let header = match parse_source_header(source) {
        Ok(header) => header,
        Err(error) => return whole(format!("file:header:{}", refusal_class(&error))),
    };
    let body_start = header.body_start.0;
    let mut grammar = match FileGrammar::new(header.prelude, &header.imports, module.clone()) {
        Ok(grammar) => grammar,
        Err(_) => return whole("file:grammar".to_owned()),
    };
    let partitioned = with_grammar(&grammar.grammar(), || {
        command_scope::partition(&source[body_start..])
    });
    let ours: BTreeMap<usize, &[u8]> = match partitioned {
        Ok(parts) => parts
            .into_iter()
            .map(|(offset, bytes)| (offset.0 + body_start, bytes))
            .collect(),
        Err(error) => {
            let mut lost = whole(format!("file:partition:{}", refusal_class(&error)));
            // The first refusal names the bytes the whole file stops at.
            let (at, what) = match &error {
                NatDefinitionParseError::Lexical { diagnostics } => diagnostics
                    .first()
                    .map_or((0, ""), |first| (first.at.0, first.message)),
                NatDefinitionParseError::OutsideSeedGrammar { at, .. } => (at.0, ""),
                _ => (0, ""),
            };
            let at = body_start + at;
            let text =
                String::from_utf8_lossy(&source[at.min(source.len())..(at + 24).min(source.len())])
                    .split('\n')
                    .next()
                    .unwrap_or_default()
                    .to_owned();
            if let Some(first) = lost.first_mut() {
                first.detail = format!("{what} at {at}: {text:?}");
            }
            return lost;
        }
    };
    let outcomes = commands
        .iter()
        .map(|pin| {
            let Some(start) = first_position(pin) else {
                return outcome("boundary".to_owned(), 0);
            };
            let Some(bytes) = ours.get(&start) else {
                return outcome("boundary".to_owned(), start);
            };
            let compared = |ours: &Syntax| match compare(pin, ours, start) {
                Ok(None) => outcome("identical".to_owned(), start),
                Ok(Some(leaf)) => Outcome {
                    class: "positions".to_owned(),
                    start,
                    detail: leaf,
                },
                Err(kind) => outcome(format!("tree:{kind}"), start),
            };
            let current = grammar.grammar();
            match with_grammar(&current, || command_scope::parse(bytes)) {
                Ok(Some(scope)) => {
                    // The command after an `in` may be one the parser refuses.
                    let inner = match &scope {
                        ScopeCommand::OpenIn { names, .. } => grammar.grammar_opening(names),
                        _ => current,
                    };
                    let tree = with_grammar(&inner, || command_scope::trees::tree(bytes));
                    grammar.apply(&scope);
                    return match tree {
                        Ok(Some(syntax)) => compared(&syntax),
                        Ok(None) => outcome(format!("no-tree:{}", scope_name(&scope)), start),
                        Err(error) => outcome(format!("refused:{}", refusal_class(&error)), start),
                    };
                }
                Ok(None) => {}
                // A scope command the scope layer refuses to read (`attribute [bv_normalize] f`,
                // `open A (x) in …`) is compared through its tree where the parser builds one, as
                // a declaration the checker refuses is.
                Err(error) => {
                    return match with_grammar(&current, || command_scope::trees::tree(bytes)) {
                        Ok(Some(syntax)) => compared(&syntax),
                        _ => outcome(format!("refused:{}", refusal_class(&error)), start),
                    };
                }
            }
            match with_grammar(&current, || parse_source_command(bytes)) {
                Err(error) => outcome(format!("refused:{}", refusal_class(&error)), start),
                Ok(parsed) => {
                    if let Err(reason) = grammar.declare(parsed.syntax()) {
                        *check.refused.entry(reason).or_default() += 1;
                        let shown = check.refused_examples.entry(reason).or_default();
                        if shown.len() < 6 {
                            shown.push(
                                String::from_utf8_lossy(bytes)
                                    .lines()
                                    .next()
                                    .unwrap_or("")
                                    .to_owned(),
                            );
                        }
                    }
                    compared(parsed.syntax())
                }
            }
        })
        .collect::<Vec<_>>();
    if let Some(module) = &module {
        check_declarations(module, grammar.declared(), check);
    }
    outcomes
}

#[test]
fn the_comparison_names_shape_and_position_differences() {
    let info = |pos: usize, end: usize| SourceInfo::Original {
        leading: ByteSpan::empty_at(BytePos(pos)),
        pos: BytePos(pos),
        trailing: ByteSpan::empty_at(BytePos(end)),
        end_pos: BytePos(end),
    };
    let atom = |pos: usize, val: &str| Syntax::Atom {
        info: info(pos, pos + val.len()),
        val: val.to_owned(),
    };
    let node = |args: Vec<Syntax>| Syntax::Node {
        info: SourceInfo::None,
        kind: fln_core::name::Name::from_components(["k"]),
        args,
    };
    let pin = node(vec![atom(10, "def"), atom(14, "x")]);
    assert_eq!(
        compare(&pin, &node(vec![atom(0, "def"), atom(4, "x")]), 10),
        Ok(None)
    );
    assert_eq!(
        compare(&pin, &node(vec![atom(0, "def"), atom(5, "x")]), 10),
        Ok(Some(
            "\"x\" pin Some((14, 15)) ours Some((15, 16))".to_owned()
        ))
    );
    assert_eq!(
        compare(&pin, &node(vec![atom(0, "def"), atom(4, "y")]), 10),
        Err("\"x\"".to_owned())
    );
    assert_eq!(
        compare(&pin, &node(vec![atom(0, "def")]), 10),
        Err("k".to_owned())
    );
}

#[ignore = "cost: FrankenLean's parser over the 72,092 commands of the pin syntax corpus, read from its cache (bead fln-pin-syntax-corpus-7b5b); a measurement lane, typed SKIP without the cache"]
#[test]
fn pin_syntax_frontier_a_measures_the_production_parser() {
    let root = workspace_root();
    let producer = format!(
        "{:016x}",
        fnv1a(&std::fs::read(root.join(PRODUCER)).expect("read the producer"))
    );
    let Some(cache) = cache_root().map(|cache| cache.join(pin_commit(&root)).join(&producer))
    else {
        eprintln!("SKIP pin_syntax_frontier: no cache directory");
        return;
    };
    let manifest = std::fs::read_to_string(root.join(MANIFEST)).expect("read the manifest");
    let files: Vec<&str> = manifest
        .lines()
        .filter(|line| !line.starts_with('#'))
        .filter_map(|line| line.split('\t').next())
        .collect();
    assert!(
        files.len() > 1000,
        "a manifest this small is broken: {}",
        files.len()
    );
    let mut histogram: BTreeMap<String, usize> = BTreeMap::new();
    let mut examples: BTreeMap<String, Vec<String>> = BTreeMap::new();
    // Files lost before partition, by what stopped them: (files, commands).
    let mut stoppers: BTreeMap<String, (usize, usize)> = BTreeMap::new();
    let mut identical_files = 0usize;
    let mut total = 0usize;
    let mut check = DeclarationCheck::default();
    for file in &files {
        let source = std::fs::read(root.join(SOURCES).join(file)).expect("read a source");
        let Ok(dump) = std::fs::read_to_string(cache.join(format!("{:016x}.dump", fnv1a(&source))))
        else {
            eprintln!(
                "SKIP pin_syntax_frontier: {file} has no cached dump; run fln-syntax's \
                 pin_syntax_corpus_against_the_pin first"
            );
            return;
        };
        let trees = pin_syntax::read(&dump, &source).expect("a cached dump reads");
        let module = file
            .strip_suffix(".lean")
            .map(|path| Name::from_components(path.split('/')));
        let outcomes = classify_file(&source, &trees, module, &mut check);
        if !outcomes.is_empty() && outcomes.iter().all(|outcome| outcome.class == "identical") {
            identical_files += 1;
        }
        total += outcomes.len();
        if let Some(first) = outcomes
            .first()
            .filter(|first| first.class.starts_with("file:"))
        {
            let reason = first.detail.split_once(" at ").map_or("", |(what, _)| what);
            let text = first.detail.rsplit_once(": ").map_or("", |(_, text)| text);
            let key = format!(
                "{} | {reason} | {}",
                first.class,
                text.chars().take(12).collect::<String>()
            );
            let entry = stoppers.entry(key).or_default();
            entry.0 += 1;
            entry.1 += outcomes.len();
        }
        for outcome in outcomes {
            let shown = examples.entry(outcome.class.clone()).or_default();
            if shown.len() < 2 {
                shown.push(format!("{file}@{} {}", outcome.start, outcome.detail));
            }
            *histogram.entry(outcome.class).or_default() += 1;
        }
    }
    let identical = histogram.get("identical").copied().unwrap_or(0);
    let mut rows: Vec<_> = histogram.iter().collect();
    rows.sort_by(|a, b| b.1.cmp(a.1).then(a.0.cmp(b.0)));
    let top: Vec<String> = rows
        .iter()
        .take(40)
        .map(|(class, count)| format!("{class} {count}"))
        .collect();
    eprintln!(
        "pin_syntax_frontier_a: {identical} of {total} commands identical; {identical_files} of {} \
         files wholly identical | {}",
        files.len(),
        top.join(", ")
    );
    for (class, _) in rows.iter().take(40) {
        eprintln!("  {class}: {}", examples[*class].join(" | "));
    }
    let mut stopped: Vec<_> = stoppers.into_iter().collect();
    stopped.sort_by_key(|entry| std::cmp::Reverse((entry.1).1));
    for (key, (files, commands)) in stopped.iter().take(30) {
        eprintln!("  stopper {commands} commands in {files} files: {key}");
    }
    eprintln!(
        "pin_syntax_frontier_a declarations: {} registered, {} identical to the census, {} \
         differing, {} absent from it; the census has {} for these modules; refused: {:?}",
        check.registered,
        check.identical,
        check.differing.len(),
        check.unnamed.len(),
        check.census,
        check.refused
    );
    for differing in check.differing.iter().take(40) {
        eprintln!("  differs: {differing}");
    }
    for unnamed in check.unnamed.iter().take(12) {
        eprintln!("  absent: {unnamed}");
    }
    for (reason, shown) in &check.refused_examples {
        eprintln!("  refused ({reason}): {}", shown.join(" || "));
    }
    // The translation is the pin's or it registers nothing: a declaration that reads differently
    // from its census row, or under a name the census lacks, is a translator defect.
    assert!(
        check.differing.is_empty() && check.unnamed.is_empty(),
        "{} declarations differ from their census rows and {} are absent from the census",
        check.differing.len(),
        check.unnamed.len()
    );
}

#[test]
fn generated_registry_parses_scopes_open_in_verso_and_local_syntax() {
    use fln_parse::builtin_interpreter::{DEFAULT_STEP_BUDGET, reference_builtin_interpreter};
    use fln_syntax::source::SourceText;

    let interp = reference_builtin_interpreter();
    let src = SourceText::from_utf8(
        br#"prelude
namespace MyScope
scoped syntax "magicTok" : term
def insideScope := magicTok
end MyScope

open scoped MyScope in
def viaOpenCmd := magicTok

def viaOpenTerm := open scoped MyScope in magicTok

set_option doc.verso true
/--
A verso paragraph with {name}`Nat`.
-/
def documented := 1

syntax (name := myTriple) "triple(" patternIgnore("!") term ")" : term
def usesLocal := triple(! documented)

declare_syntax_cat mycat
syntax "myleaf" : mycat
def usesDeclaredCatQuot := `(mycat| myleaf)

syntax myAbbrev := "abv" ident
def usesAbbrevQuot := `(myAbbrev| abv foo)
def usesAliasQuot := `(attrKind| local)

syntax "s!" interpolatedStr(term) : term
def usesInterp := s!"hello {documented}"
"#,
    )
    .unwrap();
    let parsed = interp.parse_module_with_file_grammar(
        &src,
        Some(Name::from_components(["Stage5Smoke"])),
        DEFAULT_STEP_BUDGET,
    );
    assert!(
        parsed.errors.is_empty(),
        "unexpected parse errors: {:?}",
        parsed.errors
    );
    assert!(!parsed.budget_exhausted);

    fn has_kind(stx: &Syntax, needle: &str) -> bool {
        let mut stack = vec![stx];
        while let Some(node) = stack.pop() {
            if let Syntax::Node { kind, args, .. } = node {
                if kind.to_display_string() == needle {
                    return true;
                }
                stack.extend(args.iter());
            }
        }
        false
    }

    assert!(
        parsed
            .commands
            .iter()
            .any(|c| has_kind(c, "Lean.Parser.Command.versoCommentBody")),
        "set_option doc.verso true must emit Lean.Parser.Command.versoCommentBody even at top of command"
    );
    assert!(
        parsed.commands.iter().any(|c| has_kind(c, "myTriple")),
        "local syntax declaration must register myTriple for subsequent commands"
    );
    assert!(
        parsed.commands.iter().any(|c| has_kind(c, "patternIgnore")),
        "patternIgnore alias must preserve the patternIgnore wrapper node"
    );
    assert!(
        parsed.commands.iter().any(|c| has_kind(c, "mycat.quot")),
        "declare_syntax_cat must register its mycat.quot quotation parser in term"
    );
    assert!(
        parsed.commands.iter().any(|c| has_kind(c, "myAbbrev")),
        "parserOfStack must resolve active syntaxAbbrev in dynamic quotation"
    );
    assert!(
        parsed
            .commands
            .iter()
            .any(|c| has_kind(c, "Lean.Parser.Term.attrKind")),
        "parserOfStack must resolve registered parser aliases in dynamic quotation"
    );
    assert!(
        parsed
            .commands
            .iter()
            .any(|c| has_kind(c, "interpolatedStrKind")),
        "interpolatedStr must emit interpolatedStrKind"
    );

    // Outside MyScope without `open scoped`, `magicTok` must not parse as MyScope's syntax.
    let outside = SourceText::from_utf8(
        br#"prelude
namespace MyScope
scoped syntax (name := scopedMagic) "magicTok" : term
end MyScope
def leaked := magicTok
"#,
    )
    .unwrap();
    let parsed_out = interp.parse_module_with_file_grammar(
        &outside,
        Some(Name::from_components(["Stage5Leak"])),
        DEFAULT_STEP_BUDGET,
    );
    assert!(
        !parsed_out
            .commands
            .iter()
            .any(|c| has_kind(c, "MyScope.scopedMagic")),
        "scoped syntax must deactivate after end MyScope"
    );
}

#[ignore = "cost: Stage 5 pure generated registry parser (BuiltinInterpreter + FileGrammar ParserDescr) over all 71,015 Init+Std commands from ~/.cache/fln/pin-syntax (bead franken_lean-z8j.1.10)"]
#[test]
fn pin_syntax_frontier_stage5_generated_registry() {
    use fln_parse::builtin_interpreter::{DEFAULT_STEP_BUDGET, reference_builtin_interpreter};
    use fln_syntax::source::SourceText;
    use std::time::Instant;

    let root = workspace_root();
    let producer = format!(
        "{:016x}",
        fnv1a(&std::fs::read(root.join(PRODUCER)).expect("read the producer"))
    );
    let Some(cache) = cache_root().map(|cache| cache.join(pin_commit(&root)).join(&producer))
    else {
        eprintln!("SKIP pin_syntax_frontier_stage5: no cache directory");
        return;
    };
    let manifest = std::fs::read_to_string(root.join(MANIFEST)).expect("read the manifest");
    let files: Vec<&str> = manifest
        .lines()
        .filter(|line| !line.starts_with('#'))
        .filter_map(|line| line.split('\t').next())
        .collect();
    assert!(files.len() > 1000, "manifest too small: {}", files.len());

    let interp = reference_builtin_interpreter();
    let t0 = Instant::now();
    let mut histogram: BTreeMap<String, usize> = BTreeMap::new();
    let mut examples: BTreeMap<String, Vec<String>> = BTreeMap::new();
    let mut worst_files: Vec<(usize, usize, String)> = Vec::new();
    let mut identical_headers = 0usize;
    let mut identical_files = 0usize;
    let mut files_with_errors = 0usize;
    let mut total_errors = 0usize;
    let mut budget_exhausted_files = 0usize;
    let mut total_cmds = 0usize;

    for file in &files {
        let source_bytes = std::fs::read(root.join(SOURCES).join(file)).expect("read a source");
        let Ok(dump) =
            std::fs::read_to_string(cache.join(format!("{:016x}.dump", fnv1a(&source_bytes))))
        else {
            eprintln!("SKIP pin_syntax_frontier_stage5: {file} has no cached dump");
            return;
        };
        let trees = pin_syntax::read(&dump, &source_bytes).expect("cached dump reads");
        let source = SourceText::from_utf8(&source_bytes).expect("utf-8 source");
        let module = file
            .strip_suffix(".lean")
            .map(|path| Name::from_components(path.split('/')));
        let parsed = interp.parse_module_with_file_grammar(&source, module, DEFAULT_STEP_BUDGET);

        if compare(&trees.header, &parsed.header, 0) == Ok(None) {
            identical_headers += 1;
        }
        if !parsed.errors.is_empty() {
            files_with_errors += 1;
            total_errors += parsed.errors.len();
        }
        if parsed.budget_exhausted {
            budget_exhausted_files += 1;
        }

        let pin_cmds: Vec<&Syntax> = trees
            .commands
            .iter()
            .filter(|tree| {
                !matches!(
                    tree,
                    Syntax::Node { kind, .. } if kind.to_display_string() == "Lean.Parser.Command.eoi"
                )
            })
            .collect();
        let mut ours_by_start: BTreeMap<usize, &Syntax> = BTreeMap::new();
        for cmd in &parsed.commands {
            if matches!(
                cmd,
                Syntax::Node { kind, .. } if kind.to_display_string() == "Lean.Parser.Command.eoi"
            ) {
                continue;
            }
            if let Some(pos) = first_position(cmd) {
                ours_by_start.entry(pos).or_insert(cmd);
            }
        }

        let mut file_bad = 0usize;
        for pin in &pin_cmds {
            total_cmds += 1;
            let Some(start) = first_position(pin) else {
                file_bad += 1;
                *histogram
                    .entry("boundary:pin-no-pos".to_owned())
                    .or_default() += 1;
                continue;
            };
            let Some(ours) = ours_by_start.get(&start) else {
                file_bad += 1;
                let class = if parsed.budget_exhausted {
                    "boundary:budget".to_owned()
                } else if !parsed.errors.is_empty() {
                    "boundary:after-error".to_owned()
                } else {
                    "boundary:missing".to_owned()
                };
                let shown = examples.entry(class.clone()).or_default();
                if shown.len() < 3 {
                    let first_err = parsed
                        .errors
                        .first()
                        .map(|e| format!("err@{} {}", e.pos, e.unexpected))
                        .unwrap_or_default();
                    shown.push(format!("{file}@{start} {first_err}"));
                }
                *histogram.entry(class).or_default() += 1;
                continue;
            };
            match compare(pin, ours, 0) {
                Ok(None) => {
                    *histogram.entry("identical".to_owned()).or_default() += 1;
                }
                Ok(Some(leaf)) => {
                    file_bad += 1;
                    let class = "positions".to_owned();
                    let shown = examples.entry(class.clone()).or_default();
                    if shown.len() < 3 {
                        shown.push(format!("{file}@{start} {leaf}"));
                    }
                    *histogram.entry(class).or_default() += 1;
                }
                Err(kind) => {
                    file_bad += 1;
                    let class = format!("tree:{kind}");
                    let shown = examples.entry(class.clone()).or_default();
                    if shown.len() < 3 {
                        shown.push(format!("{file}@{start} ours={}", kind_of(ours)));
                    }
                    *histogram.entry(class).or_default() += 1;
                }
            }
        }
        if !pin_cmds.is_empty() && file_bad == 0 {
            identical_files += 1;
        }
        if file_bad > 0 {
            worst_files.push((file_bad, pin_cmds.len(), (*file).to_owned()));
        }
    }

    let identical = histogram.get("identical").copied().unwrap_or(0);
    let mut rows: Vec<_> = histogram.iter().collect();
    rows.sort_by(|a, b| b.1.cmp(a.1).then(a.0.cmp(b.0)));
    eprintln!(
        "STAGE 5 GENERATED REGISTRY FRONTIER ({:.2}s): {identical}/{total_cmds} ({:.2}%) commands identical; \
         {identical_files}/{} files wholly identical; headers {identical_headers}/{}; \
         files_with_errors={files_with_errors} total_errors={total_errors} budget_exhausted={budget_exhausted_files}",
        t0.elapsed().as_secs_f64(),
        (identical as f64) * 100.0 / (total_cmds.max(1) as f64),
        files.len(),
        files.len(),
    );
    for (class, count) in rows.iter().take(40) {
        let ex = examples
            .get(*class)
            .map(|v| v.join(" | "))
            .unwrap_or_default();
        eprintln!("  {count:>6}  {class}  [{ex}]");
    }
    worst_files.sort_by(|a, b| b.0.cmp(&a.0).then(a.2.cmp(&b.2)));
    eprintln!("TOP 20 FILES BY NON-IDENTICAL COMMANDS:");
    for (bad, total, file) in worst_files.iter().take(20) {
        eprintln!("  {bad:>4}/{total:<4}  {file}");
    }
}
