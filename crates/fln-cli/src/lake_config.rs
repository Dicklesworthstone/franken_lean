//! Native `package` / `lean_lib` configuration for checked module builds.
//!
//! Lake's commands elaborate field terms at their declared types, then its loader evaluates
//! the resulting configurations (`Lake/DSL/DeclUtil.lean`, `Lake/Load/Lean/Eval.lean`). This
//! adapter implements that order for the supported library fields. It never executes Lake's
//! upstream elaborator, interprets an expression as a Rust string, or invents a FilePath type.
//! The field declarations and the user's definitions are admitted together against the real
//! `Init.System.FilePath` import world. Only selected path projections then enter Golem.
use super::*;
use fln_lake::{LakeConfigFormat, LakeTarget};
use fln_parse::command_scope::{self, ScopeCommand};
use fln_parse::extensions::{FileGrammar, with_grammar};
use fln_syntax::literal::{LiteralKind, decode_string};
use fln_syntax::run::{Event, lex_run};
use fln_syntax::source::SourceText;
use fln_syntax::token::{LexedToken, TokenKind, TokenTable};
use fln_syntax::view::SourceView;

const MAX_CONFIG_BYTES: usize = 64 * 1024;
const MAX_CONFIG_COMMANDS: usize = 1024;
const LAKE_COMMANDS: [&str; 10] = [
    "package",
    "lean_lib",
    "lean_exe",
    "require",
    "script",
    "target",
    "post_update",
    "extern_lib",
    "input_file",
    "input_dir",
];

#[derive(Debug, Clone, Copy)]
enum PathSlot {
    Source,
    Build,
    Library(usize),
}

#[derive(Debug)]
struct PathField {
    slot: PathSlot,
    declaration: String,
    label: String,
}

#[derive(Debug)]
struct ParsedConfig {
    config: LakeConfig,
    /// Ordinary source and generated, *typed* field definitions, in source order.
    program: String,
    fields: Vec<PathField>,
}

pub(super) struct LoadedConfig {
    pub(super) config: LakeConfig,
    pub(super) imports: ImportPostureReport,
}

struct Tokens {
    view: SourceView,
    tokens: Vec<LexedToken>,
}

impl Tokens {
    fn read(source: &[u8], table: &TokenTable) -> Result<Self, Failure> {
        let original = SourceText::from_utf8(source)
            .map_err(|error| Failure::input(format!("lakefile.lean: {error:?}")))?;
        let view = SourceView::of(&original);
        let run = lex_run(view.normalized(), table);
        if let Some((message, at)) = run.diagnostics().first() {
            return Err(Failure::input(format!(
                "lakefile.lean: byte {}: {message}",
                view.to_original(*at).0
            )));
        }
        Ok(Self {
            view,
            tokens: run
                .events
                .into_iter()
                .filter_map(|event| match event {
                    Event::Token(token) => Some(token),
                    _ => None,
                })
                .collect(),
        })
    }

    fn symbol(&self, at: usize, spelling: &str) -> bool {
        matches!(self.tokens.get(at).map(|token| &token.kind),
            Some(TokenKind::Symbol(symbol)) if symbol == spelling)
    }

    fn spelling(&self, at: usize) -> Option<&str> {
        self.tokens
            .get(at)
            .and_then(|token| self.view.normalized().span_str(token.extent))
    }

    fn offset(&self, at: usize) -> usize {
        self.tokens.get(at).map_or_else(
            || self.view.reconstruct_original().len(),
            |token| self.view.to_original(token.extent.start()).0,
        )
    }

    fn column(&self, at: usize) -> usize {
        let position = self.tokens[at].extent.start();
        let text = self.view.normalized();
        position.0
            - text
                .line_start(text.line_of(position))
                .expect("token line")
                .0
    }

    fn new_line(&self, at: usize) -> bool {
        at == 0
            || self
                .view
                .normalized()
                .line_of(self.tokens[at].extent.start())
                > self
                    .view
                    .normalized()
                    .line_of(self.tokens[at - 1].extent.end())
    }

    /// Locate the declaration after its doc comment and attributes. Only the Lake handler
    /// inspects the attributes; an ordinary Lean declaration keeps its original bytes.
    fn head(&self) -> Result<(usize, Vec<std::ops::Range<usize>>), Failure> {
        let mut at = usize::from(self.symbol(0, "/--"));
        let mut attributes = Vec::new();
        while self.symbol(at, "@[") {
            let start = at + 1;
            let mut depth = 1usize;
            at += 1;
            while at < self.tokens.len() && depth != 0 {
                if self.symbol(at, "[") || self.symbol(at, "@[") {
                    depth += 1;
                } else if self.symbol(at, "]") {
                    depth -= 1;
                }
                at += 1;
            }
            if depth != 0 {
                return Err(Failure::input(
                    "lakefile.lean: unclosed declaration attributes",
                ));
            }
            attributes.push(start..at - 1);
        }
        Ok((at, attributes))
    }

    fn name(&self, at: usize) -> Result<String, Failure> {
        match self.tokens.get(at).map(|token| &token.kind) {
            Some(TokenKind::Ident(name)) if !name.is_anonymous() => Ok(name.to_display_string()),
            Some(TokenKind::Literal(LiteralKind::Str)) => {
                let value = self.spelling(at).and_then(decode_string).ok_or_else(|| {
                    Failure::input("lakefile.lean: malformed package or library name")
                })?;
                if value.is_empty() {
                    return Err(Failure::input(
                        "lakefile.lean: an empty package or library name",
                    ));
                }
                // A string denotes one Name component, as expandIdentOrStrAsIdent does.
                Ok(Name::str(Name::anonymous(), value).to_display_string())
            }
            _ => Err(Failure::unsupported(
                "lakefile.lean: package and lean_lib currently require an explicit name",
            )),
        }
    }
}

/// Register just the command introducers with the existing command partitioner. The field
/// syntax below is the native handler; these descriptions confer no declaration authority and
/// supply no replacement Lake definitions. Unknown Lake commands get their own refusal rather
/// than being swallowed into the preceding field's expression.
fn grammar() -> Result<FileGrammar, Failure> {
    let mut grammar = FileGrammar::new(false, &[], Some(Name::from_components(["lakefile"])))
        .map_err(|error| Failure::new("internal-fault", format!("Init grammar: {error:?}")))?
        .own_syntax_only();
    for command in LAKE_COMMANDS {
        let source = format!("syntax (name := Lake.DSL.{command}) \"{command} \" ident : command");
        let parsed = fln_parse::parse_source_command(source.as_bytes())
            .map_err(|error| Failure::new("internal-fault", error.to_string()))?;
        grammar
            .declare(parsed.syntax())
            .map_err(|error| Failure::new("internal-fault", error))?;
    }
    Ok(grammar)
}

fn fresh_name(source: &str, next: &mut usize) -> String {
    loop {
        let name = format!("_fln_lake_path_{}", *next);
        *next += 1;
        if !source.contains(&name) {
            return name;
        }
    }
}

/// Lake's supported `where` fields, retaining each expression's original bytes. Delimiters
/// and the field layout protect nested expressions; comments and literals are lexer events.
/// Same-line field separators and trailing where-declarations remain explicit unsupported
/// forms. They are never approximated by splitting a Lean term at an arbitrary semicolon.
fn fields<'a>(
    source: &'a [u8],
    tokens: &Tokens,
    at: usize,
    declaration_column: usize,
) -> Result<Vec<(String, &'a [u8])>, Failure> {
    if at == tokens.tokens.len() {
        return Ok(Vec::new());
    }
    if tokens.symbol(at, "{") && tokens.symbol(at + 1, "}") && at + 2 == tokens.tokens.len() {
        return Ok(Vec::new());
    }
    if !tokens.symbol(at, "where") {
        return Err(Failure::unsupported(
            "lakefile.lean: supported configuration bodies use layout `where` fields",
        ));
    }
    let mut at = at + 1;
    let mut result = Vec::new();
    let mut seen = BTreeSet::new();
    while at < tokens.tokens.len() {
        let field_column = tokens.column(at);
        if field_column <= declaration_column {
            return Err(Failure::input(
                "lakefile.lean: configuration fields must be indented",
            ));
        }
        let Some(TokenKind::Ident(field)) = tokens.tokens.get(at).map(|token| &token.kind) else {
            return Err(Failure::input(
                "lakefile.lean: expected a configuration field",
            ));
        };
        let field = field.to_display_string();
        if !seen.insert(field.clone()) {
            return Err(Failure::unsupported(format!(
                "lakefile.lean: repeated configuration field `{field}` is not supported"
            )));
        }
        if !tokens.symbol(at + 1, ":=") || at + 2 == tokens.tokens.len() {
            return Err(Failure::input(format!(
                "lakefile.lean: field `{field}` needs `:=` and a Lean expression"
            )));
        }
        let start = tokens.offset(at + 2);
        at += 2;
        let mut depth = 0usize;
        while at < tokens.tokens.len() {
            if depth == 0 && tokens.new_line(at) && tokens.column(at) <= field_column {
                if tokens.column(at) != field_column
                    || !matches!(tokens.tokens[at].kind, TokenKind::Ident(_))
                    || !tokens.symbol(at + 1, ":=")
                {
                    return Err(Failure::unsupported(
                        "lakefile.lean: unsupported configuration field layout or trailing command",
                    ));
                }
                break;
            }
            if let TokenKind::Symbol(symbol) = &tokens.tokens[at].kind {
                match symbol.as_str() {
                    "(" | "[" | "{" | "#[" | "@[" => depth += 1,
                    ")" | "]" | "}" => {
                        depth = depth.checked_sub(1).ok_or_else(|| {
                            Failure::input("lakefile.lean: unmatched field-expression delimiter")
                        })?;
                    }
                    ";" if depth == 0
                        && matches!(
                            tokens.tokens.get(at + 1).map(|token| &token.kind),
                            Some(TokenKind::Ident(_))
                        )
                        && tokens.symbol(at + 2, ":=") =>
                    {
                        return Err(Failure::unsupported(
                            "lakefile.lean: put configuration fields on separate indented lines",
                        ));
                    }
                    _ => {}
                }
            }
            at += 1;
        }
        if depth != 0 {
            return Err(Failure::input(
                "lakefile.lean: unclosed field-expression delimiter",
            ));
        }
        result.push((field, &source[start..tokens.offset(at)]));
    }
    Ok(result)
}

fn parse(source: &[u8]) -> Result<ParsedConfig, Failure> {
    if source.len() > MAX_CONFIG_BYTES {
        return Err(Failure::new("resource", "lakefile.lean exceeds 64 KiB"));
    }
    let original =
        std::str::from_utf8(source).map_err(|_| Failure::input("lakefile.lean is not UTF-8"))?;
    let header = parse_source_header(source).map_err(|error| Failure::input(error.to_string()))?;
    if header.prelude || header.module_system || header.imports != [Name::from_components(["Lake"])]
    {
        return Err(Failure::unsupported(
            "lakefile.lean: this configuration slice requires the ordinary `import Lake` header only",
        ));
    }
    fln::source_check::modules::validate_source_header(
        &Name::from_components(["lakefile"]),
        &header,
    )
    .map_err(|error| {
        let (class, authority, _) = error.disposition();
        Failure {
            class,
            detail: format!("lakefile.lean: {error}"),
            authority,
        }
    })?;
    let mut grammar = grammar()?;
    let commands = with_grammar(&grammar.grammar(), || {
        command_scope::partition(&source[header.body_start.0..])
    })
    .map_err(|error| Failure::input(format!("lakefile.lean: {error}")))?;
    if commands.len() > MAX_CONFIG_COMMANDS {
        return Err(Failure::new(
            "resource",
            "lakefile.lean exceeds 1024 commands",
        ));
    }
    let mut parsed = ParsedConfig {
        config: LakeConfig {
            name: String::new(),
            default_targets: Vec::new(),
            lean_toolchain: None,
            src_dir: PathBuf::from("."),
            build_dir: PathBuf::from(".lake/build"),
            requires: Vec::new(),
            targets: Vec::new(),
            format: LakeConfigFormat::Lean,
        },
        program: String::new(),
        fields: Vec::new(),
    };
    let mut scope_depth = 0usize;
    let mut lake_open = false;
    let mut dsl_open = false;
    let mut next = 0;
    let mut target_names = BTreeSet::new();
    for (_, command) in commands {
        let active = grammar.grammar();
        let tokens = Tokens::read(command, active.table())?;
        let (head, attributes) = tokens.head()?;
        let keyword = tokens.spelling(head).unwrap_or("");
        if LAKE_COMMANDS.contains(&keyword) {
            if !matches!(keyword, "package" | "lean_lib") {
                return Err(Failure::unsupported(format!(
                    "lakefile.lean: `{keyword}` configuration is not implemented"
                )));
            }
            if !dsl_open || scope_depth != 0 {
                return Err(Failure::unsupported(
                    "lakefile.lean: package and lean_lib must be at top level after `open Lake DSL`",
                ));
            }
            let mut default_target = false;
            for attribute in attributes {
                if keyword != "lean_lib"
                    || attribute.len() != 1
                    || tokens.spelling(attribute.start) != Some("default_target")
                {
                    return Err(Failure::unsupported(
                        "lakefile.lean: only @[default_target] on lean_lib is supported",
                    ));
                }
                default_target = true;
            }
            let declaration = tokens.name(head + 1)?;
            let library = if keyword == "package" {
                if !parsed.config.name.is_empty() {
                    return Err(Failure::input(
                        "lakefile.lean: multiple package declarations",
                    ));
                }
                parsed.config.name = declaration.clone();
                None
            } else {
                if parsed.config.name.is_empty() {
                    return Err(Failure::input("lakefile.lean: lean_lib precedes package"));
                }
                // The existing module planner accepts textual path components only.
                name(&declaration)?;
                if !target_names.insert(declaration.clone()) {
                    return Err(Failure::input(format!(
                        "lakefile.lean: target `{declaration}` is already declared"
                    )));
                }
                if parsed.config.targets.len() >= MAX_MODULES {
                    return Err(Failure::new(
                        "resource",
                        "lakefile.lean exceeds 256 libraries",
                    ));
                }
                let index = parsed.config.targets.len();
                parsed.config.targets.push(LakeTarget {
                    name: declaration.clone(),
                    kind: TargetKind::Library,
                    roots: vec![declaration.clone()],
                    src_dir: None,
                });
                if default_target {
                    parsed.config.default_targets.push(declaration.clone());
                }
                Some(index)
            };
            let declaration_column = tokens.column(0).min(tokens.column(head));
            for (field, expression) in fields(command, &tokens, head + 2, declaration_column)? {
                let slot = match (library, field.as_str()) {
                    (None, "srcDir") => PathSlot::Source,
                    (None, "buildDir") => PathSlot::Build,
                    (Some(index), "srcDir") => PathSlot::Library(index),
                    _ => {
                        return Err(Failure::unsupported(format!(
                            "lakefile.lean: `{keyword}` field `{field}` is not implemented"
                        )));
                    }
                };
                let generated = fresh_name(original, &mut next);
                let expression = std::str::from_utf8(expression)
                    .map_err(|_| Failure::input("lakefile.lean: expression is not UTF-8"))?;
                parsed.program.push_str(&format!(
                    "\ndef {generated} : _root_.System.FilePath := (\n{expression}\n)\n"
                ));
                parsed.fields.push(PathField {
                    slot,
                    declaration: generated,
                    label: format!("{keyword} {declaration}.{field}"),
                });
            }
            continue;
        }
        if let Some(scope) = with_grammar(&active, || command_scope::parse(command))
            .map_err(|error| Failure::input(format!("lakefile.lean: {error}")))?
        {
            grammar.apply(&scope);
            match scope {
                ScopeCommand::Open(names) if scope_depth == 0 => {
                    let mut ordinary = Vec::new();
                    for name in names {
                        let text = name.to_display_string();
                        if text == "Lake" {
                            lake_open = true;
                        } else if text == "Lake.DSL" || (text == "DSL" && lake_open) {
                            dsl_open = true;
                        } else {
                            ordinary.push(text);
                        }
                    }
                    if !ordinary.is_empty() {
                        parsed
                            .program
                            .push_str(&format!("\nopen {}\n", ordinary.join(" ")));
                    }
                    continue;
                }
                ScopeCommand::OpenScoped(names)
                    if scope_depth == 0 && names == [Name::from_components(["Lake", "DSL"])] =>
                {
                    dsl_open = true;
                    continue;
                }
                ScopeCommand::Namespace(_)
                | ScopeCommand::Section(_)
                | ScopeCommand::SectionWithModifiers { .. } => scope_depth += 1,
                ScopeCommand::End(_) => {
                    scope_depth = scope_depth
                        .checked_sub(1)
                        .ok_or_else(|| Failure::input("lakefile.lean: unmatched end"))?;
                }
                _ => {}
            }
        } else if let Ok(parsed_command) =
            with_grammar(&active, || fln_parse::parse_source_command(command))
        {
            // Follow only native parser/scoping state here, so a later field may contain
            // the file's notation tokens. The engine replays and checks the original
            // declarations; successful lexical registration grants no logical authority.
            grammar
                .declare(parsed_command.syntax())
                .map_err(|feature| Failure::unsupported(format!("lakefile.lean: {feature}")))?;
        }
        parsed.program.push('\n');
        parsed.program.push_str(
            std::str::from_utf8(command)
                .map_err(|_| Failure::input("lakefile.lean: command is not UTF-8"))?,
        );
        parsed.program.push('\n');
    }
    if parsed.config.name.is_empty() {
        return Err(Failure::input("lakefile.lean: missing package declaration"));
    }
    if scope_depth != 0 {
        return Err(Failure::input(
            "lakefile.lean: unclosed namespace or section",
        ));
    }
    Ok(parsed)
}

fn complete<T>(outcome: Outcome<T>, phase: &str) -> Result<T, Failure> {
    match outcome {
        Outcome::Complete(value) => Ok(value),
        Outcome::Inconclusive(reason) => Err(Failure::new(
            "inconclusive",
            format!("lakefile.lean: {phase}: {reason:?}"),
        )),
        Outcome::InternalFault(fault) => Err(Failure::new(
            "internal-fault",
            format!("lakefile.lean: {phase}: {fault:?}"),
        )),
    }
}

fn evaluate(
    mut parsed: ParsedConfig,
    engine: fln::Engine,
    limits: fln::EngineExecutionLimits,
) -> Result<LakeConfig, Failure> {
    let options = fln::KVMap::new();
    let checked = engine
        .check_source_files(
            &[parsed.program.as_bytes()],
            &options,
            fln::SourceCheckLimits::new(limits.admission()),
        )
        .map_err(|error| {
            let (class, authority, _) = error.disposition();
            Failure {
                class,
                detail: format!("lakefile.lean: {error}"),
                authority,
            }
        })?;
    let checked = complete(checked, "checking configuration")?;
    for field in parsed.fields {
        let mut next = 0;
        let projection = loop {
            let name = format!("{}_result_{next}", field.declaration);
            if !checked
                .engine
                .environment()
                .contains(&Name::from_components([name.as_str()]))
            {
                break name;
            }
            next += 1;
        };
        let source = format!(
            "def {projection} : _root_.String := _root_.System.FilePath.toString _root_.{}",
            field.declaration
        );
        let execution = checked
            .engine
            .execute_source_definition(source.as_bytes(), &options, limits)
            .map_err(|error| {
                let (class, authority, _) = execution_error_disposition(&error);
                Failure {
                    class,
                    detail: format!("lakefile.lean: {}: {error}", field.label),
                    authority,
                }
            })?;
        let execution = complete(execution, &field.label)?;
        let value = match &execution.exit {
            fln::VmExit::Returned(_) => match fln::closed_vm_value(&execution.exit) {
                Ok(Some(fln::ClosedVmValue::String(value))) => value,
                other => {
                    return Err(Failure::new(
                        "internal-fault",
                        format!(
                            "lakefile.lean: {} did not return its checked String projection: {other:?}",
                            field.label
                        ),
                    ));
                }
            },
            exit => {
                return Err(Failure::new(
                    "execution",
                    format!("lakefile.lean: {} did not return: {exit:?}", field.label),
                ));
            }
        };
        let path = PathBuf::from(value);
        relative_directory(&path)?;
        match field.slot {
            PathSlot::Source => parsed.config.src_dir = path,
            PathSlot::Build => parsed.config.build_dir = path,
            PathSlot::Library(index) => parsed.config.targets[index].src_dir = Some(path),
        }
    }
    Ok(parsed.config)
}

pub(super) fn load(
    root: &Path,
    jobs: std::num::NonZeroUsize,
    posture: ImportPosture,
) -> Result<LoadedConfig, Failure> {
    let path = root.join("lakefile.lean");
    check_path(root, &path, false)?;
    let bytes = read_bounded(&path, MAX_CONFIG_BYTES, "Lake configuration")?;
    let parsed = parse(&bytes)?;
    // No Lake implementation is imported or executed. This is the actual logical FilePath
    // and its Init dependency closure, checked by the same two seats as module compilation.
    let base = source_check::load_build_base(
        &[Name::from_components(["Init", "System", "FilePath"])],
        root,
        jobs,
        posture,
    )
    .map_err(|(class, detail, authority)| Failure {
        class,
        detail,
        authority,
    })?
    .ok_or_else(|| {
        Failure::new(
            "internal-fault",
            "FilePath import has no checked environment",
        )
    })?;
    let limits = fln::EngineExecutionLimits::for_user_program(fln::Budget::for_stack_bytes(
        SOURCE_RUN_KERNEL_STACK_BYTES,
    ));
    let mut config = evaluate(parsed, base.0.engine, limits)?;
    let toolchain = root.join("lean-toolchain");
    if toolchain.is_file() {
        check_path(root, &toolchain, false)?;
        let bytes = read_bounded(&toolchain, 4096, "Lean toolchain selection")?;
        let text = std::str::from_utf8(&bytes)
            .map_err(|_| Failure::input("lean-toolchain is not UTF-8"))?
            .trim();
        if !text.is_empty() {
            config.lean_toolchain = Some(text.to_owned());
        }
    }
    Ok(LoadedConfig {
        config,
        imports: base.1,
    })
}

#[cfg(test)]
#[path = "lake_config/tests.rs"]
mod tests;

#[cfg(test)]
#[path = "lake_config/reference.rs"]
mod reference_tests;

#[cfg(test)]
#[path = "lake_config/fixture.rs"]
mod fixture_tests;
