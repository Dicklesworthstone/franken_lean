//! The syntax a source file declares, on the production paths (bead `franken_lean-z8j.1.10`, stage
//! 4; `fln_parse::extensions`).
//!
//! A file's `syntax`, `notation`, `infix`-family and `declare_syntax_cat` commands extend the
//! grammar of the commands after them, as at the pin. [`SourceGrammar`] keeps that state for one
//! file: the paths enter it around every parse ([`SourceGrammar::enter`]), advance it on every
//! scope command ([`SourceGrammar::observe`]), and hand it every command first
//! ([`SourceGrammar::declare`]), which registers a syntax-declaring one in place of admitting it.
//! Native source module boundaries record exact descriptions and quoted templates in an
//! ordered environment journal. Import replay reconstructs a fresh grammar from only the
//! module's predecessors; local declarations and scope activation never become exports.
//! A notation's uses are then expanded before elaboration (`ParsedDefinition::expanded`), with
//! the hygiene the pin's `macro_rules` gives them (fln-elab resolves a template's macro-scoped
//! name as a global).
//!
//! The pin also checks a notation's right-hand side when it is declared (the quotation
//! precheck): a free identifier must name something. Here every free identifier must name a
//! global constant in the current scope. Literal lambda binders are tracked lexically: a
//! group's domain sees earlier binders, and its names scope over the following groups and
//! body. Binding constructs whose scope is not analysed remain typed refusals.
//!
//! A quotation's identifiers are pre-resolved where it is written (`Syntax.ident`'s
//! `preresolved`), and a use takes those constants before any of its own scope: a notation
//! declared in `namespace A` over `A.foo` means `A.foo` wherever it is used, a root `foo`
//! notwithstanding. So each identifier of a template is resolved when the notation is declared
//! and written `_root_.<constant>`, which names exactly that declaration; a name that resolves to
//! several declarations (which the pin would elaborate as overloaded) is refused as not
//! implemented.
//!
//! A `macro`, and `macro_rules` for a syntax the file declared, expand the same way
//! (`fln_parse::extensions`): one rule per kind, its template a quotation of the macro's category
//! with `$x` for the variables; their names are not prechecked (the pin refuses an unknown one
//! only where it is used). A `macro` this does not translate (a `do` block, a sequence of
//! tactics, a splice) registers its syntax without a rule, `elab` is not read, and a second rule
//! for one kind removes the first (the pin tries the newest first): in each case the uses reach
//! the elaborator unexpanded and are refused there. Artifact imports' own syntax (Init's notations, as the grammar census lists them)
//! is not entered: their expansions are not in the census, so their uses would reach the
//! elaborator unexpanded too, and terms the hand grammar reads, such as `{}`, would become the
//! pin's `choice` between a notation and a structure instance.

use crate::EngineExecutionError;
use crate::Environment;
use fln_core::name::Name;
use fln_elab::source::scope::SourceScope;
use fln_parse::command_scope::ScopeCommand;
use fln_parse::extensions::{FileGrammar, NotationRule, with_grammar};
use fln_syntax::tree::Syntax;
use std::collections::BTreeMap;
use std::sync::Arc;

mod journal;
mod quotation_scope;
use quotation_scope::preresolve;

/// Tactic kinds that bind names (the pin's binder reads the identifier as written, never its
/// pre-resolution): a tactic template holding one is not prechecked here.
const TACTIC_BINDING: [&str; 16] = [
    "intro",
    "intros",
    "introMatch",
    "renameI",
    "obtain",
    "rcases",
    "rintro",
    "cases",
    "induction",
    "case",
    "case'",
    "tacticNext_=>_",
    "tacticHave_",
    "tacticLet_",
    "tacticShow_",
    "tacticSuffices_",
];

/// The command kinds that declare syntax, or a rule that expands it.
const DECLARING: [&str; 7] = [
    "syntax",
    "syntaxAbbrev",
    "notation",
    "mixfix",
    "syntaxCat",
    "macro",
    "macro_rules",
];

/// Node kinds that bind names in a term, or hold a name that is no global reference (`.foo`, a
/// field, a named argument, a projection). `quotation_scope` handles supported binder
/// shapes before applying this refusal list.
const BINDING: [&str; 15] = [
    "fun",
    "forall",
    "depArrow",
    "let",
    "have",
    "match",
    "letrec",
    "show",
    "suffices",
    "dotIdent",
    "structInst",
    "namedArgument",
    "proj",
    "pipeProj",
    "namedPattern",
];

pub(crate) struct SourceGrammar {
    file: FileGrammar,
    rule_sources: BTreeMap<Name, Arc<[u8]>>,
    module_system: bool,
    declared_syntax: bool,
}

impl SourceGrammar {
    /// The seed grammar: Init's tokens and the file's own declarations, without
    /// the census's parser registrations whose executable expansions are absent.
    pub(crate) fn implicit_init() -> SourceGrammar {
        SourceGrammar {
            file: FileGrammar::new(false, &[], Some(Name::anonymous()))
                .expect("invariant: the grammar census describes Init")
                .own_syntax_only(),
            rule_sources: BTreeMap::new(),
            module_system: false,
            declared_syntax: false,
        }
    }

    /// Native source imports carry exact descriptions and templates in the
    /// environment journal. No unknown `.olean` extension is interpreted here.
    pub(crate) fn for_environment(
        environment: &Environment,
        module: Option<&Name>,
        module_system: bool,
    ) -> Result<Self, EngineExecutionError> {
        let mut grammar = Self::for_module(module, module_system);
        if module_system && journal::present(environment) {
            return Err(Self::module_phase_refusal());
        }
        journal::load(environment, &mut grammar.file)?;
        Ok(grammar)
    }

    pub(crate) fn for_module(module: Option<&Name>, module_system: bool) -> Self {
        Self {
            file: FileGrammar::new(
                false,
                &[],
                Some(module.cloned().unwrap_or_else(Name::anonymous)),
            )
            .expect("invariant: the grammar census describes Init")
            .own_syntax_only(),
            rule_sources: BTreeMap::new(),
            module_system,
            declared_syntax: false,
        }
    }

    fn module_phase_refusal() -> EngineExecutionError {
        EngineExecutionError::NotImplemented {
            feature: "native source grammar imports/exports with module-system visibility and meta phases",
        }
    }

    pub(crate) fn import_native(
        &mut self,
        module: &fln_parse::extensions::NativeSyntaxModule,
    ) -> Result<(), EngineExecutionError> {
        if self.module_system && !module.is_empty() {
            return Err(Self::module_phase_refusal());
        }
        self.file
            .import_native(module)
            .map_err(|feature| EngineExecutionError::NotImplemented { feature })
    }

    pub(crate) fn export_native(
        &self,
    ) -> Result<fln_parse::extensions::NativeSyntaxModule, EngineExecutionError> {
        let exported = self
            .file
            .export_native()
            .map_err(|feature| EngineExecutionError::NotImplemented { feature })?;
        if self.module_system && !exported.is_empty() {
            return Err(Self::module_phase_refusal());
        }
        Ok(exported)
    }

    /// Publish only at a successfully completed source-module boundary. The
    /// existing module journal replay and exact session cache then retain it.
    pub(crate) fn record(
        &self,
        environment: &Environment,
    ) -> Result<Environment, EngineExecutionError> {
        journal::publish(
            environment,
            &self.export_native()?,
            &self.rule_sources,
            self.declared_syntax,
        )
    }

    pub(crate) fn extend_scopes(&self, scopes: &mut super::scopes::Scopes) {
        for name in self.file.native_namespace_anchors() {
            scopes.observe_syntax(&name);
        }
    }

    /// Run `parse` with this file's grammar in effect.
    pub(crate) fn enter<R>(&self, parse: impl FnOnce() -> R) -> R {
        with_grammar(&self.file.grammar(), parse)
    }

    /// Advance past one scope command.
    pub(crate) fn observe(&mut self, scope: &ScopeCommand) {
        self.file.apply(scope);
    }

    /// Register `command` if it declares syntax: `Ok(true)` then, and the caller admits nothing
    /// for it. `Ok(false)` for every other command (a parse refusal included: the caller's own
    /// parse reports it). `resolve` says what a name names in the current scope ([`resolver`]).
    pub(crate) fn declare(
        &mut self,
        command: &[u8],
        resolve: impl Fn(&Name) -> Resolution,
    ) -> Result<bool, EngineExecutionError> {
        if !may_declare(command) {
            return Ok(false);
        }
        let Ok(parsed) = self.enter(|| fln_parse::parse_source_command(command)) else {
            return Ok(false);
        };
        let syntax = parsed.syntax();
        let declaring = matches!(syntax,
        Syntax::Node { kind, .. }
            if DECLARING.iter().any(|leaf| {
                *kind == Name::from_components(["Lean", "Parser", "Command", leaf])
            }));
        if !declaring {
            return Ok(false);
        }
        let before: BTreeMap<Name, NotationRule> = self
            .file
            .rules()
            .map(|(kind, rule)| (kind.clone(), rule.clone()))
            .collect();
        self.file
            .declare(syntax)
            .map_err(|feature| EngineExecutionError::NotImplemented { feature })?;
        // Each rule the command added or replaced is pre-resolved where it is declared.
        let mut templates = Vec::new();
        for (kind, rule) in self.file.rules() {
            if before.get(kind) != Some(rule) {
                templates.push((kind.clone(), preresolve(rule, &resolve)?));
            }
        }
        for (kind, template) in templates {
            self.file.set_rule_template(&kind, template);
            // Raw identifier spans address the parser's normalized view,
            // including inside multiline CRLF quotations.
            self.rule_sources.insert(
                kind,
                Arc::from(parsed.source_view().normalized().as_bytes()),
            );
        }
        self.declared_syntax = true;
        if self.module_system {
            // Module-system syntax declarations create public meta definitions.
            // Their extra module-use/phase provenance is not yet represented by
            // the native quoted-template journal.
            return Err(Self::module_phase_refusal());
        }
        Ok(true)
    }
}

/// What a template's identifier names where the notation is declared.
pub(crate) enum Resolution {
    /// Exactly this declaration.
    Global(Name),
    /// Nothing: the quotation precheck refuses the notation.
    Nothing,
    /// Several declarations, or the scope tables could not be read.
    Undetermined,
    /// Not resolved here: the preflight, which parses and elaborates nothing.
    Unchecked,
}

/// Name resolution as the elaborator resolves a global (`resolveGlobalName`, with the
/// environment's aliases and protected names) in `scope`.
pub(crate) fn resolver<'e>(
    environment: &'e Environment,
    scope: &'e SourceScope,
) -> impl Fn(&Name) -> Resolution + 'e {
    let tables = fln_elab::aliases::AliasTable::read(environment)
        .ok()
        .zip(fln_elab::protected_names::ProtectedNames::read(environment).ok());
    move |name| {
        let Some((aliases, protected)) = &tables else {
            return Resolution::Undetermined;
        };
        match scope.resolve_with_aliases(
            name,
            |candidate| environment.contains(candidate),
            aliases,
            protected,
        ) {
            Ok(Some(global)) => Resolution::Global(global),
            Ok(None) => Resolution::Nothing,
            Err(_) => Resolution::Undetermined,
        }
    }
}

/// Whether `command` holds a declaring keyword as a word: a cheap filter, so every other command
/// is parsed once, by the path that admits it.
fn may_declare(command: &[u8]) -> bool {
    const KEYWORDS: [&[u8]; 10] = [
        b"syntax",
        b"notation",
        b"infix",
        b"infixl",
        b"infixr",
        b"prefix",
        b"postfix",
        b"declare_syntax_cat",
        b"macro",
        b"macro_rules",
    ];
    let word =
        |byte: u8| byte.is_ascii_alphanumeric() || byte == b'_' || byte == b'.' || byte >= 0x80;
    let mut at = 0;
    while at < command.len() {
        if word(command[at]) {
            let start = at;
            while at < command.len() && word(command[at]) {
                at += 1;
            }
            if KEYWORDS.contains(&&command[start..at]) {
                return true;
            }
        } else {
            at += 1;
        }
    }
    false
}
