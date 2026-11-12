//! Pinned Lean 4.32.0 frontend quotation-context hygiene seeding (`Command.lean:598-642`,
//! `Declaration.lean:43-100,150-192,239-255`, `DefView.lean:165-220`, `MutualDef.lean:1566`).
//!
//! Top-level source commands seed `quotContext` from `hash(trimmed_command_text).toUInt32`
//! (`Stage 1`), while declaration elaborators re-seed `quotContext` from the declaration
//! name(s) (`Stage 2`: `Array.hash` for def-like/mutual declarations, `Name.hash` for
//! `axiom`/`inductive`/`classInductive`/`structure`). Collisions within a module probe
//! `idx + 1` in `used_quot_ctxts`, and each `withInitQuotContext` resets `currMacroScope`
//! to `FIRST_FRONTEND_MACRO_SCOPE` (`1`) and `nextMacroScope` to `2`, restoring the outer
//! `nextMacroScope` when the top-level command finishes.
#![forbid(unsafe_code)]

use crate::imported_macros::{MacroContext, MacroState};
use fln_core::lean_hash::{mix_hash, string_hash};
use fln_core::name::hygiene::{FIRST_FRONTEND_MACRO_SCOPE, extract_macro_scopes};
use fln_core::name::{LeafView, Name};
use fln_syntax::tree::Syntax;
use std::collections::BTreeSet;

/// Lean 4's `instHashableArray` seed (`Init/Data/Array/Basic.lean`: `foldl mixHash 7`).
const ARRAY_HASH_SEED: u64 = 7;

/// Lean 4's initial frontend `nextMacroScope` (`firstFrontendMacroScope + 1 == 2`).
pub(super) const INITIAL_NEXT_MACRO_SCOPE: u64 = FIRST_FRONTEND_MACRO_SCOPE + 1;

pub(super) struct CommandHygiene {
    module: Name,
    used_quot_ctxts: BTreeSet<Name>,
    outer_macro_scope: u64,
    active_context: MacroContext,
}

impl CommandHygiene {
    pub(super) fn new(module: Name, base: &MacroContext, state: &mut MacroState) -> Self {
        state.macro_scope = INITIAL_NEXT_MACRO_SCOPE;
        let mut active_context = base.clone();
        active_context.quotation_context = module.clone();
        active_context.current_macro_scope = FIRST_FRONTEND_MACRO_SCOPE;
        Self {
            module,
            used_quot_ctxts: BTreeSet::new(),
            outer_macro_scope: INITIAL_NEXT_MACRO_SCOPE,
            active_context,
        }
    }

    pub(super) fn active_context(&self) -> &MacroContext {
        &self.active_context
    }

    pub(super) fn finish_command(&mut self, state: &mut MacroState) {
        state.macro_scope = self.outer_macro_scope;
        self.active_context.quotation_context = self.module.clone();
        self.active_context.current_macro_scope = FIRST_FRONTEND_MACRO_SCOPE;
    }

    /// Lean 4.32.0 `withInitQuotContext` (`Command.lean:605-624`). When `hint` is `None`,
    /// the active quotation context and macro scope counter remain unchanged.
    pub(super) fn enter_quot_context(&mut self, hint: Option<u64>, state: &mut MacroState) {
        let Some(hint) = hint else {
            return;
        };
        let mut idx = u64::from(hint as u32);
        loop {
            let candidate = Name::str(Name::num(self.module.clone(), idx), "_hygCtx");
            if self.used_quot_ctxts.insert(candidate.clone()) {
                self.active_context.quotation_context = candidate;
                break;
            }
            idx = idx.saturating_add(1);
        }
        self.active_context.current_macro_scope = FIRST_FRONTEND_MACRO_SCOPE;
        state.macro_scope = INITIAL_NEXT_MACRO_SCOPE;
    }
}

/// Stage 1 hint (`Command.lean:636-641`): `hash` of the command's non-trivia substring,
/// ASCII-trimmed on normalized LF text. Call inside `grammar.enter(...)`.
pub(super) fn command_quot_hint(source: &[u8]) -> Option<u64> {
    fln_parse::command_scope::command_quot_hint_text(source)
        .ok()
        .flatten()
        .map(|text| string_hash(&text))
}

/// Stage 2 hint for a single `Lean.Parser.Command.declaration` (`Declaration.lean:166-172`,
/// `DefView.lean:165-220`, `MutualDef.lean:1566`). Anonymous `instance` declarations have
/// no syntactic `declId` prior to type elaboration and therefore return `None`, retaining
/// Stage 1's command-text quotation context.
pub(super) fn declaration_quot_hint(syntax: &Syntax) -> Option<u64> {
    let decl = declaration_inner(syntax)?;
    let Syntax::Node {
        kind: decl_kind,
        args: decl_args,
        ..
    } = decl
    else {
        return None;
    };
    let kind_leaf = command_parser_leaf(decl_kind)?;
    match kind_leaf {
        "example" => {
            let example = Name::from_components(["_example"]);
            Some(array_hash(std::iter::once(&example)))
        }
        "abbrev" | "definition" | "theorem" | "opaque" => {
            let raw = decl_id_ident(decl_args.get(1)?)?;
            let short = short_decl_name(raw);
            Some(array_hash(std::iter::once(&short)))
        }
        "instance" => {
            let Syntax::Node { args: opt_args, .. } = decl_args.get(3)? else {
                return None;
            };
            let raw = decl_id_ident(opt_args.first()?)?;
            let short = short_decl_name(raw);
            Some(array_hash(std::iter::once(&short)))
        }
        "axiom" | "inductive" | "classInductive" | "structure" => {
            let raw = decl_id_ident(decl_args.get(1)?)?;
            let short = short_decl_name(raw);
            Some(short.hash())
        }
        _ => None,
    }
}

/// Stage 2 hint for a `mutual ... end` block (`Declaration.lean:188-192,239-255,289-297`,
/// `MutualDef.lean:1566`). `mutual inductive` / `structure` blocks do not enter a second
/// `withInitQuotContext` at the pin (`elabMutualInductive`) and return `None`.
pub(super) fn mutual_quot_hint(members: &[Syntax]) -> Option<u64> {
    if members.is_empty() || !members.iter().all(is_def_like_declaration) {
        return None;
    }
    let mut raw_names = Vec::with_capacity(members.len());
    for member in members {
        raw_names.push(def_like_raw_name(member)?);
    }
    let split: Option<Vec<(Name, Name)>> = raw_names.iter().map(expand_decl_namespace).collect();
    if let Some(split) = split {
        let prefixes: Vec<&Name> = split.iter().map(|(ns, _)| ns).collect();
        let common = common_name_prefix(&prefixes);
        if !common.is_anonymous() {
            let stripped: Vec<Name> = raw_names
                .iter()
                .map(|raw| strip_name_prefix_preserving_scopes(raw, &common))
                .collect();
            return Some(array_hash(stripped.iter()));
        }
    }
    Some(array_hash(raw_names.iter()))
}

fn array_hash<'a>(names: impl IntoIterator<Item = &'a Name>) -> u64 {
    names
        .into_iter()
        .fold(ARRAY_HASH_SEED, |acc, name| mix_hash(acc, name.hash()))
}

fn declaration_inner(syntax: &Syntax) -> Option<&Syntax> {
    let Syntax::Node { kind, args, .. } = syntax else {
        return None;
    };
    if command_parser_leaf(kind) != Some("declaration") || args.len() != 2 {
        return None;
    }
    Some(&args[1])
}

fn is_def_like_declaration(syntax: &Syntax) -> bool {
    let Some(Syntax::Node { kind, .. }) = declaration_inner(syntax) else {
        return false;
    };
    matches!(
        command_parser_leaf(kind),
        Some("abbrev" | "definition" | "theorem" | "opaque" | "instance" | "example")
    )
}

fn def_like_raw_name(syntax: &Syntax) -> Option<Name> {
    let Syntax::Node { kind, args, .. } = declaration_inner(syntax)? else {
        return None;
    };
    match command_parser_leaf(kind)? {
        "example" => Some(Name::from_components(["_example"])),
        "abbrev" | "definition" | "theorem" | "opaque" => decl_id_ident(args.get(1)?).cloned(),
        "instance" => {
            let Syntax::Node { args: opt_args, .. } = args.get(3)? else {
                return None;
            };
            decl_id_ident(opt_args.first()?).cloned()
        }
        _ => None,
    }
}

fn command_parser_leaf(kind: &Name) -> Option<&str> {
    let LeafView::Str(leaf) = kind.leaf_view() else {
        return None;
    };
    let parent = kind.parent();
    if parent == Name::from_components(["Lean", "Parser", "Command"]) {
        Some(leaf)
    } else {
        None
    }
}

fn decl_id_ident(decl_id: &Syntax) -> Option<&Name> {
    match decl_id {
        Syntax::Ident { val, .. } => Some(val),
        Syntax::Node { args, .. } => match args.first()? {
            Syntax::Ident { val, .. } => Some(val),
            _ => None,
        },
        _ => None,
    }
}

fn short_decl_name(raw: &Name) -> Name {
    expand_decl_namespace(raw).map_or_else(|| raw.clone(), |(_, short)| short)
}

/// Lean 4.32.0 `expandDeclNamespace?` (`Declaration.lean:90-99`).
fn expand_decl_namespace(raw: &Name) -> Option<(Name, Name)> {
    let Ok(mut view) = extract_macro_scopes(raw) else {
        return None;
    };
    if has_root_prefix(&view.name) {
        return None;
    }
    let LeafView::Str(short_name) = view.name.leaf_view() else {
        return None;
    };
    let prefix = view.name.parent();
    if prefix.is_anonymous() {
        return None;
    }
    view.name = Name::str(Name::anonymous(), short_name);
    Some((prefix, view.review()))
}

fn has_root_prefix(name: &Name) -> bool {
    let mut cursor = name.clone();
    while !cursor.is_anonymous() {
        let parent = cursor.parent();
        if parent.is_anonymous() {
            return matches!(cursor.leaf_view(), LeafView::Str("_root_"));
        }
        cursor = parent;
    }
    false
}

#[derive(Clone, PartialEq, Eq)]
enum Component {
    Str(String),
    Num(u64),
}

fn components(name: &Name) -> Vec<Component> {
    let mut out = Vec::new();
    let mut cursor = name.clone();
    while !cursor.is_anonymous() {
        match cursor.leaf_view() {
            LeafView::Anonymous => break,
            LeafView::Str(s) => out.push(Component::Str(s.to_owned())),
            LeafView::Num(n) => out.push(Component::Num(n)),
        }
        cursor = cursor.parent();
    }
    out.reverse();
    out
}

fn rebuild(parts: &[Component]) -> Name {
    let mut out = Name::anonymous();
    for part in parts {
        out = match part {
            Component::Str(s) => Name::str(out, s),
            Component::Num(n) => Name::num(out, *n),
        };
    }
    out
}

fn common_name_prefix(names: &[&Name]) -> Name {
    let Some((first, rest)) = names.split_first() else {
        return Name::anonymous();
    };
    let mut common = components(first);
    for other in rest {
        let other_parts = components(other);
        let shared = common
            .iter()
            .zip(&other_parts)
            .take_while(|(a, b)| a == b)
            .count();
        common.truncate(shared);
        if common.is_empty() {
            break;
        }
    }
    rebuild(&common)
}

fn strip_name_prefix_preserving_scopes(raw: &Name, prefix: &Name) -> Name {
    let Ok(mut view) = extract_macro_scopes(raw) else {
        return raw.clone();
    };
    let full = components(&view.name);
    let pre = components(prefix);
    if full.len() > pre.len() && full[..pre.len()] == pre[..] {
        view.name = rebuild(&full[pre.len()..]);
        view.review()
    } else {
        raw.clone()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse_single(src: &str) -> Syntax {
        fln_parse::parse_source_command(src.as_bytes())
            .unwrap()
            .syntax()
            .clone()
    }

    #[test]
    fn command_and_declaration_quot_hints_match_pinned_lean_4_32_0_reference() {
        assert_eq!(
            command_quot_hint(b"-- comment\nmk_def second  -- trailing\n").map(|h| h as u32),
            Some(3_704_307_112)
        );
        assert_eq!(
            command_quot_hint(b"mk_pair fourth fifth\n").map(|h| h as u32),
            Some(4_017_002_702)
        );
        assert_eq!(
            command_quot_hint(b"open Sub in\r\nmk_def fromOpenIn\r\n").map(|h| h as u32),
            Some(1_307_713_751)
        );

        for (src, expected_u32) in [
            ("def first : Nat := 10", 1_810_816_117_u32),
            ("def scopedDef : Nat := 20", 3_987_389_639),
            ("def Sub.dottedDef : Nat := 25", 2_818_745_212),
            ("private def privDef : Nat := 35", 1_802_530_316),
            ("def third : Nat := 30", 3_438_629_280),
            ("def fourth : Nat := 4", 23_453_005),
            ("example : Nat := 1", 2_021_293_395),
            (
                "inductive Box : Type where\n  | mk : Nat -> Box",
                391_145_845,
            ),
            ("instance namedInst : True := True.intro", 3_186_941_139),
        ] {
            assert_eq!(
                declaration_quot_hint(&parse_single(src)).map(|h| h as u32),
                Some(expected_u32),
                "{src}"
            );
        }

        // Anonymous instances have no syntactic declId before type elaboration and keep Stage 1.
        assert_eq!(
            declaration_quot_hint(&parse_single("instance : True := True.intro")),
            None
        );
        // `_root_`-prefixed declarations are not split by `expandDeclNamespace?`.
        let root_def = parse_single("def _root_.Sub.dottedDef : Nat := 25");
        assert_ne!(
            declaration_quot_hint(&root_def).map(|h| h as u32),
            Some(2_818_745_212)
        );
        assert_eq!(
            declaration_quot_hint(&root_def),
            Some(array_hash(std::iter::once(&Name::from_components([
                "_root_",
                "Sub",
                "dottedDef"
            ]))))
        );

        let mutual_defs = fln_parse::command_scope::mutual::parse(
            b"mutual\ndef mutA : Nat -> Nat\n  | 0 => 1\n  | n + 1 => mutB n\ndef mutB : Nat -> Nat\n  | 0 => 2\n  | n + 1 => mutA n\nend",
        )
        .unwrap()
        .unwrap();
        assert_eq!(
            mutual_quot_hint(&mutual_defs).map(|h| h as u32),
            Some(2_676_876_227)
        );

        let mutual_inds = fln_parse::command_scope::mutual::parse(
            b"mutual\ninductive MutA : Type where\n  | mk : Nat -> MutA\ninductive MutB : Type where\n  | mk : MutA -> MutB\nend",
        )
        .unwrap()
        .unwrap();
        assert_eq!(mutual_quot_hint(&mutual_inds), None);
    }

    #[test]
    fn command_hygiene_probes_collisions_and_restores_outer_macro_scope() {
        let base = MacroContext {
            quotation_context: Name::anonymous(),
            current_macro_scope: 0,
            current_recursion_depth: 0,
            max_recursion_depth: 100,
        };
        let mut state = MacroState::default();
        let mut hygiene = CommandHygiene::new(Name::from_components(["UseMod"]), &base, &mut state);
        assert_eq!(state.macro_scope, 2);
        assert_eq!(hygiene.active_context().current_macro_scope, 1);

        let hint = Some(2_021_293_395_u64);
        hygiene.enter_quot_context(hint, &mut state);
        assert_eq!(
            hygiene.active_context().quotation_context,
            Name::str(
                Name::num(Name::from_components(["UseMod"]), 2_021_293_395),
                "_hygCtx"
            )
        );
        state.macro_scope = 9;

        // Second `example` collides on 2021293395 and probes +1 -> 2021293396, resetting nextMacroScope to 2.
        hygiene.enter_quot_context(hint, &mut state);
        assert_eq!(
            hygiene.active_context().quotation_context,
            Name::str(
                Name::num(Name::from_components(["UseMod"]), 2_021_293_396),
                "_hygCtx"
            )
        );
        assert_eq!(state.macro_scope, 2);

        state.macro_scope = 11;
        hygiene.finish_command(&mut state);
        assert_eq!(state.macro_scope, 2);
    }
}
