//! `Syntax` — the lossless green tree (plan §9; bead franken_lean-tkr2).
//!
//! The four forms, read off `Init/Prelude.lean:4943` at the pin rather than recalled:
//!
//! ```text
//! inductive Syntax where
//!   | missing : Syntax
//!   | node  (info : SourceInfo) (kind : SyntaxNodeKind) (args : Array Syntax) : Syntax
//!   | atom  (info : SourceInfo) (val : String) : Syntax
//!   | ident (info : SourceInfo) (rawVal : Substring.Raw) (val : Name)
//!           (preresolved : List Syntax.Preresolved) : Syntax
//! ```
//!
//! with `abbrev SyntaxNodeKind := Name` (line 4919) — which is why this module could not
//! exist until the `fln-syntax -> fln-core` edge was declared (bead franken_lean-vrmi).
//! A `String` or interned-integer kind would have been a substitute for `Name`, not a
//! subset of it, and it would have diverged at exactly the point the Mirror façade has to
//! match.
//!
//! ## The leaves carry the bytes, and that is upstream's design not ours
//!
//! Prelude's own note on `node` (line 4954): "For nodes produced by the parser, the `info`
//! field is typically `Lean.SourceInfo.none`, and source information is stored in the
//! corresponding fields of identifiers and atoms." So a tree's relationship to the file is
//! entirely a property of its **leaves**, in order. That gives the composition law this
//! module is built on, and the one promised to whoever assembled the tree when the
//! attachment layer landed:
//!
//! > A tree is lossless **iff** its leaves, read left to right, are exactly the
//! > [`Attached`] sequence of an [`Attachment`] that tiles the file.
//!
//! So [`Syntax::reconstruct`] does not re-derive a walk. It collects the leaves, hands them
//! to [`Attachment`], and delegates — because a second byte-walk would be a second place
//! for the tiling law to be got wrong, and the one in `attach` is already plant-proved.
//! Node `info` deliberately contributes nothing to reconstruction: a node that claimed
//! bytes would double-count the leaves beneath it.
//!
//! ## Missing is a leaf that contributes nothing
//!
//! `missing` records that something was expected and absent. It is a leaf — it appears in
//! the sequence, so the error is visible to everything downstream — and it has no extent,
//! so the reconstruction cannot invent text the user did not write. Both halves matter and
//! each fails silently on its own.

use crate::attach::{Attached, attach_from_leaves};
use crate::source::{ByteSpan, SourceInfo, SourceText};
use fln_core::name::Name;

/// `Lean.SyntaxNodeKind` — `abbrev SyntaxNodeKind := Name` (Prelude.lean:4919).
pub type SyntaxNodeKind = Name;

/// `Lean.Syntax.Preresolved` (Prelude.lean:4930): the declarations an identifier could
/// refer to, populated by quotations.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Preresolved {
    Namespace { ns: Name },
    Decl { name: Name, fields: Vec<String> },
}

/// `Lean.Syntax` (Prelude.lean:4943), one variant per upstream constructor.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Syntax {
    /// A portion of the tree missing because of a parse error.
    Missing,
    /// An interior node. `info` is typically [`SourceInfo::None`] for parser output; the
    /// bytes live in the leaves.
    Node {
        info: SourceInfo,
        kind: SyntaxNodeKind,
        args: Vec<Syntax>,
    },
    /// A non-identifier atom: keyword, literal, punctuation, delimiter.
    Atom { info: SourceInfo, val: String },
    /// An identifier.
    ///
    /// `raw_val` is the literal substring from the input, held as a span for the reason
    /// given on [`ByteSpan`]: carrying a copy of the text would let a span and its text
    /// disagree about which text they belong to.
    Ident {
        info: SourceInfo,
        raw_val: ByteSpan,
        val: Name,
        preresolved: Vec<Preresolved>,
    },
}

impl Syntax {
    /// A node with no source info, which is what the parser produces.
    pub fn node(kind: SyntaxNodeKind, args: Vec<Syntax>) -> Syntax {
        Syntax::Node {
            info: SourceInfo::None,
            kind,
            args,
        }
    }

    pub fn atom(info: SourceInfo, val: impl Into<String>) -> Syntax {
        Syntax::Atom {
            info,
            val: val.into(),
        }
    }

    pub const fn is_missing(&self) -> bool {
        matches!(self, Syntax::Missing)
    }

    /// The node's kind, or `None` for a leaf.
    pub fn kind(&self) -> Option<&SyntaxNodeKind> {
        match self {
            Syntax::Node { kind, .. } => Some(kind),
            _ => None,
        }
    }

    /// The source info this form carries.
    pub fn info(&self) -> SourceInfo {
        match self {
            Syntax::Missing => SourceInfo::None,
            Syntax::Node { info, .. } | Syntax::Atom { info, .. } | Syntax::Ident { info, .. } => {
                *info
            }
        }
    }

    /// The leaves in source order, as attachment entries.
    ///
    /// This is the tree's entire relationship to the file. An interior node contributes
    /// nothing of its own — including when its `info` is `Original`, which the delaborator
    /// and quotations do set — because its bytes are exactly its descendants' bytes and
    /// counting both would double them.
    pub fn leaves(&self) -> Vec<Attached> {
        let mut out = Vec::new();
        self.collect_leaves(&mut out);
        out
    }

    fn collect_leaves(&self, out: &mut Vec<Attached>) {
        match self {
            Syntax::Missing => out.push(Attached::Missing {
                // A missing leaf has no position of its own; the attachment layer checks
                // placement against its neighbours, so `at` is the cursor by construction
                // when the tree was built from a well-formed attachment.
                at: crate::source::BytePos(0),
            }),
            Syntax::Node { args, .. } => {
                for arg in args {
                    arg.collect_leaves(out);
                }
            }
            Syntax::Atom { info, .. } | Syntax::Ident { info, .. } => {
                out.push(Attached::Token(*info));
            }
        }
    }

    /// Reconstruct the text this tree covers, byte for byte.
    ///
    /// Delegates to [`Attachment::reconstruct`] rather than walking the tree itself: the
    /// tiling law has one implementation, already plant-proved, and a second walk here
    /// would be a second place to get it wrong. `epilogue` is the file's trailing trivia,
    /// which belongs to the file rather than to any node — see the attachment module.
    pub fn reconstruct(&self, text: &SourceText, epilogue: ByteSpan) -> Option<Vec<u8>> {
        attach_from_leaves(self.leaves(), epilogue).reconstruct(text)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::attach::{Attachment, TokenExtent, attach};
    use crate::source::{BOM, BytePos};

    fn name(parts: &[&str]) -> Name {
        parts
            .iter()
            .fold(Name::anonymous(), |acc, part| Name::str(acc, *part))
    }

    fn text_of(raw: &[u8]) -> SourceText {
        SourceText::from_utf8(raw).expect("valid UTF-8")
    }

    /// Build a flat tree from an attachment: one node whose args are the entries. Enough to
    /// exercise the composition law without a parser.
    fn tree_from(attachment: &Attachment) -> Syntax {
        let args = attachment
            .entries()
            .iter()
            .map(|entry| match entry {
                Attached::Token(info) => Syntax::atom(*info, "t"),
                Attached::Missing { .. } => Syntax::Missing,
            })
            .collect();
        Syntax::node(name(&["Lean", "Parser", "Module"]), args)
    }

    /// **The composition law**, on the awkward corpus: a tree's leaves read left to right
    /// are exactly the attachment sequence, and the tree therefore reconstructs the
    /// original bytes.
    #[test]
    fn a_trees_leaves_are_its_attachment_and_it_reconstructs_byte_for_byte() {
        let cases: Vec<(Vec<u8>, Vec<&str>)> = vec![
            (b"a -- one\nb /- two -/ c".to_vec(), vec!["a", "b", "c"]),
            (b"-- header\ndef".to_vec(), vec!["def"]),
            ([BOM, b"a -- x\r\nb\nc\r\n"].concat(), vec!["a", "b", "c"]),
            (b"a\nb -- no final newline".to_vec(), vec!["a", "b"]),
            (b"-- only trivia\n".to_vec(), vec![]),
        ];
        for (raw, tokens) in cases {
            let text = text_of(&raw);
            let mut at = 0usize;
            let extents: Vec<TokenExtent> = tokens
                .iter()
                .map(|token| {
                    let offset = text.as_str()[at..].find(token).expect("present") + at;
                    at = offset + token.len();
                    TokenExtent::Present(
                        ByteSpan::new(BytePos(offset), BytePos(offset + token.len()))
                            .expect("forward"),
                    )
                })
                .collect();
            let attachment = attach(&text, &extents).expect("valid extents");
            let tree = tree_from(&attachment);

            // The law itself.
            assert_eq!(
                tree.leaves(),
                attachment.entries(),
                "the tree's leaves must BE the attachment sequence for {raw:?}"
            );
            // And therefore byte-identity with the ORIGINAL input.
            assert_eq!(
                tree.reconstruct(&text, attachment.epilogue()).as_deref(),
                Some(raw.as_slice()),
                "tree reconstruction lost bytes for {raw:?}"
            );
        }
    }

    /// An interior node contributes no bytes of its own, even when it carries an
    /// `Original` info — which the delaborator and quotations do set. Counting it would
    /// double the bytes of everything beneath it.
    #[test]
    fn an_interior_nodes_own_info_contributes_nothing() {
        let raw = b"ab";
        let text = text_of(raw);
        let extents = vec![
            TokenExtent::Present(ByteSpan::new(BytePos(0), BytePos(1)).expect("fwd")),
            TokenExtent::Present(ByteSpan::new(BytePos(1), BytePos(2)).expect("fwd")),
        ];
        let attachment = attach(&text, &extents).expect("valid");
        let leaves: Vec<Syntax> = attachment
            .entries()
            .iter()
            .map(|entry| match entry {
                Attached::Token(info) => Syntax::atom(*info, "t"),
                Attached::Missing { .. } => Syntax::Missing,
            })
            .collect();

        // A node whose own info spans the WHOLE file, wrapping leaves that already cover it.
        let spanning = SourceInfo::Original {
            leading: ByteSpan::empty_at(BytePos(0)),
            pos: BytePos(0),
            trailing: ByteSpan::empty_at(BytePos(2)),
            end_pos: BytePos(2),
        };
        let tree = Syntax::Node {
            info: spanning,
            kind: name(&["wrapper"]),
            args: leaves,
        };
        assert_eq!(tree.leaves().len(), 2, "only the leaves are collected");
        assert_eq!(
            tree.reconstruct(&text, attachment.epilogue()).as_deref(),
            Some(&raw[..]),
            "the node's own span must not be counted a second time"
        );
    }

    /// Missing is a leaf: present in the sequence, contributing no bytes. Both halves,
    /// because each failure is silent alone.
    #[test]
    fn a_missing_leaf_is_visible_and_contributes_nothing() {
        let raw = b"a  b";
        let text = text_of(raw);
        let extents = vec![
            TokenExtent::Present(ByteSpan::new(BytePos(0), BytePos(1)).expect("fwd")),
            TokenExtent::Missing(BytePos(2)),
            TokenExtent::Present(ByteSpan::new(BytePos(3), BytePos(4)).expect("fwd")),
        ];
        let attachment = attach(&text, &extents).expect("valid");
        let tree = tree_from(&attachment);

        // VISIBLE: the error survives into the tree and is findable.
        let leaves = tree.leaves();
        assert_eq!(leaves.len(), 3);
        assert!(leaves[1].is_missing());
        assert!(
            matches!(&tree, Syntax::Node { args, .. } if args[1].is_missing()),
            "the missing form must be a real node in the tree, not an omission"
        );

        // CONTRIBUTES NOTHING: no invented text.
        assert_eq!(leaves[1].contributed_span(), None);
        assert_eq!(
            tree.reconstruct(&text, attachment.epilogue()).as_deref(),
            Some(&raw[..])
        );
    }

    /// The forms carry what the pin says they carry, with a `Name` kind — the thing the
    /// graph edge existed for.
    #[test]
    fn the_four_forms_match_the_pins_constructors() {
        assert!(Syntax::Missing.is_missing());
        assert_eq!(Syntax::Missing.info(), SourceInfo::None);
        assert_eq!(Syntax::Missing.kind(), None);

        // node: info is SourceInfo.none for parser output, kind is a Name.
        let kind = name(&["Lean", "Parser", "Term", "app"]);
        let node = Syntax::node(kind.clone(), vec![Syntax::Missing]);
        assert_eq!(node.info(), SourceInfo::None, "parser nodes carry no info");
        assert_eq!(node.kind(), Some(&kind));
        assert_eq!(
            node.kind().map(fln_core::name::Name::to_display_string),
            Some("Lean.Parser.Term.app".to_string()),
            "the kind is a hierarchical Name, not a flat string"
        );

        // atom: a String value, no Name.
        let info = SourceInfo::Synthetic {
            pos: BytePos(0),
            end_pos: BytePos(3),
            canonical: true,
        };
        let atom = Syntax::atom(info, "def");
        assert!(matches!(&atom, Syntax::Atom { val, .. } if val == "def"));
        assert_eq!(atom.kind(), None);

        // ident: raw span, parsed Name, and preresolved candidates.
        let ident = Syntax::Ident {
            info,
            raw_val: ByteSpan::new(BytePos(0), BytePos(3)).expect("fwd"),
            val: name(&["Nat", "succ"]),
            preresolved: vec![
                Preresolved::Namespace { ns: name(&["Nat"]) },
                Preresolved::Decl {
                    name: name(&["Nat", "succ"]),
                    fields: vec!["x".to_string()],
                },
            ],
        };
        let Syntax::Ident {
            val, preresolved, ..
        } = &ident
        else {
            panic!("expected an ident");
        };
        assert_eq!(val.to_display_string(), "Nat.succ");
        assert_eq!(preresolved.len(), 2);
        assert_eq!(ident.kind(), None, "an ident is a leaf, not a kinded node");
    }

    /// Two trees with the same shape but different kinds are different trees — the kind is
    /// part of the identity, and a `Name` kind keeps hierarchical kinds distinct where a
    /// flattened string could collide.
    #[test]
    fn the_kind_is_part_of_a_trees_identity() {
        let a = Syntax::node(name(&["Lean", "Parser", "Term", "app"]), vec![]);
        let b = Syntax::node(name(&["Lean", "Parser", "Term", "fn"]), vec![]);
        assert_ne!(a, b);
        assert_eq!(
            a,
            Syntax::node(name(&["Lean", "Parser", "Term", "app"]), vec![])
        );

        // The structural Name distinction the canon layer proved matters: components are
        // not a joined string, so these two are distinct kinds rather than one.
        let nested = name(&["Lean", "Parser"]);
        let flat = Name::str(Name::anonymous(), "Lean.Parser");
        assert_ne!(
            nested, flat,
            "a dotted component is not a component sequence"
        );
        assert_ne!(Syntax::node(nested, vec![]), Syntax::node(flat, vec![]));
    }
}
