//! **fln-checker** — the independent kernel checker — deliberately different algorithms, its own decoder, WASM-clean; a consensus council member, never an authority (plan §8.3b).
//!
//! Stub crate: charter only. Implementation arrives with its workstream beads
//! (`franken_lean-gii`); the crate map and layering are governed by
//! `WORKSPACE_GRAPH.txt` (bead fln-8mj).
//!
//! # THE INDEPENDENCE BOUNDARY (bead `franken_lean-r0xu`) — read this first
//!
//! `franken_lean-gii` requires this crate to share "only reviewed data schemas"
//! with `fln-kernel`. That phrase decides what "independent" means, so it is
//! written down here, **before** any implementation exists, rather than being
//! back-derived from whatever the first implementation happened to do.
//!
//! ## What the build already enforces
//!
//! `ci/WORKSPACE_GRAPH.txt` prohibits `fln-checker ->* fln-kernel`,
//! `fln-olean`, `fln-rt` and `fln-unsafe-*`, and allows only `fln-core`,
//! `fln-hash` and `fln-bignum`. Note `fln-kernel` may depend on `fln-env` and
//! this crate may **not**: the checker brings its own environment and name
//! resolution as well as its own decoder. So the two obvious fake
//! independences — a wrapper over `fln-olean`'s decoder, or anything reusing
//! `fln-kernel`'s `whnf` — already fail to build. structure-guard is the
//! authority on that half and it predates both engines.
//!
//! ## What the build does NOT enforce, and why it matters
//!
//! The permitted crates are not inert schema. A cross-check is worth exactly
//! the set of questions its two sides answer *separately*; every answer they
//! share is a question nobody checks twice. The rule below follows from that
//! and nothing else:
//!
//! > **SCHEMA** is a description of a term — its shape, its names, its
//! > spelling. **SEMANTIC** is an *answer about* a term that a checking
//! > algorithm acts on. Sharing schema is required, so both sides talk about
//! > the same object. Sharing a semantic answer silently deletes it from the
//! > cross-check.
//!
//! ### SEMANTIC — this crate must reimplement these, never call them
//!
//! * **Universe judgments.** [`fln_core::level::Level::is_equiv`],
//!   `normalize`, `normalize_fixpoint`, `is_zero`. These are not helpers; they
//!   *are* judgments of the type theory, and `fln-kernel` returns their result
//!   directly as its verdict — `tc.rs:949` answers KR-303 sort definitional
//!   equality with `lt.is_equiv(ls)`, and `tc.rs:896`/`1224`/`1889` decide
//!   "is this a Prop?" (the KR-974 theorem check) with
//!   `level.is_equiv(&Level::zero())`. A checker that calls `is_equiv` does not
//!   check universe equivalence at all. `imax`/`max` fixpoint normalization is
//!   precisely where subtle unsoundness hides, so this is the single most
//!   important row in this table.
//! * **Traversal-pruning answers on `Expr`'s packed data word.**
//!   `loose_bvar_range`, `has_fvar`, `has_expr_mvar`, `has_level_mvar`,
//!   `has_level_param`, `approx_depth`. These are precomputed answers that the
//!   kernel *skips work* on: `instantiate` returns early when
//!   `loose_bvar_range() <= k` (`tc.rs:176`), and `abstract_fvar`,
//!   `abstract_shifted` and `abstract_replace_value` all return early when
//!   `!has_fvar()` (`tc.rs:1645`/`1707`/`1779`). An under-reporting flag makes
//!   substitution silently skip a subterm that needed rewriting. Shared, both
//!   engines skip the same subterm and agree for the same wrong reason.
//! * **Hashing that feeds a decision.** [`fln_core::lean_hash`] and the
//!   per-node seeds. Where a hash only buckets or fast-*rejects* it is
//!   harmless (see below); where it gates a semantic shortcut it is an answer.
//!
//! ### SEMANTIC — `fln-hash`: share the FORMAT, never the PARSER
//!
//! This is the case the dependency graph does **not** catch, and it is the one
//! most likely to be walked into by accident.
//!
//! `gii` requires this crate to bring "its OWN decoder over Grimoire canonical
//! wire objects". The graph enforces that by prohibiting `fln-olean` — but
//! `fln-hash` is *permitted*, and `fln-hash::canon` carries
//! `impl Canonical for Expr` (`canon.rs:1044`) whose trait supplies
//! `to_canonical_bytes` / `from_canonical_bytes` (`canon.rs:542-563`). A
//! checker can therefore read canonical bytes, call `Expr::from_canonical_bytes`,
//! and share the decode path with the rest of the workspace **while satisfying
//! every prohibition structure-guard currently enforces**. The "own decoder"
//! requirement would be silently unmet.
//!
//! So the split runs through the middle of `fln-hash`:
//!
//! * **SCHEMA — the wire format.** `SchemaId`, the domain tags
//!   ([`fln_hash::domain`]), the byte grammar itself. Both sides must agree on
//!   what the bytes *mean* or a disagreement cannot be stated.
//! * **SEMANTIC — the readers.** `Canonical::read_body` and
//!   `from_canonical_bytes` for `Expr`, `Level` and `Name`. Decoding is where
//!   `franken_lean-d17i` measured 37 real defects (24 missing private
//!   equation-compiler auxiliaries, 8 sharing that root cause, 5 definitions
//!   decoded as `Axiom` with their values stripped). A second decoder is the
//!   cheapest genuinely-independent thing this crate can offer, and sharing the
//!   first one throws it away.
//! * **Permitted, with the limit written down.** `fln_hash::blake3` and
//!   `fln_hash::root` may be shared: BLAKE3 is a pure function with a public
//!   specification, and a logical root is computed *over content each side
//!   produced independently*, so sharing the builder does not share the answer.
//!   The honest consequence is that the hash and the root builder are then not
//!   themselves covered by the cross-check, and must earn their confidence from
//!   test vectors instead.
//!
//! ### SEMANTIC — `fln-bignum`, and a contradiction resolved
//!
//! Kernel arithmetic is judgment, not utility: KR-313 literal acceleration
//! decides definitional equality of `Nat` literals by *computing*, so a wrong
//! sum is a wrong verdict in the same way a wrong universe comparison is. Two
//! engines sharing one arithmetic implementation do not check arithmetic.
//!
//! This resolves the contradiction recorded below in favour of `gii`:
//! `WORKSPACE_GRAPH.txt` permits `fln-checker -> fln-bignum`, and `gii`'s REVIEW
//! AMENDMENT forbids sharing its semantic path. **The bead is right and the
//! graph is too permissive.** The checker wants a deliberately simple, slow,
//! obviously-correct numeric implementation of its own — which is also why
//! `gii` asks for "deliberately simple" rather than "fast". Tightening the
//! graph is `ci/`-owned and belongs to whoever owns that file, not here.
//!
//! ### SCHEMA — shared on purpose
//!
//! `ExprNode`'s variants and their field types, `Name`, `Level`'s constructors
//! and node shape, `Literal`, `BinderInfo`, `DefinitionSafety`, the
//! `Outcome`/`Inconclusive`/`ResourceReason` taxonomy, `Diagnostic`, `KVMap`,
//! source positions. Both sides must denote the same term and speak the same
//! outcome vocabulary, or a disagreement cannot even be stated.
//!
//! ### Deliberately on the SCHEMA side, with the reason
//!
//! `Expr`'s `PartialEq` compares the data word first and then walks the
//! structure on a heap worklist (`expr.rs:510`). The data word is a fast
//! **reject** only, so a hash collision costs a structural walk and cannot
//! manufacture a false "equal". Sharing it is therefore safe in the direction
//! that matters. It still inherits the flag correctness above, which is why
//! the flags themselves are SEMANTIC.
//!
//! ## What the graph must be tightened to, and why it cannot be done here
//!
//! Two prohibitions are missing, and both are `ci/WORKSPACE_GRAPH.txt` edits
//! owned elsewhere. Recorded here so the checker's author knows the graph is
//! **weaker than this document** until they land:
//!
//! 1. `fln-checker -> fln-bignum` is permitted (`WORKSPACE_GRAPH.txt:110`) and
//!    should not be, per the reasoning above and `gii`'s REVIEW AMENDMENT.
//! 2. `fln-checker -> fln-hash` must stay permitted — the wire format and the
//!    domain tags have to be shared — so a crate-level prohibition cannot
//!    express the split. The `Canonical` *readers* need an item-level rule.
//!
//! ## The standing limitation
//!
//! **This classification is not yet machine-checked.** Until a structure-guard
//! rule enforces it at item granularity, it is a document, and a document is
//! not a boundary — it constrains an author who reads it and nothing else.
//! That rule is the remaining work on `franken_lean-r0xu`; nobody should read
//! the existence of this section as evidence that the boundary holds.
#![forbid(unsafe_code)]
