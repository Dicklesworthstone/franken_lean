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
//! ## Two open items this crate must not be built on top of
//!
//! 1. **`fln-bignum` is contradictory today.** `WORKSPACE_GRAPH.txt:110`
//!    permits `fln-checker -> fln-bignum`; `franken_lean-gii`'s REVIEW
//!    AMENDMENT requires "a deliberately simple numeric implementation whose
//!    semantic code, normalization, algorithms, and test-oracle path are not
//!    shared with fln-bignum or K1/K2". The graph permits exactly what the
//!    bead forbids, and structure-guard would not catch the violation. One of
//!    the two is wrong and the decision is not this crate's to make alone.
//! 2. **The classification above is not yet machine-checked.** Until a
//!    structure-guard rule enforces it at item granularity, it is a document,
//!    and a document is not a boundary.
#![forbid(unsafe_code)]
