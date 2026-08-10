//! **fln-checker** — the independent kernel checker — deliberately different algorithms, its own decoder, WASM-clean; a consensus council member, never an authority (plan §8.3b).
//!
//! The implementation begins with the parts that must not be retrofitted after
//! performance pressure appears: a versioned deterministic sampling policy, a
//! checker-owned canonical-wire decoder, eager universe semantics, and independent
//! term facts plus capture-avoiding rewrites. Public weak-head reduction eagerly
//! unfolds safe definitions from an immutable checker-owned environment with
//! independently instantiated universes. Slow conversion instead takes no-delta
//! weak heads, peels KR-308 Nat successor offsets without unary literal expansion,
//! and selects one definition step by recorded height, giving the checker a
//! deliberately separate KR-307/KR-309 strategy. Checker-owned numeric and
//! expression-reduction modules now supply independently resource-counted
//! arbitrary-precision Nat operations and the KR-313 dispatch table. Inference
//! covers KR-100 through KR-108 plus iterative metadata transparency: application
//! spines, lambda telescopes, and Forall telescopes use explicit heap
//! continuations, checking queries share one immutable reduction/conversion
//! context, and infer-only queries do not type application arguments or lambda
//! binder domains. Telescope-local identities are deterministic and capture-safe.
//! Checking forces each lambda domain type through checker-owned WHNF to a sort,
//! and the inferred body type receives KR-107's exact cheap head-beta step before
//! dependent Pi rebuilding. KR-108 checks every Forall domain and its terminal
//! codomain in both modes, then constructs the raw right-associated `imax`
//! universe independently. Lets, literals, projections, and KR-970 … KR-978
//! declaration admission are live; the remaining equality and inductive-family
//! work stays open. The crate map and layering are governed by
//! `WORKSPACE_GRAPH.txt` (bead fln-8mj).
//!
//! # THE INDEPENDENCE BOUNDARY (bead `franken_lean-r0xu`) — read this first
//!
//! `franken_lean-gii` requires this crate to share "only reviewed data schemas"
//! with `fln-kernel`. That phrase decides what "independent" means, so it is
//! preserved from the charter written **before** implementation began, rather than
//! being back-derived from whatever the first implementation happened to do.
//!
//! ## What the build already enforces
//!
//! `ci/WORKSPACE_GRAPH.txt` prohibits `fln-checker ->* fln-kernel`,
//! `fln-olean`, `fln-rt` and `fln-unsafe-*`, and allows only `fln-core` and
//! `fln-hash`. Note `fln-kernel` may depend on `fln-env` and
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
//!   directly as its verdict — `tc.rs:950` answers KR-303 sort definitional
//!   equality with `lt.is_equiv(ls)`, and `tc.rs:897`/`1225`/`1890` decide
//!   "is this a Prop?" (the KR-974 theorem check) with
//!   `level.is_equiv(&Level::zero())`. A checker that calls `is_equiv` does not
//!   check universe equivalence at all. `imax`/`max` fixpoint normalization is
//!   precisely where subtle unsoundness hides, so this is the single most
//!   important row in this table.
//! * **Traversal-pruning answers on `Expr`'s packed data word.**
//!   `loose_bvar_range`, `has_fvar`, `has_expr_mvar`, `has_level_mvar`,
//!   `has_level_param`, `approx_depth`. These are precomputed answers that the
//!   kernel *skips work* on: `instantiate` returns early when
//!   `loose_bvar_range() <= k` (`tc.rs:177`), and `abstract_fvar`,
//!   `abstract_shifted` and `abstract_replace_value` all return early when
//!   `!has_fvar()` (`tc.rs:1646`/`1708`/`1780`). An under-reporting flag makes
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
//! `impl Canonical for Expr` (`canon.rs:1133`) whose trait supplies
//! `to_canonical_bytes` / `from_canonical_bytes` (`canon.rs:631-652`). A
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
//! * **SEMANTIC — the readers.** `Canonical::read_body`, `from_canonical_bytes`
//!   and `from_canonical_bytes_budgeted` for `Expr`, `Level` and `Name`. The
//!   budgeted entry point is the one `canon.rs` steers callers to for untrusted
//!   input, so naming only the unbudgeted one would send a checker author who
//!   followed the documentation straight past the rule. It was in the inventory
//!   and absent from this list until the registry below bound the two together.
//!   Decoding is where
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
//! This resolved the contradiction recorded below in favour of `gii`: the graph
//! once permitted `fln-checker -> fln-bignum`, while `gii`'s REVIEW AMENDMENT
//! forbade sharing its semantic path. The checker wants a deliberately simple, slow,
//! obviously-correct numeric implementation of its own — which is also why
//! `gii` asks for "deliberately simple" rather than "fast". The current graph
//! tightening is recorded in the re-measurement below.
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
//! ## Where the graph stands, re-measured
//!
//! This section previously said two prohibitions were missing. **One of them has
//! landed**, and the paragraph outlived it — which is the defect this crate's own
//! matrix row was corrected for once already (`witness.rs:539`, where
//! `B3-INDEPENDENT-CHECKER` asserted a "6-line charter stub" at 149 lines, green
//! throughout). So the state is measured here rather than remembered, at
//! `53a5e3ec`:
//!
//! 1. **DONE.** `fln-checker -> fln-bignum` is no longer permitted.
//!    The `allow-direct fln-checker` declaration reads `fln-core, fln-hash`.
//!    `gii`'s REVIEW AMENDMENT
//!    is satisfied, so the checker must bring its own arithmetic. Note the old
//!    text cited `WORKSPACE_GRAPH.txt:110`, which is now *fln-kernel's*
//!    allowlist: a line-number citation moved under the claim, so cite the
//!    declaration by content.
//! 2. **DONE, and this entry was wrong about it for two days.** It read "STILL
//!    OPEN … the `Canonical` *readers* need an item-level rule and do not have one
//!    yet". They had one. `read_body` and `from_canonical_bytes` entered
//!    `FLN-STRUCT-037`'s inventory at `18b6d14b`, which is an **ancestor** of
//!    `a22c64f2` — the commit that wrote this entry, whose subject is "re-measure
//!    the two doctrine claims in its charter, both of which outlived the work that
//!    satisfied them". The re-measurement itself outlived nothing; it was false the
//!    day it was written, and `franken_lean-r0xu`'s own closing judgement already
//!    said so. `fln-checker -> fln-hash` does still stay permitted, so the split
//!    genuinely runs through the middle of one crate — that half was correct, which
//!    is exactly why the wrong half survived review.
//!
//! ## What is machine-checked, and what is not
//!
//! This section previously said the classification was "not yet machine-checked"
//! and that "a document is not a boundary". **That is now half wrong**, and in
//! the direction that understates the build:
//!
//! * **ENFORCED at item granularity.** `FLN-STRUCT-037` refuses `fln-checker`
//!   *reaching* a SEMANTIC item across this boundary
//!   (`tools/structure-guard/src/checks.rs:1113`). It is planted three ways:
//!   `seeded.rs:1296` proves the baseline clean, `seeded.rs:1306`
//!   `every_semantic_item_is_refused_inside_fln_checker` plants one violation per
//!   inventory item and asserts each fires **alone** so an over-broad matcher
//!   cannot fake green, and `seeded.rs:1341` proves that *naming* a semantic item
//!   in prose is not a violation — which is why this document may keep citing
//!   `Level::is_equiv` and `from_canonical_bytes` by name.
//! * **DECLARED AND NOT WALKED — three items, and the number is bound.** Not every
//!   name this charter calls SEMANTIC is in the inventory. `normalize` and `is_zero`
//!   are method names the checker's *own required reimplementation* legitimately
//!   wants, and the rule matches lexemes — including definitions — so enforcing them
//!   would forbid exactly what this document demands. `lean_hash` is a module path
//!   and looks enforceable on the same terms as `fln_bignum`; it is unenforced for
//!   no recorded reason, which is a candidate for repair rather than a decision.
//!   The registry below marks each `walked` or `reviewed`, and
//!   `the_charter_and_the_rule_declare_the_same_semantic_inventory` fails if a
//!   `reviewed` item is in the rule, if a `walked` item is not, or if the reviewed
//!   remainder is any size but three. **A remainder that is counted is a remainder
//!   somebody has to argue for; this bullet used to be the sentence "that half
//!   remains a document", and it was false.**
//! * **LIVE AGAINST REAL CODE.** The foundation modules now contain policy, wire,
//!   universe, and term algorithms. `FLN-STRUCT-037` scans those production sources, so the
//!   boundary is no longer exercised only by planted fixtures. The checker still has
//!   no declaration-admission authority and cannot acquire one through this crate.
//! * **AND THAT SENTENCE NOW HAS A MODULE STANDING NEXT TO IT CALLED `admit`, so it
//!   is restated rather than left to look contradicted.** `admit` implements KR-970
//!   … KR-978 and produces a `Verdict` — an *observation a council may consult*, not
//!   a capability. Three properties hold it there: `Admission` has no public
//!   constructor and no public field, so it can only come from this crate saying
//!   yes; neither it nor `Verdict` is `Clone` or `Copy`, so a verdict cannot be
//!   duplicated into something stored and presented later as authority; and there is
//!   no conversion out — `admit` takes a `&ConstantEntry` and never hands one back.
//!   Underneath all three sits the fact that makes them worth stating: this crate
//!   does not depend on `fln-kernel`, so no type that kernel's admission path
//!   consumes is nameable here at all. `the_admission_verdict_is_not_a_capability`
//!   binds the dependency half to the real manifest and the surface half to
//!   `admit.rs`, with a planted decoy proving the scan can fire — an empty result
//!   from a scan nobody showed capable of matching is this crate's own recorded
//!   defect, and it cost `gii.22` a false disclosure two commits ago.
//!   **What that does NOT earn:** it is a lexical guard over one file plus one
//!   manifest edge, so a laundering path assembled in a *different* module is
//!   outside it, and the argument that a `Verdict` cannot be laundered remains
//!   prose that no check reads.
//!
//! Nobody should read the existence of this section as evidence that the whole
//! boundary holds; read the two bullets above for which half does.
//!
//! ## Semantic registry — every name above, bound to the rule that refuses it
//!
//! **Why this exists.** Everything above is prose, and prose about enforcement rots
//! in the one direction nobody checks: *toward claiming less than the build does*, so
//! it never fails and never gets read again. The `NOT ENFORCED` bullet this section
//! replaced was false the day it was written and stayed false through two later edits
//! to this file, including one whose stated purpose was re-measuring these very claims.
//!
//! The rule is `structure_guard::checks::CHECKER_SEMANTIC`, and it is the **single**
//! producer: the seeded campaign that plants one violation per item reads that array
//! directly, and so does the test behind this registry. Nothing transcribes it any
//! more. Each row below marks a name `walked` — in the rule, refused inside this
//! crate — or `reviewed`, declared SEMANTIC here and deliberately not in the rule.
//!
//! `reviewed` is a **counted remainder, not an escape hatch**: the test pins it at
//! three, so a fourth unwalked declaration cannot be added quietly and a repaired one
//! cannot be left claiming to be unrepaired. Equality both ways, because this is a
//! measured population rather than a shrinking allowance.
//!
//! ```text
//! semantic is_equiv                     :: walked
//! semantic normalize_fixpoint           :: walked
//! semantic loose_bvar_range             :: walked
//! semantic has_fvar                     :: walked
//! semantic has_expr_mvar                :: walked
//! semantic has_level_mvar               :: walked
//! semantic has_level_param              :: walked
//! semantic approx_depth                 :: walked
//! semantic read_body                    :: walked
//! semantic from_canonical_bytes         :: walked
//! semantic from_canonical_bytes_budgeted :: walked
//! semantic fln_bignum                   :: walked
//! semantic normalize                    :: reviewed the checker's own eager normalization wants this name
//! semantic is_zero                      :: reviewed the checker's own Level reimplementation wants this name
//! semantic lean_hash                    :: reviewed no recorded reason; enforceable like fln_bignum, so a repair candidate
//! ```
//!
//! **What this does not earn.** A `walked` row proves the name is in the rule's
//! inventory. It does not prove the rule *fires* against this crate — that is the
//! seeded campaign's job, and it is vacuous against the real tree while there is no
//! checking code here. Nor does a `reviewed` row make its reason true: two of the
//! three reasons are arguments about name collision that nobody has tested, and the
//! third says plainly that there is no reason at all.
//!
//! ## Citation registry — every line number above, bound to what it points at
//!
//! **Why this exists** (bead `franken_lean-checker-charter-line-citations-unbound-68ob`). This
//! charter's authority rests on line numbers in code it does not control: 33 lines across six
//! files in five crates. A line number is a claim that rots the moment anyone inserts a line
//! above it, and nothing noticed when that happened — `witness.rs:479 (historical)` was
//! `B3-INDEPENDENT-CHECKER`'s evidence line until commit `f39eaa2c` added 25 lines above it,
//! after which 479 pointed at a *different* row whose text looked just as plausible. This crate
//! had no tests at all, so nothing could have caught it.
//!
//! Each row below names the construct the citation is *for*. The line number is then checkable
//! rather than merely asserted, and `charter_citations.rs` fails in both directions: if a cited
//! line stops containing its construct, and if the prose cites a location this registry does
//! not cover. **Fix the registry, not the test** — the registry is the source.
//!
//! **`@@ <item>` closes the tolerance that containment cannot see, and six rows carry it.**
//! Containment asks only whether line N holds construct C. Where C **recurs** in its file that
//! is satisfied by *any* occurrence, so a shift can move a citation onto a different site and
//! stay green — the tolerance is the distance between occurrences, and it is the reason
//! `0f2ae0ba` shifted four of AGENTS.md's citations by 45 lines while only two reddened. A row
//! whose construct recurs must therefore name the item the line sits inside, and that name is
//! checked. `ExprNode::Sort { level }` occurs **7** times in `tc.rs` and `!e.has_fvar()` **3**,
//! which is why exactly those six rows are sited and the other ten are not: where a construct
//! occurs once, any shift already breaks containment, so a site check there could never fail
//! and would be decoration reading as coverage.
//!
//! **Measured before it was built, at `84f35ea6`, over all 16 rows:** every one was still on
//! its original occurrence and inside its original item, so the tolerance was real and had
//! **never been exercised**. It is closed rather than merely disclosed because the shift nobody
//! watches is the next one. What that measurement does not earn: it compares each row against
//! the commit where the row last took its present form, so a row rewritten at the same commit
//! as the code it cites is verified against itself, and it establishes site identity — never
//! that the prose reading the site is sound.
//!
//! ```text
//! cite crates/fln-kernel/src/tc.rs:950 :: lt.is_equiv(ls)
//! cite crates/fln-kernel/src/tc.rs:897 :: ExprNode::Sort { level } @@ fn major_to_cnstr_when_structure
//! cite crates/fln-kernel/src/tc.rs:1225 :: ExprNode::Sort { level } @@ fn is_prop
//! cite crates/fln-kernel/src/tc.rs:1890 :: ExprNode::Sort { level } @@ fn infer_proj
//! cite crates/fln-kernel/src/tc.rs:177 :: e.loose_bvar_range() <= k
//! cite crates/fln-kernel/src/tc.rs:1646 :: !e.has_fvar() @@ fn abstract_fvar
//! cite crates/fln-kernel/src/tc.rs:1708 :: !e.has_fvar() @@ fn abstract_shifted
//! cite crates/fln-kernel/src/tc.rs:1780 :: !e.has_fvar() @@ fn replace_fvar
//! cite crates/fln-hash/src/canon.rs:1133 :: impl Canonical for Expr
//! cite crates/fln-hash/src/canon.rs:631 :: pub trait Canonical: Sized
//! cite crates/fln-core/src/expr.rs:510 :: impl PartialEq for Expr
//! cite crates/fln-conformance/src/witness.rs:539 :: id: "B3-INDEPENDENT-CHECKER"
//! cite tools/structure-guard/src/checks.rs:1113 :: code: "FLN-STRUCT-037"
//! cite tools/structure-guard/tests/seeded.rs:1296 :: fn the_checker_boundary_baseline_is_clean
//! cite tools/structure-guard/tests/seeded.rs:1306 :: fn every_semantic_item_is_refused_inside_fln_checker
//! cite tools/structure-guard/tests/seeded.rs:1341 :: fn naming_a_semantic_item_in_prose_is_not_a_violation
//! ```
//!
//! **What this does not earn.** A bound citation proves the line still holds the construct
//! named; it does not prove the surrounding prose is a correct reading of that construct. And
//! the registry covers this file only — `tools/structure-guard/src/checks.rs:980 (foreign)`/`:1006`/`:1011`
//! transcribe the same `tc.rs` line numbers into `FLN-STRUCT-037`'s finding text, so a violator
//! is still sent to a line by a guard that cannot know whether it moved. That half belongs to
//! structure-guard's owner.
//!
//! **The registry rotted twice while this paragraph stood, and repairing only the row that
//! shouted would have left the build red.** Re-derived at `ef5af198`, every row rather than the
//! loud one: `witness.rs:496 (historical)` became 535 (`f1a2b899`, then `d2cb11ae` — both `kl4h`
//! commits, so this charter was rotted by the pane that maintains it), then 538 when the
//! adjacent consensus row recorded fln-5720's seed caller; and
//! `checks.rs:1023 (historical)` became 1068 (`0f2ae0ba`). The test asserts *inside* its loop,
//! so it reports the **first** mismatch only and a green after one repair would have been the
//! next red. `0f2ae0ba` is the same commit AGENTS.md records as drifting its own four
//! `checks.rs` citations by +45: one insertion, two registries, and only the other one was
//! repaired — this registry's own defect arriving from the outside.
//!
//! **Two of the three foreign citations above cannot be seen by the conservation check**, which
//! is why they were stale and silent. Its needle is `.rs:`, so only the **first** member of a
//! `/`-joined list carries a filename; `:1006` and `:1011` are scanned by nothing, marked or
//! not. They read `:904`/`:931`/`:936` until this repair and pointed at `),`, a `.map_err` line
//! and `.file_type()`. Corrected by deriving the three sites that actually transcribe a `tc.rs`
//! line number, not by shifting the old numbers — a shift assumes they moved together, which is
//! the assumption that produced the plausible-looking `witness.rs:479 (historical)` this
//! registry exists to prevent.
#![forbid(unsafe_code)]

pub mod admit;
pub mod defeq;
pub mod environment;
pub mod infer;
pub mod instantiate;
pub mod nat_reduce;
pub mod numeric;
pub mod policy;
pub mod string_reduce;
pub mod term;
pub mod universe;
pub mod whnf;
pub mod wire;
