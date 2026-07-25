# How Vellum's test mechanisms compose — and the gap between them

Written for whoever adds the next test suite to `fln-syntax` or `fln-parse`. It records a
**measured** result, not a design intention: I expected two mechanisms to back each other up, checked
whether they do, and found they do not in the direction I assumed. The gap that remains sits between
two suites that are both green, which is the least visible kind there is.

Reproduce anything here in under a minute; the experiment is at the end.

## The two mechanisms

**`tests/golden_vellum.rs`** freezes 8 reviewed inputs as byte-exact artifacts: raw bytes, the
crlfToLf-normalized view, the token stream, and the green tree's shape including per-leaf trivia
lengths. It has **no update mode** — the tests never write the corpus, and the regeneration path is
an `#[ignore]`d test that only prints. A change to any frozen artifact fails and stays failed until a
human edits the corpus by hand.

**`tests/metamorphic_vellum.rs`** asserts six laws over transformations of arbitrary input: churn
preserves the parse modulo trivia, churn moves attachment only where the edit is, independent
reordering permutes the result, alpha-renaming preserves structure, churn is invertible, and the
composition of churn with renaming. The laws are exact equalities — a parser has no epsilon.

## What I expected them to do together

That a code change breaking a metamorphic law would also fail the goldens, so the goldens would be
the backstop and there would be no quiet drift. Stated the other way: that the metamorphic suite was
the sensitive instrument and the goldens the coarse one.

## What they actually do

I planted one real change in `chooseNiceTrailStop` — trailing trivia stopping at a carriage return
instead of a newline, which reassigns trivia ownership across the whole corpus — and ran both:

    golden_vellum        FAILED
    metamorphic_vellum   ok

**The metamorphic laws are blind to it.** The change is *uniform*: it alters attachment identically on
both sides of every comparison, so "churn preserves the parse modulo trivia" remains true — of a
different attachment rule. A self-differential cannot detect a change to the rule it is comparing
against itself. That is not a weakness in how the laws are written; it is what a metamorphic law *is*.

So the expectation was backwards. The **golden** is the sensitive instrument for this class, and the
metamorphic suite is the coarse one.

## Which mechanism is weaker than it looks in isolation

**Both are, in complementary ways, and neither weakness is visible from inside its own suite.**

*The metamorphic suite is weaker than it looks* because a green run says only "the parser is
internally consistent under these transformations". It is invariant under any uniform change to a
rule it exercises. Trivia ownership, precedence, token classification — get any of them uniformly
wrong and every law still holds. The suite's own module docs now say this, and the bead grades it as
a self-differential, but a reader who sees only a passing test name will not infer it.

*The goldens are weaker than they look* for the opposite reason: they are exactly 8 inputs. Any
behaviour that manifests only on input outside that corpus is invisible to them, however uniform or
input-dependent it is. A frozen corpus is a claim about the inputs it contains and about nothing else.

## The gap

A change that is **both**

1. uniform enough to be metamorphically invisible, and
2. only observable on inputs outside the 8 golden rows

passes both suites. Concretely: a trivia-ownership or classification rule that is wrong only for a
construct the golden corpus does not contain — a raw string, an unterminated block comment, a tab
refusal, a file that is nothing but trivia. Those are precisely the rows
`corpus/VELLUM_GOLDENS_PROVENANCE.md` lists as *worth adding and not yet added*.

That is the shape to watch for generally: two green mechanisms whose blind spots overlap. Neither
suite can report the gap, because from inside each one everything passes.

## What actually closes it

Not another self-comparison. The gap is closed by **fidelity evidence** — something that is not this
implementation:

* Pin observations. `token_table_totality` differentials the trie against a naive longest-prefix scan;
  `pratt_precedence_model` compares against six values the pinned `lean` binary printed. Those catch
  uniform rule errors because the oracle does not share the rule. This is the only category that
  addresses the gap directly.
* Growing the golden corpus, which narrows condition 2 but never eliminates it.
* A conformance harness against the pin's own parse output at scale, which would subsume both. That
  needs the Reference's parse tree rather than its diagnostics, and per AGENTS.md the Reference
  participates only inside the Tribunal (§18) — so it is Tribunal work, not `fln-syntax` work.

## Ordering, for whoever adds a suite next

1. If the property can be checked against the **pin**, do that. It is the only kind of evidence that
   survives a uniform mistake.
2. If it cannot, a golden is the next best thing, and it must have **no update mode** — the goldens
   only function as a backstop here because they cannot rewrite their own expectation.
3. A metamorphic law is worth having for input-dependent inconsistency, and is worth nothing against a
   uniform error. Grade it as a self-differential where a reader will see the grade.
4. Say in the suite's own docs what it does **not** establish. Every Vellum suite does this now, and
   it is the only reason this document could be written from the record rather than from memory.

## Reproducing the experiment

    # In crates/fln-syntax/src/attach.rs, in nice_trail_stop, change
    #   .position(|byte| *byte == b'\n')
    # to
    #   .position(|byte| *byte == b'\r')
    cargo test -p fln-syntax --test golden_vellum        # FAILS, naming the leaf and the diff
    cargo test -p fln-syntax --test metamorphic_vellum   # PASSES
    # then revert.

The golden failure reports `leaf 9..10 lead0 trail0 epilogue1` against
`leaf 9..10 lead0 trail1 epilogue0` — the newline moved from the file epilogue into the token's
trailing trivia. Note that the *reconstruction* is byte-perfect either way, so a golden that froze
only reconstructed bytes would also have passed. Freezing the shape is what makes the golden the
sensitive instrument here.
