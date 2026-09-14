# Native checked decisions

The bounded source seed includes the ordinary inductive families `False`, `True`,
and `Decidable`, the transparent definition `Not`, and checked definitions of
`ite`, `dite`, and `decide`. Every seed candidate crosses the same K1 and independent
checker admission path as user declarations. None is a new axiom.

`Decidable p` is a registered class with two constructors: `Decidable.isFalse`
requires a proof of `Not p`, and `Decidable.isTrue` requires a proof of `p`.
Constructor order and proof-field types follow the pinned Prelude. The recursor
is regenerated and checked; its proof fields do not turn the decision itself
into proof-irrelevant data. Instances for `True`, `False`, and negation are
ordinary checked definitions. No classical fallback synthesizes arbitrary
propositions. Unknown decisions remain unresolved obligations.

Both implicit instance parameters and eligible ordinary local dictionaries use
the existing transactional instance search. Users may define and register their
own decisions for any supported predicate. `decide p` maps the actual decision
to a Boolean. `dite p yes no` supplies the proof or refutation to the selected
function; `ite p yes no` ignores that evidence. These functions accept result
sorts including propositions, types and function values.

All source arguments and annotations remain ordinary typing obligations even
when conversion ultimately selects a different branch. Source checking does not
execute a VM/backend and does not trust a host computation of the proposition.

Run `fln check-source --json examples/native_decisions.lean` for a user-defined
predicate, a registered instance, dependent branch functions and computed checks.
This is a bounded library slice, not full Prelude ingestion. Arithmetic decision
instances, classical reasoning, and the `decide` tactic are separate capabilities.
