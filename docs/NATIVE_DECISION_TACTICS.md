# Checked decision-driven proof control

`by_cases h : p` splits the current goal into a positive branch with `h : p`
and a negative branch with `h : Not p`. Without a written evidence name, the
name is `h`. A local or registered `Decidable p` dictionary is required. This
bounded constructive implementation does not insert a classical choice axiom
or silently assume decidability for an arbitrary proposition.

Both branches become ordinary functions supplied to the admitted `dite`
definition. They are elaborated even when the dictionary is already known to
choose only one branch. The completed declaration crosses K1 and the independent
checker. The proposition and all of its written argument annotations remain
in that core term; branch selection does not discard typing obligations.

Evidence identities are fresh and branch-local, including when names shadow
existing dependent locals. Goals can be propositions, data, functions or types.
Bullets, `all_goals`, `<;>`, nested local proofs and transactional alternatives
reuse the existing goal worklist. The parent closes only after both branches.
Resource failures remain nonanswers and failed optional attempts restore their
instance goals, assignments and continuations without refunding work.

Run `fln check-source --json examples/native_decidable_cases.lean`.
This documents bounded source admission and conversion, not the full Lean
classical tactic fallback, interactive InfoTree integration or VM execution.

## Computed proofs with `decide`

The `decide` tactic synthesizes a `Decidable p` dictionary for the current
proposition and reduces its checked decision computation. A known true result
produces `of_decide_eq_true` applied to that same dictionary and a reflexive
Boolean equality. A false or stuck result refuses; an unavailable dictionary
is not replaced by a guessed proof. Local transparent dictionaries and registered
instance definitions participate through ordinary instance synthesis.

`of_decide_eq_true` is an admitted theorem, not an axiom. Its dependent recursor
returns the positive constructor's proof. For a negative decision, it transports
along the supplied impossible equality `false = true` using `Eq.rec` and a
Bool-indexed proposition. The source tactic's reduction is not a new acceptance
mechanism: both checking engines validate the complete theorem application and
the equality between the actual computation and `true`.

The dictionary, its proof fields and every supplied argument remain in the
resulting term. Ill-typed unused local values still reject at K1. Tactic
backtracking restores failed attempts but cannot swallow resource exhaustion.
The theorem can also be used with an explicit equality proof, including an
abstract `computed : decide p = true`. To let its result infer the target before
reflexivity, `by apply of_decide_eq_true; rfl` uses the ordinary apply path.

Run `fln check-source --json examples/native_decision_proofs.lean`.
This does not add classical decidability, `native_decide`, arithmetic decision
instances, or the complete Reference configuration grammar for `decide`.