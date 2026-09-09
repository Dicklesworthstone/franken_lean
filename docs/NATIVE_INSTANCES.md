# Native source instances

The source elaborator now solves instance-implicit arguments instead of rejecting every call that needs them. This is a bounded native implementation, not complete Synod or Lean instance-search parity. The implementation lives in `fln-elab/src/instances.rs` and `fln-elab/src/source/instances.rs`.

## Use it from source

```lean
instance (priority := 2000) preferredNat : Inhabited Nat := Inhabited.mk 7

instance constantFunction {A : Type} [Inhabited A] : Inhabited (Nat -> A) :=
  Inhabited.mk (fun x => default)

def selected : Nat := default
def nested : Nat -> Nat -> Nat := default
def dictionary : Inhabited Nat := inferInstance

theorem selected_ok : selected = 7 := by rfl
theorem nested_ok : nested 2 3 = 7 := by rfl
```

Run the repository example with `fln check-source --json examples/native_instances.lean`, or `cargo run --locked -p fln-cli --bin fln -- check-source --json examples/native_instances.lean`. The command checks the complete file through K1 and the independent checker; it does not compile or execute the source program. Checking still performs the ordinary kernel conversion needed to verify the example's equalities.

The source prelude contains the ordinary one-field `Inhabited` inductive block, its constructor, regenerated recursor, `Inhabited.default`, `default`, `inferInstance`, and registered Nat/String/Bool dictionaries. Nat's default is zero, String's is empty, and Bool's is false until a higher-precedence instance is selected. No new axiom asserts that an arbitrary type is inhabited. `inferInstance` is the ordinary identity definition with an instance-implicit argument, not a special proof acceptance instruction.

Both `[Inhabited A]` and `[i : Inhabited A]` are accepted in signatures. The newest eligible local instance is considered before registered globals. Ordinary parameters such as `(i : Inhabited A)` and class-valued local lets also qualify. Class discovery unfolds abbreviations, but neither ordinary definition aliases nor local type aliases; ordinary functions returning a class do not qualify. The same reduction policy governs instance binder annotations and search targets. Source instance declarations require an explicit name and result type. Global priorities are nonnegative decimal `u32` values, defaulting to 1000; higher values precede lower values, and newer registrations precede older ones at equal priority.

An instance declaration is a safe definition candidate. Only after its normal K1-plus-checker admission does the engine register its name for search. Failed declarations and late failures in an ordered multi-file check expose neither a new declaration snapshot nor a registration. The returned result root describes the successor after registration, not the pre-registration intermediate.

## Search and tactic integration

Application and expected-result inference create typed, synthetic-opaque instance holes. Search waits until their class inputs and universe arguments are known rather than choosing a dictionary to guess the missing input. Candidate conclusion matching uses the native unifier. Instance prerequisites recursively invoke the same search using an explicit work stack.

A failed candidate restores metavariables, equations, local context, pending goals and fresh-name state before trying an alternative. Spent work is retained. An exact cyclic branch can fall back to a later candidate; resource stops remain typed nonanswers, never successful search or authoritative absence. Search depth is bounded to 128 frames and candidate attempts to 4096 per search, in addition to the source elaboration budget. There is no persistent negative cache.

`apply`, `rw`, `rewrite` and `simp only` can synthesize instance arguments of selected lemmas. Successful terms retain actual dictionary applications. A missing instance does not become an ordinary tactic premise chosen from an arbitrary hypothesis. In particular, `simp only` still cannot discharge an unrelated logical premise from an unselected local proof merely because instance search is enabled.

The independent checker now considers the major expression beneath a projection when choosing lazy definition unfolding. This allows projections out of defined dictionaries to convert normally. Wrong structure names, invalid projection fields and unsafe definitions do not gain conversion authority.

## Registration API and limits

`fln_elab::instances::register_class` and `register_instance` return immutable environment successors referring only to already admitted declarations. The journal uses its own versioned native schema, structural name encoding, bounded rows/payloads, and explicit merge/checkpoint semantics. Malformed or incompatible metadata is a refusal, not an empty candidate table. These registrations participate in logical roots.

Source `class`/`structure` declarations, anonymous or scoped instances, automatic derived instances, `outParam`/`semiOutParam`, full tabling, SearchCards, complete coercion/default-instance semantics and Reference trace parity are not implemented by this increment. The native journal is not the Reference `.olean` instance extension. Import-free `check-source` files are the current source publication path; the separate execution command refuses instance declarations rather than running dictionary definitions or dropping their registrations.

The W6 Synod workstream remains open. The regression targets are `fln::source_instances`, `fln-elab::native_unification`, `fln-checker::projection_delta` and `fln-cli::source_check`, alongside the existing parser, elaborator, engine and CLI suites. Tests cover computation, local precedence, global priority, recursion/fallback, rollback, canonical source reconstruction, malformed metadata, missing dictionaries, kernel resource stops and the real installed CLI. Scoped test results are not a whole-workspace test-suite or release-gate claim.
