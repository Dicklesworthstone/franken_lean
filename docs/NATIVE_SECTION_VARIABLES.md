# Native section variables

Source files and source modules accept typed `variable` telescopes. Explicit,
implicit, strict-implicit, and named or anonymous instance parameters use the
same parser and elaborator as declaration binders. For example:

```lean
section
variable {A : Type u} (x : A)
def identity := x
theorem self : x = x := by rfl
end
theorem works : identity 7 = 7 := by rfl
```

The variable command resolves names and checks the entire telescope immediately,
including unused domains. It creates no global assumptions. Section and namespace
exit restore the previous parameter context; file boundaries discard it. Checked
definitions and theorems remain available with ordinary closed Pi/lambda binders,
and pass the existing kernel plus independent checker admission path.

Definitions and named instances generalize parameters used in their types or
values, along with transitive type dependencies, in variable declaration order
before written parameters. Unused variables are not added. Section variables
stay fixed during recursive calls; explicit declaration parameters can shadow
them. Resolved variable types are not reparsed after later `open` commands.

Theorem parameters are selected from the header before elaborating the proof.
Instance-implicit section parameters whose dependencies are all selected are
also available. Other section locals are removed from the proof context, so
editing a proof cannot silently introduce additional assumptions. The resulting
theorem retains the selected header parameters, including unused instances.

Named `include` and `omit` commands explicitly control theorem parameters:

```lean
section
variable (p : Prop) (h : p)
include h
theorem selected : p := by exact h
omit h
theorem independent : 7 = 7 := by rfl
end
```

Including a hypothesis also includes all its type dependencies. Included
parameters remain in the theorem even when the proof does not use them.
Omitting a named instance disables its automatic inclusion; omitting a variable
needed by the theorem header or an included hypothesis is an error. Selections
refer to declared variable identities, preserve escaped names, are atomic on
errors, and are restored on section/namespace exit. They affect theorem headers,
not the used-variable generalization of definitions. Named selections persist
across later `variable` commands but never across source-file boundaries.

This increment covers definitions, theorems, named instances, records, classes,
and supported single or mutual inductive families. Variable binder-style changes,
instance-pattern `omit [Class ...]`, and command-local `in` scopes remain
unimplemented. This does not claim the whole source elaboration workstream or
Reference parity is complete.
The source regressions are `crates/fln/tests/source_section_variables.rs`;
parser layout and malformed-input tests live with the variable command parser.
## Records and classes

Section parameters also generalize `structure` and `class` declarations. The
selection spans written parameter types, physical parent/field types, and all
field-default bodies. Its transitive type dependencies are included in section
order before the written parameters. Unused variables and theorem-only
`include`/`omit` selections do not affect the record.

```lean
section
variable {A : Type} [inh : Inhabited A] (unused : Nat)
structure Defaulted where
  value : A := default
end
def defaulted : Defaulted (A := Nat) := {}
theorem works : defaulted.value = 0 := by rfl
```

Default helpers are closed only after the entire record's parameter list is
known. Even an early, constant default receives parameters discovered in a later
field or default. They use the same constructor-prefix telescope, including
inherited physical fields and dependent method arguments. This supports defaults,
updates, parent coercions and class instance search without leaking section locals
into the checked environment. Both checkers and the complete-batch publication
rule are unchanged. Generalized parameters count toward the record binder budget.

The additional regressions are `fln::source_section_records`.

## Inductive families

Supported single and mutual inductive declarations select section parameters from
the family signatures and every constructor field and result index. Type
dependencies and their universes close transitively. The selected parameters
precede written parameters and retain their original binder styles on the family;
constructor and recursor parameter conventions follow the existing generator.

```lean
section
variable (A : Type) (unused : Nat)
inductive Chain where
  | nil
  | cons (head : A) (tail : Chain)
end
def sum (xs : Chain Nat) : Nat := match xs with
  | .nil => 0
  | .cons n tail => n + sum tail
theorem computes : sum (Chain.cons 20 (Chain.cons 22 Chain.nil)) = 42 := by rfl
```

Recursive references inside a declaration still use its written-parameter
interface. When producing the closed candidate, each local family reference is
replaced by its constant applied to the captured section prefix. This is also
necessary for mutual blocks: every member shares the union of dependencies, even
when only a sibling's constructor mentions a section variable. Canonicalizing
written mutual parameters preserves the lexical section context.

The existing generator's positivity, uniformity, universe and binder-budget
checks and both admission engines remain authoritative. Invalid members, invalid
result ascriptions and late false proofs cannot publish a prefix. Indexed data,
proposition-valued single families, local dictionaries in constructor indices, and
namespace-qualified mutual groups have executable source-checking regressions
in `fln::source_section_inductives`. This does not expand the generator's supported
recursion shapes or provide general mutual-function execution.
