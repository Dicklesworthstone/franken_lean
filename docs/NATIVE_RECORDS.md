# Native source records and classes

The import-free `check-source` path accepts named nonrecursive `structure` and
`class` declarations. Records are ordinary one-constructor inductive blocks with
regenerated eliminators and generated projections. Each block and projection
passes K1 and the independent checker; class registration happens only after the
complete declaration batch succeeds. This is not a new admission authority.

```lean
structure Package where
  carrier : Type
  value : carrier

def wrapped : Package := Package.mk Nat 23
theorem wrapped_ok : Package.value wrapped = 23 := by rfl

class Choice (A : Type) where
  value : A

instance natChoice : Choice Nat := Choice.mk 11
instance functionChoice {A : Type} [Choice A] : Choice (Nat -> A) :=
  Choice.mk (fun x => Choice.value)

def chosen : Nat -> Nat -> Nat := Choice.value
theorem chosen_ok : chosen 4 5 = 11 := by rfl
```

Run `fln check-source --json examples/native_records.lean` with an installed build.
The command checks the file; it does not compile or execute its declarations.

Header parameters use the existing dependent/implicit/instance binder elaborator.
Named field types can refer to those parameters and earlier fields. Method
signatures such as `transform (x : A) : A` become dependent function-valued fields.
Field/result types are elaborated in their real local scopes, not substituted
textually. In the absence of a result annotation, the positive record universe
is inferred from the field domains; a field `carrier : Type` therefore raises
the universe instead of incorrectly putting its record in `Type`. An explicit
result annotation is checked normally and is not widened to hide a mismatch.

Constructors and ordinary projections infer record parameters. Class projections
have instance-implicit receivers and therefore use the existing local/global
instance engine. Regular structures are not registered as classes. Later commands
and later supplied files can use successful records, projections, and instances.

`Engine::admit_source_command` returns a `DeclarationBatchAdmission`, preserving
the individual block/projection admission records and the final successor root.
The earlier `admit_source_declaration` API retains its one-declaration contract.
`check_source_files` uses the batch-aware command path. Command counts describe
source commands, not the number of generated kernel declarations.

A collision on a late projection, a checker refusal, a registration error, or a
later file failure exposes no successful prefix. Invalid field scopes, duplicate
fields, unresolved holes, unsupported result sorts, malformed indentation, and
unsupported syntax are refused. Resource stops remain distinct from rejection.

Current scope: simple named fields, typed method arguments, empty records,
nonrecursive Type-valued records, and named class/instance declarations. Source
inheritance, custom constructor names, grouped fields, deriving,
explicit universe-polymorphic headers, numeric
projections and general extended field notation remain outside this increment. Core `RecordSpec` generation supports universe
parameters separately; this is not evidence for full source-level universe or
Reference record elaboration parity. Built-in-name checker specializations may
also refuse incompatible user declarations with those names.

Regression targets: `fln::source_records`, `fln::record_generation`, parser record
roundtrips/refusals, and `fln-cli::source_check`, plus the existing frontend, proof,
instance and engine tests. Positive tests use real checking engines, including
dependent projection conversion and recursive dictionaries of user-defined classes.

## Constructing and accessing records

Named-field literals now elaborate against their expected or explicit record type:

```lean
structure Package where
  carrier : Type
  value : carrier

def wrapped : Package := { value := 23, carrier := Nat }
def unpack (p : Package) : p.carrier := p.value
theorem wrapped_ok : (wrapped).value = 23 := by rfl
```

Values are elaborated in constructor-field order, even when written in a different
order, so each dependent field receives the actual earlier values in its expected
type. Nested literals, method lambdas, proof terms, punned fields (`{ value }`),
empty records and a trailing comma are supported. Either `{ value := 7 : Box Nat }`
or `({ value := 7 } : Box Nat)` supplies an explicit type. Fields without registered defaults must be
present exactly once; unknown, duplicate, missing required, ill-typed or unresolved fields
are refused. No record type is guessed from field labels.

Field access supports both `receiver.field` and `(expression).field`, including
chained paths and function-valued fields. Dependent projection types retain the
actual receiver. Explicit class receivers are applied directly rather than
replaced with a dictionary from instance search. Exact local/global qualified
names are resolved first; only unresolved names fall back to field access.
Escaped dots remain parts of an identifier, not path separators.

Field receivers insert ordinary implicit and instance arguments. For example,
`point.x` and `(point).x` work when `point [Inhabited Nat] : Point` needs a
dictionary. Known dictionaries are resolved before selecting the record type;
unknown class inputs remain deferred so the expected field type can infer them.
The actual receiver is preserved even when it returns a class dictionary and a
different ambient instance exists. Strict-implicit and explicit receiver arguments
remain unapplied; field access does not count as an explicit argument.

Type annotations also insert ordinary implicit and instance arguments. A class
projection such as `Factory.carrier` can supply a declaration or binder type,
an arrow operand, a let or term annotation, or an explicit record type.
Later binders can constrain earlier implicit types before the complete header
resolves its instance goals. An explicit result annotation must leave the entire
header resolved before the body; an inferred result can still determine ordinary
parameter holes. Nested annotations retain the surrounding term's inference.
Ascriptions preserve the value's actual type for instance selection while keeping
the written annotation in the checked term. Lambdas can infer their function type
when an annotation leaves it unknown and any required dictionary is available;
a known non-function type is still refused.
Strict-implicit and explicit type-function parameters remain unapplied.
Nested let expressions remain outside the bounded source parser's grammar;
the supported top-level let chain retains its local dictionaries.

This bounded field notation selects actual named fields of admitted single-
constructor records. It does not search arbitrary namespace functions, base
structures or numeric fields. Literal fields currently require comma separators;
inheritance and omitted required fields remain explicit unsupported cases. Parsing and elaboration use heap worklists, including nested literals and
parenthesized type ascriptions.

`examples/native_record_values.lean` exercises dependent fields and explicit versus
inferred class receivers through the installed `fln check-source --json` command.
The `fln::source_record_literals` tests cover failure atomicity as well as positive
kernel/checker acceptance; installed CLI tests verify the same code path.

## Checked field defaults

A typed field or method can provide `:= value`. Defaults elaborate in the real
context of the record parameters, earlier fields and that method's arguments:

```lean
structure Config where
  base : Nat := 3
  twice : Nat := base + base
  transform (x : Nat) : Nat := x + twice

def standard : Config := {}
def custom : Config := { base := 7 }
def copied := { custom with base := 20 }

theorem standard_ok : standard.twice = 6 := by rfl
theorem custom_ok : custom.twice = 14 := by rfl
theorem copied_ok : copied.twice = 14 := by rfl
```

Explicit fields take precedence, then ordered update sources, then registered
defaults. Each default receives the actual preceding values, not their original
default expressions. Updates therefore preserve copied fields and do not
recompute them when an earlier field changes. Dependent types, function fields,
nested record literals, local lets, and class instance parameters use the same
elaborator as ordinary source terms. Class dictionaries can be built from `{}`
when every field has a default.

The elaborator emits ordinary safe helper definitions named
`Record.field._default`, closed over the parameters and preceding fields. Every
helper passes K1 and the independent checker as part of the complete record
batch, even when a later literal would override its field. A native versioned
journal registers references only after the full batch succeeds; registration
validates each helper against the constructor field's complete telescope. The
successor logical root includes this journal. A similarly named definition with
no registration is never selected as a default. Malformed metadata, signature
mismatches, duplicate registrations, and resource exhaustion are visible failures.
There is no separate default-value admission authority.

Defaults must type-check for the declared preceding fields: a proof default
cannot assume that an overridable preceding value equals its default expression.
Forward references, implicit field-type inference, inheritance and field-level
`tactic` defaults remain outside this bounded increment. This native journal is
not Reference `.olean` structure-extension parity.

Run `fln check-source --json examples/native_record_defaults.lean` to exercise the
checked example. Regressions live in `fln::source_record_defaults`, the parser's
record tests, the default registry's malformed-input tests, and the installed
CLI `source_check` tests. These are scoped execution checks, not a full Lean
compatibility claim.
