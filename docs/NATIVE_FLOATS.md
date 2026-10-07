# Native Float and Float32 source programs

The bounded source frontend accepts decimal and scientific literals, ordinary
numerals at `Float` and `Float32`, arithmetic negation, and numeric operator
notation. Checked terms retain the ordinary `OfScientific`, `OfNat`, `Neg`, and
heterogeneous operator class applications. The runtime executes supported
operations through the native floating-point VM rows.

```lean
def affine (x : Float) (slope : Float) : Float := x * slope + 0.5
def small : Float32 := -(1.5 + 2 * (4.0 - 0.5))

#eval affine 2.5 4.0
#eval small
#eval Float32.isInf (1.0 / 0.0)
#eval UInt64.toNat (Float.toUInt64 (1.5 + 2.25))
#eval Float.toString (2.1 : Float) ++ "!"
```

Run a source program with the native `lean` binary or
`cargo run --locked -p fln-cli --bin lean -- examples/native_floats.lean`.
Admission-only `fln check-source` accepts definitions and proofs and refuses
`#eval`; execution uses the source program path. The standalone example exercises
both precisions, function arguments, branches, captured values, and callbacks.
The runtime and CLI regression targets additionally cover conversions,
exceptional values, and string output.

## Elaboration and exact literal conversion

Literals such as `1.25`, `1.25e+2`, `125E-2`, and `1_2.3_4e5_6` use the pinned
lexer's spelling rules. The decimal significand and exponent become arbitrary
precision natural arguments, with a separate exponent-sign Boolean. Thus
`(1.25 : Float)` elaborates as
`OfScientific.ofScientific Float instOfScientificFloat (nat_lit 125) true (nat_lit 2)`.
The `nat_lit` notation here describes raw kernel literals; these arguments do not
recursively invoke `OfNat`.

The expected type selects the dictionary, including inside nested arithmetic
and function arguments. Unconstrained scientific literals default to `Float`;
the pinned default priority is `mid+1`, or 501, below the homogeneous operator
adapters at 1000. Explicit `Float32` contexts therefore reach the operands before
the `Float` fallback. Field notation defaults an unresolved numeric receiver
before method lookup, so `(2).succ` and `(1.5).abs` work. Source-defined scientific
dictionaries and heterogeneous operator dictionaries retain their chosen
implementations; a scientific literal is not intrinsically a machine float.

After admission by both checking engines, the runtime can lower a closed
canonical Float conversion to its bit representation. This uses the pinned
`Float.ofScientific` integer algorithm, including its intermediate truncation and
rounding, rather than parsing the spelling with the host's floating-point parser.
The checked declaration remains unchanged. Intermediate arithmetic is bounded by
the executable-literal byte limit and a ceiling of 4096 64-bit limbs; exhaustion
is a typed resource refusal.

## Supported runtime surface and boundaries

The source bridge supplies separate `Float`, `Float32`, `UInt32`, and `UInt64`
representations. Floating-point arithmetic, negation, absolute value,
classifications, supported comparisons, precision conversions, bit conversions,
unsigned integer conversions, and `toString` route to their native VM operations.
The unary math surface — `sqrt`, `ceil`, `floor`, `round`, `sin`, `cos`, `tan`,
`asin`, `acos`, `atan`, `sinh`, `cosh`, `tanh`, `asinh`, `acosh`, `atanh`,
`exp`, `exp2`, `log`, `log2`, `log10`, `cbrt` — and the binary `pow` and
`atan2` (argument order `atan2 (y x)`, as in the pin) execute on `fln-libm`,
the owned deterministic numerics plane (plan §6.8, D21), at each width's own
precision. Results are therefore bit-identical across hosts by construction and
are **not** claimed to match the pin's platform-libm bits ULP-for-ULP; a
domain-edge input (for example `Float.log (-1.0)`) yields the canonical NaN
value, never a refusal. `Float.frExp` (pair result) and `Float.scaleB` (an
`Int` exponent) remain unsupported and refuse typed.
Values can be passed to source functions, reused in locals, selected by branches,
and captured by closures. Printing uses each value's actual runtime type; the
numeric bit payload alone does not determine its display.

The native source seed is a bounded collection of checked declarations and
registered class metadata. Its Float types and primitive declarations are
explicit native seed contracts. This does not establish full imported `Init`
declaration equality, complete `FloatSpec` support, or whole-toolchain T2 parity.
Reference `.olean` class and instance extensions are not yet replayed into the
native registry. The class-free raw-Nat fixture and current imported-declaration
path keep their existing behavior; they do not acquire fabricated dictionaries.
Unsigned types currently expose the conversion operations required by this
bridge, not a complete unsigned arithmetic source library. General runtime
scientific conversion with nonconstant mantissa or exponent remains unsupported,
including `Float.ofNat` or `Float32.ofNat` applied to a computed natural value.

Regression targets are `fln::source_numeric_literals`,
`fln::runtime_float_source`, `fln-cli::source_floats`, the parser's scientific
literal/negation test, the elaborator's raw scientific component test, and
`fln-vm::scientific`. They cover checked term structure, contextual precision,
custom and heterogeneous instances, native execution, ownership-sensitive reuse,
negative zero, conversions, output, and fail-closed publication. Reference
semantics are anchored in the pinned `Init/Data/OfScientific.lean`,
`Init/Meta/Defs.lean`, `Lean/Elab/BuiltinTerm.lean`, and `Lean/Elab/Extra.lean`.
