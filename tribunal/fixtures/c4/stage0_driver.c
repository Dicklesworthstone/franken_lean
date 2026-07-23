/* stage0 execution driver (bead franken_lean-83r slice 4; plan §6.6/§18.2).
 *
 * THE membrane test: the Reference's own stage0-generated Init/Prelude.c —
 * compiled untouched from the pinned tree — is linked against Marrow's
 * exported lean_* surface and EXECUTED: its module initializer runs (every
 * static Name/string/closure minted through our membrane, once cells, marks,
 * bignum literals), then real generated functions are called, including
 * closure application through a generated instance object. The same driver
 * plus the SAME Prelude.o linked against libleanshared must emit
 * byte-identical facts.
 *
 * TEST APPARATUS ONLY (D8): stage0 code never enters a release artifact.
 */

#include <lean/lean.h>
#include <stdio.h>

/* stage0 Init/Prelude.c exports (declared here exactly as generated C
 * declares them across translation units). */
extern lean_object *initialize_Init_Prelude(uint8_t builtin);
extern const lean_object *l_instAddNat;
extern const lean_object *l_instMulNat;
extern uint8_t l_instDecidableEqNat(lean_object *, lean_object *);
extern uint8_t l_Bool_not(uint8_t);

static void fact(const char *probe, long long value) {
    printf("{\"schema\":\"fln-83r-stage0-driver/1\",\"probe\":\"%s\",\"value\":%lld}\n",
           probe, value);
}

int main(void) {
    /* The real generated module initializer, on whichever runtime is
     * underneath. builtin=1 is the toolchain posture. */
    lean_object *res = initialize_Init_Prelude(1);
    fact("stage0.init.ok", !lean_io_result_is_error(res));
    lean_dec_ref(res);

    /* Generated decidable equality over Nat — scalar and bignum operands
     * (args are consumed by the generated code). */
    fact("stage0.decEqNat.eq", l_instDecidableEqNat(lean_box(7), lean_box(7)));
    fact("stage0.decEqNat.ne", l_instDecidableEqNat(lean_box(7), lean_box(8)));
    lean_object *b1 = lean_big_uint64_to_nat(0xFFFFFFFFFFFFFFFFull);
    lean_object *b2 = lean_big_uint64_to_nat(0xFFFFFFFFFFFFFFFFull);
    fact("stage0.decEqNat.big", l_instDecidableEqNat(b1, b2));

    /* Generated pure function on scalars. */
    fact("stage0.bool_not", l_Bool_not(1));

    /* Closure application through REAL generated instance objects. The
     * compiler unboxes the trivial `Add Nat`/`Mul Nat` structures, so the
     * static instances ARE the operation closures directly (tag 245). */
    lean_object *add_fn = (lean_object *)l_instAddNat;
    fact("stage0.instAdd.is_closure", lean_ptr_tag(add_fn) == LeanClosure);
    lean_inc(add_fn); /* persistent: a no-op, but the ownership shape of a caller */
    lean_object *sum = lean_apply_2(add_fn, lean_box(20), lean_box(22));
    fact("stage0.instAdd.apply", (long long)lean_unbox(sum));

    lean_object *mul_fn = (lean_object *)l_instMulNat;
    lean_inc(mul_fn);
    lean_object *prod = lean_apply_2(mul_fn, lean_box(6), lean_box(7));
    fact("stage0.instMul.apply", (long long)lean_unbox(prod));

    /* Under-application through the same generated closure: fix one
     * argument (a fresh curried closure is minted through OUR membrane),
     * then apply the rest. */
    lean_object *mul_fn2 = (lean_object *)l_instMulNat;
    lean_inc(mul_fn2);
    lean_object *times9 = lean_apply_1(mul_fn2, lean_box(9));
    fact("stage0.curry.tag_is_closure", lean_ptr_tag(times9) == LeanClosure);
    lean_object *r63 = lean_apply_1(times9, lean_box(7));
    fact("stage0.curry.apply", (long long)lean_unbox(r63));

    return 0;
}
