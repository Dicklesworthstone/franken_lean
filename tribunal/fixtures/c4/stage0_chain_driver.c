/* stage0 module-DAG execution driver (bead franken_lean-83r slice 5; plan
 * §6.6/§18.2).
 *
 * Slice 4 proved one module (Init/Prelude.o) executes on Marrow. This driver
 * proves the MODULE INITIALIZER DAG does: Init/SizeOf's generated initializer
 * chains through Init/Tactics and Init/Notation into Init/Coe and
 * Init/Prelude — a diamond (SizeOf -> {Notation, Tactics}, Tactics ->
 * Notation) whose shared nodes must initialize exactly once through the
 * generated once-guards, with every static Name/string/closure of five real
 * translation units minted through the membrane. Re-initialization of an
 * already-initialized module (both at the DAG root and at a leaf) must be an
 * observable no-op, and cross-module values must flow: a SizeOf-instance
 * closure applied through the membrane yields Nats that Prelude's generated
 * decidable equality then consumes.
 *
 * The same driver plus the SAME five .o files linked against libleanshared
 * must emit byte-identical facts. TEST APPARATUS ONLY (D8): stage0 code never
 * enters a release artifact.
 */

#include <lean/lean.h>
#include <stdio.h>

/* stage0 exports, declared exactly as generated C declares them across
 * translation units. */
extern lean_object *initialize_Init_SizeOf(uint8_t builtin);
extern lean_object *initialize_Init_Prelude(uint8_t builtin);
extern const lean_object *l_instSizeOfNat;
extern lean_object *l_instSizeOfNat___lam__0___boxed(lean_object *);
extern uint8_t l_instDecidableEqNat(lean_object *, lean_object *);

static void fact(const char *probe, long long value) {
    printf("{\"schema\":\"fln-83r-stage0-chain/1\",\"probe\":\"%s\",\"value\":%lld}\n",
           probe, value);
}

int main(void) {
    /* The DAG root: initializing SizeOf must chain-initialize Tactics,
     * Notation, Coe and Prelude in generated order. */
    lean_object *res = initialize_Init_SizeOf(1);
    fact("chain.init_sizeof.ok", !lean_io_result_is_error(res));
    lean_dec_ref(res);

    /* Root re-initialization: the module's own once-guard must short-circuit
     * to a fresh io-ok without re-running anything observable. */
    res = initialize_Init_SizeOf(1);
    fact("chain.init_sizeof.again_ok", !lean_io_result_is_error(res));
    lean_dec_ref(res);

    /* Leaf re-initialization: Prelude was initialized THROUGH the chain, so
     * its guard must already be set when called directly. */
    res = initialize_Init_Prelude(1);
    fact("chain.init_prelude.after_chain_ok", !lean_io_result_is_error(res));
    lean_dec_ref(res);

    /* The SizeOf Nat instance is a static generated closure (the compiler
     * unboxes the trivial instance). Emit its observable shape as facts —
     * the differential decides, not this driver's assumptions. */
    lean_object *sizeof_fn = (lean_object *)l_instSizeOfNat;
    fact("chain.instSizeOfNat.tag", lean_ptr_tag(sizeof_fn));
    fact("chain.instSizeOfNat.arity", lean_closure_arity(sizeof_fn));

    /* Closure application through the membrane, scalar operand. */
    lean_inc(sizeof_fn);
    lean_object *n = lean_apply_1(sizeof_fn, lean_box(42));
    fact("chain.sizeof_nat.scalar_is_scalar", lean_is_scalar(n));
    fact("chain.sizeof_nat.scalar", (long long)lean_unbox(n));

    /* Bignum operand: the result crosses back into Prelude's generated
     * decidable equality — a cross-module value flow over the membrane. */
    lean_inc(sizeof_fn);
    lean_object *big = lean_big_uint64_to_nat(0xFFFFFFFFFFFFFFFFull);
    lean_object *big_sz = lean_apply_1(sizeof_fn, big);
    fact("chain.sizeof_nat.big_is_scalar", lean_is_scalar(big_sz));
    lean_object *big_expect = lean_big_uint64_to_nat(0xFFFFFFFFFFFFFFFFull);
    fact("chain.sizeof_nat.big_eq", l_instDecidableEqNat(big_sz, big_expect));

    /* The generated lambda called directly, no apply machinery. */
    lean_object *direct = l_instSizeOfNat___lam__0___boxed(lean_box(9));
    fact("chain.lam0.direct", (long long)lean_unbox(direct));

    return 0;
}
