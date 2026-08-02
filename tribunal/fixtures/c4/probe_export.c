/* stage0 ABI gauntlet probe, export direction (corpus family C4, plan §18.2;
 * bead franken_lean-83r). Compiled by the optional D2 system C compiler as
 * TEST APPARATUS ONLY (§6.6) against the PINNED toolchain's lean.h — then
 * linked TWICE: once to the real Reference runtime (libleanshared) and once
 * to Marrow's exported lean_* surface (the fln-unsafe-abi staticlib). The
 * same binary source, the same inline layer, two runtimes underneath: the
 * emitted NDJSON facts must be byte-identical, and the panic modes must
 * terminate with identical exit codes and stderr.
 *
 * Everything here reaches the runtime through the lean.h inlines exactly as
 * stage0-generated C does — allocation lands on mi_malloc_small /
 * lean_alloc_object, release on lean_dec_ref_cold / lean_free_object /
 * mi_free — so the link set is precisely the slice-1 implemented tranche of
 * ci/ABI_EXPORT_STATUS.txt.
 *
 * Modes: no argument = fact emission; "panic-internal" = lean_internal_panic
 * (expect exit 1, "INTERNAL PANIC: …" on stderr); "panic-fn" =
 * exit-on-panic lean_panic_fn (expect exit 1, message on stderr — the
 * exit path writes to the PROCESS stderr in both runtimes, so the
 * Lean-IO-buffer restriction of the non-exiting path never enters the
 * differential); "panic-promise-new" = lean_io_promise_new before any task
 * manager runs (expect exit 1, the pin's named INTERNAL PANIC — both
 * runtimes refuse identically, fln-3gv slice 2); "panic-get-or-block-none" =
 * exit-on-panic lean_option_get_or_block(none) (expect exit 1, the pin's
 * "PANIC: Promise.result!: …" line).
 */

#include <lean/lean.h>
#include <stdio.h>
#include <string.h>

static void fact(const char *probe, long long value) {
    printf("{\"schema\":\"fln-83r-gauntlet-probe/1\",\"probe\":\"%s\",\"value\":%lld}\n",
           probe, value);
}

static long long bytesum(const char *p, size_t n) {
    long long s = 0;
    for (size_t i = 0; i < n; i++) s += (unsigned char)p[i];
    return s;
}

/* fln-3gv slice 1 externs the pin's lean.h does not declare (extern-census
 * class, like lean_sorry): declared here exactly as generated C declares
 * them. */
extern lean_object *lean_st_ref_take(lean_object *ref);
extern uint8_t lean_st_ref_ptr_eq(lean_object *ref1, lean_object *ref2);
extern uint8_t lean_system_platform_windows(lean_object *w);
extern uint8_t lean_system_platform_osx(lean_object *w);
extern uint8_t lean_system_platform_emscripten(lean_object *w);

/* fln-3gv slice 2 externs (extern-census class): the promise/task-state
 * wrappers the runtime exports outside lean.h, declared here exactly as
 * generated C declares them (stage0 Init/System/Promise.c:16-25). */
extern lean_object *lean_io_promise_new();
extern lean_object *lean_io_promise_resolve(lean_object *value, lean_object *promise);
extern lean_object *lean_io_promise_result_opt(lean_object *promise);
extern uint8_t lean_io_get_task_state(lean_object *t);
extern lean_object *lean_option_get_or_block(lean_object *opt);

/* Apply targets for the task facts, closured exactly as generated C does. */
static lean_object *probe_double(lean_object *x) {
    return lean_box(lean_unbox(x) * 2);
}
static lean_object *probe_str_size(lean_object *s) {
    lean_object *r = lean_box(lean_string_size(s));
    lean_dec(s);
    return r;
}

static void facts_mode(void) {
    /* ---- ctor through the inline small path (mi_malloc_small underneath) */
    lean_object *o = lean_alloc_ctor(2, 2, 8);
    lean_ctor_set(o, 0, lean_box(41));
    lean_ctor_set(o, 1, lean_box(42));
    lean_ctor_set_uint64(o, 16, 0xFEEDFACEu);
    fact("ctor.tag", lean_ptr_tag(o));
    fact("ctor.num_objs", o->m_other);
    fact("ctor.byte_size", (long long)lean_object_byte_size(o));
    fact("ctor.data_byte_size", (long long)lean_object_data_byte_size(o));
    fact("ctor.scalar_readback", (long long)lean_ctor_get_uint64(o, 16));
    fact("ctor.child0_unboxed", (long long)lean_unbox(lean_ctor_get(o, 0)));
    lean_inc(o);
    fact("ctor.rc_after_inc", o->m_rc);
    lean_dec(o);
    fact("ctor.rc_after_dec", o->m_rc);
    lean_dec(o); /* death through lean_dec_ref_cold */

    /* ---- child teardown through the exported cold path (mutant 83r-M1's
     * discriminator: a no-op lean_dec_ref_cold leaves the child at 2) */
    lean_object *child = lean_mk_string("child");
    lean_inc(child);
    lean_object *parent = lean_alloc_ctor(0, 1, 0);
    lean_ctor_set(parent, 0, child);
    lean_dec(parent);
    fact("rc.child.after_parent_death", child->m_rc);
    lean_dec(child);

    /* ---- strings: the exported constructor family */
    lean_object *s = lean_mk_string("h\xc3\xa9llo");
    fact("string.size", (long long)lean_string_size(s));
    fact("string.len", (long long)lean_string_len(s));
    fact("string.byte_size", (long long)lean_object_byte_size(s));
    fact("string.data_byte_size", (long long)lean_object_data_byte_size(s));
    fact("string.bytesum", bytesum(lean_string_cstr(s), lean_string_size(s)));
    lean_object *t = lean_mk_string("h\xc3\xa9llo");
    lean_object *u = lean_mk_string("h\xc3\xa9llp");
    fact("string.eq", lean_string_eq(s, t));
    fact("string.ne", lean_string_eq(s, u));

    /* lossy recovery (object.cpp:1989-2012): U+FFFD, count includes it */
    lean_object *b = lean_mk_string_from_bytes("ab\xff" "cd", 5);
    fact("string.lossy.size", (long long)lean_string_size(b));
    fact("string.lossy.len", (long long)lean_string_len(b));
    fact("string.lossy.bytesum", bytesum(lean_string_cstr(b), lean_string_size(b)));

    /* the pin's bug-compatible garbage stepping */
    fact("utf8.strlen", (long long)lean_utf8_strlen("h\xc3\xa9llo"));
    fact("utf8.n_strlen.garbage", (long long)lean_utf8_n_strlen("\xff" "abc", 4));

    lean_dec(s); lean_dec(t); lean_dec(u); lean_dec(b);

    /* ---- array / sarray through the exported big path */
    lean_object *a = lean_alloc_array(2, 4);
    lean_array_cptr(a)[0] = lean_box(7);
    lean_array_cptr(a)[1] = lean_box(9);
    fact("array.byte_size", (long long)lean_object_byte_size(a));
    fact("array.data_byte_size", (long long)lean_object_data_byte_size(a));
    fact("array.cs_sz_is_zero", a->m_cs_sz == 0);
    lean_dec(a);
    lean_object *sa = lean_alloc_sarray(1, 3, 3);
    lean_sarray_cptr(sa)[0] = 1; lean_sarray_cptr(sa)[1] = 2; lean_sarray_cptr(sa)[2] = 3;
    fact("sarray.byte_size", (long long)lean_object_byte_size(sa));
    fact("sarray.data_byte_size", (long long)lean_object_data_byte_size(sa));
    lean_dec(sa);

    /* ---- persistence through the exported mark */
    lean_object *p = lean_alloc_ctor(3, 0, 0);
    lean_mark_persistent(p);
    fact("rc.persistent.after_mark", p->m_rc);
    lean_inc(p); /* persistent objects are never counted */
    fact("rc.persistent.after_inc", p->m_rc);
    /* deliberately leaked, exactly as compact-region residents are */

    /* ---- slice 2: List ⇄ Array through the exported conversions */
    lean_object *lst = lean_box(0);
    for (int i = 3; i >= 1; i--) { /* [10, 20, 30] */
        lean_object *cell = lean_alloc_ctor(1, 2, 0);
        lean_ctor_set(cell, 0, lean_box(10 * i));
        lean_ctor_set(cell, 1, lst);
        lst = cell;
    }
    lean_object *am = lean_array_mk(lst);
    fact("array_mk.size", (long long)lean_array_size(am));
    fact("array_mk.capacity", (long long)lean_array_capacity(am));
    fact("array_mk.elem0", (long long)lean_unbox(lean_array_cptr(am)[0]));
    fact("array_mk.elem2", (long long)lean_unbox(lean_array_cptr(am)[2]));
    lean_object *back = lean_array_to_list(am);
    long long list_sum = 0, list_len = 0;
    for (lean_object *c2 = back; !lean_is_scalar(c2); c2 = lean_ctor_get(c2, 1)) {
        list_sum += lean_unbox(lean_ctor_get(c2, 0));
        list_len++;
    }
    fact("array_to_list.len", list_len);
    fact("array_to_list.sum", list_sum);
    lean_dec(back);

    /* ---- slice 2: the exact push growth laws */
    lean_object *pa = lean_alloc_array(0, 0);
    for (int i = 0; i < 3; i++) pa = lean_array_push(pa, lean_box(i));
    fact("array_push.size", (long long)lean_array_size(pa));
    fact("array_push.capacity", (long long)lean_array_capacity(pa));
    lean_inc(pa); /* shared push takes the nonlinear copy path */
    lean_object *pb = lean_array_push(pa, lean_box(9));
    fact("array_push.shared.orig_size", (long long)lean_array_size(pa));
    fact("array_push.shared.new_size", (long long)lean_array_size(pb));
    fact("array_push.shared.new_capacity", (long long)lean_array_capacity(pb));
    lean_dec(pb);
    lean_dec(pa);

    /* ---- slice 2: byte arrays */
    lean_object *bsrc = lean_alloc_array(3, 3);
    lean_array_cptr(bsrc)[0] = lean_box(7);
    lean_array_cptr(bsrc)[1] = lean_box(8);
    lean_array_cptr(bsrc)[2] = lean_box(9);
    lean_object *bm = lean_byte_array_mk(bsrc);
    fact("byte_array_mk.size", (long long)lean_sarray_size(bm));
    fact("byte_array_mk.bytesum", bytesum((char const *)lean_sarray_cptr(bm), 3));
    bm = lean_byte_array_push(bm, 0xAB);
    fact("byte_array_push.size", (long long)lean_sarray_size(bm));
    fact("byte_array_push.capacity", (long long)lean_sarray_capacity(bm));
    lean_object *bd = lean_byte_array_data(bm);
    fact("byte_array_data.size", (long long)lean_array_size(bd));
    fact("byte_array_data.elem3", (long long)lean_unbox(lean_array_cptr(bd)[3]));
    lean_dec(bd);

    /* ---- slice 3: bignum-backed Nat families */
    lean_object *big = lean_big_uint64_to_nat(0xFFFFFFFFFFFFFFFFull); /* 2^64-1 */
    fact("nat.big.is_scalar", lean_is_scalar(big));
    lean_object *big2 = lean_nat_big_add(big, lean_box(1)); /* 2^64, mpz */
    fact("nat.add.is_scalar", lean_is_scalar(big2));
    lean_object *one = lean_nat_big_sub(big2, big);
    fact("nat.sub.normalized", lean_is_scalar(one));
    fact("nat.sub.value", (long long)lean_unbox(one));
    fact("nat.sub.underflow", (long long)lean_unbox(lean_nat_big_sub(lean_box(5), big)));
    fact("nat.mul.zero", (long long)lean_unbox(lean_nat_big_mul(lean_box(0), big)));
    lean_object *sq = lean_nat_big_mul(big, big);
    fact("nat.mul.big_is_scalar", lean_is_scalar(sq));
    fact("nat.div.small", (long long)lean_unbox(lean_nat_big_div(lean_box(7), big)));
    fact("nat.div.by_zero", (long long)lean_unbox(lean_nat_big_div(big, lean_box(0))));
    fact("nat.div.value", (long long)lean_unbox(lean_nat_big_div(big2, big)));
    fact("nat.mod.small", (long long)lean_unbox(lean_nat_big_mod(lean_box(9), big)));
    lean_object *modz = lean_nat_big_mod(big, lean_box(0)); /* retained input */
    fact("nat.mod.by_zero.same", modz == big);
    fact("nat.mod.by_zero.rc", big->m_rc);
    lean_dec(modz);
    fact("nat.mod.value", (long long)lean_unbox(lean_nat_big_mod(big2, big)));
    fact("nat.eq.mixed", lean_nat_big_eq(lean_box(3), big));
    fact("nat.eq.same", lean_nat_big_eq(big, big));
    fact("nat.le.scalar_big", lean_nat_big_le(lean_box(3), big));
    fact("nat.le.big_scalar", lean_nat_big_le(big, lean_box(3)));
    fact("nat.lt.big_big", lean_nat_big_lt(big, big2));
    lean_object *pw = lean_nat_pow(lean_box(2), lean_box(80));
    fact("nat.pow.is_scalar", lean_is_scalar(pw));
    uint64_t pw64 = lean_uint64_of_big_nat(pw);
    fact("nat.pow.trunc64", (long long)pw64);
    lean_object *of = lean_nat_overflow_mul((size_t)1 << 40, (size_t)1 << 40);
    fact("nat.overflow_mul.is_scalar", lean_is_scalar(of));
    fact("nat.overflow_mul.trunc64", (long long)lean_uint64_of_big_nat(of));
    lean_object *c128 = lean_cstr_to_nat("340282366920938463463374607431768211457");
    fact("nat.cstr.usize_trunc", (long long)lean_usize_of_big_nat(c128));
    fact("nat.cstr.u8_trunc", lean_uint8_of_big_nat(c128));
    uint64_t bt = lean_uint64_of_big_nat(big);
    fact("nat.trunc64.hi", (long long)(bt >> 32));
    fact("nat.trunc64.lo", (long long)(bt & 0xFFFFFFFFu));
    lean_object *sou = lean_string_of_usize(9007199254740993);
    fact("nat.string_of_usize.bytesum", bytesum(lean_string_cstr(sou), lean_string_size(sou)));
    lean_dec(sou);
    lean_dec(one); lean_dec(sq); lean_dec(pw); lean_dec(of); lean_dec(c128);
    lean_dec(big2); lean_dec(big);

    /* ---- slice 3: Name equality (hash at scalar offset 16, prefix walk) */
    {
        lean_object *anon = lean_box(0);
        lean_object *s1 = lean_mk_string("foo");
        lean_object *nm1 = lean_alloc_ctor(1, 2, 8);
        lean_ctor_set(nm1, 0, anon); lean_ctor_set(nm1, 1, s1);
        lean_ctor_set_uint64(nm1, 16, 0x1234);
        lean_object *s2 = lean_mk_string("foo");
        lean_object *nm2 = lean_alloc_ctor(1, 2, 8);
        lean_ctor_set(nm2, 0, anon); lean_ctor_set(nm2, 1, s2);
        lean_ctor_set_uint64(nm2, 16, 0x1234);
        lean_object *s3 = lean_mk_string("bar");
        lean_object *nm3 = lean_alloc_ctor(1, 2, 8);
        lean_ctor_set(nm3, 0, anon); lean_ctor_set(nm3, 1, s3);
        lean_ctor_set_uint64(nm3, 16, 0x1234);
        fact("name.eq.structural", lean_name_eq(nm1, nm2));
        fact("name.eq.text_differs", lean_name_eq(nm1, nm3));
        fact("name.eq.scalar_vs_node", lean_name_eq(anon, nm1));
        lean_dec(nm1); lean_dec(nm2); lean_dec(nm3);
    }

    /* ---- slice 2: String ⇄ List Char + the hash */
    lean_object *sm = lean_mk_string("h\xc3\xa9llo");
    uint64_t hh = lean_string_hash(sm);
    fact("string_hash.hi", (long long)(hh >> 32));
    fact("string_hash.lo", (long long)(hh & 0xFFFFFFFFu));
    lean_inc(sm);
    lean_object *chars = lean_string_data(sm);
    long long char_len = 0, char_sum = 0;
    for (lean_object *c3 = chars; !lean_is_scalar(c3); c3 = lean_ctor_get(c3, 1)) {
        char_sum += lean_unbox(lean_ctor_get(c3, 0));
        char_len++;
    }
    fact("string_data.len", char_len);
    fact("string_data.codesum", char_sum);
    lean_object *sm2 = lean_string_mk(chars);
    fact("string_mk.roundtrip_eq", lean_string_eq(sm, sm2));
    lean_dec(sm);
    lean_dec(sm2);

    /* ---- fln-3gv slice 1: ST refs, utf8 get/set, platform ---- */
    lean_object *cell = lean_st_mk_ref(lean_box(11));
    fact("st_ref.get0", (long long)lean_unbox(lean_st_ref_get(cell)));
    lean_dec(lean_st_ref_set(cell, lean_box(22)));
    fact("st_ref.swap_old", (long long)lean_unbox(lean_st_ref_swap(cell, lean_box(33))));
    fact("st_ref.taken", (long long)lean_unbox(lean_st_ref_take(cell)));
    lean_dec(lean_st_ref_set(cell, lean_box(44)));
    fact("st_ref.ptr_eq_self", lean_st_ref_ptr_eq(cell, cell));
    lean_object *cell2 = lean_st_mk_ref(lean_box(44));
    fact("st_ref.ptr_eq_other", lean_st_ref_ptr_eq(cell, cell2));
    lean_object *sv = lean_mk_string("refcell");
    lean_dec(lean_st_ref_set(cell, sv));
    lean_object *sg = lean_st_ref_get(cell);
    fact("st_ref.str_size", (long long)lean_string_size(sg) - 1);
    lean_dec(sg);
    lean_dec(cell);
    lean_dec(cell2);
    lean_object *u8s = lean_mk_string("h\xc3\xa9llo");
    fact("utf8.get0", lean_string_utf8_get(u8s, lean_box(0)));
    fact("utf8.get1", lean_string_utf8_get(u8s, lean_box(1)));
    fact("utf8.get_cont", lean_string_utf8_get(u8s, lean_box(2)));
    fact("utf8.get_oob", lean_string_utf8_get(u8s, lean_box(99)));
    u8s = lean_string_utf8_set(u8s, lean_box(0), 'H');
    fact("utf8.set_ascii_get0", lean_string_utf8_get(u8s, lean_box(0)));
    u8s = lean_string_utf8_set(u8s, lean_box(1), 0x2603);
    fact("utf8.set_multi_get1", lean_string_utf8_get(u8s, lean_box(1)));
    fact("utf8.after_set_size", (long long)lean_string_size(u8s) - 1);
    fact("utf8.after_set_len", (long long)lean_string_len(u8s));
    lean_dec(u8s);
    fact("platform.windows", lean_system_platform_windows(lean_box(0)));
    fact("platform.osx", lean_system_platform_osx(lean_box(0)));
    fact("platform.emscripten", lean_system_platform_emscripten(lean_box(0)));

    /* ---- fln-3gv slice 2: the promise/task-state family (managerless
     * envelope — no lean_init_task_manager anywhere in this probe, so the
     * Reference serves every fact below through its own explicit
     * !g_task_manager arms: object.cpp:1162/1176/1187/1260, io.cpp:1627) */
    lean_object *tp = lean_task_pure(lean_box(21));
    fact("task.pure.state", lean_io_get_task_state(tp));
    fact("task.pure.rc", tp->m_rc);
    fact("task.pure.get", (long long)lean_unbox(lean_task_get(tp)));
    fact("task.pure.rc_after_get", tp->m_rc); /* get borrows */
    lean_object *fdouble = lean_alloc_closure((void *)probe_double, 1, 0);
    lean_object *tm = lean_task_map(fdouble, tp, lean_box(0), 0); /* consumes tp */
    fact("task.map.state", lean_io_get_task_state(tm));
    fact("task.map.get", (long long)lean_unbox(lean_task_get(tm)));
    fact("task.map.rc", tm->m_rc);
    lean_dec(tm);
    /* sync := true on an already-finished input is the same eager arm */
    lean_object *tp2 = lean_task_pure(lean_box(21));
    lean_object *fdouble2 = lean_alloc_closure((void *)probe_double, 1, 0);
    lean_object *tm2 = lean_task_map(fdouble2, tp2, lean_box(0), 1);
    fact("task.map.sync.get", (long long)lean_unbox(lean_task_get(tm2)));
    lean_dec(tm2);
    /* a heap payload rides get_own's scalar-checked inc/dec (the slice-1
     * differential's lesson class) */
    lean_object *ts = lean_task_pure(lean_mk_string("tasked"));
    lean_object *fsize = lean_alloc_closure((void *)probe_str_size, 1, 0);
    lean_object *tm3 = lean_task_map(fsize, ts, lean_box(0), 0);
    fact("task.map.str_size", (long long)lean_unbox(lean_task_get(tm3)));
    lean_dec(tm3);
    /* a SHARED source task: map's eager arm releases exactly one token
     * (mutant 3gv-M2's discriminator: a dropped release leaves this at 2) */
    lean_object *tshared = lean_task_pure(lean_box(5));
    lean_inc(tshared);
    lean_object *fdouble3 = lean_alloc_closure((void *)probe_double, 1, 0);
    lean_object *tm4 = lean_task_map(fdouble3, tshared, lean_box(0), 0);
    fact("task.map.shared_src_rc", tshared->m_rc);
    fact("task.map.shared.get", (long long)lean_unbox(lean_task_get(tm4)));
    lean_dec(tshared);
    lean_dec(tm4);
    /* option_get_or_block's some arm: scalar payload, then a heap payload
     * whose steal must leave exactly one token */
    lean_object *someb = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(someb, 0, lean_box(77));
    fact("option.get_or_block.some", (long long)lean_unbox(lean_option_get_or_block(someb)));
    lean_object *ssv = lean_mk_string("resolved");
    lean_object *some2 = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(some2, 0, ssv);
    lean_object *got = lean_option_get_or_block(some2);
    fact("option.get_or_block.str_rc", got->m_rc);
    fact("option.get_or_block.str_size", (long long)lean_string_size(got) - 1);
    lean_dec(got);
}

int main(int argc, char **argv) {
    if (argc > 1 && strcmp(argv[1], "panic-internal") == 0) {
        lean_internal_panic("gauntlet-boom");
        return 99; /* unreachable: both runtimes terminate */
    }
    if (argc > 1 && strcmp(argv[1], "panic-fn") == 0) {
        lean_set_exit_on_panic(true);
        lean_panic_fn(lean_box(0), lean_mk_string("gauntlet-panic-msg"));
        return 99; /* unreachable: exit-on-panic terminates with 1 */
    }
    if (argc > 1 && strcmp(argv[1], "panic-promise-new") == 0) {
        lean_io_promise_new();
        return 99; /* unreachable: both runtimes refuse pre-manager (fln-3gv slice 2) */
    }
    if (argc > 1 && strcmp(argv[1], "panic-get-or-block-none") == 0) {
        lean_set_exit_on_panic(true);
        lean_option_get_or_block(lean_box(0));
        return 99; /* unreachable: exit-on-panic terminates with 1 */
    }
    facts_mode();
    return 0;
}
