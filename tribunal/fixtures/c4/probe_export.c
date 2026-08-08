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
#include <dlfcn.h>
#include <fcntl.h>
#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>

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

/* fln-3gv slice 5a externs (extern-census class): the runtime init entry
 * every generated main stub calls (init_module.cpp:19), and the stdio
 * plane — the stream trio, the handle prims the println path drives, and
 * the Lean-@[export]ed stream ctor, declared exactly as stage0
 * Init/System/IO.c declares them. */
extern void lean_initialize_runtime_module(void);
extern lean_object *lean_get_stdout(void);
extern lean_object *lean_get_set_stdout(lean_object *h);
extern lean_object *lean_io_prim_handle_mk(lean_object *filename, uint8_t mode);
extern lean_object *lean_io_prim_handle_put_str(lean_object *h, lean_object *s);
extern lean_object *lean_io_prim_handle_read(lean_object *h, size_t nbytes);
extern lean_object *lean_io_prim_handle_get_line(lean_object *h);
extern lean_object *lean_io_prim_handle_rewind(lean_object *h);
extern lean_object *lean_io_prim_handle_truncate(lean_object *h);
extern lean_object *lean_io_prim_handle_lock(lean_object *h, uint8_t x);
extern lean_object *lean_io_prim_handle_try_lock(lean_object *h, uint8_t x);
extern lean_object *lean_io_prim_handle_unlock(lean_object *h);
extern lean_object *lean_chmod(lean_object *filename, uint32_t mode);
extern lean_object *lean_io_create_dir(lean_object *p);
extern lean_object *lean_io_remove_dir(lean_object *p);
extern lean_object *lean_io_rename(lean_object *from, lean_object *to);
extern lean_object *lean_io_current_dir(void);
extern lean_object *lean_io_realpath(lean_object *filename);
extern lean_object *lean_io_read_dir(lean_object *dirname);
extern lean_object *lean_io_remove_file(lean_object *filename);
extern lean_object *lean_io_hard_link(lean_object *orig, lean_object *link);
extern lean_object *lean_io_create_tempfile(lean_object *w);
extern lean_object *lean_io_create_tempdir(lean_object *w);
extern lean_object *lean_io_metadata(lean_object *filename);
extern lean_object *lean_io_symlink_metadata(lean_object *filename);
extern lean_object *lean_io_getenv(lean_object *env_var);
extern lean_object *lean_io_mono_ms_now(void);
extern lean_object *lean_io_mono_nanos_now(void);
extern uint64_t lean_io_get_tid(void);
extern uint32_t lean_io_process_get_pid(void);
extern lean_object *lean_io_app_path(void);
extern uint8_t lean_io_initializing(void);
extern void lean_io_mark_end_initialization(void);
extern lean_object *lean_io_get_random_bytes(size_t nbytes);
extern lean_object *lean_runtime_mark_multi_threaded(lean_object *a);
extern lean_object *lean_runtime_mark_persistent(lean_object *a);
extern lean_object *lean_runtime_forget(lean_object *o);
extern uint8_t lean_string_validate_utf8(lean_object *a);
extern lean_object *lean_byte_array_copy_slice(lean_object *src, lean_object *src_off, lean_object *dest, lean_object *dest_off, lean_object *len, bool exact);
extern lean_object *lean_stream_of_handle(lean_object *h);

/* fln-3gv slice 3b externs (extern-census class): the io.cpp wrapper
 * family, declared exactly as stage0 Init/System/IO.c declares them. */
extern lean_object *lean_io_as_task(lean_object *act, lean_object *prio);
extern lean_object *lean_io_map_task(lean_object *f, lean_object *t, lean_object *prio, uint8_t sync);
extern lean_object *lean_io_bind_task(lean_object *t, lean_object *f, lean_object *prio, uint8_t sync);
extern uint8_t lean_io_check_canceled();
extern lean_object *lean_io_cancel(lean_object *t);
extern lean_object *lean_io_wait(lean_object *t);
extern lean_object *lean_io_wait_any(lean_object *task_list);
extern lean_object *lean_io_get_num_heartbeats(void);
extern lean_object *lean_io_set_heartbeats(lean_object *count);

/* fln-3gv slice 8a extern (extern-census class): the Lean-compiled IO.Error
 * pretty-printer, declared exactly as util/io.h:13 declares it
 * (lean_io_result_show_error is already in lean.h:2950). */
extern lean_object *lean_io_error_to_string(lean_object *err);

/* fln-3gv slice 8b externs (extern-census class): the exit pair, declared
 * exactly as stage0 Init/System/IO.c:1099/1101 declares them. */
extern lean_object *lean_io_exit(uint8_t code);
extern lean_object *lean_io_force_exit(uint8_t code);

/* fln-3gv slice 8d extern (extern-census class): the stderr get_set twin of
 * the get_set_stdout already declared above (io.cpp:119-127). */
extern lean_object *lean_get_set_stderr(lean_object *h);

/* fln-3gv slice 8e fixtures: the float once cells (lean.h:3272 declares
 * lean_once_cell_t; the float pair is declared there too) driven twice each
 * with a counting initializer, so both runtimes must agree the initializer
 * ran exactly once per cell. */
static int errstr_float_once_calls = 0;
static float once_init_f32(void) {
    errstr_float_once_calls++;
    return 1.5f;
}
static double once_init_f64(void) {
    errstr_float_once_calls++;
    return 2.25;
}

/* Slice 8a fixture builders: every IO.Error ctor shape synthesized directly
 * over the generated layout (IOError.c: 1-obj-field families u32 at
 * sizeof(void*)*1, 2-obj-field families at sizeof(void*)*2), so the arm
 * sweep below is deterministic on both runtimes. */
static lean_object *errstr_err1(uint8_t tag, const char *details, uint32_t code) {
    lean_object *r = lean_alloc_ctor(tag, 1, 4);
    lean_ctor_set(r, 0, lean_mk_string(details));
    lean_ctor_set_uint32(r, sizeof(void *) * 1, code);
    return r;
}
static lean_object *errstr_err2(uint8_t tag, lean_object *f0, const char *details,
                                uint32_t code) {
    lean_object *r = lean_alloc_ctor(tag, 2, 4);
    lean_ctor_set(r, 0, f0);
    lean_ctor_set(r, 1, lean_mk_string(details));
    lean_ctor_set_uint32(r, sizeof(void *) * 2, code);
    return r;
}
static lean_object *errstr_some(const char *s) {
    lean_object *c = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(c, 0, lean_mk_string(s));
    return c;
}
/* Emit the pretty-printed string's content length and bytesum for one arm;
 * consumes err. */
static void errstr_facts(const char *arm, lean_object *err) {
    lean_object *s = lean_io_error_to_string(err);
    char name[96];
    snprintf(name, sizeof name, "corpus.errstr.%s_bytes", arm);
    fact(name, (long long)lean_string_size(s) - 1);
    snprintf(name, sizeof name, "corpus.errstr.%s_sum", arm);
    fact(name, bytesum(lean_string_cstr(s), lean_string_size(s) - 1));
    lean_dec(s);
}

/* Apply targets for the task facts, closured exactly as generated C does. */
static lean_object *probe_double(lean_object *x) {
    return lean_box(lean_unbox(x) * 2);
}
static lean_object *probe_str_size(lean_object *s) {
    lean_object *r = lean_box(lean_string_size(s));
    lean_dec(s);
    return r;
}
/* fln-3gv slice 3 targets: spawn body, identity map, and the bind target
 * that returns a captured (still-unfinished) task — the re-arm shape. */
static lean_object *probe_forty_two(lean_object *w) {
    (void)w;
    return lean_box(42);
}
static lean_object *probe_ident(lean_object *x) {
    return x;
}
static lean_object *probe_return_task(lean_object *t, lean_object *v) {
    lean_dec(v);
    return t;
}
/* slice 3b targets under the compiled BaseIO convention (bare results). */
static lean_object *probe_double_io(lean_object *a, lean_object *w) {
    (void)w;
    return lean_box(lean_unbox(a) * 2);
}
static lean_object *probe_task_succ(lean_object *a, lean_object *w) {
    (void)w;
    return lean_task_pure(lean_box(lean_unbox(a) + 1));
}
/* fln-3gv slice 4 targets: the tasks.lean corpus bodies
 * (crates/fln-vm/fixtures/g03/tasks.lean). The asTask actions compute on
 * the worker and publish the compiled toBaseIO shape — a bare Except.ok
 * ctor (index 1). */
static lean_object *probe_corpus_except_ok(lean_object *v) {
    lean_object *r = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(r, 0, v);
    return r;
}
static lean_object *probe_corpus_add(lean_object *a, lean_object *b, lean_object *w) {
    (void)w;
    return probe_corpus_except_ok(lean_box(lean_unbox(a) + lean_unbox(b)));
}
static lean_object *probe_corpus_mul(lean_object *a, lean_object *b, lean_object *w) {
    (void)w;
    return probe_corpus_except_ok(lean_box(lean_unbox(a) * lean_unbox(b)));
}
static lean_object *probe_corpus_six_seven(lean_object *u) {
    (void)u;
    return lean_box(6 * 7);
}
static lean_object *probe_corpus_succ(lean_object *x) {
    return lean_box(lean_unbox(x) + 1);
}

/* One worker cell for the real generated-C allocator matrix below. The
 * counter is thread-local in both runtimes, so each worker records its own
 * terminal value and the parent only publishes the all-workers predicate. */
struct heartbeat_worker_cell {
    uint64_t seed;
    long long terminal_heartbeat;
};

static void *heartbeat_worker(void *opaque) {
    struct heartbeat_worker_cell *cell = opaque;
    lean_io_set_heartbeats(lean_uint64_to_nat(cell->seed));
    for (unsigned size = 8; size < 1024; size += 8) {
        lean_object *block = lean_alloc_small_object(size);
        lean_free_small_object(block);
    }
    cell->terminal_heartbeat =
        (long long)lean_unbox(lean_io_get_num_heartbeats());
    return NULL;
}

static void run_heartbeat_thread_matrix(unsigned width, uint64_t seed,
                                        long long expected, const char *edge) {
    pthread_t threads[32];
    struct heartbeat_worker_cell cells[32] = {0};
    int all_at_expected = 1;

    for (unsigned worker = 0; worker < width; worker++) {
        cells[worker].seed = seed;
        if (pthread_create(&threads[worker], NULL, heartbeat_worker,
                           &cells[worker]) != 0) {
            lean_internal_panic("gauntlet heartbeat worker creation failed");
        }
    }
    for (unsigned worker = 0; worker < width; worker++) {
        if (pthread_join(threads[worker], NULL) != 0) {
            lean_internal_panic("gauntlet heartbeat worker join failed");
        }
        if (cells[worker].terminal_heartbeat != expected) all_at_expected = 0;
    }
    char probe[64];
    snprintf(probe, sizeof(probe),
             "heartbeat.inline_classes.%s.width_%u_all_expected", edge, width);
    fact(probe, all_at_expected);
}

static void facts_mode(void) {
    /* Both runtimes initialize as a generated main would (fln-3gv slice
     * 5a): the Reference's stream globals are built in initialize_io, and
     * Marrow's twin seeds its trio + the SIGPIPE disposition here. */
    lean_initialize_runtime_module();

    /* ---- heartbeat through the real generated-C small path
     * The direct IO externs are intentionally reset before this cell.  The
     * `lean.h` ctor inline below performs one `lean_inc_heartbeat` before its
     * raw small allocation in the pin's LEAN_MIMALLOC configuration. */
    lean_io_set_heartbeats(lean_box(0));
    fact("heartbeat.after_reset", (long long)lean_unbox(lean_io_get_num_heartbeats()));
    lean_object *heartbeat_ctor = lean_alloc_ctor(0, 0, 0);
    fact("heartbeat.after_small_ctor", (long long)lean_unbox(lean_io_get_num_heartbeats()));
    lean_dec(heartbeat_ctor);

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

    /* The active LEAN_MIMALLOC generated-C inline takes its supported 8-byte
     * classes through lean_inc_heartbeat + mi_malloc_small. At this pin the
     * fast path is strict below 1024: a 1024-byte request faults inside
     * mi_malloc_small, so this real C cell exercises the 127 valid 8..=1016
     * classes instead of asserting a wider configuration contract. Seed
     * precisely 127 ticks below wrap; the final scalar getter must observe
     * zero in both runtimes. The seed follows the fixture's bignum lifecycle,
     * whose pin order is itself part of this real generated-C probe. */
    lean_io_set_heartbeats(lean_uint64_to_nat(UINT64_MAX - 126));
    for (unsigned size = 8; size < 1024; size += 8) {
        lean_object *block = lean_alloc_small_object(size);
        lean_free_small_object(block);
    }
    fact("heartbeat.after_inline_mimalloc_classes_wrap", (long long)lean_unbox(lean_io_get_num_heartbeats()));

    /* The Rust unit matrix proves every owned class through 4096. This
     * generated-C differential independently binds the pin's active inline
     * window (8..=1016) at the FL-INV-01 widths, with a per-worker near-wrap
     * seed so a missing or doubled charge is observable without timestamps or
     * scheduler order entering the fact stream. */
    run_heartbeat_thread_matrix(1, UINT64_MAX - 126, 0, "wrap");
    run_heartbeat_thread_matrix(8, UINT64_MAX - 126, 0, "wrap");
    run_heartbeat_thread_matrix(32, UINT64_MAX - 126, 0, "wrap");
    /* Adjacent input control: the same 127 allocations from one tick later
     * end at one. This makes a hidden reset or an off-by-one charge fail a
     * separate, real generated-C cell at each declared thread width. */
    run_heartbeat_thread_matrix(1, UINT64_MAX - 125, 1, "one_short");
    run_heartbeat_thread_matrix(8, UINT64_MAX - 125, 1, "one_short");
    run_heartbeat_thread_matrix(32, UINT64_MAX - 125, 1, "one_short");

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

    /* ---- fln-3gv slice 3: the task manager goes live. Everything below
     * runs AFTER lean_init_task_manager_using(2): both runtimes schedule on
     * real workers now, so only get-forced points and sync-ordering
     * guarantees are probed — never the transient state of a queued task. */
    lean_init_task_manager_using(2);
    /* spawn + get across a worker */
    lean_object *spc = lean_alloc_closure((void *)probe_forty_two, 1, 0);
    lean_object *sp = lean_task_spawn(spc, lean_box(0));
    fact("mgr.spawn.get", (long long)lean_unbox(lean_task_get_own(sp)));
    /* the promise lifecycle */
    lean_object *pr = lean_io_promise_new();
    lean_object *prt = lean_io_promise_result_opt(pr);
    fact("mgr.promise.state_unresolved", lean_io_get_task_state(prt));
    lean_dec(lean_io_promise_resolve(lean_box(5), pr));
    fact("mgr.promise.state_resolved", lean_io_get_task_state(prt));
    lean_object *rsome = lean_task_get(prt); /* borrowed some(5) */
    fact("mgr.promise.some_tag", lean_ptr_tag(rsome));
    fact("mgr.promise.value", (long long)lean_unbox(lean_ctor_get(rsome, 0)));
    /* 3gv-M3's discriminator: resolve_core marks the published value MT */
    fact("mgr.promise.resolved_value_is_mt", rsome->m_rc < 0);
    lean_inc(rsome);
    fact("mgr.promise.get_or_block",
         (long long)lean_unbox(lean_option_get_or_block(rsome)));
    lean_dec(lean_io_promise_resolve(lean_box(9), pr));
    fact("mgr.promise.first_resolve_wins",
         (long long)lean_unbox(lean_ctor_get(lean_task_get(prt), 0)));
    lean_dec(prt);
    lean_dec(pr);
    /* sync := true dependent of an UNFINISHED promise task: Waiting before,
     * finished INLINE by the time resolve returns (the CancelToken.onSet
     * ordering law, enqueue_core's LEAN_SYNC_PRIO arm) */
    lean_object *pr2 = lean_io_promise_new();
    lean_object *prt2 = lean_io_promise_result_opt(pr2);
    lean_object *fid = lean_alloc_closure((void *)probe_ident, 1, 0);
    lean_object *m = lean_task_map(fid, prt2, lean_box(0), 1);
    fact("mgr.sync_dep.state_before", lean_io_get_task_state(m));
    lean_dec(lean_io_promise_resolve(lean_box(3), pr2));
    fact("mgr.sync_dep.state_after_resolve", lean_io_get_task_state(m));
    fact("mgr.sync_dep.value",
         (long long)lean_unbox(lean_ctor_get(lean_task_get(m), 0)));
    lean_dec(m);
    lean_dec(pr2);
    /* dropping an unresolved promise publishes none */
    lean_object *pr3 = lean_io_promise_new();
    lean_object *prt3 = lean_io_promise_result_opt(pr3);
    lean_dec(pr3);
    fact("mgr.promise.dropped_state", lean_io_get_task_state(prt3));
    fact("mgr.promise.dropped_is_none", lean_is_scalar(lean_task_get(prt3)));
    lean_dec(prt3);
    /* bind through the re-arm path, deterministic under sync: the outer
     * resolve runs bind_fn1 inline, f returns a still-unfinished task, the
     * bound task re-arms Waiting on it; the inner resolve finishes it */
    lean_object *pr4 = lean_io_promise_new();
    lean_object *prt4 = lean_io_promise_result_opt(pr4);
    lean_object *pr5 = lean_io_promise_new();
    lean_object *prt5 = lean_io_promise_result_opt(pr5);
    lean_object *fb = lean_alloc_closure((void *)probe_return_task, 2, 1);
    lean_closure_set(fb, 0, prt5);
    lean_object *bnd = lean_task_bind(prt4, fb, lean_box(0), 1);
    lean_dec(lean_io_promise_resolve(lean_box(2), pr4));
    fact("mgr.bind.rearmed_state", lean_io_get_task_state(bnd));
    lean_dec(lean_io_promise_resolve(lean_box(8), pr5));
    fact("mgr.bind.value",
         (long long)lean_unbox(lean_ctor_get(lean_task_get(bnd), 0)));
    lean_dec(bnd);
    lean_dec(pr4);
    lean_dec(pr5);
    /* off-task cancellation probe answers false in both runtimes */
    fact("mgr.check_canceled.off_task", lean_io_check_canceled_core());

    /* ---- fln-3gv slice 3b: the io.cpp wrapper family over the live
     * cores. BaseIO results are bare values at this pin. */
    lean_object *act = lean_alloc_closure((void *)probe_forty_two, 1, 0);
    lean_object *iot = lean_io_as_task(act, lean_box(0));
    fact("iow.as_task.wait", (long long)lean_unbox(lean_io_wait(iot)));
    lean_object *mt2 = lean_io_map_task(
        lean_alloc_closure((void *)probe_double_io, 2, 0),
        lean_task_pure(lean_box(21)), lean_box(0), 0);
    fact("iow.map_task.wait", (long long)lean_unbox(lean_io_wait(mt2)));
    lean_object *bt2 = lean_io_bind_task(
        lean_task_pure(lean_box(5)),
        lean_alloc_closure((void *)probe_task_succ, 2, 0), lean_box(0), 0);
    fact("iow.bind_task.wait", (long long)lean_unbox(lean_io_wait(bt2)));
    /* waitAny answers with the first FINISHED member in list order */
    lean_object *anyp = lean_io_promise_new();
    lean_object *anypt = lean_io_promise_result_opt(anyp);
    lean_object *fin3 = lean_task_pure(lean_box(3));
    lean_object *wl2 = lean_alloc_ctor(1, 2, 0);
    lean_ctor_set(wl2, 0, fin3);
    lean_ctor_set(wl2, 1, lean_box(0));
    lean_object *wl1 = lean_alloc_ctor(1, 2, 0);
    lean_ctor_set(wl1, 0, anypt);
    lean_ctor_set(wl1, 1, wl2);
    fact("iow.wait_any.first_finished", (long long)lean_unbox(lean_io_wait_any(wl1)));
    lean_dec(wl1);
    lean_dec(anyp);
    /* the cancel wrapper's finished no-op, and the check wrapper off-task */
    lean_object *fc = lean_task_pure(lean_box(1));
    lean_dec(lean_io_cancel(fc));
    fact("iow.cancel.finished_state", lean_io_get_task_state(fc));
    lean_dec(fc);
    fact("iow.check_canceled", lean_io_check_canceled());

    /* ---- fln-3gv slice 4: the G0-3 tasks.lean corpus observables
     * (crates/fln-vm/fixtures/g03/tasks.lean), computed through the live
     * manager on BOTH runtimes — the io/tasks residue franken_lean-7xe
     * recorded as waiting on the effect runtime. The pinned oracle bytes
     * are "sum 45" / "chained 43" (tasks.lean.expected). */
    lean_object *ca1 = lean_alloc_closure((void *)probe_corpus_add, 3, 2);
    lean_closure_set(ca1, 0, lean_box(2));
    lean_closure_set(ca1, 1, lean_box(3));
    lean_object *ct1 = lean_io_as_task(ca1, lean_box(0));
    lean_object *ca2 = lean_alloc_closure((void *)probe_corpus_mul, 3, 2);
    lean_closure_set(ca2, 0, lean_box(10));
    lean_closure_set(ca2, 1, lean_box(4));
    lean_object *ct2 = lean_io_as_task(ca2, lean_box(0));
    /* tasks.lean:4-5 — Task.get is the lean_task_get_own inline; ofExcept's
     * ok-arm takes field 0 of the Except.ok ctor (index 1). */
    lean_object *ce1 = lean_task_get_own(ct1);
    lean_object *ce2 = lean_task_get_own(ct2);
    fact("corpus.tasks.ok_tag", lean_ptr_tag(ce1));
    fact("corpus.tasks.sum",
         (long long)lean_unbox(lean_ctor_get(ce1, 0)) +
             (long long)lean_unbox(lean_ctor_get(ce2, 0)));
    lean_dec(ce1);
    lean_dec(ce2);
    /* tasks.lean:7-8 — Task.spawn (fun _ => 6 * 7) |>.map (+1) |>.get */
    lean_object *csp = lean_task_spawn(
        lean_alloc_closure((void *)probe_corpus_six_seven, 1, 0), lean_box(0));
    lean_object *cch = lean_task_map(
        lean_alloc_closure((void *)probe_corpus_succ, 1, 0), csp, lean_box(0),
        false);
    fact("corpus.tasks.chained", (long long)lean_unbox(lean_task_get_own(cch)));

    lean_finalize_task_manager(); /* both runtimes drain and join here */

    /* ---- fln-3gv slice 5a: the io_println.lean corpus observables
     * through the swap-capture seam (crates/fln-vm/fixtures/g03/
     * io_println.lean; pinned oracle "first\n" "second 2\n" "third\n").
     * A stream over a temp-file handle becomes this thread's stdout via
     * lean_get_set_stdout — the withStdout shape — and each println is
     * getStdout>>putStr on the CURRENT stream, exactly as compiled code
     * runs it; the captured bytes are the differential facts. */
    char iop_path[128];
    snprintf(iop_path, sizeof iop_path, "/tmp/fln-g03-println-%lld",
             (long long)getpid());
    remove(iop_path);
    lean_object *iop_fname = lean_mk_string(iop_path);
    lean_object *iop_res = lean_io_prim_handle_mk(iop_fname, 1);
    fact("corpus.io_println.mk_ok", lean_ptr_tag(iop_res) == 0);
    lean_object *iop_h = lean_ctor_get(iop_res, 0);
    lean_inc(iop_h);
    lean_dec(iop_res);
    lean_dec(iop_fname);
    lean_object *iop_old = lean_get_set_stdout(lean_stream_of_handle(iop_h));
    long long iop_ok = 0;
    for (int li = 0; li < 3; li++) {
        lean_object *cur = lean_get_stdout();
        lean_object *put = lean_ctor_get(cur, 4); /* putStr, field 4 */
        lean_inc(put);
        lean_object *s;
        if (li == 1) {
            /* s!"second {1 + 1}": the interpolation's compiled shape is
             * the live append arm (s1 owned, s2 borrowed). */
            lean_object *two = lean_mk_string("2\n");
            s = lean_string_append(lean_mk_string("second "), two);
            lean_dec(two);
        } else {
            s = lean_mk_string(li == 0 ? "first\n" : "third\n");
        }
        lean_object *res = lean_apply_2(put, s, lean_box(0));
        iop_ok += lean_ptr_tag(res) == 0;
        lean_dec(res);
        lean_dec(cur);
    }
    fact("corpus.io_println.put_ok", iop_ok);
    { /* flush through the stream's own flush field (field 0) */
        lean_object *cur = lean_get_stdout();
        lean_object *fl = lean_ctor_get(cur, 0);
        lean_inc(fl);
        lean_object *res = lean_apply_1(fl, lean_box(0));
        fact("corpus.io_println.flush_ok", lean_ptr_tag(res) == 0);
        lean_dec(res);
        lean_dec(cur);
    }
    /* restore the initial stdout; dropping ours fcloses the FILE* */
    lean_dec(lean_get_set_stdout(iop_old));
    {
        FILE *rf = fopen(iop_path, "rb");
        long long iop_n = 0, iop_sum = 0;
        int ch;
        while (rf && (ch = fgetc(rf)) != EOF) {
            iop_n++;
            iop_sum += ch;
        }
        if (rf) {
            fclose(rf);
        }
        remove(iop_path);
        fact("corpus.io_println.bytes", iop_n);
        fact("corpus.io_println.bytesum", iop_sum);
    }

    /* ---- fln-3gv slice 5b: the io_file.lean corpus roundtrip through the
     * read/write prims (crates/fln-vm/fixtures/g03/io_file.lean; the
     * pinned runtime observable is "read back: roundtrip payload
     * FORALL (20 chars)"). writeFile's shape: mk(write)+putStr+drop, the
     * drop's fclose publishing; readFile's: mk(read)+read, plus the pin's
     * EOF arm (io.cpp:598-601). */
    char iof_path[128];
    snprintf(iof_path, sizeof iof_path, "/tmp/fln-g03-file-%lld",
             (long long)getpid());
    remove(iof_path);
    lean_object *iof_fname = lean_mk_string(iof_path);
    lean_object *iof_wres = lean_io_prim_handle_mk(iof_fname, 1);
    fact("corpus.io_file.wmk_ok", lean_ptr_tag(iof_wres) == 0);
    lean_object *iof_wh = lean_ctor_get(iof_wres, 0);
    lean_inc(iof_wh);
    lean_dec(iof_wres);
    lean_object *iof_content = lean_mk_string("roundtrip payload \xE2\x88\x80\n");
    lean_object *iof_pres = lean_io_prim_handle_put_str(iof_wh, iof_content);
    fact("corpus.io_file.put_ok", lean_ptr_tag(iof_pres) == 0);
    lean_dec(iof_pres);
    lean_dec(iof_content);
    lean_dec(iof_wh); /* the finalizer's fclose publishes the bytes */
    lean_object *iof_rres = lean_io_prim_handle_mk(iof_fname, 0);
    fact("corpus.io_file.rmk_ok", lean_ptr_tag(iof_rres) == 0);
    lean_object *iof_rh = lean_ctor_get(iof_rres, 0);
    lean_inc(iof_rh);
    lean_dec(iof_rres);
    lean_dec(iof_fname);
    lean_object *iof_chunk = lean_io_prim_handle_read(iof_rh, 1024);
    fact("corpus.io_file.read_ok", lean_ptr_tag(iof_chunk) == 0);
    lean_object *iof_ba = lean_ctor_get(iof_chunk, 0);
    {
        long long iof_n = (long long)lean_sarray_size(iof_ba);
        uint8_t *iof_p = lean_sarray_cptr(iof_ba);
        long long iof_sum = 0, iof_chars = 0;
        for (long long i = 0; i < iof_n; i++) {
            iof_sum += iof_p[i];
            iof_chars += (iof_p[i] & 0xC0) != 0x80; /* non-continuation */
        }
        fact("corpus.io_file.bytes", iof_n);
        fact("corpus.io_file.bytesum", iof_sum);
        fact("corpus.io_file.chars", iof_chars);
    }
    lean_object *iof_eof = lean_io_prim_handle_read(iof_rh, 1024);
    fact("corpus.io_file.eof_ok", lean_ptr_tag(iof_eof) == 0);
    fact("corpus.io_file.eof_size",
         (long long)lean_sarray_size(lean_ctor_get(iof_eof, 0)));
    lean_dec(iof_eof);
    lean_dec(iof_chunk);
    lean_dec(iof_rh);
    remove(iof_path);

    /* ---- fln-3gv slice 5c: Handle.getLine's four arms (io.cpp:635-659)
     * through both runtimes over one scratch file — a terminated line
     * (newline retained), a line carrying a raw 0xFF (the ok arms run
     * lean_mk_string_from_bytes, so the byte recovers lossily as U+FFFD),
     * an unterminated tail (the EOF partial-line arm), and a read at EOF
     * (the empty string, still ok). */
    char igl_path[128];
    snprintf(igl_path, sizeof igl_path, "/tmp/fln-get-line-%lld",
             (long long)getpid());
    remove(igl_path);
    {
        FILE *seed = fopen(igl_path, "w");
        static const unsigned char igl_bytes[] = {
            'f', 'i', 'r', 's', 't', ' ', 'l', 'i', 'n', 'e', '\n',
            'f', 'o', 0xFF, 'o', '\n',
            't', 'a', 'i', 'l'};
        fwrite(igl_bytes, 1, sizeof igl_bytes, seed);
        fclose(seed);
    }
    lean_object *igl_fname = lean_mk_string(igl_path);
    lean_object *igl_rres = lean_io_prim_handle_mk(igl_fname, 0);
    fact("corpus.get_line.rmk_ok", lean_ptr_tag(igl_rres) == 0);
    lean_object *igl_rh = lean_ctor_get(igl_rres, 0);
    lean_inc(igl_rh);
    lean_dec(igl_rres);
    lean_dec(igl_fname);
    for (int igl_i = 0; igl_i < 4; igl_i++) {
        static const char *const igl_names[4][4] = {
            {"corpus.get_line.l1_ok", "corpus.get_line.l1_bytes",
             "corpus.get_line.l1_bytesum", "corpus.get_line.l1_chars"},
            {"corpus.get_line.l2_ok", "corpus.get_line.l2_bytes",
             "corpus.get_line.l2_bytesum", "corpus.get_line.l2_chars"},
            {"corpus.get_line.l3_ok", "corpus.get_line.l3_bytes",
             "corpus.get_line.l3_bytesum", "corpus.get_line.l3_chars"},
            {"corpus.get_line.l4_ok", "corpus.get_line.l4_bytes",
             "corpus.get_line.l4_bytesum", "corpus.get_line.l4_chars"}};
        lean_object *igl_res = lean_io_prim_handle_get_line(igl_rh);
        fact(igl_names[igl_i][0], lean_ptr_tag(igl_res) == 0);
        lean_object *igl_s = lean_ctor_get(igl_res, 0);
        long long igl_n = (long long)lean_string_size(igl_s) - 1;
        const uint8_t *igl_p = (const uint8_t *)lean_string_cstr(igl_s);
        long long igl_sum = 0;
        for (long long i = 0; i < igl_n; i++) {
            igl_sum += igl_p[i];
        }
        fact(igl_names[igl_i][1], igl_n);
        fact(igl_names[igl_i][2], igl_sum);
        fact(igl_names[igl_i][3], (long long)lean_string_len(igl_s));
        lean_dec(igl_res);
    }
    lean_dec(igl_rh);
    remove(igl_path);

    /* ---- fln-3gv slice 5d: the remaining handle prims (io.cpp:480-582,
     * non-Windows arms) — rewind/truncate as a roundtrip on one r+ handle,
     * and the flock family as a real contention pair across two opens of
     * one path (flock is per open file description). */
    char ictl_path[128];
    snprintf(ictl_path, sizeof ictl_path, "/tmp/fln-handle-ctl-%lld",
             (long long)getpid());
    remove(ictl_path);
    {
        FILE *seed = fopen(ictl_path, "w");
        fclose(seed);
    }
    lean_object *ictl_fname = lean_mk_string(ictl_path);
    lean_object *ictl_hres = lean_io_prim_handle_mk(ictl_fname, 3);
    fact("corpus.handle_ctl.mk_ok", lean_ptr_tag(ictl_hres) == 0);
    lean_object *ictl_h = lean_ctor_get(ictl_hres, 0);
    lean_inc(ictl_h);
    lean_dec(ictl_hres);
    lean_object *ictl_payload = lean_mk_string("hello world");
    lean_object *ictl_pres = lean_io_prim_handle_put_str(ictl_h, ictl_payload);
    fact("corpus.handle_ctl.put_ok", lean_ptr_tag(ictl_pres) == 0);
    lean_dec(ictl_pres);
    lean_dec(ictl_payload);
    lean_object *ictl_rw = lean_io_prim_handle_rewind(ictl_h);
    fact("corpus.handle_ctl.rewind_ok", lean_ptr_tag(ictl_rw) == 0);
    lean_dec(ictl_rw);
    lean_object *ictl_chunk = lean_io_prim_handle_read(ictl_h, 5);
    fact("corpus.handle_ctl.read_ok", lean_ptr_tag(ictl_chunk) == 0);
    {
        lean_object *ictl_ba = lean_ctor_get(ictl_chunk, 0);
        long long ictl_n = (long long)lean_sarray_size(ictl_ba);
        uint8_t *ictl_p = lean_sarray_cptr(ictl_ba);
        long long ictl_sum = 0;
        for (long long i = 0; i < ictl_n; i++) {
            ictl_sum += ictl_p[i];
        }
        fact("corpus.handle_ctl.read_bytes", ictl_n);
        fact("corpus.handle_ctl.read_bytesum", ictl_sum);
    }
    lean_dec(ictl_chunk);
    lean_object *ictl_tr = lean_io_prim_handle_truncate(ictl_h);
    fact("corpus.handle_ctl.truncate_ok", lean_ptr_tag(ictl_tr) == 0);
    lean_dec(ictl_tr);
    lean_dec(ictl_h); /* fclose */
    {
        FILE *check = fopen(ictl_path, "r");
        long long csum = 0, cn = 0;
        int cc;
        while ((cc = fgetc(check)) != EOF) {
            csum += cc;
            cn++;
        }
        fclose(check);
        fact("corpus.handle_ctl.post_truncate_bytes", cn);
        fact("corpus.handle_ctl.post_truncate_bytesum", csum);
    }
    lean_object *ictl_f1 = lean_mk_string(ictl_path);
    lean_object *ictl_h1res = lean_io_prim_handle_mk(ictl_f1, 0);
    lean_object *ictl_h1 = lean_ctor_get(ictl_h1res, 0);
    lean_inc(ictl_h1);
    lean_dec(ictl_h1res);
    lean_object *ictl_h2res = lean_io_prim_handle_mk(ictl_f1, 0);
    lean_object *ictl_h2 = lean_ctor_get(ictl_h2res, 0);
    lean_inc(ictl_h2);
    lean_dec(ictl_h2res);
    lean_dec(ictl_f1);
    lean_dec(ictl_fname);
    lean_object *ictl_lk = lean_io_prim_handle_lock(ictl_h1, 1);
    fact("corpus.handle_ctl.lock_ok", lean_ptr_tag(ictl_lk) == 0);
    lean_dec(ictl_lk);
    lean_object *ictl_busy = lean_io_prim_handle_try_lock(ictl_h2, 1);
    fact("corpus.handle_ctl.trylock_held_ok", lean_ptr_tag(ictl_busy) == 0);
    fact("corpus.handle_ctl.trylock_held_value",
         lean_unbox(lean_ctor_get(ictl_busy, 0)));
    lean_dec(ictl_busy);
    lean_object *ictl_un = lean_io_prim_handle_unlock(ictl_h1);
    fact("corpus.handle_ctl.unlock_ok", lean_ptr_tag(ictl_un) == 0);
    lean_dec(ictl_un);
    lean_object *ictl_free = lean_io_prim_handle_try_lock(ictl_h2, 1);
    fact("corpus.handle_ctl.trylock_free_ok", lean_ptr_tag(ictl_free) == 0);
    fact("corpus.handle_ctl.trylock_free_value",
         lean_unbox(lean_ctor_get(ictl_free, 0)));
    lean_dec(ictl_free);
    lean_object *ictl_un2 = lean_io_prim_handle_unlock(ictl_h2);
    lean_dec(ictl_un2);
    lean_dec(ictl_h2);
    lean_dec(ictl_h1);
    remove(ictl_path);

    /* ---- fln-3gv slice 6a: the errno-decoded fs family (io.cpp:372-382,
     * 1002-1227, 1409-1417) — create_dir with its EEXIST arm, read_dir's
     * DirEntry shape over planted names, rename, realpath (OWNED argument;
     * the missing arm is noFileOrDirectory with EMPTY details), chmod,
     * current_dir, remove_dir. */
    char ifs_base[128];
    snprintf(ifs_base, sizeof ifs_base, "/tmp/fln-fs-dir-%lld",
             (long long)getpid());
    char ifs_sub[160], ifs_sub2[160], ifs_file[192];
    snprintf(ifs_sub, sizeof ifs_sub, "%s/child", ifs_base);
    snprintf(ifs_sub2, sizeof ifs_sub2, "%s/renamed", ifs_base);
    lean_object *ifs_base_obj = lean_mk_string(ifs_base);
    lean_object *ifs_mk0 = lean_io_create_dir(ifs_base_obj);
    fact("corpus.fs_dir.mkbase_ok", lean_ptr_tag(ifs_mk0) == 0);
    lean_dec(ifs_mk0);
    lean_object *ifs_sub_obj = lean_mk_string(ifs_sub);
    lean_object *ifs_mk1 = lean_io_create_dir(ifs_sub_obj);
    fact("corpus.fs_dir.mksub_ok", lean_ptr_tag(ifs_mk1) == 0);
    lean_dec(ifs_mk1);
    lean_object *ifs_dup = lean_io_create_dir(ifs_sub_obj);
    fact("corpus.fs_dir.mkdup_err", lean_ptr_tag(ifs_dup) == 1);
    fact("corpus.fs_dir.mkdup_variant",
         lean_ptr_tag(lean_ctor_get(ifs_dup, 0)));
    lean_dec(ifs_dup);
    snprintf(ifs_file, sizeof ifs_file, "%s/alpha.txt", ifs_sub);
    {
        FILE *pf = fopen(ifs_file, "w");
        fputc('a', pf);
        fclose(pf);
    }
    snprintf(ifs_file, sizeof ifs_file, "%s/beta.txt", ifs_sub);
    {
        FILE *pf = fopen(ifs_file, "w");
        fputc('b', pf);
        fclose(pf);
    }
    lean_object *ifs_rd = lean_io_read_dir(ifs_sub_obj);
    fact("corpus.fs_dir.readdir_ok", lean_ptr_tag(ifs_rd) == 0);
    {
        lean_object *ifs_arr = lean_ctor_get(ifs_rd, 0);
        long long ifs_n = (long long)lean_array_size(ifs_arr);
        long long ifs_namesum = 0;
        for (long long i = 0; i < ifs_n; i++) {
            lean_object *ifs_e = lean_array_cptr(ifs_arr)[i];
            lean_object *ifs_nm = lean_ctor_get(ifs_e, 1);
            const uint8_t *np = (const uint8_t *)lean_string_cstr(ifs_nm);
            long long nn = (long long)lean_string_size(ifs_nm) - 1;
            for (long long j = 0; j < nn; j++) {
                ifs_namesum += np[j];
            }
        }
        fact("corpus.fs_dir.readdir_count", ifs_n);
        fact("corpus.fs_dir.readdir_namesum", ifs_namesum);
    }
    lean_dec(ifs_rd);
    lean_object *ifs_sub2_obj = lean_mk_string(ifs_sub2);
    lean_object *ifs_rn = lean_io_rename(ifs_sub_obj, ifs_sub2_obj);
    fact("corpus.fs_dir.rename_ok", lean_ptr_tag(ifs_rn) == 0);
    lean_dec(ifs_rn);
    lean_inc(ifs_sub2_obj); /* realpath consumes its argument */
    lean_object *ifs_rp = lean_io_realpath(ifs_sub2_obj);
    fact("corpus.fs_dir.realpath_ok", lean_ptr_tag(ifs_rp) == 0);
    {
        lean_object *ifs_rps = lean_ctor_get(ifs_rp, 0);
        const char *rp = lean_string_cstr(ifs_rps);
        size_t rl = strlen(rp);
        fact("corpus.fs_dir.realpath_tail",
             rl >= 8 && strcmp(rp + rl - 8, "/renamed") == 0);
    }
    lean_dec(ifs_rp);
    lean_object *ifs_missing = lean_mk_string("/tmp/fln-fs-dir-definitely-missing");
    lean_inc(ifs_missing);
    lean_object *ifs_rpm = lean_io_realpath(ifs_missing);
    fact("corpus.fs_dir.realpath_missing_err", lean_ptr_tag(ifs_rpm) == 1);
    {
        lean_object *ifs_err = lean_ctor_get(ifs_rpm, 0);
        fact("corpus.fs_dir.realpath_missing_variant", lean_ptr_tag(ifs_err));
        fact("corpus.fs_dir.realpath_missing_details_size",
             (long long)lean_string_size(lean_ctor_get(ifs_err, 1)));
    }
    lean_dec(ifs_rpm);
    lean_dec(ifs_missing);
    lean_object *ifs_ch = lean_chmod(ifs_sub2_obj, 0755);
    fact("corpus.fs_dir.chmod_ok", lean_ptr_tag(ifs_ch) == 0);
    lean_dec(ifs_ch);
    lean_object *ifs_cwd = lean_io_current_dir();
    fact("corpus.fs_dir.cwd_ok", lean_ptr_tag(ifs_cwd) == 0);
    fact("corpus.fs_dir.cwd_nonempty",
         lean_string_size(lean_ctor_get(ifs_cwd, 0)) > 1);
    lean_dec(ifs_cwd);
    snprintf(ifs_file, sizeof ifs_file, "%s/alpha.txt", ifs_sub2);
    remove(ifs_file);
    snprintf(ifs_file, sizeof ifs_file, "%s/beta.txt", ifs_sub2);
    remove(ifs_file);
    lean_object *ifs_rm = lean_io_remove_dir(ifs_sub2_obj);
    fact("corpus.fs_dir.rmsub_ok", lean_ptr_tag(ifs_rm) == 0);
    lean_dec(ifs_rm);
    lean_object *ifs_rm2 = lean_io_remove_dir(ifs_base_obj);
    fact("corpus.fs_dir.rmbase_ok", lean_ptr_tag(ifs_rm2) == 0);
    lean_dec(ifs_rm2);
    lean_dec(ifs_sub2_obj);
    lean_dec(ifs_sub_obj);
    lean_dec(ifs_base_obj);

    /* ---- fln-3gv slice 6b: the uv-decoded pair (io.cpp:1229-1245,
     * 1339-1350) — hardLink + removeFile, and the missing arm's uv shape:
     * osCode is the NEGATED errno wrapped to u32 and the details are
     * uv_strerror's strings, both distinct from the glibc decoder's. */
    char iuv_orig[160], iuv_link[160];
    snprintf(iuv_orig, sizeof iuv_orig, "/tmp/fln-uv-pair-%lld-orig",
             (long long)getpid());
    snprintf(iuv_link, sizeof iuv_link, "/tmp/fln-uv-pair-%lld-link",
             (long long)getpid());
    remove(iuv_orig);
    remove(iuv_link);
    {
        FILE *seed = fopen(iuv_orig, "w");
        fputs("payload", seed);
        fclose(seed);
    }
    lean_object *iuv_orig_obj = lean_mk_string(iuv_orig);
    lean_object *iuv_link_obj = lean_mk_string(iuv_link);
    lean_object *iuv_hl = lean_io_hard_link(iuv_orig_obj, iuv_link_obj);
    fact("corpus.uv_pair.hardlink_ok", lean_ptr_tag(iuv_hl) == 0);
    lean_dec(iuv_hl);
    lean_object *iuv_rm = lean_io_remove_file(iuv_link_obj);
    fact("corpus.uv_pair.remove_ok", lean_ptr_tag(iuv_rm) == 0);
    lean_dec(iuv_rm);
    lean_object *iuv_rm2 = lean_io_remove_file(iuv_link_obj);
    fact("corpus.uv_pair.remove_missing_err", lean_ptr_tag(iuv_rm2) == 1);
    {
        lean_object *iuv_err = lean_ctor_get(iuv_rm2, 0);
        fact("corpus.uv_pair.remove_missing_variant", lean_ptr_tag(iuv_err));
        fact("corpus.uv_pair.remove_missing_code",
             (long long)lean_ctor_get_uint32(iuv_err, 2 * sizeof(void *)));
        lean_object *iuv_details = lean_ctor_get(iuv_err, 1);
        const uint8_t *dp = (const uint8_t *)lean_string_cstr(iuv_details);
        long long dn = (long long)lean_string_size(iuv_details) - 1;
        long long dsum = 0;
        for (long long i = 0; i < dn; i++) {
            dsum += dp[i];
        }
        fact("corpus.uv_pair.remove_missing_details_bytes", dn);
        fact("corpus.uv_pair.remove_missing_details_bytesum", dsum);
    }
    lean_dec(iuv_rm2);
    lean_object *iuv_rm3 = lean_io_remove_file(iuv_orig_obj);
    fact("corpus.uv_pair.remove_orig_ok", lean_ptr_tag(iuv_rm3) == 0);
    lean_dec(iuv_rm3);
    lean_dec(iuv_link_obj);
    lean_dec(iuv_orig_obj);

    /* ---- fln-3gv slice 6c: the temp family (io.cpp:1248-1337). The
     * template paths are random, so the facts are the SHAPE invariants:
     * the pair structure, the tmp.XXXXXXXX basename, a write-read
     * roundtrip through the pair's own handle, and the tempdir's
     * existence — identical values from both runtimes. */
    lean_object *itmp_tf = lean_io_create_tempfile(lean_box(0));
    fact("corpus.temp.tempfile_ok", lean_ptr_tag(itmp_tf) == 0);
    {
        lean_object *itmp_pair = lean_ctor_get(itmp_tf, 0);
        lean_object *itmp_h = lean_ctor_get(itmp_pair, 0);
        lean_object *itmp_p = lean_ctor_get(itmp_pair, 1);
        const char *tp = lean_string_cstr(itmp_p);
        const char *base = strrchr(tp, '/');
        fact("corpus.temp.tempfile_basename_shape",
             base != NULL && strncmp(base + 1, "tmp.", 4) == 0 &&
                 strlen(base + 1) == 12);
        lean_object *itmp_body = lean_mk_string("temp payload");
        lean_object *itmp_put = lean_io_prim_handle_put_str(itmp_h, itmp_body);
        fact("corpus.temp.tempfile_put_ok", lean_ptr_tag(itmp_put) == 0);
        lean_dec(itmp_put);
        lean_dec(itmp_body);
        char itmp_path_copy[512];
        snprintf(itmp_path_copy, sizeof itmp_path_copy, "%s", tp);
        lean_dec(itmp_tf); /* handle finalizer fcloses -> publish */
        FILE *rb = fopen(itmp_path_copy, "r");
        long long rn = 0, rsum = 0;
        int rc_;
        while ((rc_ = fgetc(rb)) != EOF) {
            rn++;
            rsum += rc_;
        }
        fclose(rb);
        fact("corpus.temp.tempfile_roundtrip_bytes", rn);
        fact("corpus.temp.tempfile_roundtrip_bytesum", rsum);
        remove(itmp_path_copy);
    }
    lean_object *itmp_td = lean_io_create_tempdir(lean_box(0));
    fact("corpus.temp.tempdir_ok", lean_ptr_tag(itmp_td) == 0);
    {
        lean_object *itmp_dp = lean_ctor_get(itmp_td, 0);
        const char *dp = lean_string_cstr(itmp_dp);
        const char *dbase = strrchr(dp, '/');
        fact("corpus.temp.tempdir_basename_shape",
             dbase != NULL && strncmp(dbase + 1, "tmp.", 4) == 0 &&
                 strlen(dbase + 1) == 12);
        char probe_path[512];
        snprintf(probe_path, sizeof probe_path, "%s/probe", dp);
        FILE *pw = fopen(probe_path, "w");
        fact("corpus.temp.tempdir_writable", pw != NULL);
        if (pw) {
            fclose(pw);
            remove(probe_path);
        }
        char dcopy[512];
        snprintf(dcopy, sizeof dcopy, "%s", dp);
        lean_dec(itmp_td);
        rmdir(dcopy);
    }

    /* ---- fln-3gv slice 6d: the metadata family (io.cpp:1107-1165) — a
     * planted 137-byte file's size/nlink/type, the stat-vs-lstat symlink
     * split, and the missing arm's uv variant. Timestamps differ between
     * the two runtimes' runs, so the time fact is window membership, not
     * the raw value. */
    char imd_file[160], imd_sym[160];
    snprintf(imd_file, sizeof imd_file, "/tmp/fln-md-%lld-file",
             (long long)getpid());
    snprintf(imd_sym, sizeof imd_sym, "/tmp/fln-md-%lld-sym",
             (long long)getpid());
    remove(imd_sym);
    remove(imd_file);
    {
        FILE *pf = fopen(imd_file, "w");
        for (int i = 0; i < 137; i++) {
            fputc(7, pf);
        }
        fclose(pf);
    }
    long long imd_before = (long long)time(NULL);
    fact("corpus.metadata.symlink_planted", symlink(imd_file, imd_sym) == 0);
    lean_object *imd_file_obj = lean_mk_string(imd_file);
    lean_object *imd_md = lean_io_metadata(imd_file_obj);
    fact("corpus.metadata.file_ok", lean_ptr_tag(imd_md) == 0);
    {
        lean_object *md = lean_ctor_get(imd_md, 0);
        fact("corpus.metadata.file_size",
             (long long)lean_ctor_get_uint64(md, 2 * sizeof(void *)));
        fact("corpus.metadata.file_nlink",
             (long long)lean_ctor_get_uint64(md, 2 * sizeof(void *) + 8));
        fact("corpus.metadata.file_type",
             lean_ctor_get_uint8(md, 2 * sizeof(void *) + 16));
        lean_object *mtime = lean_ctor_get(md, 1);
        long long sec = (long long)(int)(unsigned)lean_unbox(lean_ctor_get(mtime, 0));
        long long imd_after = (long long)time(NULL);
        fact("corpus.metadata.file_mtime_in_window",
             sec >= imd_before - 5 && sec <= imd_after);
    }
    lean_dec(imd_md);
    lean_object *imd_sym_obj = lean_mk_string(imd_sym);
    lean_object *imd_smd = lean_io_metadata(imd_sym_obj);
    fact("corpus.metadata.sym_stat_type",
         lean_ctor_get_uint8(lean_ctor_get(imd_smd, 0), 2 * sizeof(void *) + 16));
    lean_dec(imd_smd);
    lean_object *imd_lmd = lean_io_symlink_metadata(imd_sym_obj);
    fact("corpus.metadata.sym_lstat_type",
         lean_ctor_get_uint8(lean_ctor_get(imd_lmd, 0), 2 * sizeof(void *) + 16));
    lean_dec(imd_lmd);
    lean_object *imd_missing = lean_mk_string("/tmp/fln-md-definitely-missing");
    lean_object *imd_err = lean_io_metadata(imd_missing);
    fact("corpus.metadata.missing_err", lean_ptr_tag(imd_err) == 1);
    fact("corpus.metadata.missing_variant",
         lean_ptr_tag(lean_ctor_get(imd_err, 0)));
    lean_dec(imd_err);
    lean_dec(imd_missing);
    lean_dec(imd_sym_obj);
    lean_dec(imd_file_obj);
    remove(imd_sym);
    remove(imd_file);

    /* ---- fln-3gv slice 7a: the env/misc family (io.cpp:81-83, 843-857,
     * 865-925, 964-1000, 1354-1407; process.cpp:330-352). */
    fact("corpus.env.setenv_ok",
         setenv("FLN_PROBE_ENV", "probe value", 1) == 0);
    lean_object *ienv_name = lean_mk_string("FLN_PROBE_ENV");
    lean_object *ienv_some = lean_io_getenv(ienv_name);
    fact("corpus.env.getenv_present_is_some", !lean_is_scalar(ienv_some));
    {
        lean_object *v = lean_ctor_get(ienv_some, 0);
        fact("corpus.env.getenv_bytes", (long long)lean_string_size(v) - 1);
    }
    lean_dec(ienv_some);
    lean_dec(ienv_name);
    lean_object *ienv_absent = lean_mk_string("FLN_PROBE_ENV_ABSENT");
    fact("corpus.env.getenv_absent_is_none",
         lean_io_getenv(ienv_absent) == lean_box(0));
    lean_dec(ienv_absent);
    {
        long long ms1 = (long long)lean_unbox(lean_io_mono_ms_now());
        long long ns = (long long)lean_unbox(lean_io_mono_nanos_now());
        long long ms2 = (long long)lean_unbox(lean_io_mono_ms_now());
        fact("corpus.env.mono_ms_monotone", ms1 <= ms2);
        fact("corpus.env.mono_ns_dominates", ns / 1000000 >= ms1);
    }
    fact("corpus.env.tid_nonzero", lean_io_get_tid() != 0);
    fact("corpus.env.pid_matches", lean_io_process_get_pid() == (uint32_t)getpid());
    {
        lean_object *ap = lean_io_app_path();
        fact("corpus.env.app_path_ok", lean_ptr_tag(ap) == 0);
        fact("corpus.env.app_path_nonempty",
             lean_string_size(lean_ctor_get(ap, 0)) > 1);
        lean_dec(ap);
    }
    fact("corpus.env.initializing_starts_true", lean_io_initializing() == 1);
    lean_io_mark_end_initialization();
    fact("corpus.env.initializing_flips", lean_io_initializing() == 0);
    {
        lean_object *rz = lean_io_get_random_bytes(0);
        fact("corpus.env.random_zero_ok", lean_ptr_tag(rz) == 0);
        fact("corpus.env.random_zero_empty",
             (long long)lean_sarray_size(lean_ctor_get(rz, 0)));
        lean_dec(rz);
        lean_object *r1 = lean_io_get_random_bytes(32);
        lean_object *r2 = lean_io_get_random_bytes(32);
        fact("corpus.env.random_fill",
             lean_sarray_size(lean_ctor_get(r1, 0)) == 32 &&
                 lean_sarray_size(lean_ctor_get(r2, 0)) == 32);
        fact("corpus.env.random_draws_differ",
             memcmp(lean_sarray_cptr(lean_ctor_get(r1, 0)),
                    lean_sarray_cptr(lean_ctor_get(r2, 0)), 32) != 0);
        lean_dec(r1);
        lean_dec(r2);
    }

    /* ---- fln-3gv slice 7b: the runtime skins and the byte-array slice
     * (io.cpp:1602-1626; object.cpp:2037-2040, 2584-2603). */
    {
        lean_object *ma = lean_alloc_ctor(0, 0, 8);
        fact("corpus.rt.mark_mt_identity",
             lean_runtime_mark_multi_threaded(ma) == ma);
        lean_object *mp = lean_alloc_ctor(0, 0, 8);
        fact("corpus.rt.mark_persistent_identity",
             lean_runtime_mark_persistent(mp) == mp);
        lean_object *fg = lean_alloc_ctor(0, 0, 8);
        fact("corpus.rt.forget_unit", lean_runtime_forget(fg) == lean_box(0));
        lean_object *vok = lean_alloc_sarray(1, 3, 3);
        memcpy(lean_sarray_cptr(vok), "abc", 3);
        fact("corpus.rt.validate_ok", lean_string_validate_utf8(vok));
        lean_sarray_cptr(vok)[1] = 0xFF;
        fact("corpus.rt.validate_bad", lean_string_validate_utf8(vok));
        lean_dec(vok);
        lean_object *csrc = lean_alloc_sarray(1, 10, 10);
        for (int i = 0; i < 10; i++) {
            lean_sarray_cptr(csrc)[i] = (uint8_t)(i + 1);
        }
        lean_object *cdst = lean_alloc_sarray(1, 4, 4);
        memset(lean_sarray_cptr(cdst), 0, 4);
        lean_object *cres = lean_byte_array_copy_slice(
            csrc, lean_box(2), cdst, lean_box(1), lean_box(5), true);
        {
            long long cn = (long long)lean_sarray_size(cres);
            long long csum = 0;
            for (long long i = 0; i < cn; i++) {
                csum += lean_sarray_cptr(cres)[i];
            }
            fact("corpus.rt.copy_slice_size", cn);
            fact("corpus.rt.copy_slice_bytesum", csum);
        }
        lean_dec(cres);
        lean_dec(csrc);
    }

    /* ---- fln-3gv slice 8a: the IO.Error pretty-printer + result_show_error
     * (Init/System/IOError.lean:271-298 through the generated IOError.c
     * dispatch; io.cpp:61-67). The full arm sweep is synthesized so it is
     * deterministic; one error rides the LIVE errno decoder end to end; and
     * show_error's stderr bytes are captured through a dup2'd fd 2. */
    {
        /* The Reference's printer is LEAN-COMPILED: its Nat.repr once-cells
         * live in module globals only initialize_Init_System_IOError fills
         * in (measured: without it l_Nat_reprFast faults inside
         * lean_obj_once_cold). Marrow's printer is native and carries no
         * such initializer, so the symbol is resolved dynamically — present
         * means run it, absent means nothing to run. One probe source, both
         * links, and NO fact is emitted about which case ran. */
        void *self = dlopen(NULL, RTLD_LAZY);
        void *init_sym = self ? dlsym(self, "initialize_Init_System_IOError") : NULL;
        if (init_sym) {
            lean_object *(*init_ioerror)(uint8_t) = (lean_object * (*)(uint8_t)) init_sym;
            lean_dec(init_ioerror(1));
        }

        errstr_facts("eof", lean_box(17));
        {
            lean_object *ue = lean_alloc_ctor(18, 1, 0);
            lean_ctor_set(ue, 0, lean_mk_string("Boom Msg"));
            errstr_facts("user", ue);
        }
        errstr_facts("already_some", errstr_err2(0, errstr_some("f"), "File Exists", 17));
        errstr_facts("already_none", errstr_err2(0, lean_box(0), "File Exists", 17));
        errstr_facts("other", errstr_err1(1, "Some Odd Error", 5));
        errstr_facts("busy", errstr_err1(2, "Device Or Resource Busy", 16));
        errstr_facts("vanished", errstr_err1(3, "Resource Vanished Here", 32));
        errstr_facts("unsupported", errstr_err1(4, "Not Supported Today", 95));
        errstr_facts("hardware", errstr_err1(5, "Dropped Details", 5));
        errstr_facts("unsatisfied", errstr_err1(6, "Dropped Too", 39));
        errstr_facts("illegal", errstr_err1(7, "Illegal Op Details", 25));
        errstr_facts("protocol", errstr_err1(8, "Protocol Details", 71));
        errstr_facts("time", errstr_err1(9, "Timed Out Details", 62));
        errstr_facts("interrupted",
                     errstr_err2(10, lean_mk_string("F.txt"), "Interrupted System Call", 4));
        errstr_facts("nofile",
                     errstr_err2(11, lean_mk_string("/nope/x"), "Ignored Details", 2));
        errstr_facts("invalid_some",
                     errstr_err2(12, errstr_some("cfg.txt"), "Invalid Argument", 22));
        errstr_facts("invalid_none",
                     errstr_err2(12, lean_box(0), "Invalid Argument", 22));
        errstr_facts("perm_some",
                     errstr_err2(13, errstr_some("/root/f"), "Permission Denied", 13));
        errstr_facts("perm_none", errstr_err2(13, lean_box(0), "Permission Denied", 13));
        errstr_facts("exhausted_some",
                     errstr_err2(14, errstr_some("q"), "Quota Exceeded", 122));
        errstr_facts("exhausted_none",
                     errstr_err2(14, lean_box(0), "Quota Exceeded", 122));
        errstr_facts("inapp_some", errstr_err2(15, errstr_some("d"), "Is A Directory", 21));
        errstr_facts("inapp_none", errstr_err2(15, lean_box(0), "Is A Directory", 21));
        errstr_facts("nosuch_some", errstr_err2(16, errstr_some("s"), "No Such Device", 6));
        errstr_facts("nosuch_none", errstr_err2(16, lean_box(0), "No Such Device", 6));
        /* Decapitalization edges: a non-ASCII first char is untouched, an
         * empty details prints empty, a digit first char is untouched. */
        errstr_facts("unicode_first", errstr_err1(1, "\xe2\x88\x80 Unicode First", 0));
        errstr_facts("empty_details", errstr_err1(3, "", 32));
        errstr_facts("digit_first", errstr_err1(1, "9 Numbers First", 1));

        /* End to end through the LIVE errno decoder: chmod on a missing
         * path; the noFileOrDirectory arm drops the glibc details, so the
         * string is host-independent. */
        {
            lean_object *cf = lean_mk_string("/fln-gauntlet-errstr-nope");
            lean_object *cr = lean_chmod(cf, 0);
            fact("corpus.errstr.live_is_error", lean_ptr_tag(cr) == 1);
            lean_object *le = lean_ctor_get(cr, 0);
            lean_inc(le);
            errstr_facts("live_chmod", le);
            lean_dec(cr);
            lean_dec(cf);
        }

        /* show_error: "uncaught exception: " + toString + '\n' on fd 2,
         * captured through a temp file so the bytes are a fact. */
        {
            lean_object *res =
                lean_io_result_mk_error(errstr_err1(1, "Boom Goes The Error", 7));
            char tmpl[] = "/tmp/fln-errstr-XXXXXX";
            int tf = mkstemp(tmpl);
            fact("corpus.errstr.show_error_capture_ready", tf >= 0);
            fflush(stderr);
            int saved = dup(2);
            dup2(tf, 2);
            lean_io_result_show_error(res);
            fflush(stderr);
            dup2(saved, 2);
            close(saved);
            long long n = (long long)lseek(tf, 0, SEEK_END);
            lseek(tf, 0, SEEK_SET);
            char buf[256];
            long long rd = (long long)read(tf, buf, sizeof buf);
            close(tf);
            unlink(tmpl);
            fact("corpus.errstr.show_error_bytes", n);
            fact("corpus.errstr.show_error_sum",
                 bytesum(buf, (size_t)(rd > 0 ? rd : 0)));
            lean_dec(res);
        }
    }

    /* ---- fln-3gv slice 8c: the stdin corpus cell — the first cell whose
     * subject is FD 0 ITSELF. The stream trio's closure fields cannot be
     * invoked cross-runtime (lean_apply_* is 7xe's), so the cell drives
     * the same ported prim the stdin stream's getLine field wraps, over a
     * handle opened at /dev/stdin AFTER a fixture is dup2'd onto fd 0 —
     * the process's own stdin, the real prim, all four getLine arms
     * (terminated, lossy 0xFF, unterminated tail, read at EOF). */
    {
        char sin_path[128];
        snprintf(sin_path, sizeof sin_path, "/tmp/fln-stdin-cell-%lld",
                 (long long)getpid());
        remove(sin_path);
        {
            FILE *seed = fopen(sin_path, "w");
            static const unsigned char sin_bytes[] = {
                's', 't', 'd', 'i', 'n', ' ', 'o', 'n', 'e', '\n',
                'b', 0xFF, 'r', '\n',
                'e', 'n', 'd'};
            fwrite(sin_bytes, 1, sizeof sin_bytes, seed);
            fclose(seed);
        }
        int sin_fd = open(sin_path, O_RDONLY);
        int sin_saved0 = dup(0);
        fact("corpus.stdin.redirect_ready", sin_fd >= 0 && sin_saved0 >= 0);
        dup2(sin_fd, 0);
        close(sin_fd);
        lean_object *sin_fname = lean_mk_string("/dev/stdin");
        lean_object *sin_mres = lean_io_prim_handle_mk(sin_fname, 0);
        fact("corpus.stdin.mk_ok", lean_ptr_tag(sin_mres) == 0);
        lean_object *sin_h = lean_ctor_get(sin_mres, 0);
        lean_inc(sin_h);
        lean_dec(sin_mres);
        lean_dec(sin_fname);
        for (int sin_i = 0; sin_i < 4; sin_i++) {
            static const char *const sin_names[4][4] = {
                {"corpus.stdin.l1_ok", "corpus.stdin.l1_bytes",
                 "corpus.stdin.l1_bytesum", "corpus.stdin.l1_chars"},
                {"corpus.stdin.l2_ok", "corpus.stdin.l2_bytes",
                 "corpus.stdin.l2_bytesum", "corpus.stdin.l2_chars"},
                {"corpus.stdin.l3_ok", "corpus.stdin.l3_bytes",
                 "corpus.stdin.l3_bytesum", "corpus.stdin.l3_chars"},
                {"corpus.stdin.l4_ok", "corpus.stdin.l4_bytes",
                 "corpus.stdin.l4_bytesum", "corpus.stdin.l4_chars"}};
            lean_object *sin_res = lean_io_prim_handle_get_line(sin_h);
            fact(sin_names[sin_i][0], lean_ptr_tag(sin_res) == 0);
            lean_object *sin_s = lean_ctor_get(sin_res, 0);
            long long sin_n = (long long)lean_string_size(sin_s) - 1;
            const uint8_t *sin_p = (const uint8_t *)lean_string_cstr(sin_s);
            long long sin_sum = 0;
            for (long long i = 0; i < sin_n; i++) {
                sin_sum += sin_p[i];
            }
            fact(sin_names[sin_i][1], sin_n);
            fact(sin_names[sin_i][2], sin_sum);
            fact(sin_names[sin_i][3], (long long)lean_string_len(sin_s));
            lean_dec(sin_res);
        }
        lean_dec(sin_h);
        dup2(sin_saved0, 0);
        close(sin_saved0);
        remove(sin_path);
    }

    /* ---- fln-3gv slice 8d: the panic-hook seam's native half — a
     * NON-FATAL panic's message routes through the thread-current stderr
     * STREAM (panic_eprintln's io_eprintln arm, object.cpp:130-137): one
     * putStr of msg ++ "\n". LEAN_BACKTRACE=0 keeps the Reference's
     * address-nondeterministic backtrace block out of the stream so the
     * file bytes are deterministic on both runtimes; exit_on_panic is
     * never set here, so the panic returns and the process continues. */
    {
        setenv("LEAN_BACKTRACE", "0", 1);
        char pnc_path[128];
        snprintf(pnc_path, sizeof pnc_path, "/tmp/fln-panic-stream-%lld",
                 (long long)getpid());
        remove(pnc_path);
        lean_object *pnc_fname = lean_mk_string(pnc_path);
        lean_object *pnc_hres = lean_io_prim_handle_mk(pnc_fname, 1);
        fact("corpus.panic_stream.mk_ok", lean_ptr_tag(pnc_hres) == 0);
        lean_object *pnc_h = lean_ctor_get(pnc_hres, 0);
        lean_inc(pnc_h);
        lean_dec(pnc_hres);
        lean_dec(pnc_fname);
        lean_object *pnc_old =
            lean_get_set_stderr(lean_stream_of_handle(pnc_h));
        lean_object *pnc_ret =
            lean_panic_fn(lean_box(0), lean_mk_string("gauntlet-nonfatal-panic"));
        fact("corpus.panic_stream.default_answered", pnc_ret == lean_box(0));
        lean_dec(lean_get_set_stderr(pnc_old));
        {
            FILE *back = fopen(pnc_path, "r");
            char pbuf[128];
            size_t prd = back ? fread(pbuf, 1, sizeof pbuf, back) : 0;
            if (back) {
                fclose(back);
            }
            fact("corpus.panic_stream.bytes", (long long)prd);
            fact("corpus.panic_stream.sum", bytesum(pbuf, prd));
        }
        remove(pnc_path);
        unsetenv("LEAN_BACKTRACE");
    }

    /* ---- fln-3gv slice 8e: the float once cells and the task-state core
     * symbol (object.cpp:2903-2921, 1260-1265). */
    {
        static lean_once_cell_t f32_cell;
        static float f32_loc;
        static lean_once_cell_t f64_cell;
        static double f64_loc;
        float fa = lean_float32_once_cold(&f32_loc, &f32_cell, once_init_f32);
        float fb = lean_float32_once_cold(&f32_loc, &f32_cell, once_init_f32);
        double da = lean_float_once_cold(&f64_loc, &f64_cell, once_init_f64);
        double db = lean_float_once_cold(&f64_loc, &f64_cell, once_init_f64);
        fact("corpus.once_float.f32_value_x4", fa == 1.5f && fb == 1.5f && f32_loc == 1.5f);
        fact("corpus.once_float.f64_value_x4", da == 2.25 && db == 2.25 && f64_loc == 2.25);
        fact("corpus.once_float.inits_exactly_two", errstr_float_once_calls);
        lean_object *ts_t = lean_task_pure(lean_box(9));
        fact("corpus.once_float.task_state_core_agrees",
             lean_io_get_task_state_core(ts_t) == lean_io_get_task_state(ts_t) &&
                 lean_io_get_task_state_core(ts_t) == 2);
        lean_dec(ts_t);
    }

    /* ---- franken_lean-83r export slice: the decode/mk-error trio under
     * the pin's exported names, bound END TO END through the landed
     * pretty-printer over aggregate errno sweeps — any single-arm
     * divergence (variant, code, details, filename handling) moves the
     * rolling totals. The uv sweep keeps a non-null fname throughout: the
     * pin's bare-String arms lean_assert on null (release UB), which ours
     * refuses typed — a disclosed deviation, deliberately outside this
     * differential. The io null sweep skips EINTR/ENOENT (2, 4), whose
     * arms require a filename in both runtimes. */
    {
        lean_object *dec_f = lean_mk_string("sweep.txt");
        long long dc = 0, db = 0, ds = 0;
        for (int e = 1; e <= 140; e++) {
            lean_object *err = lean_decode_io_error(e, dec_f);
            lean_object *s = lean_io_error_to_string(err);
            dc++;
            db += (long long)lean_string_size(s) - 1;
            ds += bytesum(lean_string_cstr(s), lean_string_size(s) - 1);
            lean_dec(s);
        }
        fact("corpus.decode.io_fname_count", dc);
        fact("corpus.decode.io_fname_bytes", db);
        fact("corpus.decode.io_fname_sum", ds);
        dc = db = ds = 0;
        for (int e = 1; e <= 140; e++) {
            if (e == 2 || e == 4) {
                continue; /* bare-fname arms: filename required both sides */
            }
            lean_object *err = lean_decode_io_error(e, NULL);
            lean_object *s = lean_io_error_to_string(err);
            dc++;
            db += (long long)lean_string_size(s) - 1;
            ds += bytesum(lean_string_cstr(s), lean_string_size(s) - 1);
            lean_dec(s);
        }
        fact("corpus.decode.io_null_count", dc);
        fact("corpus.decode.io_null_bytes", db);
        fact("corpus.decode.io_null_sum", ds);
        dc = db = ds = 0;
        for (int e = 1; e <= 140; e++) {
            lean_object *err = lean_decode_uv_error(-e, dec_f);
            lean_object *s = lean_io_error_to_string(err);
            dc++;
            db += (long long)lean_string_size(s) - 1;
            ds += bytesum(lean_string_cstr(s), lean_string_size(s) - 1);
            lean_dec(s);
        }
        fact("corpus.decode.uv_count", dc);
        fact("corpus.decode.uv_bytes", db);
        fact("corpus.decode.uv_sum", ds);
        lean_dec(dec_f);
        /* Spot arms: the EFAULT-default join, an unmapped errno, and the
         * userError identity through the exported ctor. */
        {
            lean_object *s = lean_io_error_to_string(lean_decode_io_error(14, NULL));
            fact("corpus.decode.efault_bytes", (long long)lean_string_size(s) - 1);
            fact("corpus.decode.efault_sum",
                 bytesum(lean_string_cstr(s), lean_string_size(s) - 1));
            lean_dec(s);
            lean_object *u = lean_io_error_to_string(
                lean_mk_io_user_error(lean_mk_string("User Boom")));
            fact("corpus.decode.user_bytes", (long long)lean_string_size(u) - 1);
            fact("corpus.decode.user_sum",
                 bytesum(lean_string_cstr(u), lean_string_size(u) - 1));
            lean_dec(u);
        }
        /* The mk_io_error ctor family, spot-checked one per shape class
         * through the printer (the sweeps above already pin the layouts). */
        {
            lean_object *m1 = lean_io_error_to_string(
                lean_mk_io_error_already_exists(17, lean_mk_string("File Exists")));
            fact("corpus.decode.mk_plain_bytes", (long long)lean_string_size(m1) - 1);
            fact("corpus.decode.mk_plain_sum",
                 bytesum(lean_string_cstr(m1), lean_string_size(m1) - 1));
            lean_dec(m1);
            lean_object *m2 = lean_io_error_to_string(lean_mk_io_error_no_file_or_directory(
                lean_mk_string("gone.txt"), 2, lean_mk_string("Ignored")));
            fact("corpus.decode.mk_bare_bytes", (long long)lean_string_size(m2) - 1);
            fact("corpus.decode.mk_bare_sum",
                 bytesum(lean_string_cstr(m2), lean_string_size(m2) - 1));
            lean_dec(m2);
            fact("corpus.decode.mk_eof_is_box17",
                 lean_mk_io_error_eof(lean_box(0)) == lean_box(17));
        }
    }

    /* ---- franken_lean-83r: the dbg trio through the same captured-stream
     * apparatus as the panic cell — trace writes msg ++ newline through the
     * current stderr stream and answers the applied thunk; if_shared fires
     * only on a non-exclusive heap arg; sleep(0) just applies. */
    {
        char dbg_path[128];
        snprintf(dbg_path, sizeof dbg_path, "/tmp/fln-dbg-stream-%lld",
                 (long long)getpid());
        remove(dbg_path);
        lean_object *dbg_fname = lean_mk_string(dbg_path);
        lean_object *dbg_hres = lean_io_prim_handle_mk(dbg_fname, 1);
        fact("corpus.dbg.mk_ok", lean_ptr_tag(dbg_hres) == 0);
        lean_object *dbg_h = lean_ctor_get(dbg_hres, 0);
        lean_inc(dbg_h);
        lean_dec(dbg_hres);
        lean_dec(dbg_fname);
        lean_object *dbg_old = lean_get_set_stderr(lean_stream_of_handle(dbg_h));
        lean_object *tfn = lean_alloc_closure((void *)probe_forty_two, 1, 0);
        lean_object *tr = lean_dbg_trace(lean_mk_string("dbg line one"), tfn);
        fact("corpus.dbg.trace_result", (long long)lean_unbox(tr));
        lean_object *sfn = lean_alloc_closure((void *)probe_forty_two, 1, 0);
        lean_object *sr = lean_dbg_sleep(0, sfn);
        fact("corpus.dbg.sleep_result", (long long)lean_unbox(sr));
        /* if_shared: an exclusive arg stays silent; a shared one fires.
         * (s is never settled by the pin's own body — the probe mirrors
         * the call shape and lets both leak identically on both sides.) */
        lean_object *excl = lean_mk_string("exclusive-arg");
        fact("corpus.dbg.if_shared_excl_passthrough",
             lean_dbg_trace_if_shared(lean_mk_string("silent"), excl) == excl);
        lean_dec(excl);
        lean_object *shared = lean_mk_string("shared-arg");
        lean_inc(shared);
        fact("corpus.dbg.if_shared_shared_passthrough",
             lean_dbg_trace_if_shared(lean_mk_string("loud"), shared) == shared);
        lean_dec(shared);
        lean_dec(shared);
        lean_dec(lean_get_set_stderr(dbg_old));
        {
            FILE *back = fopen(dbg_path, "r");
            char dbuf[256];
            size_t drd = back ? fread(dbuf, 1, sizeof dbuf, back) : 0;
            if (back) {
                fclose(back);
            }
            fact("corpus.dbg.stream_bytes", (long long)drd);
            fact("corpus.dbg.stream_sum", bytesum(dbuf, drd));
        }
        remove(dbg_path);
    }
}

int main(int argc, char **argv) {
    /* Line-buffered facts: a mutant that HANGS mid-run (a real divergence
     * class — 83r-M1 deadlocks the promise drop-to-none cell) is killed by
     * the drill's timeout, and every fact emitted before the hang must
     * already be on disk. Identical in both runtimes; flush timing only,
     * never bytes. */
    setvbuf(stdout, NULL, _IOLBF, 0);
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
    /* fln-3gv slice 8b exit-parity modes: the marker has NO newline, so
     * under the _IOLBF set above it sits in the stdio buffer when the prim
     * fires — exit(3) flushes it, _Exit drops it, and that split IS the
     * observable difference between the two prims. */
    if (argc > 1 && strcmp(argv[1], "exit-flush") == 0) {
        printf("EXIT-FLUSH-MARKER");
        lean_io_exit(42);
        return 99; /* unreachable: exit(3) terminates with 42 */
    }
    if (argc > 1 && strcmp(argv[1], "force-exit") == 0) {
        printf("FORCE-EXIT-MARKER");
        lean_io_force_exit(43);
        return 99; /* unreachable: _Exit terminates with 43, marker dropped */
    }
    facts_mode();
    return 0;
}
