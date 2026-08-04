# Miri concurrency guard for Marrow (fln-unsafe-abi + fln-rt)

The answer to "can any of this run under a sanitizer in CI" is **yes**, it is
cheap, and it demonstrably catches the real defect. This file is the runnable
spec; bead `fln-nhf5` tracks wiring it into CI, which is not this crate's domain.

## The command

```bash
rustup component add --toolchain nightly-2026-07-13-x86_64-unknown-linux-gnu miri rust-src

MIRIFLAGS="-Zmiri-disable-isolation -Zmiri-ignore-leaks" \
  cargo +nightly-2026-07-13 miri test -p fln-unsafe-abi --lib \
    mark_mt_negates_and_atomics_conserve
MIRIFLAGS="-Zmiri-disable-isolation -Zmiri-ignore-leaks" \
  cargo +nightly-2026-07-13 miri test -p fln-unsafe-abi --lib \
    mt_object_dies_on_last_dec
MIRIFLAGS="-Zmiri-disable-isolation -Zmiri-ignore-leaks" \
  cargo +nightly-2026-07-13 miri test -p fln-unsafe-abi --lib \
    rc_clone_and_drop_balance
MIRIFLAGS="-Zmiri-disable-isolation -Zmiri-ignore-leaks" \
  cargo +nightly-2026-07-13 miri test -p fln-rt --test region_engine \
    concurrent_publication
```

Measured wall time, whole set: **~12 s** (9.26 + 0.39 + 0.35 + 2.02).

## Why it is a targeted set and not `miri test`

Running the *whole* fln-unsafe-abi suite under Miri exceeds ten minutes and was
killed — Miri is roughly two orders of magnitude slower than native, and most of
those 39 tests are layout and codec assertions with no threads in them, so they
buy nothing for the cost. The four above are the ones that actually spawn
threads or contend on a shared artifact. Naming them explicitly is the point:
the guard covers the concurrency protocols, and this file says so rather than
implying whole-crate coverage.

## Why each flag

| Flag | Reason |
|---|---|
| `-Zmiri-disable-isolation` | `region_engine` writes real files; the publication test is *about* the filesystem rename, so it cannot be stubbed. |
| `-Zmiri-ignore-leaks` | `mt_object_dies_on_last_dec` enables the ownership shadow, which **quarantines** freed memory instead of releasing it — deliberate, and exactly what Miri's leak checker reports. Without this flag the run fails on intentional retention. |

## Proof that it catches the real thing

Not asserted — executed. With the `dec_ref` mode probe reverted to the plain
`ptr::read` it had before commit `8cd1d3b`, on the pinned toolchain, against the
real crate:

```
error: Undefined Behavior: Data race detected between (1) non-atomic read on
thread `unnamed-2` and (2) atomic read-modify-write on thread `unnamed-3`
  --> crates/fln-unsafe-abi/src/rc.rs:167:13    (the reverted probe)
  --> crates/fln-unsafe-abi/src/rc.rs:147:18    (the atomic fetch_sub)
```

Restored, the same command passes. So this is a guard, not a green rubber stamp:
it fails on the defect it exists to prevent.

## What this does NOT cover

* **`fln-unsafe-region`** (the mmap primitive). Miri cannot execute `mmap`, and
  that crate is not in this domain. The region *engine* in fln-rt is covered
  because it is pure slice arithmetic; the *mapping* under it is not.
* **The exported C surface under a real C caller.** Miri runs Rust; the stage0
  ABI gauntlet is the instrument for that, not this.
* ~~**TSAN.**~~ **Attempted and it works** — see the section below. This entry
  said TSAN was worth attempting; it has now been attempted, measured, and
  proven to fail on the same reverted defect.
* **Everything single-threaded.** This is a concurrency guard. It is not a
  substitute for the ordinary suite, which still runs natively.

## The second detector: ThreadSanitizer (bead `fln-nhf5`)

**TSAN runs at the pin.** The earlier claim that it could not was wrong for the
same reason the earlier claim about Miri was wrong: nobody had installed
`rust-src` for the pinned nightly and tried. `-Zbuild-std` rebuilds `std` under
the same `-Zsanitizer=thread`, which removes the ABI-mismatch refusal
(`mixing -Zsanitizer will cause an ABI mismatch ... incompatible with unset
-Zsanitizer in dependency memchr`) that made it look impossible.

```bash
export CARGO_TARGET_DIR=/some/isolated/dir   # see the warning below
export RUSTFLAGS="-Zsanitizer=thread"
export RUSTDOCFLAGS="-Zsanitizer=thread"
T=x86_64-unknown-linux-gnu

cargo +nightly-2026-07-13 test -Zbuild-std --target $T \
  -p fln-unsafe-abi --lib mark_mt_negates_and_atomics_conserve
cargo +nightly-2026-07-13 test -Zbuild-std --target $T \
  -p fln-unsafe-abi --lib mt_object_dies_on_last_dec
cargo +nightly-2026-07-13 test -Zbuild-std --target $T \
  -p fln-unsafe-abi --lib rc_clone_and_drop_balance
cargo +nightly-2026-07-13 test -Zbuild-std --target $T \
  -p fln-rt --test region_engine concurrent_publication
```

Measured: **~25 s** for the one-time `-Zbuild-std` compile, then **under 3 s**
for all four lanes warm — four times cheaper than the Miri set, because TSAN
instruments native code instead of interpreting it. Same four tests, because the
workload a detector needs is the same workload.

### THE TRAP: a green libtest line and a failing process

On the planted defect, the run prints

```
test tests::mark_mt_negates_and_atomics_conserve ... ok
test result: ok. 1 passed; 0 failed; ...
```

**and exits 66.** TSAN reports at process teardown, after libtest has already
declared the test green. A CI lane that greps for `test result: ok`, or that
reads the last line of output, will report a clean run while a data race was
detected and printed. **The exit code is the only reliable signal**; the race
text is on stderr above a summary line, not in the libtest verdict. Any wiring
of these commands must assert `exit == 0` and must not infer success from the
absence of an error line.

### Proof that it catches the real thing

Not asserted — executed, the same way and against the same defect as the Miri
half. With `dec_ref`'s mode probe reverted to the plain `ptr::read` it had
before `8cd1d3b`, on the pinned toolchain, against the real crate:

```
WARNING: ThreadSanitizer: data race (pid=1607964)
SUMMARY: ThreadSanitizer: data race .../core/src/ptr/mod.rs:1731:9
         in core::ptr::read::<i32>
WARNING: ThreadSanitizer: data race (pid=1607964)
SUMMARY: ThreadSanitizer: data race .../core/src/sync/atomic.rs:4002:24
         in core::sync::atomic::atomic_sub::<i32, i32>
exit 66
```

Restored, the same command exits 0. Note that the two detectors name the *same*
race from opposite ends — Miri says "non-atomic read versus atomic
read-modify-write" and points at `rc.rs`; TSAN points at the `core` primitives
each side bottoms out in. That agreement is worth something precisely because
neither was derived from the other.

### Why two detectors rather than the better one

Neither subsumes the other, so a single detector agreeing with itself certifies
nothing about what it cannot see:

| | Miri | TSAN |
|---|---|---|
| threads | interpreted, scheduled by Miri | real OS threads |
| allocator | Miri's own | the real one |
| memory model | stricter than hardware; catches UB with no observable effect | reports races the run actually exhibited |
| cost (this set) | ~12 s | ~3 s warm, ~25 s cold |
| `mmap`, real syscalls | cannot execute | executes |

Miri finds UB that never misbehaves on this hardware — which is exactly the
class the fixed defect belonged to, since aligned 32-bit loads do not tear. TSAN
finds what the schedule actually produced, in the real allocator, and can run
the parts Miri refuses. Running one because it is stricter, or the other because
it is faster, would be choosing which half of the evidence to discard.

### Isolate the target directory

`-Zsanitizer=thread` in `RUSTFLAGS` invalidates every cached artifact built
without it. Sharing the repository's usual `CARGO_TARGET_DIR` forces a full
rebuild of the workspace for whoever runs next, and then another when they
rebuild without it. Point these lanes at their own directory.

## The recurring hazard, for whoever audits Marrow next

All three defects found in this crate so far are **the same shape**: the
single-threaded-to-multi-threaded ownership transition.

1. The ST refcount could overflow and *wrap into the MT encoding* — a positive
   count becoming negative silently reclassifies the object's threading
   discipline (fixed: `checked_add` that faults in every profile).
2. Every mode probe read `m_rc` non-atomically while MT threads did atomic RMWs
   on it — the read that *decides* which discipline applies was itself racing
   (fixed: `Relaxed` loads).
3. Region publication keyed its staging file per-process, so two threads
   publishing one target shared it — a transition from one writer to many with
   no per-writer identity (fixed: per-thread staging names).

The pattern: **wherever this crate decides "how many owners does this have", the
decision itself is unsynchronised.** Start there. The tri-state encoding is a
concurrency protocol wearing an integer's clothes, and a wrong answer does not
error — it silently reinterprets the object as a different kind.
